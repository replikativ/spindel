(ns org.replikativ.spindel.pubsub.fork-ctx-reentrancy-test
  "Reentrancy bug repro: pubsub round-trip inside an outer spin where
   the source/mult/pub are constructed on a fork-context.

   Mimics the topology dvergr.bus uses:
     mailbox → mult → tap → pub → topic-mult → tap

   The failing pattern in dvergr.proposals/propose!:
     (sp/spawn!
       (sp/spin
         (let [fork  (fork-context parent-ctx)
               ;; build bus (mailbox+mult+pub) on fork-ctx
               ;; subscribe to topic A (worker)
               ;; subscribe to topic B (asker)
               ;; post message to topic A
               ;; participant spin reads A, posts reply to topic B
               reply (await ...on topic B sub...)]
            ...)))

   This namespace strips dvergr away to test whether the bug lives in
   spindel's lazy pump-start + fork-context interaction."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.pubsub.mult :as mult]
            [org.replikativ.spindel.pubsub.pub :as pub]
            [org.replikativ.spindel.pubsub.buffer :as buf]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.combinators :as comb]
            [org.replikativ.spindel.core :as sp]
            [org.replikativ.spindel.effects.await :refer [await]]
            [is.simm.partial-cps.sequence :refer [anext]]))

;; A "bus" = mailbox + mult + a single :to-keyed pub over a tap of the mult.
;; This mimics dvergr.bus minus the type-pub and log-drain — the smallest
;; surface that triggers the deadlock.
(defn- make-bus
  [bus-ctx]
  (binding [ec/*execution-context* bus-ctx]
    (let [source  (sync/create-mailbox bus-ctx)
          m       (mult/mult source)
          to-tap  (mult/tap m (buf/fixed-buffer 256))
          to-pub  (pub/pub to-tap :to)]
      {:ctx bus-ctx :source source :mult m :to-pub to-pub})))

(defn- bus-subscribe!
  [bus topic-val buffer]
  (binding [ec/*execution-context* (:ctx bus)]
    (pub/sub (:to-pub bus) topic-val buffer)))

(defn- bus-post!
  [bus msg]
  (binding [ec/*execution-context* (:ctx bus)]
    (sync/post! (:source bus) msg)))

(def ^:dynamic *trace* (atom []))

(defn- log-trace [tag & extra]
  (swap! *trace* conj (vec (cons tag extra))))

(defn- spawn-echo-worker!
  "Subscribe a worker on [:to worker-id]; on each msg, post a reply back to
   the sender."
  [bus worker-id]
  (let [sub (bus-subscribe! bus worker-id (buf/fixed-buffer 16))]
    (binding [ec/*execution-context* (:ctx bus)]
      (sp/spawn!
        (spin
          (log-trace :worker-spin-start)
          (loop [s sub]
            (log-trace :worker-awaiting)
            (when-let [[msg r] (await (anext s))]
              (log-trace :worker-got msg)
              (bus-post! bus {:to (:from msg) :from worker-id :content "reply"})
              (log-trace :worker-posted-reply)
              (recur r))))))
    sub))

(deftest fork-ctx-pubsub-inline-roundtrip
  (testing "Round-trip over a pub built on a fork-context's source, all
            happening inside ONE outer spin. Mirrors dvergr.proposals/propose!'s
            (fork-room + join + ask) inline pattern. Without the bug, the
            outer spin's await returns the worker's reply."
    (reset! *trace* [])
    (let [parent-ctx (ctx/create-execution-context)
          worker-id  :worker
          done       (promise)]
      (binding [ec/*execution-context* parent-ctx]
        (sp/spawn!
          (spin
            (log-trace :outer-spin-start)
            (let [;; All of these happen inside the outer spin frame ─────
                  fork-ctx (ctx/fork-context parent-ctx)
                  _ (log-trace :forked)
                  bus      (make-bus fork-ctx)
                  _ (log-trace :bus-made)
                  _worker  (spawn-echo-worker! bus worker-id)
                  _ (log-trace :worker-spawned)
                  asker-id (keyword (str "ask-" (rand-int 1000000)))
                  asker-sub (bus-subscribe! bus asker-id (buf/fixed-buffer 1))
                  _ (log-trace :asker-subscribed)
                  _        (bus-post! bus {:to worker-id :from asker-id
                                           :content "go"})
                  _ (log-trace :posted-go)
                  [reply _] (await (anext asker-sub))]
              (log-trace :outer-got-reply reply)
              (deliver done {:reply (:content reply)})))))
      (let [result (deref done 3000 :TIMEOUT)]
        (ctx/stop-context! parent-ctx)
        (println "TRACE:" (pr-str @*trace*))
        (is (= {:reply "reply"} result)
            "Expected the worker's reply to flow back through the pub.")))))

(deftest fork-ctx-pubsub-bus-built-outside
  (testing "CONTROL: same flow but bus + worker built OUTSIDE the outer
            spin. Should pass — confirms the bug is specific to the
            inline pattern, not the topology."
    (let [parent-ctx (ctx/create-execution-context)
          worker-id  :worker
          fork-ctx   (binding [ec/*execution-context* parent-ctx]
                       (ctx/fork-context parent-ctx))
          bus        (make-bus fork-ctx)
          _worker    (spawn-echo-worker! bus worker-id)
          asker-id   (keyword (str "ask-" (rand-int 1000000)))
          asker-sub  (binding [ec/*execution-context* fork-ctx]
                       (bus-subscribe! bus asker-id (buf/fixed-buffer 1)))
          done       (promise)]
      (binding [ec/*execution-context* fork-ctx]
        (sp/spawn!
          (spin
            (bus-post! bus {:to worker-id :from asker-id :content "go"})
            (let [[reply _] (await (anext asker-sub))]
              (deliver done {:reply (:content reply)})))))
      (let [result (deref done 3000 :TIMEOUT)]
        (ctx/stop-context! parent-ctx)
        (is (= {:reply "reply"} result))))))

(deftest fork-ctx-pubsub-inline-no-fork
  (testing "CONTROL 2: same as the failing test but uses parent-ctx for
            the bus (no fork-context). Isolates whether fork-context is
            the necessary ingredient."
    (let [parent-ctx (ctx/create-execution-context)
          worker-id  :worker
          done       (promise)]
      (binding [ec/*execution-context* parent-ctx]
        (sp/spawn!
          (spin
            (let [bus       (make-bus parent-ctx)   ; same ctx, no fork
                  _worker   (spawn-echo-worker! bus worker-id)
                  asker-id  (keyword (str "ask-" (rand-int 1000000)))
                  asker-sub (bus-subscribe! bus asker-id (buf/fixed-buffer 1))
                  _         (bus-post! bus {:to worker-id :from asker-id
                                            :content "go"})
                  [reply _] (await (anext asker-sub))]
              (deliver done {:reply (:content reply)})))))
      (let [result (deref done 3000 :TIMEOUT)]
        (ctx/stop-context! parent-ctx)
        (is (= {:reply "reply"} result))))))

(deftest fork-ctx-mult-only-inline-roundtrip
  (testing "Strip the pub layer. Just: source mailbox → mult → two taps.
            One tap consumed by worker, second tap consumed by outer spin.
            If THIS fails, the bug is in mult/fork-ctx interaction. If
            it passes, the bug is specifically in the pub layer."
    (reset! *trace* [])
    (let [parent-ctx (ctx/create-execution-context)
          done       (promise)]
      (binding [ec/*execution-context* parent-ctx]
        (sp/spawn!
          (spin
            (log-trace :outer-start)
            (let [fork-ctx (ctx/fork-context parent-ctx)
                  _ (log-trace :forked)
                  source    (binding [ec/*execution-context* fork-ctx]
                              (sync/create-mailbox fork-ctx))
                  m         (binding [ec/*execution-context* fork-ctx]
                              (mult/mult source))
                  worker-tap (binding [ec/*execution-context* fork-ctx]
                               (mult/tap m (buf/fixed-buffer 16)))
                  result-tap (binding [ec/*execution-context* fork-ctx]
                               (mult/tap m (buf/fixed-buffer 16)))
                  _ (log-trace :taps-made)
                  _worker (binding [ec/*execution-context* fork-ctx]
                            (sp/spawn!
                              (spin
                                (log-trace :worker-start)
                                (when-let [[msg _] (await (anext worker-tap))]
                                  (log-trace :worker-got msg)
                                  ;; Post "reply" back to source so result-tap sees it
                                  (binding [ec/*execution-context* fork-ctx]
                                    (sync/post! source {:k :reply :for msg}))
                                  (log-trace :worker-posted)))))
                  _ (log-trace :worker-spawned)
                  _ (binding [ec/*execution-context* fork-ctx]
                      (sync/post! source {:k :go}))
                  _ (log-trace :posted-go)
                  [first-msg _] (await (anext result-tap))
                  _ (log-trace :outer-got-first first-msg)
                  ;; If first-msg is :go, await again for :reply
                  [r _] (if (= :reply (:k first-msg))
                          [first-msg nil]
                          (await (anext result-tap)))]
              (log-trace :outer-got-final r)
              (deliver done r)))))
      (let [result (deref done 3000 :TIMEOUT)
            ;; Reach into the TapSeq's internal state to see what's in result-tap's buffer
            inspect-tap (fn [tap label]
                          (try
                            (let [tsa (.-tap-state-atom tap)
                                  state @tsa
                                  buffer (:buffer state)]
                              (println label "buffer-count:"
                                       (when buffer (count buffer))
                                       "closed?:" (when-let [c (:closed? state)] @c)))
                            (catch Throwable e
                              (println label "inspect error:" (.getMessage e)))))]
        (when-let [last-trace @*trace*]
          (println "MULT-ONLY TRACE:" (pr-str last-trace)))
        (ctx/stop-context! parent-ctx)
        (is (= :reply (:k result))
            "Reply should flow through second tap.")))))

(deftest fork-ctx-pubsub-inline-using-with-context
  (testing "Same as failing test but NO outer spawn — uses with-context
            to bind parent-ctx around the work without an outer Spin.
            This isolates whether the bug requires being inside a Spin
            CPS body, or whether merely binding parent ctx then forking
            inline reproduces it."
    (let [parent-ctx (ctx/create-execution-context)
          worker-id  :worker
          done       (promise)]
      (binding [ec/*execution-context* parent-ctx]
        (let [fork-ctx (ctx/fork-context parent-ctx)
              bus     (make-bus fork-ctx)
              _worker (spawn-echo-worker! bus worker-id)
              asker-id (keyword (str "ask-" (rand-int 1000000)))
              asker-sub (bus-subscribe! bus asker-id (buf/fixed-buffer 1))]
          (bus-post! bus {:to worker-id :from asker-id :content "go"})
          (binding [ec/*execution-context* fork-ctx]
            (sp/spawn!
              (spin
                (let [[reply _] (await (anext asker-sub))]
                  (deliver done {:reply (:content reply)})))))))
      (let [result (deref done 3000 :TIMEOUT)]
        (ctx/stop-context! parent-ctx)
        (is (= {:reply "reply"} result)
            "Should work since the setup happened outside the spin.")))))
