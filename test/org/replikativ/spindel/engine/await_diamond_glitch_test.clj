(ns org.replikativ.spindel.engine.await-diamond-glitch-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [is.simm.partial-cps.async :as cps]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.executor :as ex]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.engine.impl.graph :as graph]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.core :as sc]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.test-async :refer [await-drain]]))

(defn- cached [rt s]
  (let [r (rtp/current-result rt (sc/spin-id s))]
    [(:variant r) (:payload r)]))

(defn- start! [s]
  (let [result (promise)]
    (s #(deliver result [:ok %]) #(deliver result [:error %]))
    (let [v (deref result 1000 ::timeout)]
      (is (not= ::timeout v) "initial body completes within a bounded wait")
      v)))

(deftest synchronous-await-diamond
  ;; Vary addresses to exercise both sibling completion orders.
  (doseq [nonce (range 8)]
    (let [rt (ctx/create-execution-context :executor (ex/synchronous-executor))]
      (try
        (binding [ec/*execution-context* rt cps/*in-trampoline* false]
          (dotimes [_ nonce] (sig/signal 0))
          (let [a (sig/signal 0)
                seen (atom [])
                prefix (atom 0)
                between (atom [])
                b (spin (* 2 (iv/get-new (track a))))
                c (spin (* 3 (iv/get-new (track a))))
                d (spin (swap! prefix inc)
                        (let [bv (await b)
                              _ (swap! between conj bv)
                              cv (await c)]
                          (swap! seen conj [bv cv])
                          (+ bv cv)))]
            (is (= [:ok 0] (start! d)))
            (doseq [x [-1 2 2]]
              (reset! a x)
              (await-drain rt)
              (is (= (* 5 x) (:payload (rtp/current-result rt (sc/spin-id d))))))
            (is (= [[0 0] [-2 -3] [4 6] [4 6]] @seen) (str "nonce " nonce))
            (is (= [0 -2 4 4] @between) "resume at the earliest affected await once")
            (is (= 1 @prefix) "keep the captured prefix; never restart the body")))
        (finally (ctx/close-context! rt))))))

(deftest unaffected-earlier-await-keeps-its-captured-slice
  (doseq [mode [:following :frozen]]
    (let [rt (ctx/create-execution-context :executor (ex/synchronous-executor))]
      (try
        (binding [ec/*execution-context* rt cps/*in-trampoline* false]
          (let [a (sig/signal [])
                b-source (sig/signal 0)
                c-source (sig/signal 0)
                seen (atom [])
                between (atom [])
                b (spin (iv/get-new (track b-source)))
                c (spin (iv/get-new (track c-source)))
                d (spin (let [bv (await b)
                              ia (track a)
                              _ (swap! between conj bv)
                              cv (await c)]
                          (swap! seen conj [ia bv cv])
                          (+ bv cv)))]
            (is (= [:ok 0] (start! d)))
            (swap! a conj :x)
            (await-drain rt)
            (let [captured (ffirst (reverse @seen))
                  fork (ctx/fork-context rt :mode mode)]
              (try
                (binding [ec/*execution-context* fork]
                  (reset! c-source 3)
                  (await-drain fork)
                  (is (= [captured 0 3] (last @seen)))
                  (is (identical? captured (first (last @seen)))
                      "later re-entry retains the captured Interval object")
                  (is (= [0 0] @between) "an unaffected earlier await is not resumed")
                  (is (= [:ok 3] (cached fork d)))
                  (reset! b-source 2)
                  (await-drain fork)
                  (is (= [[:x] 2 3]
                         (let [[ia bv cv] (last @seen)]
                           [(iv/get-new ia) bv cv])))
                  (is (= [0 0 2] @between))
                  (is (= [:ok 5] (cached fork d))))
                (finally (ctx/close-context! fork))))))
        (finally (ctx/close-context! rt))))))

(defn- in-runtime [f]
  (let [rt (ctx/create-execution-context :executor (ex/synchronous-executor))]
    (try
      (binding [ec/*execution-context* rt cps/*in-trampoline* false]
        (f rt))
      (finally (ctx/close-context! rt)))))

(defn- pair-graph []
  (let [bs (sig/signal 0)
        cs (sig/signal 0)
        trace (atom [])
        b (spin (iv/get-new (track bs)))
        c (spin (iv/get-new (track cs)))
        d (spin (swap! trace conj :prefix)
                (let [bv (await b)
                      _ (swap! trace conj [:b bv])
                      cv (await c)]
                  (swap! trace conj [:pair bv cv])
                  [bv cv]))]
    (is (= [:ok [0 0]] (start! d)))
    {:bs bs :cs cs :b b :c c :d d :trace trace}))

(deftest ordered-diamond-completions-and-errors
  (doseq [order [:b-first :c-first] fail? [false true]]
    (testing (str [order fail?])
      (in-runtime
       (fn [rt]
         (let [a (sig/signal 0)
               trace (atom [])
               b (spin (let [v (iv/get-new (track a))]
                         (if (and fail? (pos? v)) (throw (ex-info "earlier" {})) (* 2 v))))
               c (spin (* 3 (iv/get-new (track a))))
               d (spin (swap! trace conj :prefix)
                       (try
                         (let [bv (await b)
                               _ (swap! trace conj [:b bv])
                               cv (await c)]
                           (swap! trace conj [:pair bv cv])
                           [bv cv])
                         (catch Exception _ (swap! trace conj :error) :failed)))
               ids (mapv sc/spin-id (if (= :b-first order) [b c] [c b]))
               completions (atom [])
               enqueue! simple/enqueue-completion-event!]
           (is (= [:ok [0 0]] (start! d)))
           (with-redefs [graph/ordered-observers (fn [_ _] ids)
                         simple/enqueue-completion-event!
                         (fn [world sid]
                           (when (some #{sid} ids) (swap! completions conj sid))
                           (enqueue! world sid))]
             (reset! a 1))
           (await-drain rt 1000)
           (is (= ids (vec (distinct @completions))) "exercise the specified completion order")
           (is (= [:ok (if fail? :failed [2 3])] (cached rt d)))
           (is (= (if fail?
                    [:prefix [:b 0] [:pair 0 0] :error]
                    [:prefix [:b 0] [:pair 0 0] [:b 2] [:pair 2 3]])
                  @trace))
           (when fail?
             (is (not-any? #(= [:spin/complete (sc/spin-id c)] (:event-key %))
                           (vals (rtp/get-state rt [:await-conts (sc/spin-id d)])))
                 "the unreached success suffix is retired"))))))))

(deftest branch-exit-retires-later-await
  (in-runtime
   (fn [rt]
     (let [bs (sig/signal true)
           cs (sig/signal 0)
           trace (atom [])
           b (spin (iv/get-new (track bs)))
           c (spin (iv/get-new (track cs)))
           d (spin (if (await b)
                     (let [v (await c)] (swap! trace conj v) v)
                     (do (swap! trace conj :exit) :exit)))]
       (is (= [:ok 0] (start! d)))
       (reset! bs false)
       (await-drain rt 1000)
       (is (= [:ok :exit] (cached rt d)))
       (reset! cs 1)
       (await-drain rt 1000)
       (is (= [:ok :exit] (cached rt d)))
       (is (= [0 :exit] @trace))))))

(deftest cancelled-earlier-child-progresses-on-later-completion
  (doseq [invalidated? [false true]]
    (in-runtime
     (fn [rt]
       (let [{:keys [b cs d trace]} (pair-graph)]
         (when invalidated?
           (rtp/swap-state! rt [:nodes (sc/spin-id b)] simple/invalidate-node))
         (sc/cancel-spin! b)
         (reset! cs 3)
         (await-drain rt 1000)
         (let [[variant err] (cached rt d)]
           (is (= :error variant))
           (is (= sc/spin-cancelled (:type (ex-data err)))))
         (is (= [:prefix [:b 0] [:pair 0 0]] @trace))
         (is (= 1 (count (rtp/get-state rt [:await-conts (sc/spin-id d)])))))))))

(deftest following-fork-consumes-parent-advance-without-notification
  (in-runtime
   (fn [rt]
     (let [{:keys [bs cs d trace]} (pair-graph)
           fork (ctx/fork-context rt)]
       (try
         (reset! bs 2)
         (await-drain rt 1000)
         (let [prefix @trace]
           (binding [ec/*execution-context* fork]
             (reset! cs 3)
             (await-drain fork 1000)
             (is (= [:ok [2 3]] (cached fork d)))
             (is (= (into prefix [[:b 2] [:pair 2 3]]) @trace))
             (is (= [:ok [2 0]] (cached rt d)))))
         (finally (ctx/close-context! fork)))))))

(deftest frozen-fork-between-cache-and-consumption
  (in-runtime
   (fn [rt]
     (let [{:keys [bs cs b d trace]} (pair-graph)
           forked (atom nil)
           enqueue! simple/enqueue-completion-event!]
       (try
         (with-redefs [simple/enqueue-completion-event!
                       (fn [world sid]
                         (when (and (= sid (sc/spin-id b)) (nil? @forked))
                           (reset! forked (ctx/fork-context world :mode :frozen)))
                         (enqueue! world sid))]
           (reset! bs 2))
         (is (some? @forked))
         (let [prefix @trace]
           (binding [ec/*execution-context* @forked]
             (reset! cs 3)
             (await-drain @forked 1000)
             (is (= [:ok [2 3]] (cached @forked d)))
             (is (= (into prefix [[:b 2] [:pair 2 3]]) @trace))))
         (finally (when @forked (ctx/close-context! @forked))))))))

(deftest inherited-earlier-claim-is-not-a-delivery
  (in-runtime
   (fn [rt]
     (let [{:keys [bs cs b d trace]} (pair-graph)
           forked (atom nil)
           claim! simple/claim-continuation-for-resume!]
       (try
         (with-redefs [simple/claim-continuation-for-resume!
                       (fn [world pid cid opts]
                         (let [claimed (claim! world pid cid opts)]
                           (when (and claimed (= pid (sc/spin-id d))
                                      (= [:spin/complete (sc/spin-id b)] (:event-key claimed))
                                      (not (:inline? opts)) (nil? @forked))
                             (reset! forked (ctx/fork-context world :mode :frozen)))
                           claimed))]
           (reset! bs 2))
         (is (some? @forked))
         (let [prefix @trace]
           (binding [ec/*execution-context* @forked]
             (reset! cs 3)
             (await-drain @forked 1000)
             (is (= [:ok [2 3]] (cached @forked d)))
             (is (= (into prefix [[:b 2] [:pair 2 3]]) @trace))))
         (finally (when @forked (ctx/close-context! @forked))))))))

(deftest await-reentry-cancels-displaced-external-suffix
  (in-runtime
   (fn [rt]
     (let [bs (sig/signal true)
           b (spin (iv/get-new (track bs)))
           gate (sync/deferred)
           trace (atom [])
           d (spin (if (await b)
                     (let [v (await gate)] (swap! trace conj v) v)
                     (do (swap! trace conj :exit) :exit)))]
       (d identity identity)
       (reset! bs false)
       (await-drain rt 1000)
       (is (= [:ok :exit] (cached rt d)))
       (sync/deliver! gate :stale)
       (await-drain rt 1000)
       (is (= [:ok :exit] (cached rt d)))
       (is (= [:exit] @trace))))))

(defn- reusable-child [source runs]
  (spin (swap! runs inc) (iv/get-new (track source))))

(deftest adopted-dirty-child-has-a-dispatch-path
  (in-runtime
   (fn [rt]
     (let [bs (sig/signal 0)
           cs (sig/signal 0)
           runs (atom 0)
           ;; Signals initialize lazily. The anchor must already contain the
           ;; dependency snapshot, or adoption correctly rejects the subtree.
           _ (sig/ensure-signal-initialized! bs)
           fork (ctx/fork-context rt :mode :frozen)]
       (try
         (let [b (reusable-child bs runs)]
           (is (= [:ok 0] (start! b)))
           (binding [ec/*execution-context* fork]
             (rtp/swap-state! fork [:engine/reuse-source] (constantly rt))
             (let [adopted (reusable-child bs runs)]
               (is (= (sc/spin-id b) (sc/spin-id adopted)))
               (is (= 1 @runs) "registration adopts without running the child")
               (is (identical? (rtp/current-result rt (sc/spin-id b))
                               (rtp/current-result fork (sc/spin-id adopted))))
               (is (empty? (rtp/get-state fork [:track-subscriptions (sc/spin-id adopted)])))
               (rtp/swap-state! fork [:engine/reuse-source] (constantly nil))
               (let [c (spin (iv/get-new (track cs)))
                     trace (atom [])
                     d (spin (let [bv (await adopted) cv (await c)]
                               (swap! trace conj [bv cv]) [bv cv]))]
                 (is (= [:ok [0 0]] (start! d)))
                 (reset! bs 2)
                 (is (rtp/dirty? fork (sc/spin-id adopted))
                     "a signal change invalidates an adopted cache without track dispatch")
                 (is (= 1 @runs) "the adopted child has no track dispatch")
                 (reset! cs 3)
                 (await-drain fork 1000)
                 (is (= [:ok [2 3]] (cached fork d)))
                 (is (= [[0 0] [2 3]] @trace))
                 (is (= 2 @runs) "the earlier await schedules the dirty adopted child")))))
         (finally (ctx/close-context! fork)))))))

(deftest exact-result-wrapper-after-dirty-earlier-site
  (in-runtime
   (fn [rt]
     (let [{:keys [b c d trace]} (pair-graph)
           old-result (rtp/current-result rt (sc/spin-id b))
           trigger! simple/trigger-drain!]
       (with-redefs [simple/trigger-drain! (fn [& _])]
         (simple/mark-dirty! rt (sc/spin-id b))
         (simple/cache-result! rt (sc/spin-id c) (sc/ok 3))
         (simple/process-event! rt {:type :spin-completion :id (sc/spin-id c)})
         (is (= [:prefix [:b 0] [:pair 0 0]] @trace) "later slice is parked")
         ;; Model an exact cache-wrapper reuse before the scheduled execution.
         ;; No new b completion is posted by this cache write.
         (simple/cache-result! rt (sc/spin-id b) old-result))
       (trigger! rt (:executor rt))
       (await-drain rt 1000)
       (is (identical? old-result (rtp/current-result rt (sc/spin-id b))))
       (is (= [:ok [0 3]] (cached rt d)))
       (is (= [:prefix [:b 0] [:pair 0 0] [:b 0] [:pair 0 3]] @trace))))))

(deftest uncaught-earlier-error-in-both-orders
  (doseq [b-first? [true false]]
    (in-runtime
     (fn [rt]
       (let [a (sig/signal 0)
             boom (ex-info "earlier child failed" {})
             seen (atom [])
             b (spin (let [v (iv/get-new (track a))]
                       (if (pos? v) (throw boom) v)))
             c (spin (iv/get-new (track a)))
             d (spin (let [bv (await b) cv (await c)]
                       (swap! seen conj [bv cv]) [bv cv]))]
         (is (= [:ok [0 0]] (start! d)))
         (with-redefs [graph/ordered-observers
                       (fn [_ _] (mapv sc/spin-id (if b-first? [b c] [c b])))]
           (reset! a 1))
         (await-drain rt 1000)
         (is (= [:error boom] (cached rt d)))
         (is (= [[0 0]] @seen)))))))

(deftest running-earlier-child-retains-a-wakeup
  (in-runtime
   (fn [rt]
     (let [bs (sig/signal 0)
           cs (sig/signal 0)
           gate (sync/deferred)
           child-prefix (atom 0)
           seen (atom [])
           b (spin (swap! child-prefix inc)
                   (let [v (iv/get-new (track bs))]
                     (when (pos? v) (await gate))
                     v))
           c (spin (iv/get-new (track cs)))
           d (spin (let [bv (await b) cv (await c)]
                     (swap! seen conj [bv cv]) [bv cv]))]
       (is (= [:ok [0 0]] (start! d)))
       (reset! bs 2)
       (reset! cs 3)
       (is (= [[0 0]] @seen) "the later completion cannot run its old closure")
       (is (seq (rtp/get-state rt [:subscriptions [:spin/complete (sc/spin-id b)]])))
       (sync/deliver! gate :ready)
       (await-drain rt 1000)
       (is (= [:ok [2 3]] (cached rt d)))
       (is (= [[0 0] [2 3]] @seen))
       (is (= 1 @child-prefix) "join the live child run, preserving its prefix")))))

(deftest fork-does-not-inherit-a-dirty-childs-scheduled-wakeup
  (in-runtime
   (fn [rt]
     (let [bs (sig/signal 0)
           cs (sig/signal 0)
           gate (sync/deferred)
           child-prefix (atom 0)
           seen (atom [])
           b (spin (swap! child-prefix inc)
                   (let [v (iv/get-new (track bs))]
                     (when (pos? v) (await gate))
                     v))
           c (spin (iv/get-new (track cs)))
           d (spin (let [bv (await b) cv (await c)]
                     (swap! seen conj [bv cv]) [bv cv]))]
       (is (= [:ok [0 0]] (start! d)))
       (reset! bs 2)
       (reset! cs 3)
       (let [fork (ctx/fork-context rt :mode :frozen)]
         (try
           (binding [ec/*execution-context* fork]
             (reset! cs 4)
             (is (= 2 @child-prefix) "schedule a fresh child run in the fork")
             (sync/deliver! gate :ready)
             (await-drain fork 1000)
             (is (= [:ok [2 4]] (cached fork d)))
             (is (= [[0 0] [2 4]] @seen))
             (is (= [:ok [0 0]] (cached rt d)) "the parent's wait remains independent"))
           (finally (ctx/close-context! fork))))))))

(deftest joined-earlier-run-invalidated-before-completion-is-retried
  (in-runtime
   (fn [rt]
     (let [bs (sig/signal 0)
           cs (sig/signal 0)
           gate (sync/deferred)
           child-prefix (atom 0)
           seen (atom [])
           b (spin (swap! child-prefix inc)
                   (let [v (iv/get-new (track bs))]
                     (when (pos? v) (await gate))
                     v))
           c (spin (iv/get-new (track cs)))
           d (spin (let [bv (await b) cv (await c)]
                     (swap! seen conj [bv cv]) [bv cv]))]
       (is (= [:ok [0 0]] (start! d)))
       (reset! bs 2)
       (reset! cs 3)
       ;; The queued execution joined the live run. Invalidate it before
       ;; its callback fires, as a re-registration with changed captures does.
       (rtp/swap-state! rt [:nodes (sc/spin-id b)] simple/invalidate-node)
       (sync/deliver! gate :ready)
       (await-drain rt 1000)
       (is (= [:ok [2 3]] (cached rt d)))
       (is (= [[0 0] [2 3]] @seen))
       (is (rtp/clean? rt (sc/spin-id b)) "a dirty completion schedules a fresh attempt")
       (is (= 2 @child-prefix))))))

(deftest invalidated-inline-child-schedules-without-an-outer-drain
  (in-runtime
   (fn [rt]
     (let [a (sig/signal 1)
           b (spin (iv/get-new (track a)))
           prefix (atom 0)
           d (spin (swap! prefix inc) (await b))
           cache! ec/spin-cache-result!
           invalidated? (atom false)]
       (with-redefs [ec/spin-cache-result!
                     (fn
                       ([sid result] (cache! sid result))
                       ([sid result run]
                        (when (and (= sid (sc/spin-id b))
                                   (compare-and-set! invalidated? false true))
                          (rtp/swap-state! rt [:nodes sid] simple/invalidate-node))
                        (cache! sid result run)))]
         (is (= [:ok 1] (start! d))))
       (await-drain rt 1000)
       (is @invalidated?)
       (is (= [:ok 1] (cached rt d)))
       (is (rtp/clean? rt (sc/spin-id b)))
       (is (= 1 @prefix))))))

(deftest cancellation-before-a-queued-child-refresh-stays-terminal
  (in-runtime
   (fn [rt]
     (let [{:keys [b c d trace]} (pair-graph)
           trigger! simple/trigger-drain!]
       (with-redefs [simple/trigger-drain! (fn [& _])]
         (rtp/swap-state! rt [:nodes (sc/spin-id b)] simple/invalidate-node)
         (simple/cache-result! rt (sc/spin-id c) (sc/ok 3))
         (simple/process-event! rt {:type :spin-completion :id (sc/spin-id c)})
         (sc/cancel-spin! b))
       (trigger! rt (:executor rt))
       (await-drain rt 1000)
       (is (= :error (first (cached rt d))))
       (is (sc/spin-cancelled? b))
       (is (= [:prefix [:b 0] [:pair 0 0]] @trace))))))

(deftest frozen-fork-before-the-earlier-sibling-was-dispatched
  (in-runtime
   (fn [rt]
     (let [a (sig/signal 0)
           cs (sig/signal 0)
           prefix (atom 0)
           seen (atom [])
           b (spin (* 2 (iv/get-new (track a))))
           c (spin (let [av (iv/get-new (track a))
                         cv (iv/get-new (track cs))]
                     (+ (* 3 av) cv)))
           d (spin (swap! prefix inc)
                   (let [bv (await b) cv (await c)]
                     (swap! seen conj [bv cv]) [bv cv]))
           forked (atom nil)
           enqueue! simple/enqueue-completion-event!]
       (is (= [:ok [0 0]] (start! d)))
       (try
         (with-redefs [graph/ordered-observers (fn [_ _] (mapv sc/spin-id [c b]))
                       simple/enqueue-completion-event!
                       (fn [world sid]
                         (when (and (= sid (sc/spin-id c)) (nil? @forked))
                           (reset! forked (ctx/fork-context world :mode :frozen)))
                         (enqueue! world sid))]
           (reset! a 1))
         (is (some? @forked))
         (is (rtp/dirty? @forked (sc/spin-id b)) "freeze the pending invalidation, not a clean old cache")
         (binding [ec/*execution-context* @forked]
           (reset! cs 1)
           (await-drain @forked 1000)
           (is (= [:ok [2 4]] (cached @forked d)))
           (is (= [[0 0] [2 3] [2 4]] @seen))
           (is (= 1 @prefix)))
         (finally (when @forked (ctx/close-context! @forked))))))))
