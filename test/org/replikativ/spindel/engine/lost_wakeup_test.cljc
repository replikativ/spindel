(ns org.replikativ.spindel.engine.lost-wakeup-test
  "Regression tests for issue #27 (lost wakeup / silently wedged
  consumers) — the failure-routing contract:

  1. A throw inside a resumed spin BODY slice already rejects the spin
     loudly (partial-cps `safe-r` + the spin macro's breakpoint
     wrapping). Pinned here so a CPS-emission change can never silently
     reintroduce the wedge.
  2. A throw in the thin GLUE — a raw waiter/reader continuation
     registered outside `await` — is reported through the engine fault
     hook, does not kill the drain, and does not strand OTHER
     readers/waiters (per-reader isolation in `deliver-inline!`, the
     guarded resume in `post-inline!`).
  3. `spin/supervisor` restart policies observe the failure (they ride
     on `spawn!`'s `:on-error`), so a crashed consumer is restarted and
     drains the backlog — the production wedge scenario, end to end.
  4. Executor tasks that throw are reported, not swallowed in a
     discarded Future (JVM) / lost to the global handler (CLJS)."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer [deftest is testing] :include-macros true])
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.fault :as fault]
            [org.replikativ.spindel.engine.executor :as executor]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.state-backend :as backend]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.spin.supervisor :as sup]
            #?(:clj [org.replikativ.spindel.spin.cps :refer [spin]])
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.test-helpers :as th])
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]]
                            [org.replikativ.spindel.test-helpers :refer [with-ctx async]])))

;; -----------------------------------------------------------------------------
;; Helpers
;; -----------------------------------------------------------------------------

(defn- capture-faults!
  "Install a capturing fault reporter; returns [faults-atom restore-fn]."
  []
  (let [orig (fault/current-fault-reporter)
        faults (atom [])]
    (fault/set-fault-reporter! (fn [ev data] (swap! faults conj [ev data])))
    [faults (fn [] (fault/set-fault-reporter! orig))]))

#?(:clj
   (defn- poll-until
     "Poll pred every 10ms up to timeout-ms. Returns (pred) truthiness."
     [pred timeout-ms]
     (let [deadline (+ (System/currentTimeMillis) timeout-ms)]
       (loop []
         (cond
           (pred) true
           (>= (System/currentTimeMillis) deadline) false
           :else (do (Thread/sleep 10) (recur)))))))

;; -----------------------------------------------------------------------------
;; 1. Body throw → loud rejection (pins the CPS safety wrapper)
;; -----------------------------------------------------------------------------

#?(:clj
   (deftest body-throw-rejects-spin-loudly-not-pending
     (testing "a consumer whose body throws after (await mbx) REJECTS — spawn!'s
             :on-error fires, the node holds :error, no silent PENDING"
       (th/with-ctx [ctx]
         (let [mbx (sync/create-mailbox ctx)
               seen (atom [])
               errs (atom [])
               consumer (spin
                         (loop []
                           (let [m (await mbx)]
                             (when (= m :boom)
                               (throw (ex-info "kaboom" {:test true})))
                             (swap! seen conj m)
                             (recur))))]
           (sync/spawn! consumer {:on-error (fn [e] (swap! errs conj e))})
           (sync/post! mbx :a)
           (is (poll-until #(= [:a] @seen) 2000) "consumer runs normally first")
           (sync/post! mbx :boom)
           (is (poll-until #(seq @errs) 2000)
               "spawn! :on-error observed the body throw (loud failure)")
           (is (= "kaboom" (ex-message (first @errs))))
           (let [node (rtp/get-state ctx [:nodes (spin-core/spin-id consumer)])]
             (is (not (:running? node)) "consumer is not stuck running")
             (is (= :error (some-> node :result :variant))
                 "consumer's node carries the error result — not PENDING")))))))

;; -----------------------------------------------------------------------------
;; 2a. Raw deferred readers: per-reader isolation + fault report
;; -----------------------------------------------------------------------------

#?(:clj
   (deftest deferred-raw-reader-isolation
     (testing "reader 2 throwing (raw glue, outside await/safe-r) must not
             strand readers 1 and 3, and must be reported"
       (let [[faults restore!] (capture-faults!)]
         (try
           (th/with-ctx [ctx]
             (let [d (sync/create-deferred ctx)
                   called (atom [])]
               ;; Raw readers via the 2-arity — deliberately BYPASSES await's
               ;; safe-r wrapping, modeling glue-level failure.
               (d (fn [v] (swap! called conj [:r1 v])) (fn [_e] nil))
               (d (fn [_v] (throw (ex-info "reader-2 glue boom" {}))) (fn [_e] nil))
               (d (fn [v] (swap! called conj [:r3 v])) (fn [_e] nil))
               (sync/deliver! d :val)
               (is (poll-until #(= 2 (count @called)) 2000)
                   "readers 1 and 3 both resolved despite reader 2's throw")
               (is (= [[:r1 :val] [:r3 :val]] @called))
               (is (poll-until #(seq @faults) 2000) "fault reported")
               (let [[ev data] (first @faults)]
                 (is (= ::fault/continuation-fault ev))
                 (is (= :deferred (:site data))))))
           (finally (restore!)))))))

;; -----------------------------------------------------------------------------
;; 2b. Raw mailbox waiter: drain survives, fault reported, mailbox usable
;; -----------------------------------------------------------------------------

#?(:clj
   (deftest raw-mailbox-waiter-throw-reports-and-drain-survives
     (testing "a raw waiter's throwing resolve is reported; the drain and the
             mailbox keep working for subsequent takes"
       (let [[faults restore!] (capture-faults!)]
         (try
           (th/with-ctx [ctx]
             (let [mbx (sync/create-mailbox ctx)
                   got (atom nil)]
               (mbx (fn [_m] (throw (ex-info "waiter glue boom" {}))) (fn [_e] nil))
               (sync/post! mbx :first)
               (is (poll-until #(seq @faults) 2000) "fault reported")
               (is (= :mailbox (:site (second (first @faults)))))
               ;; The engine is still alive: a fresh waiter receives the next post.
               (mbx (fn [m] (reset! got m)) (fn [_e] nil))
               (sync/post! mbx :second)
               (is (poll-until #(= :second @got) 2000)
                   "drain survived — subsequent delivery works")))
           (finally (restore!)))))))

;; -----------------------------------------------------------------------------
;; 3. Supervisor restarts a crashed consumer, which drains the backlog
;; -----------------------------------------------------------------------------

#?(:clj
   (deftest supervisor-restarts-throwing-consumer
     (testing "the production wedge scenario end-to-end: consumer crashes on a
             poison message, supervisor restarts it, backlog drains"
       (let [[_faults restore!] (capture-faults!)]
         (try
           (th/with-ctx [ctx]
             (let [mbx (sync/create-mailbox ctx)
                   seen (atom [])
                   make-consumer (fn []
                                   (spin
                                    (loop []
                                      (let [m (await mbx)]
                                        (when (= m :boom)
                                          (throw (ex-info "poison" {})))
                                        (swap! seen conj m)
                                        (recur)))))
                   s (sup/supervisor
                      [{:id :consumer :start make-consumer}]
                      {:strategy :one-for-one
                       :max-restarts 3
                       :window-ms 60000})]
               ;; The supervisor is itself a spin — spawn it to start the
               ;; children + monitoring loop.
               (sync/spawn! s)
               (sync/post! mbx :a)
               (is (poll-until #(= [:a] @seen) 2000))
               (sync/post! mbx :boom)
               (sync/post! mbx :c)
               (is (poll-until #(= [:a :c] @seen) 4000)
                   "restarted consumer drained the post-crash backlog")))
           (finally (restore!)))))))

;; -----------------------------------------------------------------------------
;; 4. Executor task seam: escaped throws are reported, not swallowed
;; -----------------------------------------------------------------------------

#?(:clj
   (deftest executor-task-fault-is-reported
     (testing "a throw escaping an executor task lands in the fault hook
             instead of a discarded Future"
       (let [[faults restore!] (capture-faults!)]
         (try
           (th/with-ctx [ctx]
             (executor/execute! (:executor ctx)
                                (fn [] (throw (ex-info "task boom" {}))))
             (is (poll-until #(some (fn [[ev _]]
                                      (= ::fault/executor-task-fault ev))
                                    @faults)
                             2000)
                 "executor task fault reported"))
           (finally (restore!)))))))

#?(:clj
   (deftest guard-task-restores-interrupt-flag
     (testing "an InterruptedException in a guarded task restores the thread's
             interrupt flag and reports"
       (let [[faults restore!] (capture-faults!)]
         (try
           (let [guarded (executor/guard-task
                          (fn [] (throw (InterruptedException. "cancel"))))]
             (guarded)
             (is (.isInterrupted (Thread/currentThread))
                 "interrupt flag restored for pool machinery")
             ;; clear it so we don't poison the test runner's thread
             (Thread/interrupted)
             (is (some (fn [[ev data]]
                         (and (= ::fault/executor-task-fault ev)
                              (:interrupted? data)))
                       @faults)))
           (finally (restore!)))))))

;; -----------------------------------------------------------------------------
;; 4b. Phase C: transactional handoff + re-post-on-cancelled
;; -----------------------------------------------------------------------------

#?(:clj
   (deftest cont-resume-reposts-message-for-waiter-cancelled-in-window
     (testing "a :cont-resume whose waiter was cancelled between enqueue and
             processing RE-POSTS the mailbox message instead of feeding it to
             a gated no-op (lossless — nothing of the continuation ran)"
       (th/with-ctx [ctx]
         (let [mbx (sync/create-mailbox ctx)
               token (keyword "external-await-cancel" (str (random-uuid)))
               fired (atom false)]
           ;; Simulate the race deterministically: the waiter's token is
           ;; ALREADY in :engine/cancelled-tokens when its :cont-resume
           ;; event (as post-inline! would have enqueued it) processes.
           (rtp/swap-state! ctx [:engine/cancelled-tokens]
                            (fn [s] (conj (or s #{}) token)))
           (rtp/enqueue! ctx {:type :cont-resume
                              :site :mailbox
                              :spin-id nil
                              :cancel-token token
                              :resolve (fn [_] (reset! fired true))
                              :value :msg-1
                              :mailbox mbx})
           (is (poll-until
                #(= [:msg-1]
                    (binding [ec/*execution-context* ctx]
                      (vec (:queue @(.-state-atom mbx)))))
                2000)
               "message re-posted into the mailbox queue (no live waiter)")
           (is (not @fired) "the cancelled waiter's continuation never ran")
           (is (not (contains? (rtp/get-state ctx [:engine/cancelled-tokens]) token))
               "the consumed cancel-token was self-cleaned"))))))

#?(:clj
   (deftest backend-write-2-is-atomic-and-cow-seeds
     (testing "AtomBackend: both paths transformed in one commit"
       (let [b (backend/create-atom-backend {:a {:x 1} :engine/pending []})]
         (backend/backend-write-2! b [:a :x] [:engine/pending]
                                   (fn [x pending]
                                     [(inc x) (conj pending {:ev (inc x)})]))
         (is (= 2 (backend/backend-read b [:a :x])))
         (is (= [{:ev 2}] (backend/backend-read b [:engine/pending])))))
     (testing "OverlayBackend: shared path CoW-seeds the entity from the
             parent; fork-local path writes directly; parent untouched"
       (let [parent (backend/create-atom-backend
                     {:atoms {:mbx {:value {:queue [] :waiters [:w]}}}
                      :engine/pending [:parent-event]})
             fork (backend/create-overlay-backend parent)]
         (backend/backend-write-2! fork [:atoms :mbx :value] [:engine/pending]
                                   (fn [mbx-state pending]
                                     [(update mbx-state :waiters rest)
                                      (conj (vec pending) {:ev 1})]))
         (is (= [] (vec (:waiters (backend/backend-read fork [:atoms :mbx :value]))))
             "fork sees the popped waiter (CoW copy)")
         (is (= [:w] (:waiters (backend/backend-read parent [:atoms :mbx :value])))
             "parent's copy is untouched (fork diverged)")
         (is (= [{:ev 1}] (backend/backend-read fork [:engine/pending]))
             "fork-local pending written directly — parent's queue not read")))))

;; -----------------------------------------------------------------------------
;; 5. CLJS: non-Error throw values must not slip past the catches
;; -----------------------------------------------------------------------------

#?(:cljs
   (deftest non-error-throw-value-rejects-spin
     (testing "a thrown string (non-Error) reaches the reject path — the
             :default catches must not miss it"
       (async done
              (th/with-ctx [ctx]
                (let [t (spin (throw "string-boom"))]
                  (th/run-spin! t
                                (fn [_v]
                                  (is false "must not resolve")
                                  (done))
                                (fn [e]
                                  (is (= "string-boom" e))
                                  (done)))))))))
