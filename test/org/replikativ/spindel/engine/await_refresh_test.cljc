(ns org.replikativ.spindel.engine.await-refresh-test
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
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
            [org.replikativ.spindel.spin.core :as sc]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.test-helpers :as helpers :refer [async with-ctx run-spin!]]))

(defn- cached [world s]
  (let [r (rtp/current-result world (sc/spin-id s))]
    [(:variant r) (:payload r)]))

(defn- queue-refresh! [world b c]
  (simple/mark-dirty! world (sc/spin-id b))
  (simple/cache-result! world (sc/spin-id c) (sc/ok 3))
  (simple/process-event! world {:type :spin-completion :id (sc/spin-id c)}))

(deftest completion-before-join-registration
  (async done
         (with-redefs [helpers/create-test-context
                       (fn [] (ctx/create-execution-context :executor (ex/synchronous-executor)))]
           (with-ctx [world]
             (binding [ec/*execution-context* (assoc world :executor (ex/synchronous-executor))
                       cps/*in-trampoline* false]
               (let [world (ec/current-execution-context)
                     bs (sig/signal 0)
                     gate (sync/deferred)
                     b (spin (let [v (iv/get-new (track bs))]
                               (when (pos? v) (await gate)) v))
                     c (spin 0)
                     d (spin [(await b) (await c)])
                     add! simple/add-pending-callback!
                     forced? (atom false)]
                 (run-spin! d
                            (fn [_])
                            (fn [e] (is false (str e))))
                 (reset! bs 2)
                 (with-redefs [simple/add-pending-callback!
                               (fn [rt sid cb]
                                 (when (and (= sid (sc/spin-id b))
                                            (compare-and-set! forced? false true))
                            ;; The join already saw b running. Complete and
                            ;; serve its callback list BEFORE registration.
                                   (rtp/swap-state! rt [:nodes sid] simple/invalidate-node)
                                   (simple/process-event! rt {:type :deferred-delivery :deferred gate :value :ready})
                                   (let [delivery (simple/dequeue-event! rt)]
                                     (is (= :cont-resume (:type delivery)))
                                     (simple/process-event! rt delivery))
                                   (is (not (simple/running? rt sid)))
                                   (is (empty? (rtp/get-state rt [:pending-callbacks sid]))))
                                 (add! rt sid cb))]
                   (queue-refresh! world b c)
                   (simple/drain-events! world (:executor world)))
                 (is @forced?)
                 (is (= [:ok [2 3]] (cached world d)))
                 (is (rtp/clean? world (sc/spin-id b)))
                 (is (empty? (rtp/get-state world [:pending-callbacks (sc/spin-id b)])))
                 (is (empty? (mapv :id (filter ::simple/refresh? (vals (rtp/get-state world [:await-conts (sc/spin-id d)]))))))))))
         (done)))

(deftest restored-refresh-acknowledges-in-its-execution-world
  (async done
         (with-redefs [helpers/create-test-context
                       (fn [] (ctx/create-execution-context :executor (ex/synchronous-executor)))]
           (with-ctx [source]
             (binding [cps/*in-trampoline* false]
               (doseq [mode [:cached :cancelled :fresh :failure]]
                 (let [runs (atom 0)
                       b (spin (swap! runs inc) 2)
                       c (spin 0)
                       d (spin [(await b) (await c)])
                       trigger! simple/trigger-drain!]
                   (run-spin! d (fn [_]) (fn [e] (is false (str e))))
                   (let [restored
                         (with-redefs [simple/trigger-drain! (fn [& _])]
                           (queue-refresh! source b c)
                           (case mode
                             :cached (simple/cache-result! source (sc/spin-id b) (sc/ok 2))
                             :cancelled (sc/cancel-spin! b)
                             nil)
                           (let [snapshot (ctx/snapshot-context source :include-pending? true)
                                 claim! simple/try-claim-execution!
                                 failed? (atom false)]
                             (with-redefs [simple/try-claim-execution!
                                           (fn claim-with-failure
                                             ([rt sid] (claim-with-failure rt sid nil))
                                             ([rt sid opts]
                                              (if (and (= mode :failure) (= sid (sc/spin-id b))
                                                       (compare-and-set! failed? false true))
                                                (throw (ex-info "refresh execution failed" {}))
                                                (claim! rt sid opts))))]
                        ;; restore-snapshot drains explicitly while SOURCE is bound.
                               (ctx/restore-snapshot snapshot))))]
                     (is (= [:ok [2 0]] (cached source d)) (str mode " leaves source untouched"))
                     (if (= mode :cancelled)
                       (is (= :error (first (cached restored d))))
                       (is (= [:ok [2 3]] (cached restored d)) (str mode)))
                     (is (empty? (mapv :id (filter ::simple/refresh? (vals (rtp/get-state restored [:await-conts (sc/spin-id d)]))))))
                     (ctx/close-context! restored))
            ;; Retire the deliberately undrained source obligations.
                   (sc/cancel-spin! d)
                   (trigger! source (:executor source)))))))
         (done)))

(deftest retired-refresh-does-not-run-child-effects
  (async done
         (with-redefs [helpers/create-test-context
                       (fn [] (ctx/create-execution-context :executor (ex/synchronous-executor)))]
           (with-ctx [world]
             (binding [cps/*in-trampoline* false]
               (doseq [retirement [:branch-exit :parent-cancel]]
                 (let [active (sig/signal true)
                       effects (atom 0)
                       b (spin (swap! effects inc) 2)
                       c (spin 0)
                       d (spin (if (iv/get-new (track active))
                                 [(await b) (await c)] :exit))
                       trigger! simple/trigger-drain!]
                   (run-spin! d (fn [_]) (fn [_]))
                   (with-redefs [simple/trigger-drain! (fn [& _])]
                     (queue-refresh! world b c)
                     (case retirement
                       :branch-exit (do
                                      (reset! active false)
                               ;; Force branch retirement ahead of the queued execution.
                                      (simple/process-event! world {:type :signal-change :id (:id active)}))
                       :parent-cancel (sc/cancel-spin! d)))
                   (trigger! world (:executor world))
                   (simple/drain-events! world (:executor world))
                   (is (= 1 @effects) (str retirement " discards the obsolete handoff"))
                   (is (empty? (rtp/get-state world [:pending-callbacks (sc/spin-id b)])))
                   (if (= retirement :branch-exit)
                     (is (= [:ok :exit] (cached world d)))
                     (is (= :error (first (cached world d))))))))))
         (done)))

(deftest consumed-cancellation-token-is-not-rearmed
  (async done
         (with-redefs [helpers/create-test-context
                       (fn [] (ctx/create-execution-context :executor (ex/synchronous-executor)))]
           (with-ctx [world]
             (binding [cps/*in-trampoline* false]
               (let [active (sig/signal true)
                     gate (sync/deferred)
                     d (spin (if (iv/get-new (track active)) (await gate) :exit))
                     forced? (atom false)]
                 (run-spin! d (fn [_]) (fn [_]))
                 (let [cont (first (vals (rtp/get-state world [:await-conts (sc/spin-id d)])))
                       token (:cancel-token cont)
                       deliver-external! (:resolve-fn cont)
                       cancel! (:cancel! cont)]
                   (rtp/swap-state! world [:await-conts (sc/spin-id d) (:id cont)]
                                    #(assoc % :cancel!
                                            (fn [rt]
                                         ;; Detachment has committed and armed the gate.
                                         ;; Deliver inside a custom post-commit hook.
                                              (is (contains? (rtp/get-state rt [:engine/cancelled-tokens]) token))
                                              (deliver-external! :stale)
                                              (reset! forced? true)
                                              (is (not (contains? (rtp/get-state rt [:engine/cancelled-tokens]) token)))
                                              (when cancel! (cancel! rt)))))
                   (reset! active false)
                   (simple/drain-events! world (:executor world))
                   (is @forced?)
                   (is (= [:ok :exit] (cached world d)))
                   (is (not (contains? (rtp/get-state world [:engine/cancelled-tokens]) token))))))))
         (done)))

(deftest cached-later-completion-repairs-frozen-prefix
  (async done
         (with-redefs [helpers/create-test-context
                       (fn [] (ctx/create-execution-context :executor (ex/synchronous-executor)))]
           (with-ctx [world]
             (binding [cps/*in-trampoline* false]
               (let [bs (sig/signal 0)
                     b (spin (iv/get-new (track bs)))
                     c (spin 0)
                     seen (atom [])
                     d (spin (let [pair [(await b) (await c)]] (swap! seen conj pair) pair))
                     forked (atom nil)
                     enqueue! simple/enqueue-completion-event!]
                 (run-spin! d (fn [_]) (fn [e] (is false (str e))))
                 (try
                   (with-redefs [simple/enqueue-completion-event!
                                 (fn [rt sid]
                                   (when (and (= sid (sc/spin-id b)) (nil? @forked))
                                     (reset! forked (ctx/fork-context rt :mode :frozen)))
                                   (enqueue! rt sid))]
                     (reset! bs 2))
                   (is (some? @forked))
                   (is (= [:ok [0 0]] (cached @forked d)))
                   (is (= [:ok 2] (cached @forked b)))
                   (let [prefix @seen
                         result (rtp/current-result @forked (sc/spin-id c))]
                     (binding [ec/*execution-context* @forked]
                  ;; Spin's cached invocation posts a completion with the SAME wrapper.
                       (c identity identity)
                       (simple/drain-events! @forked (:executor @forked))
                       (is (identical? result (rtp/current-result @forked (sc/spin-id c))))
                       (is (= [:ok [2 0]] (cached @forked d)))
                       (is (= (conj prefix [2 0]) @seen))))
                   (finally (when @forked (ctx/close-context! @forked))))))))
         (done)))

(deftest frozen-pending-observer-is-fresh-for-new-consumer
  (async done
         (with-redefs [helpers/create-test-context
                       (fn [] (ctx/create-execution-context :executor (ex/synchronous-executor)))]
           (with-ctx [world]
             (binding [cps/*in-trampoline* false]
               (let [a (sig/signal 0)
                     b (spin (* 2 (iv/get-new (track a))))
                     c (spin (* 3 (iv/get-new (track a))))
                     forked (atom nil)
                     enqueue! simple/enqueue-completion-event!]
            ;; No ordered-await consumer exists during the source dispatch.
                 (run-spin! b (fn [_]) (fn [e] (is false (str e))))
                 (run-spin! c (fn [_]) (fn [e] (is false (str e))))
                 (try
                   (with-redefs [graph/ordered-observers (fn [_ _] (mapv sc/spin-id [c b]))
                                 simple/enqueue-completion-event!
                                 (fn [rt sid]
                                   (when (and (= sid (sc/spin-id c)) (nil? @forked))
                                     (reset! forked (ctx/fork-context rt :mode :frozen)))
                                   (enqueue! rt sid))]
                     (reset! a 1))
                   (is (some? @forked))
                   (is (= [:ok 3] (cached @forked c)))
                   (is (rtp/dirty? @forked (sc/spin-id b)) "pending invalidation survives freezing")
                   (binding [ec/*execution-context* @forked]
                     (let [seen (atom [])
                           d (spin (let [pair [(await b) (await c)]] (swap! seen conj pair) pair))]
                       (run-spin! d (fn [_]) (fn [e] (is false (str e))))
                       (is (= [:ok [2 3]] (cached @forked d)))
                       (is (= [[2 3]] @seen) "the first publication must already be fresh")))
                   (finally (when @forked (ctx/close-context! @forked))))))))
         (done)))

(defn- reusable-child [source runs]
  (spin (swap! runs inc) (iv/get-new (track source))))

(deftest queued-adopted-completion-refreshes-dirty-requested-child
  (async done
         (with-redefs [helpers/create-test-context
                       (fn [] (ctx/create-execution-context :executor (ex/synchronous-executor)))]
           (with-ctx [source]
             (binding [cps/*in-trampoline* false]
               (let [bs (sig/signal 0)
                     runs (atom 0)
                     _ (sig/ensure-signal-initialized! bs)
                     world (ctx/fork-context source :mode :frozen)]
                 (try
                   (let [b (reusable-child bs runs)]
                     (run-spin! b (fn [_]) (fn [e] (is false (str e))))
                     (binding [ec/*execution-context* world]
                       (rtp/swap-state! world [:engine/reuse-source] (constantly source))
                       (let [adopted (reusable-child bs runs)
                             result (rtp/current-result world (sc/spin-id adopted))]
                         (is (= (sc/spin-id b) (sc/spin-id adopted)))
                         (is (= 1 @runs) "adoption does not execute b")
                         (is (empty? (rtp/get-state world [:track-subscriptions (sc/spin-id adopted)])))
                         (rtp/swap-state! world [:engine/reuse-source] (constantly nil))
                         (let [c (spin 0)
                               seen (atom [])
                               d (spin (let [pair [(await adopted) (await c)]]
                                         (swap! seen conj pair) pair))]
                           (run-spin! d (fn [_]) (fn [e] (is false (str e))))
                           (is (= [:ok [0 0]] (cached world d)))
                           (with-redefs [simple/trigger-drain! (fn [& _])]
                             (reset! bs 2)
                             (adopted identity identity)
                             (is (identical? result (rtp/current-result world (sc/spin-id adopted))))
                             (is (= [:signal-change :spin-completion]
                                    (mapv :type (rtp/get-state world [:engine/pending])))))
                           (simple/drain-events! world (:executor world))
                           (is (= [:ok [2 0]] (cached world d)))
                           (is (= [[0 0] [2 0]] @seen) "publication trace before any repairing deref")
                           (is (= 2 @runs) "the completion refreshes its own dirty child")))))
                   (finally (ctx/close-context! world)))))))
         (done)))

(deftest batch-duplicate-still-repairs-an-affected-prefix
  (async done
         (with-redefs [helpers/create-test-context
                       (fn [] (ctx/create-execution-context :executor (ex/synchronous-executor)))]
           (with-ctx [world]
             (binding [cps/*in-trampoline* false]
               (let [runs (atom 0)
                     b (spin (swap! runs inc))
                     c (spin 3)
                     seen (atom [])
                     d (spin (let [pair [(await b) (await c)]] (swap! seen conj pair) pair))]
                 (run-spin! d (fn [_]) (fn [e] (is false (str e))))
                 (with-redefs [simple/trigger-drain! (fn [& _])]
                   ;; Keep a batch active across two completion dispatches.
                   (rtp/swap-state! world [:engine/current-batch]
                                    (constantly (simple/create-batch world :test)))
                   (try
                     (simple/cache-result! world (sc/spin-id c) (sc/ok 3))
                     (simple/process-event! world {:type :spin-completion :id (sc/spin-id c)})
                     (is (= [:ok [1 3]] (cached world d)))
                     (let [batch (rtp/get-state world [:engine/current-batch])]
                       (is (contains? @(:resumed-conts batch)
                                      [(sc/spin-id d) (sc/spin-id c) (:generation batch)])))
                     (simple/mark-dirty! world (sc/spin-id b))
                     (simple/process-event! world {:type :spin-completion :id (sc/spin-id c)})
                     (simple/drain-events! world (:executor world))
                     (is (= [:ok [2 3]] (cached world d)))
                     (is (= [[1 3] [1 3] [2 3]] @seen))
                     (finally
                       (rtp/swap-state! world [:engine/current-batch] (constantly nil)))))))))
         (done)))

(deftest held-claim-retries-acknowledged-same-wrapper-refresh
  (async done
         (with-redefs [helpers/create-test-context
                       (fn [] (ctx/create-execution-context :executor (ex/synchronous-executor)))]
           (with-ctx [world]
             (binding [cps/*in-trampoline* false]
               (let [b (spin 0)
                     c (spin 0)
                     seen (atom [])
                     d (spin (let [pair [(await b) (await c)]] (swap! seen conj pair) pair))
                     release! simple/release-reactive-resume!
                     forced? (atom false)]
                 (run-spin! d (fn [_]) (fn [e] (is false (str e))))
                 (with-redefs [simple/trigger-drain! (fn [& _])]
                   (let [result (sc/ok 2)]
                     (simple/cache-result! world (sc/spin-id b) result)
                     (with-redefs [simple/release-reactive-resume!
                                   (fn [rt pid owner]
                                     (when (and (= pid (sc/spin-id d))
                                                (= (:event-key owner) [:spin/complete (sc/spin-id b)])
                                                (compare-and-set! forced? false true))
                                       (is (= [:ok [2 0]] (cached world d)))
                                       ;; Pause between body resume and claim release.
                                       ;; Refresh b, reusing its wrapper before execution.
                                       (queue-refresh! world b c)
                                       (simple/cache-result! world (sc/spin-id b) result)
                                       (simple/drain-events! world (:executor world))
                                       (is (identical? result (rtp/current-result world (sc/spin-id b))))
                                       (is (= [:ok [2 0]] (cached world d)) "the owner still holds the slice"))
                                     (release! rt pid owner))]
                       (simple/process-event! world {:type :spin-completion :id (sc/spin-id b)}))
                     (simple/drain-events! world (:executor world))
                     (is @forced?)
                     (is (= [:ok [2 3]] (cached world d)))
                     (is (= [[0 0] [2 0] [2 3]] @seen))
                     (is (not-any? ::simple/refresh?
                                   (vals (rtp/get-state world [:await-conts (sc/spin-id d)]))))))))))
         (done)))

(deftest queued-completion-reads-selected-result-in-the-claim
  (async done
         (with-redefs [helpers/create-test-context
                       (fn [] (ctx/create-execution-context :executor (ex/synchronous-executor)))]
           (with-ctx [source]
             (binding [cps/*in-trampoline* false]
               (let [b (spin 0)
                     c (spin 0)
                     seen (atom [])
                     d (spin (let [pair [(await b) (await c)]] (swap! seen conj pair) pair))
                     claim! simple/claim-continuation-for-resume!
                     forced? (atom false)]
                 (run-spin! d (fn [_]) (fn [e] (is false (str e))))
                 (let [world (ctx/fork-context source :mode :following)
                       old (rtp/current-result world (sc/spin-id b))]
                   (try
                     (binding [ec/*execution-context* world]
                       (with-redefs [simple/trigger-drain! (fn [& _])
                                     simple/claim-continuation-for-resume!
                                     (fn
                                       ([rt pid cid] (claim! rt pid cid))
                                       ([rt pid cid opts]
                                        (when (and (= pid (sc/spin-id d))
                                                   (compare-and-set! forced? false true))
                                          (is (identical? old (:result opts)))
                                          ;; The following world sees a source cache
                                          ;; commit AFTER dispatch sampled the Result.
                                          ;; Future source completions do not wake it.
                                          (simple/cache-result! source (sc/spin-id b) (sc/ok 2)))
                                        (claim! rt pid cid opts)))]
                         (b identity identity)
                         (simple/drain-events! world (:executor world)))
                       (is @forced?)
                       (is (= [:ok [2 0]] (cached world d)))
                       (is (= [[0 0] [2 0]] @seen))
                       (is (= [:ok [0 0]] (cached source d))))
                     (finally (ctx/close-context! world))))))))
         (done)))
