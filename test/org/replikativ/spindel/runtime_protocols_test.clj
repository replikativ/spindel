(ns org.replikativ.spindel.runtime-protocols-test
  "Tests for runtime protocol implementations: PGraph, PDepsTracking, PSpinLifecycle, PState, etc."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.engine.impl.graph :as graph]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.test-async :refer [await-drain]]))

;; =============================================================================
;; PGraph Protocol Tests - Dependency Graph Management
;; =============================================================================

(deftest test-pgraph-record-deps
  (testing "record-deps! commits tracked dependencies to graph"
    (let [ctx (ctx/create-execution-context)]
      (binding [ec/*execution-context* ctx]
        (let [signal1 (sig/signal 0)
              signal2 (sig/signal 0)
              spin-id :test-spin]

          ;; Simulate tracking dependencies
          (rtp/track-signal-dep! ctx spin-id (:id signal1))
          (rtp/track-signal-dep! ctx spin-id (:id signal2))

          ;; Commit to graph
          (rtp/record-deps! ctx spin-id)

          ;; Verify dependencies stored in SpinNode (Phase 1B)
          (let [spin-node (ec/get-state [:nodes spin-id])
                deps (:deps spin-node)]
            (is (some? spin-node))
            (is (contains? (:signals deps) (:id signal1)))
            (is (contains? (:signals deps) (:id signal2)))))))))

(deftest test-pgraph-clear-deps
  (testing "clear-deps! removes spin from graph and observers"
    (let [ctx (ctx/create-execution-context)]
      (binding [ec/*execution-context* ctx]
        (let [signal1 (sig/signal 0)
              spin-id :test-spin]

          ;; Setup dependencies
          (rtp/track-signal-dep! ctx spin-id (:id signal1))
          (rtp/record-deps! ctx spin-id)

          ;; Verify dependencies exist (Phase 1B: check SpinNode deps)
          (let [spin-node (ec/get-state [:nodes spin-id])]
            (is (some? spin-node))
            (is (some? (:deps spin-node))))

          ;; Clear dependencies
          (rtp/clear-deps! ctx spin-id)

          ;; Verify cleanup (deps should be empty)
          (let [spin-node (ec/get-state [:nodes spin-id])
                deps (:deps spin-node)]
            (is (empty? (:signals deps)))
            (is (empty? (:spins deps))))
          (let [signal-state (sig/get-signal-state signal1)]
            (is (not (contains? (:observers signal-state) spin-id)))))))))

(deftest test-pgraph-ordered-observers
  (testing "ordered-observers returns observers in topological order"
    (let [ctx (ctx/create-execution-context)]
      (binding [ec/*execution-context* ctx]
        (let [counter (sig/signal 0)
              spin1 (spin
                      (let [{:keys [new]} (track counter)]
                        new))
              spin2 (spin
                      (let [t1-val (await spin1)]
                        (* 2 t1-val)))
              spin3 (spin
                      (let [t2-val (await spin2)]
                        (* 3 t2-val)))]

          ;; Execute to establish dependencies
          @spin1
          @spin2
          @spin3

          ;; Get ordered observers for the signal
          (let [rt-state (ec/get-state [])
                observers (graph/ordered-observers rt-state (:id counter))]
            ;; All three spins should be in the list
            (is (seq observers))
            ;; spin1 should come before spin2, spin2 before spin3
            (let [t1-idx (.indexOf observers (spin-core/spin-id spin1))
                  t2-idx (.indexOf observers (spin-core/spin-id spin2))
                  t3-idx (.indexOf observers (spin-core/spin-id spin3))]
              (is (< t1-idx t2-idx) "spin1 should be before spin2")
              (is (< t2-idx t3-idx) "spin2 should be before spin3"))))))))

;; =============================================================================
;; PDepsTracking Protocol Tests - Transient Dependency Tracking
;; =============================================================================

(deftest test-pdeps-tracking-signal
  (testing "track-signal-dep! records signal dependencies"
    (let [ctx (ctx/create-execution-context)]
      (binding [ec/*execution-context* ctx]
        (let [signal1 (sig/signal 0)
              spin-id :test-spin]

          ;; Track signal dependency
          (rtp/track-signal-dep! ctx spin-id (:id signal1))

          ;; Verify tracking state (stored in :signal-generations map)
          (let [tracked (ec/get-state [:spin-tracking spin-id])]
            (is (some? tracked))
            (is (contains? (:signal-generations tracked) (:id signal1)))))))))

(deftest test-pdeps-tracking-spin
  (testing "track-spin-dep! records spin dependencies"
    (let [ctx (ctx/create-execution-context)]
      (binding [ec/*execution-context* ctx]
        (let [parent-id :parent-spin
              child-id :child-spin]

          ;; Track spin dependency
          (rtp/track-spin-dep! ctx parent-id child-id)

          ;; Verify tracking state (stored in :spin-hashes map)
          (let [tracked (ec/get-state [:spin-tracking parent-id])]
            (is (some? tracked))
            (is (contains? (:spin-hashes tracked) child-id))))))))

(deftest test-pdeps-tracking-multiple
  (testing "Multiple dependencies can be tracked"
    (let [ctx (ctx/create-execution-context)]
      (binding [ec/*execution-context* ctx]
        (let [sig1 (sig/signal 0)
              sig2 (sig/signal 0)
              spin-id :test-spin
              child-id :child-spin]

          ;; Track multiple dependencies
          (rtp/track-signal-dep! ctx spin-id (:id sig1))
          (rtp/track-signal-dep! ctx spin-id (:id sig2))
          (rtp/track-spin-dep! ctx spin-id child-id)

          ;; Verify all tracked (stored in :signal-generations and :spin-hashes maps)
          (let [tracked (ec/get-state [:spin-tracking spin-id])]
            (is (= 2 (count (:signal-generations tracked))))
            (is (= 1 (count (:spin-hashes tracked))))))))))

;; =============================================================================
;; PSpinLifecycle Protocol Tests - Spin Lifecycle Management
;; =============================================================================

(deftest test-pspin-lifecycle-register
  (testing "register-spin! stores spin metadata"
    (let [ctx (ctx/create-execution-context)]
      (binding [ec/*execution-context* ctx]
        (let [spin-id :test-spin
              spin-meta {:created-at (System/currentTimeMillis)}]

          ;; Register spin
          (rtp/register-spin! ctx spin-id spin-meta)

          ;; Verify metadata stored
          (let [stored-meta (ec/get-state [:spins-meta spin-id])]
            (is (some? stored-meta))
            (is (= spin-meta stored-meta))))))))

(deftest test-pspin-lifecycle-cache-value
  (testing "cache-result! stores result and marks clean"
    (let [ctx (ctx/create-execution-context)]
      (binding [ec/*execution-context* ctx]
        (let [spin-id :test-spin]

          ;; Cache successful result
          (rtp/cache-result! ctx spin-id (spin-core/ok 42))

          ;; Verify cached
          (let [cached (ec/get-state [:nodes spin-id])
                res (rtp/current-result ctx spin-id)]
            (is (some? cached))
            (is (= :clean (:status cached)))
            (is (spin-core/ok? res))
            (is (= 42 (spin-core/unwrap res)))
            (is (true? (:completed? cached)))))))))

(deftest test-pspin-lifecycle-cache-error
  (testing "cache-result! stores errors"
    (let [ctx (ctx/create-execution-context)]
      (binding [ec/*execution-context* ctx]
        (let [spin-id :test-spin
              error (ex-info "Test error" {:code 42})]

          ;; Cache error result
          (rtp/cache-result! ctx spin-id (spin-core/error error))

          ;; Verify cached
          (let [cached (ec/get-state [:nodes spin-id])
                res (rtp/current-result ctx spin-id)]
            (is (= :clean (:status cached)))
            (is (spin-core/error? res))
            (is (thrown? clojure.lang.ExceptionInfo (spin-core/unwrap res)))))))))

(deftest test-pspin-lifecycle-mark-dirty
  (testing "mark-dirty! changes status to dirty"
    (let [ctx (ctx/create-execution-context)]
      (binding [ec/*execution-context* ctx]
        (let [spin-id :test-spin]

          ;; Cache clean value
          (rtp/cache-result! ctx spin-id (spin-core/ok 42))
          (is (= :clean (get-in (ec/get-state [:nodes spin-id]) [:status])))
          (is (true? (rtp/clean? ctx spin-id)))

          ;; Mark dirty
          (rtp/mark-dirty! ctx spin-id)

          ;; Verify dirty
          (let [cached (ec/get-state [:nodes spin-id])]
            (is (false? (:completed? cached)))
            (is (= :dirty (:status cached)))
            (is (true? (rtp/dirty? ctx spin-id)))))))))

(deftest test-pspin-lifecycle-current-value
  (testing "current-result retrieves cached result"
    (let [ctx (ctx/create-execution-context)]
      (binding [ec/*execution-context* ctx]
        (let [spin-id :test-spin]

          ;; Initially no cached value
          (is (nil? (rtp/current-result ctx spin-id)))

          ;; Cache value
          (rtp/cache-result! ctx spin-id (spin-core/ok 42))

          ;; Retrieve cached value
          (let [res (rtp/current-result ctx spin-id)]
            (is (spin-core/ok? res))
            (is (= 42 (spin-core/unwrap res)))))))))

;; =============================================================================
;; PContinuation Protocol Tests - Continuation Management
;; =============================================================================

(deftest test-pcontinuation-add-remove
  (testing "add-continuation! and remove-continuation! work correctly"
    (let [ctx (ctx/create-execution-context)]
      (binding [ec/*execution-context* ctx]
        (let [spin-id :test-spin
              cont {:event-key [:signal :sig-1]
                    :on-resume (fn [_] 42)
                    :resolve-fn identity
                    :reject-fn identity}]

          ;; Add continuation
          (let [added-cont (rtp/add-continuation! ctx spin-id cont)]
            (is (some? (:id added-cont)))
            (is (some? (:order added-cont)))

            ;; Verify stored
            (let [stored (ec/get-state [:continuations spin-id (:id added-cont)])]
              (is (some? stored)))

            ;; Remove continuation
            (rtp/remove-continuation! ctx spin-id (:id added-cont))

            ;; Verify removed
            (is (nil? (ec/get-state [:continuations spin-id (:id added-cont)])))))))))

(deftest test-pcontinuation-earliest
  (testing "earliest-continuation returns earliest by order"
    (let [ctx (ctx/create-execution-context)]
      (binding [ec/*execution-context* ctx]
        (let [spin-id :test-spin
              sig-id :sig-1
              cont1 {:event-key [:signal sig-id]
                     :on-resume (fn [_] 1)
                     :resolve-fn identity
                     :reject-fn identity}
              cont2 {:event-key [:signal sig-id]
                     :on-resume (fn [_] 2)
                     :resolve-fn identity
                     :reject-fn identity}]

          ;; Add two continuations
          (rtp/add-continuation! ctx spin-id cont1)
          (rtp/add-continuation! ctx spin-id cont2)

          ;; Get earliest
          (let [earliest (rtp/earliest-continuation ctx spin-id sig-id)]
            (is (some? earliest))
            (is (= 1 (:order earliest)))))))))

;; =============================================================================
;; PState Protocol Tests - State Management
;; =============================================================================

(deftest test-pstate-swap
  (testing "swap-state! atomically updates state"
    (let [ctx (ctx/create-execution-context)]
      (binding [ec/*execution-context* ctx]
        ;; Initialize some state
        (ec/swap-state! [:test-data] (constantly {:counter 0}))

        ;; Update via swap-state!
        (ec/swap-state! [:test-data :counter] inc)

        ;; Verify updated
        (is (= 1 (ec/get-state [:test-data :counter])))))))

(deftest test-pstate-swap-with-function
  (testing "swap-state! applies function correctly"
    (let [ctx (ctx/create-execution-context)]
      (binding [ec/*execution-context* ctx]
        ;; Initialize
        (ec/swap-state! [:numbers] (constantly []))

        ;; Append multiple values
        (ec/swap-state! [:numbers] #(conj % 1))
        (ec/swap-state! [:numbers] #(conj % 2))
        (ec/swap-state! [:numbers] #(conj % 3))

        ;; Verify
        (is (= [1 2 3] (ec/get-state [:numbers])))))))

(deftest test-pstate-get
  (testing "get-state retrieves values at path"
    (let [ctx (ctx/create-execution-context)]
      (binding [ec/*execution-context* ctx]
        ;; Set up nested state
        (ec/swap-state! [:test-data] (constantly {:a {:b {:c 42}}}))

        ;; Retrieve at different levels
        (is (some? (ec/get-state [:test-data])))
        (is (some? (ec/get-state [:test-data :a])))
        (is (some? (ec/get-state [:test-data :a :b])))
        (is (= 42 (ec/get-state [:test-data :a :b :c])))

        ;; Non-existent path
        (is (nil? (ec/get-state [:non-existent])))))))

(deftest test-pstate-nested-updates
  (testing "swap-state! works with nested paths"
    (let [ctx (ctx/create-execution-context)]
      (binding [ec/*execution-context* ctx]
        ;; Initialize nested structure
        (ec/swap-state! [:users] (constantly {}))
        (ec/swap-state! [:users :user-1] (constantly {:name "Alice" :age 30}))
        (ec/swap-state! [:users :user-2] (constantly {:name "Bob" :age 25}))

        ;; Update nested value
        (ec/swap-state! [:users :user-1 :age] inc)

        ;; Verify
        (is (= 31 (ec/get-state [:users :user-1 :age])))
        (is (= 25 (ec/get-state [:users :user-2 :age])))))))

;; =============================================================================
;; PEngine Protocol Tests - Event Queue
;; =============================================================================

(deftest test-penqueue-event!
  (testing "enqueue! adds events to queue"
    (let [ctx (ctx/create-execution-context)]
      (binding [ec/*execution-context* ctx]
        ;; Enqueue signal change event
        (rtp/enqueue! ctx {:type :signal-change :id :sig-1})

        ;; Verify event in queue (implementation detail, but we can check)
        (let [pending (ec/get-state [:engine/pending])]
          (is (some? pending)))))))

;; =============================================================================
;; Integration Tests - Multiple Protocols Working Together
;; =============================================================================

(deftest test-protocols-integration-signal-spin-flow
  (testing "Full flow: track deps, cache value, mark dirty, re-execute"
    (let [ctx (ctx/create-execution-context)]
      (binding [ec/*execution-context* ctx]
        (let [counter (sig/signal 0)
              doubled (spin
                        (let [{:keys [new]} (track counter)]
                          (* 2 new)))]

          ;; Execute spin - establishes dependencies
          (is (= 0 @doubled))

          ;; Verify spin is cached
          (let [res (rtp/current-result ctx (spin-core/spin-id doubled))]
            (is (rtp/clean? ctx (spin-core/spin-id doubled)))
            (is (spin-core/ok? res))
            (is (= 0 (spin-core/unwrap res))))

          ;; Update signal - marks spin dirty
          (swap! counter inc)
          (await-drain ctx)  ; Wait for :signal-updated event to be processed

          ;; Re-execute - gets new value
          (is (= 2 @doubled))

          ;; Verify new cached value
          (let [res (rtp/current-result ctx (spin-core/spin-id doubled))]
            (is (rtp/clean? ctx (spin-core/spin-id doubled)))
            (is (spin-core/ok? res))
            (is (= 2 (spin-core/unwrap res)))))))))

(deftest test-protocols-integration-observer-chain
  (testing "Observer chain maintains consistency across protocols"
    (let [ctx (ctx/create-execution-context)]
      (binding [ec/*execution-context* ctx]
        (let [source (sig/signal 1)
              spin1 (spin
                      (let [{:keys [new]} (track source)]
                        (* 2 new)))
              spin2 (spin
                      (let [t1 (await spin1)]
                        (* 3 t1)))]

          ;; Execute chain
          @spin1
          @spin2

          ;; Verify dependencies recorded (Phase 1B: read from SpinNode :deps)
          (let [t1-node (ec/get-state [:nodes (spin-core/spin-id spin1)])
                t2-node (ec/get-state [:nodes (spin-core/spin-id spin2)])
                t1-deps (:deps t1-node)
                t2-deps (:deps t2-node)]
            (is (contains? (:signals t1-deps) (:id source)))
            (is (contains? (:spins t2-deps) (spin-core/spin-id spin1))))

          ;; Update signal
          (swap! source + 1)
          (await-drain ctx)

          ;; Both spins should update
          (is (= 4 @spin1))
          (is (= 12 @spin2)))))))
