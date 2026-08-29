(ns org.replikativ.spindel.runtime-protocols-test
  "Tests for runtime protocol implementations: PGraph, PDepsTracking, PSpinLifecycle, PState, etc."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.engine.impl.graph :as graph]
            [org.replikativ.spindel.engine.nodes :as nodes]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.test-async :refer [await-drain]]
            [org.replikativ.spindel.test-helpers :as th]))

;; =============================================================================
;; PGraph Protocol Tests - Dependency Graph Management
;; =============================================================================

(deftest test-pgraph-record-deps
  (testing "record-deps! commits tracked dependencies to graph"
    (th/with-ctx [ctx]
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
          (is (contains? (:signals deps) (:id signal2))))))))

(deftest test-pgraph-clear-deps
  (testing "clear-deps! removes spin from graph and observers"
    (th/with-ctx [ctx]
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
          (is (not (contains? (:observers signal-state) spin-id))))))))

(deftest test-pgraph-ordered-observers
  (testing "ordered-observers returns observers in topological order"
    (th/with-ctx [ctx]
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
            (is (< t2-idx t3-idx) "spin2 should be before spin3")))))))

;; =============================================================================
;; PDepsTracking Protocol Tests - Transient Dependency Tracking
;; =============================================================================

(deftest test-pdeps-tracking-signal
  (testing "track-signal-dep! records signal dependencies"
    (th/with-ctx [ctx]
      (let [signal1 (sig/signal 0)
            spin-id :test-spin]

        ;; Track signal dependency
        (rtp/track-signal-dep! ctx spin-id (:id signal1))

        ;; Verify tracking state
        (let [tracked (ec/get-state [:spin-tracking spin-id])]
          (is (some? tracked))
          (is (contains? (:signals tracked) (:id signal1))))))))

(deftest test-pdeps-tracking-spin
  (testing "track-spin-dep! records spin dependencies"
    (th/with-ctx [ctx]
      (let [parent-id :parent-spin
            child-id :child-spin]

        ;; Track spin dependency
        (rtp/track-spin-dep! ctx parent-id child-id)

        ;; Verify tracking state
        (let [tracked (ec/get-state [:spin-tracking parent-id])]
          (is (some? tracked))
          (is (contains? (:spins tracked) child-id)))))))

(deftest test-pdeps-tracking-multiple
  (testing "Multiple dependencies can be tracked"
    (th/with-ctx [ctx]
      (let [sig1 (sig/signal 0)
            sig2 (sig/signal 0)
            spin-id :test-spin
            child-id :child-spin]

        ;; Track multiple dependencies
        (rtp/track-signal-dep! ctx spin-id (:id sig1))
        (rtp/track-signal-dep! ctx spin-id (:id sig2))
        (rtp/track-spin-dep! ctx spin-id child-id)

        ;; Verify all tracked
        (let [tracked (ec/get-state [:spin-tracking spin-id])]
          (is (= 2 (count (:signals tracked))))
          (is (= 1 (count (:spins tracked)))))))))

;; =============================================================================
;; PSpinLifecycle Protocol Tests - Spin Lifecycle Management
;; =============================================================================

(deftest test-pspin-lifecycle-register
  (testing "register-spin! stores spin metadata"
    (th/with-ctx [ctx]
      (let [spin-id :test-spin
            spin-meta {:created-at (System/currentTimeMillis)}]

        ;; Register spin
        (rtp/register-spin! ctx spin-id spin-meta)

        ;; Verify metadata stored
        (let [stored-meta (ec/get-state [:spins-meta spin-id])]
          (is (some? stored-meta))
          (is (= spin-meta stored-meta)))))))

(deftest test-pspin-lifecycle-cache-value
  (testing "cache-result! stores result and marks clean"
    (th/with-ctx [ctx]
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
          (is (true? (:completed? cached))))))))

(deftest test-pspin-lifecycle-cache-error
  (testing "cache-result! stores errors"
    (th/with-ctx [ctx]
      (let [spin-id :test-spin
            error (ex-info "Test error" {:code 42})]

        ;; Cache error result
        (rtp/cache-result! ctx spin-id (spin-core/error error))

        ;; Verify cached
        (let [cached (ec/get-state [:nodes spin-id])
              res (rtp/current-result ctx spin-id)]
          (is (= :clean (:status cached)))
          (is (spin-core/error? res))
          (is (thrown? clojure.lang.ExceptionInfo (spin-core/unwrap res))))))))

(deftest test-pspin-lifecycle-mark-dirty
  (testing "mark-dirty! changes status to dirty"
    (th/with-ctx [ctx]
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
          (is (true? (rtp/dirty? ctx spin-id))))))))

(deftest test-pspin-lifecycle-current-value
  (testing "current-result retrieves cached result"
    (th/with-ctx [ctx]
      (let [spin-id :test-spin]

        ;; Initially no cached value
        (is (nil? (rtp/current-result ctx spin-id)))

        ;; Cache value
        (rtp/cache-result! ctx spin-id (spin-core/ok 42))

        ;; Retrieve cached value
        (let [res (rtp/current-result ctx spin-id)]
          (is (spin-core/ok? res))
          (is (= 42 (spin-core/unwrap res))))))))

;; =============================================================================
;; PContinuation Protocol Tests - Continuation Management
;; =============================================================================

(deftest test-pcontinuation-add-remove
  (testing "add-continuation! and remove-continuation! work correctly"
    (th/with-ctx [ctx]
      (let [spin-id :test-spin
            cont {:event-key [:signal :sig-1]
                  :kind :track
                  :on-resume (fn [_] 42)
                  :resolve-fn identity
                  :reject-fn identity}]

        ;; Add continuation
        (let [added-cont (rtp/add-continuation! ctx spin-id cont)]
          (is (some? (:id added-cont)))
          (is (some? (:order added-cont)))

          ;; Verify stored — a :track cont lands in :track-subscriptions.
          (let [stored (ec/get-state [:track-subscriptions spin-id (:id added-cont)])]
            (is (some? stored)))

          ;; Remove continuation. Exactly one caller claims the descriptor.
          (is (= (:id added-cont)
                 (:id (rtp/remove-continuation! ctx spin-id (:id added-cont)))))
          (is (nil? (rtp/remove-continuation! ctx spin-id (:id added-cont)))
              "a spent continuation cannot be claimed twice")

          ;; Verify removed
          (is (nil? (ec/get-state [:track-subscriptions spin-id (:id added-cont)]))))))))

(deftest replacing-continuation-detaches-previous-reverse-edge
  (testing "a deterministic continuation ID can advance to another child"
    (let [context (ctx/create-execution-context)
          spin-id :reawait-parent
          cont-id :reused-await-cont
          base {:id cont-id
                :kind :await-once
                :on-resume identity
                :resolve-fn identity
                :reject-fn identity}]
      (try
        (rtp/add-continuation!
         context spin-id (assoc base :event-key [:spin/complete :old-child]))
        (rtp/add-continuation!
         context spin-id (assoc base :event-key [:spin/complete :new-child]))
        (is (empty? (or (rtp/get-state
                         context
                         [:subscriptions [:spin/complete :old-child] spin-id])
                        #{}))
            "the obsolete child cannot resume the replacement")
        (is (= #{cont-id}
               (rtp/get-state
                context
                [:subscriptions [:spin/complete :new-child] spin-id])))
        (is (= :new-child
               (-> (rtp/get-state context [:await-conts spin-id cont-id])
                   :event-key second)))
        (is (some? (simple/claim-continuation-for-resume!
                    context spin-id cont-id)))
        (is (contains? (rtp/get-state context [:engine/resuming-conts])
                       [spin-id cont-id]))
        (simple/release-continuation-resume! context spin-id cont-id)
        (is (not (contains? (rtp/get-state context [:engine/resuming-conts])
                            [spin-id cont-id])))
        (finally
          (ctx/close-context! context))))))

(deftest truncating-stale-continuations-detaches-reverse-edges
  (testing "reactive resume truncates both halves of every later await edge"
    (let [context (ctx/create-execution-context)
          spin-id :truncate-parent
          mk-cont (fn [cont-id child-id order]
                    {:id cont-id
                     :event-key [:spin/complete child-id]
                     :kind :await-once
                     :order order
                     :on-resume identity
                     :resolve-fn identity
                     :reject-fn identity})
          resumed (mk-cont :resumed :resumed-child 0)
          stale (mk-cont :stale :stale-child 1)]
      (try
        (rtp/add-continuation! context spin-id stale)
        ((ns-resolve 'org.replikativ.spindel.engine.impl.simple
                     'truncate-stale-conts!)
         context spin-id resumed)
        (is (nil? (rtp/get-state context [:await-conts spin-id :stale])))
        (is (empty? (or (rtp/get-state
                         context
                         [:subscriptions [:spin/complete :stale-child] spin-id])
                        #{}))
            "the obsolete completion cannot repeatedly diagnose a missing cont")
        (finally
          (ctx/close-context! context))))))

(deftest terminal-parent-converges-stale-completion-edge
  (testing "an in-flight completion after terminal settlement is benign and pruned"
    (let [context (ctx/create-execution-context)
          parent-id :terminal-parent
          child-id :late-child
          cont-id :already-spent]
      (try
        (rtp/swap-state! context [:nodes parent-id]
                         (constantly
                          (nodes/->spin-node :cancelled :clean true false
                                             #{} {} nil #{})))
        (rtp/swap-state! context
                         [:subscriptions [:spin/complete child-id] parent-id]
                         (constantly #{cont-id}))
        (simple/process-event! context {:type :spin-completion :id child-id})
        (is (empty? (or (rtp/get-state
                         context
                         [:subscriptions [:spin/complete child-id] parent-id])
                        #{}))
            "one late event repairs the obsolete reverse edge")
        (finally
          (ctx/close-context! context))))))

(deftest fork-overlay-continuation-claim-has-one-winner
  (testing "completion and cancellation atomically arbitrate in a fork overlay"
    (let [parent (ctx/create-execution-context)]
      (try
        ;; Register before forking: await conts and their reverse subscriptions
        ;; are copied into one fork-local graph snapshot.
        (dotimes [i 100]
          (let [spin-id (keyword (str "fork-claim-spin-" i))
                child-id (keyword (str "fork-claim-child-" i))
                cont-id (keyword (str "fork-claim-cont-" i))
                cont {:id cont-id
                      :event-key [:spin/complete child-id]
                      :kind :await-once
                      :on-resume identity
                      :resolve-fn identity
                      :reject-fn identity}]
            (rtp/add-continuation! parent spin-id cont)))
        (let [fork (ctx/fork-context parent)]
          (try
            (dotimes [i 100]
              (let [spin-id (keyword (str "fork-claim-spin-" i))
                    child-id (keyword (str "fork-claim-child-" i))
                    cont-id (keyword (str "fork-claim-cont-" i))
                    start (promise)
                    completion (future
                                 @start
                                 (simple/claim-continuation-for-resume!
                                  fork spin-id cont-id))
                    cancellation (future
                                   @start
                                   (rtp/remove-continuation!
                                    fork spin-id cont-id {:cancel? true}))]
                (deliver start true)
                (is (= 1 (count (filter some? [@completion @cancellation])))
                    "exactly one side owns the CPS continuation")
                (is (empty? (or (rtp/get-state
                                 fork
                                 [:subscriptions [:spin/complete child-id] spin-id])
                                #{}))
                    "a tombstone prevents the removed reverse edge falling through")))
            (finally
              (ctx/close-context! fork))))
        (finally
          (ctx/close-context! parent))))))

(deftest fork-does-not-observe-post-fork-parent-subscriptions
  (testing "a fork cannot see one half of a continuation registered later"
    (let [parent (ctx/create-execution-context)
          fork (ctx/fork-context parent)
          spin-id :post-fork-parent
          child-id :post-fork-child
          cont-id :post-fork-cont]
      (try
        (rtp/add-continuation!
         parent spin-id
         {:id cont-id
          :event-key [:spin/complete child-id]
          :kind :await-once
          :on-resume identity
          :resolve-fn identity
          :reject-fn identity})
        (is (some? (rtp/get-state parent [:await-conts spin-id cont-id])))
        (is (contains? (rtp/get-state
                        parent [:subscriptions [:spin/complete child-id] spin-id])
                       cont-id))
        (is (nil? (rtp/get-state fork [:await-conts spin-id cont-id])))
        (is (empty? (or (rtp/get-state
                         fork [:subscriptions [:spin/complete child-id] spin-id])
                        #{}))
            "the reverse index shares the continuation snapshot boundary")
        (finally
          (ctx/close-context! fork)
          (ctx/close-context! parent))))))

(deftest nested-fork-removal-does-not-resurrect-reverse-subscription
  (testing "whole-state claims materialize the complete overlay ancestry"
    (let [root (ctx/create-execution-context)
          spin-id :nested-parent
          child-a :nested-child-a
          child-b :nested-child-b]
      (try
        (doseq [[child-id cont-id] [[child-a :nested-cont-a]
                                    [child-b :nested-cont-b]]]
          (rtp/add-continuation!
           root spin-id
           {:id cont-id
            :event-key [:spin/complete child-id]
            :kind :await-once
            :on-resume identity
            :resolve-fn identity
            :reject-fn identity}))
        (let [fork-1 (ctx/fork-context root)]
          (try
            (is (some? (rtp/remove-continuation!
                        fork-1 spin-id :nested-cont-a {:cancel? true})))
            (let [fork-2 (ctx/fork-context fork-1)]
              (try
                (is (some? (simple/claim-continuation-for-resume!
                            fork-2 spin-id :nested-cont-b)))
                (is (empty? (or (rtp/get-state
                                 fork-2
                                 [:subscriptions [:spin/complete child-b]
                                  spin-id])
                                #{}))
                    "the removed edge cannot fall through either overlay")
                (is (nil? (rtp/get-state
                           fork-2 [:await-conts spin-id :nested-cont-a]))
                    "the parent fork's tombstone remains materialized")
                (finally
                  (ctx/close-context! fork-2))))
            (finally
              (ctx/close-context! fork-1))))
        (finally
          (ctx/close-context! root))))))

(deftest reactive-resume-release-preserves-absent-continuation
  (testing "cancellation during resume is not replaced with a nil entry"
    (let [context (ctx/create-execution-context)]
      (try
        (simple/release-reactive-resume! context :reactive-parent :spent-cont)
        (is (nil? (rtp/get-state
                   context [:await-conts :reactive-parent :spent-cont])))
        (is (empty? (or (rtp/get-state
                         context [:await-conts :reactive-parent])
                        {})))
        (finally
          (ctx/close-context! context))))))

(deftest test-pcontinuation-earliest
  (testing "earliest-continuation returns earliest by order"
    (th/with-ctx [ctx]
      (let [spin-id :test-spin
            sig-id :sig-1
            cont1 {:event-key [:signal sig-id]
                   :kind :track
                   :on-resume (fn [_] 1)
                   :resolve-fn identity
                   :reject-fn identity}
            cont2 {:event-key [:signal sig-id]
                   :kind :track
                   :on-resume (fn [_] 2)
                   :resolve-fn identity
                   :reject-fn identity}]

        ;; Add two continuations
        (rtp/add-continuation! ctx spin-id cont1)
        (rtp/add-continuation! ctx spin-id cont2)

        ;; Get earliest
        (let [earliest (rtp/earliest-continuation ctx spin-id sig-id)]
          (is (some? earliest))
          (is (= 1 (:order earliest))))))))

;; =============================================================================
;; PState Protocol Tests - State Management
;; =============================================================================

(deftest test-pstate-swap
  (testing "swap-state! atomically updates state"
    (th/with-ctx [_ctx]
      ;; Initialize some state
      (ec/swap-state! [:test-data] (constantly {:counter 0}))

      ;; Update via swap-state!
      (ec/swap-state! [:test-data :counter] inc)

      ;; Verify updated
      (is (= 1 (ec/get-state [:test-data :counter]))))))

(deftest test-pstate-swap-with-function
  (testing "swap-state! applies function correctly"
    (th/with-ctx [_ctx]
      ;; Initialize
      (ec/swap-state! [:numbers] (constantly []))

      ;; Append multiple values
      (ec/swap-state! [:numbers] #(conj % 1))
      (ec/swap-state! [:numbers] #(conj % 2))
      (ec/swap-state! [:numbers] #(conj % 3))

      ;; Verify
      (is (= [1 2 3] (ec/get-state [:numbers]))))))

(deftest test-pstate-get
  (testing "get-state retrieves values at path"
    (th/with-ctx [_ctx]
      ;; Set up nested state
      (ec/swap-state! [:test-data] (constantly {:a {:b {:c 42}}}))

      ;; Retrieve at different levels
      (is (some? (ec/get-state [:test-data])))
      (is (some? (ec/get-state [:test-data :a])))
      (is (some? (ec/get-state [:test-data :a :b])))
      (is (= 42 (ec/get-state [:test-data :a :b :c])))

      ;; Non-existent path
      (is (nil? (ec/get-state [:non-existent]))))))

(deftest test-pstate-nested-updates
  (testing "swap-state! works with nested paths"
    (th/with-ctx [_ctx]
      ;; Initialize nested structure
      (ec/swap-state! [:users] (constantly {}))
      (ec/swap-state! [:users :user-1] (constantly {:name "Alice" :age 30}))
      (ec/swap-state! [:users :user-2] (constantly {:name "Bob" :age 25}))

      ;; Update nested value
      (ec/swap-state! [:users :user-1 :age] inc)

      ;; Verify
      (is (= 31 (ec/get-state [:users :user-1 :age])))
      (is (= 25 (ec/get-state [:users :user-2 :age]))))))

;; =============================================================================
;; PEngine Protocol Tests - Event Queue
;; =============================================================================

(deftest test-penqueue-event!
  (testing "enqueue! adds events to queue"
    (th/with-ctx [ctx]
      ;; Enqueue signal change event
      (rtp/enqueue! ctx {:type :signal-change :id :sig-1})

      ;; Verify event in queue (implementation detail, but we can check)
      (let [pending (ec/get-state [:engine/pending])]
        (is (some? pending))))))

;; =============================================================================
;; Integration Tests - Multiple Protocols Working Together
;; =============================================================================

(deftest test-protocols-integration-signal-spin-flow
  (testing "Full flow: track deps, cache value, mark dirty, re-execute"
    (th/with-ctx [ctx]
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
          (is (= 2 (spin-core/unwrap res))))))))

(deftest test-protocols-integration-observer-chain
  (testing "Observer chain maintains consistency across protocols"
    (th/with-ctx [ctx]
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
        (is (= 12 @spin2))))))
