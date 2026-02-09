(ns org.replikativ.spindel.runtime.execution-context-test
  "Tests for ExecutionContext - Phase 2 fork-safe runtime."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.runtime.context :as ctx]
            [org.replikativ.spindel.runtime.core :as rtc]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.runtime.protocols :as rtp]
            [org.replikativ.spindel.runtime.impl.simple :as simple]
            [org.replikativ.spindel.runtime.state-backend :as backend]
            [org.replikativ.spindel.runtime.nodes :as nodes]))

(deftest test-execution-context-creation
  (testing "ExecutionContext can be created with default options"
    (let [ctx (ctx/create-execution-context)]
      (try
        (is (some? ctx))
        (is (some? (:fork-id ctx)))
        (is (nil? (:parent-ctx ctx)))
        (is (some? (:backend ctx)))
        (is (some? (:executor ctx)))
        (is (= {} (:bindings ctx)))
        (is (= {} (:metadata ctx)))
        (finally
          (ctx/stop-context! ctx))))))

(deftest test-execution-context-protocols
  (testing "ExecutionContext implements all required protocols"
    (let [ctx (ctx/create-execution-context)]
      (try
        (is (satisfies? rtp/PGraph ctx))
        (is (satisfies? rtp/PDepsTracking ctx))
        (is (satisfies? rtp/PSpinLifecycle ctx))
        (is (satisfies? rtp/PContinuation ctx))
        (is (satisfies? rtp/PEngine ctx))
        (is (satisfies? rtp/PScheduler ctx))
        (is (satisfies? rtp/PState ctx))
        (finally
          (ctx/stop-context! ctx))))))

(deftest test-execution-context-state-operations
  (testing "ExecutionContext state operations work correctly"
    (let [ctx (ctx/create-execution-context)]
      (try
        ;; Test swap-state!
        (rtp/swap-state! ctx [:test-key] (constantly 42))
        (is (= 42 (rtp/get-state ctx [:test-key])))

        ;; Test swap-state-args! - initialize vector first
        (rtp/swap-state! ctx [:test-vec] (constantly []))
        (rtp/swap-state-args! ctx [:test-vec] conj [1])
        (rtp/swap-state-args! ctx [:test-vec] conj [2])
        (rtp/swap-state-args! ctx [:test-vec] conj [3])
        (is (= [1 2 3] (rtp/get-state ctx [:test-vec])))

        ;; Test cas-state!
        (let [success (rtp/cas-state! ctx [:test-key] 42 99)]
          (is (= true success))
          (is (= 99 (rtp/get-state ctx [:test-key]))))

        ;; CAS should fail with wrong old value
        (let [success (rtp/cas-state! ctx [:test-key] 42 123)]
          (is (= false success))
          (is (= 99 (rtp/get-state ctx [:test-key]))))
        (finally
          (ctx/stop-context! ctx))))))

(deftest test-fork-creation
  (testing "Can fork execution context"
    (let [parent-ctx (ctx/create-execution-context)]
      (try
        ;; Set some state in parent
        (rtp/swap-state! parent-ctx [:test-data] (constantly {:value 42}))

        ;; Fork the context
        (let [fork-ctx (ctx/fork-context parent-ctx
                                         :metadata {:particle-id 1})]
          (is (some? fork-ctx))
          (is (some? (:fork-id fork-ctx)))
          (is (= parent-ctx (:parent-ctx fork-ctx)))
          (is (= {:particle-id 1} (:metadata fork-ctx)))

          ;; Fork should see parent state via overlay
          (is (= {:value 42} (rtp/get-state fork-ctx [:test-data])))

          ;; Mutations in fork don't affect parent
          (rtp/swap-state! fork-ctx [:test-data :value] (constantly 99))
          (is (= 99 (get-in (rtp/get-state fork-ctx [:test-data]) [:value])))
          (is (= 42 (get-in (rtp/get-state parent-ctx [:test-data]) [:value]))))
        (finally
          (ctx/stop-context! parent-ctx))))))

(deftest test-fork-with-state-updates
  (testing "Fork can update state during creation"
    (let [parent-ctx (ctx/create-execution-context)]
      (try
        (rtp/swap-state! parent-ctx [:signals] (constantly {:sig-1 {:snapshot 42}}))

        ;; Fork with initial overlay state
        (let [fork1 (ctx/fork-context parent-ctx
                                      :state-updates {:signals {:sig-1 {:snapshot 99}}})]
          (is (= 99 (get-in (rtp/get-state fork1 [:signals]) [:sig-1 :snapshot])))
          (is (= 42 (get-in (rtp/get-state parent-ctx [:signals]) [:sig-1 :snapshot]))))

        ;; Fork with different overlay state
        (let [fork2 (ctx/fork-context parent-ctx
                                      :state-updates {:signals {:sig-1 {:snapshot 77}}})]
          (is (= 77 (get-in (rtp/get-state fork2 [:signals]) [:sig-1 :snapshot]))))
        (finally
          (ctx/stop-context! parent-ctx))))))

(deftest test-fork-local-bindings
  (testing "Fork-local bindings are stored and merged correctly"
    (let [parent-ctx (ctx/create-execution-context
                      :bindings {:http-client :real-client
                                 :storage :real-storage})]
      (try
        ;; Check parent bindings
        (is (= {:http-client :real-client
                :storage :real-storage}
               (:bindings parent-ctx)))

        ;; Fork with override
        (let [fork-ctx (ctx/fork-context parent-ctx
                                         :bindings {:http-client :mock-client})]
          ;; Fork should have merged bindings (override http-client, keep storage)
          (is (= {:http-client :mock-client
                  :storage :real-storage}
                 (:bindings fork-ctx)))

          ;; Parent unchanged
          (is (= {:http-client :real-client
                  :storage :real-storage}
                 (:bindings parent-ctx))))

        ;; Fork with additional binding
        (let [fork-ctx (ctx/fork-context parent-ctx
                                         :bindings {:random-seed 12345})]
          ;; Fork should have all bindings
          (is (= {:http-client :real-client
                  :storage :real-storage
                  :random-seed 12345}
                 (:bindings fork-ctx))))
        (finally
          (ctx/stop-context! parent-ctx))))))

;; =============================================================================
;; Phase 3: Fork Testing & Validation
;; =============================================================================

(deftest test-fork-isolation-with-spins
  (testing "Spins execute with fork-local state (isolation)"
    ;; Create signal in parent BEFORE forking
    (let [parent-ctx (ctx/create-execution-context)]
      (try
        (binding [rtc/*execution-context* parent-ctx]
          (let [counter (sig/signal 100)]
            ;; NOW fork - both forks get copy of signal state
            (let [fork1 (ctx/fork-context parent-ctx)
                  fork2 (ctx/fork-context parent-ctx)]

              ;; Mutate signal in fork1 to value 42
              (binding [rtc/*execution-context* fork1]
                (swap! counter (constantly 42))
                (let [doubled (spin
                                (let [{:keys [new]} (track counter)]
                                  (* 2 new)))]
                  ;; Fork1 should see 42 * 2 = 84
                  (is (= 84 @doubled))))

              ;; Mutate signal in fork2 to value 99
              (binding [rtc/*execution-context* fork2]
                (swap! counter (constantly 99))
                (let [doubled (spin
                                (let [{:keys [new]} (track counter)]
                                  (* 2 new)))]
                  ;; Fork2 should see 99 * 2 = 198
                  (is (= 198 @doubled)))))))
        (finally
          (ctx/stop-context! parent-ctx))))))

(deftest test-local-cache-per-fork
  (testing "Spins cache independently in each fork"
    (let [parent-ctx (ctx/create-execution-context)
          execution-count (atom 0)]
      (try
        ;; Create signal and spin in parent BEFORE forking
        (binding [rtc/*execution-context* parent-ctx]
          (let [counter (sig/signal 42)
                ;; Create spin in parent that counts executions
                ;; Counter AFTER track so it increments on continuation resumption
                counting-spin (spin
                                (let [{:keys [new]} (track counter)]
                                  (swap! execution-count inc)
                                  (* 2 new)))]
            ;; Fork after spin creation - forks get copy of signal state
            (let [fork1 (ctx/fork-context parent-ctx)
                  fork2 (ctx/fork-context parent-ctx)]
              ;; Execute in fork1 (should run and cache)
              (binding [rtc/*execution-context* fork1]
                (is (= 84 @counting-spin))
                (is (= 1 @execution-count))
                ;; Execute again in fork1 (should hit cache)
                (is (= 84 @counting-spin))
                (is (= 1 @execution-count))) ; Still 1 - cache hit!
              ;; Execute in fork2 (independent cache - should re-execute)
              (binding [rtc/*execution-context* fork2]
                (is (= 84 @counting-spin))
                (is (= 2 @execution-count)) ; Incremented - cache miss!
                ;; Execute again in fork2 (should hit fork2's cache)
                (is (= 84 @counting-spin))
                (is (= 2 @execution-count))))))  ; Still 2 - cache hit!
        (finally
          (ctx/stop-context! parent-ctx))))))

(deftest test-fork-lazy-invalidation
  (testing "Fork only invalidates spins affected by modified signals"
    (let [parent-ctx (ctx/create-execution-context)
          count-1 (atom 0)
          count-2 (atom 0)]

      (binding [rtc/*execution-context* parent-ctx]
        (let [sig-1 (sig/signal 100)
              sig-2 (sig/signal 200)
              ;; spin-1 depends only on sig-1
              ;; Counter AFTER track so it increments on continuation resumption
              spin-1 (spin
                       (let [{:keys [new]} (track sig-1)]
                         (swap! count-1 inc)
                         new))
              ;; spin-2 depends only on sig-2
              ;; Counter AFTER track so it increments on continuation resumption
              spin-2 (spin
                       (let [{:keys [new]} (track sig-2)]
                         (swap! count-2 inc)
                         new))]

          ;; Execute both in parent
          (is (= 100 @spin-1))
          (is (= 1 @count-1))
          (is (= 200 @spin-2))
          (is (= 1 @count-2))

          ;; Fork and modify ONLY sig-1
          (let [fork (ctx/fork-context parent-ctx)]
            (binding [rtc/*execution-context* fork]
              ;; Modify sig-1 in fork
              (swap! sig-1 (constantly 42))

              ;; Wait for async drain from signal swap to complete
              ;; The async drain processes the :signal-change event and marks spins dirty
              (simple/await-drain-complete! fork)

              ;; spin-1 should re-execute (dirty due to sig-1 change)
              (is (= 42 @spin-1))
              (is (= 2 @count-1)) ; Incremented!

              ;; spin-2 should NOT re-execute (still clean - sig-2 unchanged)
              (is (= 200 @spin-2))
              (is (= 1 @count-2)))) ; Should stay 1 (not re-executed)

          ;; Verify parent unchanged
          (is (= 100 @spin-1))
          (is (= 2 @count-1))  ; Fork execution incremented count-1 (shared atom)
          (is (= 200 @spin-2))
          (is (= 1 @count-2))))))) ; spin-2 never re-executed

;; =============================================================================
;; Phase 3: Snapshot & Serialization Tests
;; =============================================================================

(deftest test-snapshot-independence
  (testing "Snapshot is fully independent from parent"
    (let [parent-ctx (ctx/create-execution-context)]
      (try
        (binding [rtc/*execution-context* parent-ctx]
          (let [sig (sig/signal 100)
                spin-1 (spin (let [{:keys [new]} (track sig)] new))]
            ;; Execute in parent
            (is (= 100 @spin-1))

            ;; Create snapshot
            (let [snapshot (ctx/snapshot-context parent-ctx)]

              ;; Modify signal in parent
              (swap! sig inc)
              (simple/await-drain-complete! parent-ctx)

              ;; Parent sees change
              (is (= 101 @sig))

              ;; Snapshot should be unchanged (independent copy)
              (binding [rtc/*execution-context* snapshot]
                (is (= 100 @sig))
                (is (= 100 @spin-1))))))
        (finally
          (ctx/stop-context! parent-ctx))))))

(deftest test-snapshot-backend-type
  (testing "Snapshot has immutable backend"
    (let [parent-ctx (ctx/create-execution-context)]
      (try
        (let [snapshot (ctx/snapshot-context parent-ctx)]
          (is (= :immutable (backend/backend-type (:backend snapshot))))
          (is (nil? (:parent-ctx snapshot)))  ; No parent
          (is (true? (get-in (:metadata snapshot) [:snapshot?]))))
        (finally
          (ctx/stop-context! parent-ctx))))))

(deftest test-serialization-roundtrip
  (testing "Serialize and deserialize preserves state"
    (let [ctx (ctx/create-execution-context)]
      (try
        (binding [rtc/*execution-context* ctx]
          (let [sig (sig/signal 42)
                spin-1 (spin (let [{:keys [new]} (track sig)] (* 2 new)))]
            ;; Execute spin
            (is (= 84 @spin-1))

            ;; Snapshot and serialize
            (let [snap (ctx/snapshot-context ctx)
                  serialized (ctx/serialize-context snap)]

              ;; Deserialize
              (let [restored-snap (ctx/deserialize-context serialized (:executor ctx))
                    restored (ctx/restore-snapshot restored-snap)]

                ;; State should be preserved
                (binding [rtc/*execution-context* restored]
                  (is (= 42 @sig))
                  (is (= 84 @spin-1)))))))
        (finally
          (ctx/stop-context! ctx))))))

(deftest test-restore-makes-backend-mutable
  (testing "Restore converts immutable backend to mutable"
    (let [ctx (ctx/create-execution-context)]
      (try
        (let [snap (ctx/snapshot-context ctx)
              restored (ctx/restore-snapshot snap)]

          ;; Snapshot is immutable
          (is (= :immutable (backend/backend-type (:backend snap))))

          ;; Restored is mutable (atom)
          (is (= :atom (backend/backend-type (:backend restored))))

          ;; Can modify state after restore
          (binding [rtc/*execution-context* restored]
            (let [sig (sig/signal 100)]
              (swap! sig inc)
              (is (= 101 @sig)))))
        (finally
          (ctx/stop-context! ctx))))))

(deftest test-signal-swap-after-restore
  (testing "Can swap signals after restore and spins re-execute"
    (let [ctx (ctx/create-execution-context)
          execution-count (atom 0)]
      (try
        (binding [rtc/*execution-context* ctx]
          (let [sig (sig/signal 10)
                ;; Counter AFTER track so it increments on continuation resumption
                spin-1 (spin
                         (let [{:keys [new]} (track sig)]
                           (swap! execution-count inc)
                           (* 2 new)))]

            ;; Execute in parent
            (is (= 20 @spin-1))
            (is (= 1 @execution-count))

            ;; Snapshot and restore
            (let [snap (ctx/snapshot-context ctx)
                  restored (ctx/restore-snapshot snap)]

              ;; Modify signal in restored context
              (binding [rtc/*execution-context* restored]
                (swap! sig (constantly 42))
                (simple/await-drain-complete! restored)

                ;; Spin should re-execute with new value
                (is (= 84 @spin-1))
                (is (= 2 @execution-count))))))
        (finally
          (ctx/stop-context! ctx))))))

(deftest test-clean-in-flight-spins
  (testing "In-flight spins are cleaned up in snapshot"
    (let [ctx (ctx/create-execution-context)]
      (try
        (binding [rtc/*execution-context* ctx]
          (let [sig (sig/signal 10)
                spin-1 (spin (let [{:keys [new]} (track sig)] new))]

            ;; Execute spin
            @spin-1

            ;; Manually mark spin as running (simulate in-flight)
            (rtc/swap-state! [:nodes (.-spin-id spin-1) :running?] (constantly true))
            (rtc/swap-state! [:nodes (.-spin-id spin-1) :completed?] (constantly false))

            ;; Create snapshot with clean-in-flight? true
            (let [snap (ctx/snapshot-context ctx :clean-in-flight? true)
                  restored (ctx/restore-snapshot snap)]

              ;; Spin should be marked dirty in snapshot
              (binding [rtc/*execution-context* restored]
                (is (not (rtc/spin-result-clean? (.-spin-id spin-1))))
                (is (rtc/spin-result-dirty? (.-spin-id spin-1)))))))
        (finally
          (ctx/stop-context! ctx))))))

(deftest test-pending-events-after-restore
  (testing "Pending events are processed after restore"
    (let [ctx (ctx/create-execution-context)
          count-1 (atom 0)]
      (try
        (binding [rtc/*execution-context* ctx]
          (let [sig (sig/signal 100)
                ;; Counter AFTER track so it increments on continuation resumption
                spin-1 (spin
                         (let [{:keys [new]} (track sig)]
                           (swap! count-1 inc)
                           new))]

            ;; Execute spin
            (is (= 100 @spin-1))
            (is (= 1 @count-1))

            ;; Change signal - manually enqueue event WITHOUT triggering drain
            ;; (bypass swap! to avoid auto-drain)
            (let [sig-id (:id sig)]
              (rtp/swap-state! ctx [:nodes sig-id :snapshot] (fn [_] 101))
              (rtp/swap-state! ctx [:engine/pending] (fn [q] (conj (or q []) {:type :signal-change :id sig-id}))))

            ;; Event is now pending (not drained)
            ;; Snapshot with pending event
            (let [snap (ctx/snapshot-context ctx :include-pending? true)
                  ;; Restore WITH draining
                  restored (ctx/restore-snapshot snap :drain-events? true)]

              ;; Event should have been processed during restore
              (binding [rtc/*execution-context* restored]
                ;; Spin should be CLEAN after event processing - the continuation
                ;; resumed and completed the spin with the new signal value
                (is (rtc/spin-result-clean? (.-spin-id spin-1)))

                ;; Spin already re-executed during drain via continuation
                ;; @spin-1 returns cached result (no additional execution)
                (is (= 101 @spin-1))
                ;; count-1 = 2: initial @spin-1 (1) + continuation during drain (1)
                (is (= 2 @count-1))))))
        (finally
          (ctx/stop-context! ctx))))))

(deftest test-snapshot-without-pending-events
  (testing "Snapshot can exclude pending events"
    (let [ctx (ctx/create-execution-context)]
      (try
        (binding [rtc/*execution-context* ctx]
          (let [sig (sig/signal 100)
                spin-1 (spin (let [{:keys [new]} (track sig)] new))]

            ;; Execute spin
            @spin-1

            ;; Change signal (enqueues event) and drain so state is settled
            (swap! sig inc)
            (simple/await-drain-complete! ctx)

            ;; Now take snapshot WITHOUT pending events (there shouldn't be any)
            ;; The spin has been re-executed with the new value (101)
            (let [snap (ctx/snapshot-context ctx :include-pending? false)
                  restored (ctx/restore-snapshot snap :drain-events? true)]

              ;; In the restored context, the spin should have the drained value
              (binding [rtc/*execution-context* restored]
                (is (= 101 @spin-1))

                ;; Now change signal again in parent (should NOT affect snapshot)
                (binding [rtc/*execution-context* ctx]
                  (swap! sig inc)
                  (simple/await-drain-complete! ctx))

                ;; Snapshot is isolated — still sees 101
                (is (= 101 @spin-1))))))
        (finally
          (ctx/stop-context! ctx))))))

(deftest test-overlay-vs-snapshot-isolation
  (testing "Overlay and snapshot have different isolation semantics"
    (let [parent (ctx/create-execution-context)]
      (try
        (binding [rtc/*execution-context* parent]
          (let [sig (sig/signal 100)
                spin-1 (spin (let [{:keys [new]} (track sig)] new))]

            ;; Execute in parent
            @spin-1

            ;; Create overlay fork and snapshot fork
            (let [overlay-fork (ctx/fork-context parent)
                  snapshot-fork (ctx/snapshot-context parent)]

              ;; Change signal in parent
              (swap! sig inc)
              (simple/await-drain-complete! parent)

              ;; Parent sees change
              (is (= 101 @sig))

              ;; Overlay sees parent's change (reads fall through)
              (binding [rtc/*execution-context* overlay-fork]
                (is (= 101 @sig)))

              ;; Snapshot does NOT see parent's change (independent copy)
              (binding [rtc/*execution-context* snapshot-fork]
                (is (= 100 @sig))))))
        (finally
          (ctx/stop-context! parent))))))

(deftest test-overlay-fork-independent-events
  (testing "Overlay fork has independent event queue from parent"
    (let [parent (ctx/create-execution-context)
          count-1 (atom 0)]
      (try
        (binding [rtc/*execution-context* parent]
          (let [sig (sig/signal 100)
                ;; Counter AFTER track so it increments on continuation resumption
                spin-1 (spin
                         (let [{:keys [new]} (track sig)]
                           (swap! count-1 inc)
                           new))]

            ;; Execute in parent
            @spin-1

            ;; Fork
            (let [fork (ctx/fork-context parent)]

              ;; Change signal in fork only
              (binding [rtc/*execution-context* fork]
                (swap! sig (constantly 42))
                (simple/await-drain-complete! fork)

                ;; Fork sees change
                (is (= 42 @sig))
                (is (= 42 @spin-1))
                (is (= 2 @count-1)))  ; Re-executed in fork (counter increments on continuation resumption)

              ;; Parent unchanged (overlay didn't modify parent)
              (is (= 100 @sig))
              (is (= 100 @spin-1))
              (is (= 2 @count-1)))))
        (finally
          (ctx/stop-context! parent))))))  ; count-1 is shared atom (executed 2 times total)

(deftest test-snapshot-clears-continuations
  (testing "In-memory snapshots preserve continuations, serialization drops them"
    (let [ctx (ctx/create-execution-context)]
      (try
        (binding [rtc/*execution-context* ctx]
          ;; Add some continuations to parent
          (rtp/add-continuation! ctx :test-spin-1 {:id :cont-1 :type :test})
          (rtp/add-continuation! ctx :test-spin-2 {:id :cont-2 :type :test})

          ;; Verify parent has continuations
          (is (= 2 (count (keys (rtp/get-state ctx [:continuations])))))

          ;; Create snapshot
          (let [snap (ctx/snapshot-context ctx)]
            ;; In-memory snapshot PRESERVES continuations (for checkpoinodes/restore)
            (is (= 2 (count (keys (rtp/get-state snap [:continuations])))))

            ;; Snapshot should have cleared draining flag
            (is (false? (rtp/get-state snap [:engine/draining?]))))

          ;; Parent should still have continuations (unchanged)
          (is (= 2 (count (keys (rtp/get-state ctx [:continuations]))))))
        (finally
          (ctx/stop-context! ctx))))))

(deftest test-snapshot-clears-in-flight-spins
  (testing "Snapshot marks in-flight spins as dirty"
    (let [ctx (ctx/create-execution-context)]
      (try
        (binding [rtc/*execution-context* ctx]
          ;; Create a long-running spin by manually setting running flag
          (rtp/swap-state! ctx [:nodes :test-spin]
            (constantly (nodes/->spin-node
                          nil     ; no result
                          :clean  ; status
                          false   ; not completed
                          true    ; running!
                          #{}     ; observers
                          {}      ; deps
                          nil     ; deps-hash
                          {}      ; deps-values
                          nil     ; created-by
                          #{})))  ; created-spins

          ;; Verify spin is running
          (is (true? (rtp/get-state ctx [:nodes :test-spin :running?])))
          (is (false? (rtp/get-state ctx [:nodes :test-spin :completed?])))

          ;; Create snapshot
          (let [snap (ctx/snapshot-context ctx)]
            ;; In-flight spin should be cleaned
            (is (false? (rtp/get-state snap [:nodes :test-spin :running?])))
            (is (false? (rtp/get-state snap [:nodes :test-spin :completed?])))
            (is (= :dirty (rtp/get-state snap [:nodes :test-spin :status])))
            (is (nil? (rtp/get-state snap [:nodes :test-spin :result])))))
        (finally
          (ctx/stop-context! ctx))))))

(deftest test-snapshot-with-clean-in-flight-option
  (testing "clean-in-flight? option controls spin cleanup"
    (let [ctx (ctx/create-execution-context)]
      (try
        (binding [rtc/*execution-context* ctx]
          ;; Add in-flight spin
          (rtp/swap-state! ctx [:nodes :test-spin]
            (constantly (nodes/->spin-node nil :clean false true #{} {} nil {} nil #{})))

          ;; Snapshot with clean-in-flight? false
          (let [snap-dirty (ctx/snapshot-context ctx :clean-in-flight? false)]
            ;; Should keep running flag
            (is (true? (rtp/get-state snap-dirty [:nodes :test-spin :running?]))))

          ;; Snapshot with clean-in-flight? true (default)
          (let [snap-clean (ctx/snapshot-context ctx)]
            ;; Should clear running flag
            (is (false? (rtp/get-state snap-clean [:nodes :test-spin :running?])))))
        (finally
          (ctx/stop-context! ctx))))))
