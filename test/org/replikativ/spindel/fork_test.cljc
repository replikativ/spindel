(ns org.replikativ.spindel.fork-test
  "Tests for runtime forking and checkpointing.
   Ported from laufzeit, adapted for spindel's execution-context API.
   CLJ-only: requires sig/signal macro which uses &form metadata."
  (:refer-clojure :exclude [await])
  #?(:clj
     (:require [clojure.test :refer [deftest testing is]]
               [org.replikativ.spindel.engine.context :as ctx]
               [org.replikativ.spindel.engine.core :as ec]
               [org.replikativ.spindel.signal :as sig]
               [org.replikativ.spindel.spin.cps :refer [spin]]
               [org.replikativ.spindel.effects.track :refer [track]])
     :cljs
     (:require [cljs.test :refer-macros [deftest testing is]])))

;; =============================================================================
;; All fork tests are CLJ-only due to:
;; - sig/signal macro uses &form metadata (not available in CLJS)
;; - Context forking/snapshotting is primarily a CLJ feature
;; =============================================================================

;; =============================================================================
;; Fork Runtime Basic Tests
;; =============================================================================

#?(:clj
   (deftest test-fork-runtime-basic
     (testing "Forking creates independent runtime with shared initial state"
       (let [ctx-main (ctx/create-execution-context)]
         (try
           ;; Initialize signal in main context
           (binding [ec/*execution-context* ctx-main]
             (let [counter (sig/signal 0)]
               (swap! counter inc)
               (is (= 1 @counter))

               ;; Fork the context via snapshot
               (let [snapshot (ctx/snapshot-context ctx-main)
                     ctx-fork (ctx/restore-snapshot snapshot)]

                 ;; Fork should have same signal value initially
                 (binding [ec/*execution-context* ctx-fork]
                   (is (= 1 @counter))

                   ;; Modify fork - should not affect main
                   (swap! counter inc)
                   (is (= 2 @counter)))

                 ;; Main should still have original value
                 (binding [ec/*execution-context* ctx-main]
                   (is (= 1 @counter))

                   ;; Modify main - should not affect fork
                   (swap! counter inc)
                   (is (= 2 @counter)))

                 ;; Verify fork still has its value
                 (binding [ec/*execution-context* ctx-fork]
                   (is (= 2 @counter))))))
           (finally
             (ctx/stop-context! ctx-main)))))))

#?(:clj
   (deftest test-fork-runtime-structural-sharing
     (testing "Forked runtime uses structural sharing (copy-on-write)"
       (let [ctx-main (ctx/create-execution-context)]
         (try
           (binding [ec/*execution-context* ctx-main]
             (let [sig1 (sig/signal 1)
                   sig2 (sig/signal 2)
                   sig3 (sig/signal 3)]

               ;; Initialize multiple signals
               (swap! sig1 inc)
               (swap! sig2 inc)
               (swap! sig3 inc)

               ;; Fork via snapshot
               (let [snapshot (ctx/snapshot-context ctx-main)
                     ctx-fork (ctx/restore-snapshot snapshot)]

                 ;; Before any writes, signal values should be identical
                 ;; Read via protocol methods
                 (binding [ec/*execution-context* ctx-fork]
                   (is (= 2 @sig1) "sig1 fork should have same value as main")
                   (is (= 3 @sig2) "sig2 fork should have same value as main")
                   (is (= 4 @sig3) "sig3 fork should have same value as main"))

                 ;; After writing to fork, modified signal should differ
                 (binding [ec/*execution-context* ctx-fork]
                   (swap! sig1 inc))  ; sig1 is now 3 in fork

                 ;; Fork has 3, main still has 2
                 (binding [ec/*execution-context* ctx-fork]
                   (is (= 3 @sig1) "sig1 in fork should be incremented"))

                 (is (= 2 @sig1) "sig1 in main should be unchanged")

                 ;; Unmodified signals should still match in both contexts
                 (is (= 3 @sig2) "sig2 in main should be unchanged")
                 (binding [ec/*execution-context* ctx-fork]
                   (is (= 3 @sig2) "sig2 in fork should match main")))))
           (finally
             (ctx/stop-context! ctx-main)))))))

#?(:clj
   (deftest test-fork-runtime-spins-independent
     (testing "Spins in fork are independent from main runtime"
       (let [ctx-main (ctx/create-execution-context)]
         (try
           ;; Create spin in main context
           (binding [ec/*execution-context* ctx-main]
             (let [counter (sig/signal 0)
                   doubled-main (spin
                                 (let [{:keys [new]} (track counter)]
                                   (* 2 new)))]
               (is (= 0 @doubled-main))

               ;; Fork the context
               (let [snapshot (ctx/snapshot-context ctx-main)
                     ctx-fork (ctx/restore-snapshot snapshot)]

                 ;; Create spin in fork with same logic
                 (binding [ec/*execution-context* ctx-fork]
                   (let [doubled-fork (spin
                                       (let [{:keys [new]} (track counter)]
                                         (* 2 new)))]
                     (is (= 0 @doubled-fork))

                     ;; Update signal in fork
                     (swap! counter inc)
                     ;; Note: The forked spin needs to be re-dereferenced to see the update
                     ;; since spins are cached
                     ))

                 ;; Main context should be unchanged
                 (binding [ec/*execution-context* ctx-main]
                   (is (= 0 @counter))
                   (is (= 0 @doubled-main))))))
           (finally
             (ctx/stop-context! ctx-main)))))))

;; =============================================================================
;; Checkpoint/Restore Tests
;; =============================================================================

#?(:clj
   (deftest test-checkpoint-restore
     (testing "Checkpoint and restore runtime state"
       (let [ctx (ctx/create-execution-context)]
         (try
           (binding [ec/*execution-context* ctx]
             (let [counter (sig/signal 0)
                   todos (sig/signal [])]
               ;; Set initial state
               (reset! counter 5)
               (swap! todos conj "spin-1")

               (is (= 5 @counter))
               (is (= ["spin-1"] @todos))

               ;; Create checkpoint
               (let [checkpoint (ctx/snapshot-context ctx)]

                 ;; Modify state after checkpoint
                 (swap! counter inc)
                 (swap! todos conj "spin-2")

                 (is (= 6 @counter))
                 (is (= ["spin-1" "spin-2"] @todos))

                 ;; Restore to checkpoint
                 (let [restored-ctx (ctx/restore-snapshot checkpoint)]
                   (binding [ec/*execution-context* restored-ctx]
                     (is (= 5 @counter))
                     (is (= ["spin-1"] @todos)))))))
           (finally
             (ctx/stop-context! ctx)))))))

;; =============================================================================
;; Divergent Timelines Tests
;; =============================================================================

#?(:clj
   (deftest test-divergent-timelines
     (testing "Multiple forks create divergent timelines"
       (let [ctx-main (ctx/create-execution-context)]
         (try
           (binding [ec/*execution-context* ctx-main]
             (let [value (sig/signal 10)]
               ;; Set initial value
               (swap! value inc)  ; => 11

               ;; Create two divergent timelines
               (let [snapshot (ctx/snapshot-context ctx-main)
                     ctx-timeline-a (ctx/restore-snapshot snapshot)
                     ctx-timeline-b (ctx/restore-snapshot snapshot)]

                 ;; Both start with same value
                 (binding [ec/*execution-context* ctx-timeline-a]
                   (is (= 11 @value)))

                 (binding [ec/*execution-context* ctx-timeline-b]
                   (is (= 11 @value)))

                 ;; Timeline A: double the value
                 (binding [ec/*execution-context* ctx-timeline-a]
                   (swap! value #(* 2 %))
                   (is (= 22 @value)))

                 ;; Timeline B: square the value
                 (binding [ec/*execution-context* ctx-timeline-b]
                   (swap! value #(* % %))
                   (is (= 121 @value)))

                 ;; Main timeline unchanged
                 (binding [ec/*execution-context* ctx-main]
                   (is (= 11 @value)))

                 ;; Fork from timeline A
                 (let [snapshot-a (ctx/snapshot-context ctx-timeline-a)
                       ctx-timeline-c (ctx/restore-snapshot snapshot-a)]

                   (binding [ec/*execution-context* ctx-timeline-c]
                     (is (= 22 @value))

                     ;; Timeline C diverges from A
                     (swap! value inc)
                     (is (= 23 @value)))

                   ;; Timeline A unchanged
                   (binding [ec/*execution-context* ctx-timeline-a]
                     (is (= 22 @value)))))))
           (finally
             (ctx/stop-context! ctx-main)))))))

;; =============================================================================
;; Undo/Redo via Checkpoints
;; =============================================================================

#?(:clj
   (deftest test-checkpoint-undo-redo
     (testing "Use checkpoints for undo/redo functionality"
       (let [ctx (ctx/create-execution-context)
             history (atom [])]
         (try
           (binding [ec/*execution-context* ctx]
             (let [counter (sig/signal 0)]
               ;; Initial state
               (swap! history conj (ctx/snapshot-context ctx))
               (is (= 0 @counter))

               ;; Action 1: increment
               (swap! counter inc)
               (swap! history conj (ctx/snapshot-context ctx))
               (is (= 1 @counter))

               ;; Action 2: increment
               (swap! counter inc)
               (swap! history conj (ctx/snapshot-context ctx))
               (is (= 2 @counter))

               ;; Action 3: increment
               (swap! counter inc)
               (swap! history conj (ctx/snapshot-context ctx))
               (is (= 3 @counter))

               ;; Undo: restore to checkpoint 2
               (let [ctx-2 (ctx/restore-snapshot (nth @history 2))]
                 (binding [ec/*execution-context* ctx-2]
                   (is (= 2 @counter))))

               ;; Undo: restore to checkpoint 1
               (let [ctx-1 (ctx/restore-snapshot (nth @history 1))]
                 (binding [ec/*execution-context* ctx-1]
                   (is (= 1 @counter))))

               ;; Undo: restore to initial
               (let [ctx-0 (ctx/restore-snapshot (nth @history 0))]
                 (binding [ec/*execution-context* ctx-0]
                   (is (= 0 @counter))))

               ;; Redo: restore to checkpoint 1
               (let [ctx-1-redo (ctx/restore-snapshot (nth @history 1))]
                 (binding [ec/*execution-context* ctx-1-redo]
                   (is (= 1 @counter))))))
           (finally
             (ctx/stop-context! ctx)))))))

;; =============================================================================
;; Serialization Round-Trip Tests
;; =============================================================================

#?(:clj
   (deftest test-serialization-round-trip
     (testing "Serialize and deserialize runtime state"
       (let [ctx (ctx/create-execution-context)]
         (try
           (binding [ec/*execution-context* ctx]
             (let [counter (sig/signal 0)
                   name-sig (sig/signal "Alice")]
               ;; Set some state
               (reset! counter 42)
               (reset! name-sig "Bob")

               (is (= 42 @counter))
               (is (= "Bob" @name-sig))

               ;; Serialize
               (let [serialized (ctx/serialize-context ctx)]
                 (is (string? serialized))

                 ;; Deserialize
                 (let [restored (ctx/deserialize-context serialized (:executor ctx))]
                   (binding [ec/*execution-context* restored]
                     (is (= 42 @counter))
                     (is (= "Bob" @name-sig)))))))
           (finally
             (ctx/stop-context! ctx)))))))

;; =============================================================================
;; Fork with Rebuild Mode Tests
;; =============================================================================

#?(:clj
   (deftest test-fork-with-rebuild-mode
     (testing "Fork followed by rebuild mode preserves cached values"
       (let [ctx (ctx/create-execution-context)
             call-count (atom 0)]
         (try
           (binding [ec/*execution-context* ctx]
             (let [counter (sig/signal 0)
                   ;; Create spin that tracks call count
                   doubled (spin
                            (swap! call-count inc)
                            (let [{:keys [new]} (track counter)]
                              (* 2 new)))]

               ;; First execution
               (is (= 0 @doubled))
               (is (= 1 @call-count))

               ;; Snapshot for fork
               (let [snapshot (ctx/snapshot-context ctx)
                     ;; Prepare for rebuild
                     rebuild-ctx (ctx/prepare-rebuild-context snapshot)]

                 ;; In rebuild mode, body executes but returns cached value
                 (reset! call-count 0)

                 (binding [ec/*execution-context* rebuild-ctx]
                   ;; Create same spin - should rebuild
                   (let [doubled-rebuilt (spin
                                          (swap! call-count inc)
                                          (let [{:keys [new]} (track counter)]
                                            (* 2 new)))]
                     ;; Body executed (call-count incremented)
                     ;; But returns cached value
                     (is (= 0 @doubled-rebuilt))
                     (is (= 1 @call-count) "Body should execute in rebuild mode"))))))
           (finally
             (ctx/stop-context! ctx)))))))
