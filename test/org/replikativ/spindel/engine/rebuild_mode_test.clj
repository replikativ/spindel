(ns org.replikativ.spindel.engine.rebuild-mode-test
  "Tests for rebuild mode - execution state recovery after serialization.

  Rebuild mode allows spins to re-execute their bodies (for side effects like
  nested spin creation and continuation registration) while returning cached values.

  This enables:
  - Serialization/deserialization of execution contexts
  - Recovery of continuations for incremental reactivity
  - Cross-platform state transfer (CLJ <-> CLJS)"
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.addressing :as addressing]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.engine.protocols :as rtp]))

;; =============================================================================
;; Helper Functions
;; =============================================================================

(defn wait-for-completion
  "Wait for events to complete processing.

  Deterministic: blocks until the engine's pending queue is empty, no drain
  is in progress, and no spin has :running? true."
  [ctx]
  (simple/await-drain-complete! ctx))

;; =============================================================================
;; Execution Mode Tests
;; =============================================================================

(deftest test-execution-mode-helpers
  (testing "get-execution-mode returns nil by default"
    (let [ctx (ctx/create-execution-context)]
      (try
        (is (nil? (ctx/get-execution-mode ctx)))
        (finally
          (ctx/stop-context! ctx)))))

  (testing "set-execution-mode returns new context with mode set"
    (let [ctx (ctx/create-execution-context)
          rebuild-ctx (ctx/set-execution-mode ctx :rebuild)]
      (try
        (is (= :rebuild (ctx/get-execution-mode rebuild-ctx)))
        ;; Original context unchanged
        (is (nil? (ctx/get-execution-mode ctx)))
        (finally
          (ctx/stop-context! ctx)))))

  (testing "rebuild-mode? correctly detects rebuild mode"
    (let [ctx (ctx/create-execution-context)
          rebuild-ctx (ctx/set-execution-mode ctx :rebuild)
          normal-ctx (ctx/set-execution-mode ctx :normal)]
      (try
        (is (false? (ctx/rebuild-mode? ctx)))
        (is (true? (ctx/rebuild-mode? rebuild-ctx)))
        (is (false? (ctx/rebuild-mode? normal-ctx)))
        (finally
          (ctx/stop-context! ctx))))))

;; =============================================================================
;; Simple Rebuild Tests
;; =============================================================================

(deftest test-rebuild-mode-returns-cached-value
  (testing "Spin returns cached value in rebuild mode"
    (let [ctx (ctx/create-execution-context)
          call-counter (atom 0)
          make-spin (fn []
                      (spin
                       (swap! call-counter inc)
                       42))]
      (try
        ;; First execution - normal mode
        (binding [ec/*execution-context* ctx
                  ec/*execution-context* ctx]
          (let [t1 (make-spin)]
            (is (= 42 @t1))
            (is (= 1 @call-counter))))

        ;; Reset chain-head for rebuild
        (addressing/set-chain-head! ctx nil)
        (reset! call-counter 0)

        ;; Second execution - rebuild mode
        (let [rebuild-ctx (ctx/set-execution-mode ctx :rebuild)]
          (binding [ec/*execution-context* rebuild-ctx
                    ec/*execution-context* rebuild-ctx]
            (let [t2 (make-spin)]
              ;; Spin body should execute (counter increments)
              ;; But result should be cached value (42)
              (is (= 42 @t2))
              (is (= 1 @call-counter) "Body should execute in rebuild mode"))))
        (finally
          (ctx/stop-context! ctx))))))

(deftest test-rebuild-mode-executes-body-for-side-effects
  (testing "Spin body executes for side effects in rebuild mode"
    (let [ctx (ctx/create-execution-context)
          side-effect-log (atom [])
          make-spin (fn []
                      (spin
                       (swap! side-effect-log conj :executed)
                       100))]
      (try
        ;; First execution - normal mode
        (binding [ec/*execution-context* ctx
                  ec/*execution-context* ctx]
          (let [t1 (make-spin)]
            (is (= 100 @t1))
            (is (= [:executed] @side-effect-log))))

        ;; Reset chain-head for rebuild
        (addressing/set-chain-head! ctx nil)
        (reset! side-effect-log [])

        ;; Second execution - rebuild mode
        (let [rebuild-ctx (ctx/set-execution-mode ctx :rebuild)]
          (binding [ec/*execution-context* rebuild-ctx
                    ec/*execution-context* rebuild-ctx]
            (let [t2 (make-spin)]
              (is (= 100 @t2))
              ;; Body DID execute (side effect logged)
              (is (= [:executed] @side-effect-log) "Body should execute in rebuild mode"))))
        (finally
          (ctx/stop-context! ctx))))))

;; =============================================================================
;; Nested Spin Tests
;; =============================================================================

(deftest test-rebuild-mode-creates-nested-spins
  (testing "Nested spins are created in rebuild mode"
    (let [ctx (ctx/create-execution-context)
          inner-spin-ids (atom [])
          make-model (fn []
                       (spin
                        (let [inner (spin
                                     (swap! inner-spin-ids conj ec/*spin-id*)
                                     99)]
                          (await inner))))]
      (try
        ;; First execution - normal mode
        (binding [ec/*execution-context* ctx
                  ec/*execution-context* ctx]
          (let [outer (make-model)]
            (is (= 99 @outer))
            (is (= 1 (count @inner-spin-ids)))))

        ;; Capture inner spin ID from first execution
        (let [first-inner-id (first @inner-spin-ids)]

          ;; Reset chain-head for rebuild
          (addressing/set-chain-head! ctx nil)
          (reset! inner-spin-ids [])

          ;; Second execution - rebuild mode
          (let [rebuild-ctx (ctx/set-execution-mode ctx :rebuild)]
            (binding [ec/*execution-context* rebuild-ctx
                      ec/*execution-context* rebuild-ctx]
              (let [outer (make-model)]
                (is (= 99 @outer))
                ;; Inner spin was created again
                (is (= 1 (count @inner-spin-ids)) "Inner spin should be created in rebuild mode")
                ;; Same spin ID (deterministic addressing)
                (is (= first-inner-id (first @inner-spin-ids))
                    "Inner spin should have same ID due to deterministic addressing")))))
        (finally
          (ctx/stop-context! ctx))))))

;; =============================================================================
;; Chain Head Consistency Tests
;; =============================================================================

(deftest test-rebuild-preserves-chain-head-consistency
  (testing "Rebuild mode preserves deterministic addressing"
    (let [ctx (ctx/create-execution-context)
          spin-ids-run-1 (atom [])
          spin-ids-run-2 (atom [])
          make-model (fn [id-log]
                       (spin
                        (swap! id-log conj ec/*spin-id*)
                        (let [a (spin (swap! id-log conj ec/*spin-id*) 1)
                              b (spin (swap! id-log conj ec/*spin-id*) 2)]
                          (+ (await a) (await b)))))]
      (try
        ;; First execution - normal mode
        (binding [ec/*execution-context* ctx
                  ec/*execution-context* ctx]
          (let [outer (make-model spin-ids-run-1)]
            (is (= 3 @outer))))

        ;; Reset chain-head for rebuild
        (addressing/set-chain-head! ctx nil)

        ;; Second execution - rebuild mode
        (let [rebuild-ctx (ctx/set-execution-mode ctx :rebuild)]
          (binding [ec/*execution-context* rebuild-ctx
                    ec/*execution-context* rebuild-ctx]
            (let [outer (make-model spin-ids-run-2)]
              (is (= 3 @outer)))))

        ;; Spin IDs should match
        (is (= @spin-ids-run-1 @spin-ids-run-2)
            "Spin IDs should be identical between normal and rebuild execution")
        (finally
          (ctx/stop-context! ctx))))))

;; =============================================================================
;; Prepare/Finalize Rebuild Context Tests
;; =============================================================================

(deftest test-prepare-rebuild-context
  (testing "prepare-rebuild-context sets up context correctly"
    (let [ctx (ctx/create-execution-context)]
      (try
        ;; First execution to populate state
        (binding [ec/*execution-context* ctx
                  ec/*execution-context* ctx]
          @(spin 42))

        ;; Snapshot the context
        (let [snapshot (ctx/snapshot-context ctx)
              ;; Prepare for rebuild
              rebuild-ctx (ctx/prepare-rebuild-context snapshot)]

          ;; Should be in rebuild mode
          (is (ctx/rebuild-mode? rebuild-ctx))

          ;; Chain head should be reset to nil
          (is (nil? (addressing/get-chain-head rebuild-ctx))))
        (finally
          (ctx/stop-context! ctx))))))

(deftest test-finalize-rebuild-context
  (testing "finalize-rebuild-context clears rebuild mode"
    (let [ctx (ctx/create-execution-context)
          rebuild-ctx (ctx/set-execution-mode ctx :rebuild)]
      (try
        ;; Verify rebuild mode is set
        (is (ctx/rebuild-mode? rebuild-ctx))

        ;; Finalize
        (let [final-ctx (ctx/finalize-rebuild-context rebuild-ctx :drain-events? false)]
          ;; Mode should be cleared
          (is (not (ctx/rebuild-mode? final-ctx))))
        (finally
          (ctx/stop-context! ctx))))))

;; =============================================================================
;; Full Round-Trip Tests (Serialization + Rebuild)
;; =============================================================================

(deftest test-full-serialization-rebuild-cycle
  (testing "Full cycle: execute -> serialize -> deserialize -> rebuild"
    (let [ctx (ctx/create-execution-context)
          spin-ids (atom [])
          values (atom [])
          make-model (fn []
                       (spin
                        (swap! spin-ids conj ec/*spin-id*)
                        (let [a (spin
                                 (swap! spin-ids conj ec/*spin-id*)
                                 10)
                              b (spin
                                 (swap! spin-ids conj ec/*spin-id*)
                                 20)]
                          (let [result (+ (await a) (await b))]
                            (swap! values conj result)
                            result))))]
      (try
        ;; Phase 1: Original execution
        (binding [ec/*execution-context* ctx
                  ec/*execution-context* ctx]
          (let [model (make-model)]
            (is (= 30 @model))))

        (let [original-spin-ids @spin-ids
              original-values @values]

          ;; Phase 2: Serialize
          (let [serialized (ctx/serialize-context ctx)
                _ (is (string? serialized))

                ;; Phase 3: Deserialize
                deserialized (ctx/deserialize-context serialized (:executor ctx))]

            ;; Reset for rebuild tracking
            (reset! spin-ids [])
            (reset! values [])

            ;; Phase 4: Rebuild
            (let [live-ctx (ctx/with-rebuild-context deserialized {}
                             @(make-model))]

              ;; Spin IDs should match (deterministic)
              (is (= original-spin-ids @spin-ids)
                  "Spin IDs should be identical after rebuild")

              ;; Values should match (cached)
              (is (= original-values @values)
                  "Values should be identical after rebuild"))))
        (finally
          (ctx/stop-context! ctx))))))

;; =============================================================================
;; Edge Cases
;; =============================================================================

(deftest test-rebuild-without-cache-falls-back-to-computation
  (testing "Rebuild mode without cache computes new values"
    (let [ctx (ctx/create-execution-context)
          make-spin (fn [] (spin (+ 1 2 3)))]
      (try
        ;; Execute in rebuild mode WITHOUT prior cache
        (let [rebuild-ctx (ctx/set-execution-mode ctx :rebuild)]
          (binding [ec/*execution-context* rebuild-ctx
                    ec/*execution-context* rebuild-ctx]
            (let [t (make-spin)]
              ;; Should compute normally when no cache exists
              (is (= 6 @t)))))
        (finally
          (ctx/stop-context! ctx))))))

(deftest test-normal-mode-still-uses-cache
  (testing "Normal mode still uses cache (rebuild mode doesn't break caching)"
    (let [ctx (ctx/create-execution-context)
          call-counter (atom 0)
          make-spin (fn []
                      (spin
                       (swap! call-counter inc)
                       99))]
      (try
        (binding [ec/*execution-context* ctx
                  ec/*execution-context* ctx]
          ;; First call - computes
          (let [t1 (make-spin)]
            (is (= 99 @t1))
            (is (= 1 @call-counter)))

          ;; Reset chain-head to get same spin ID
          (addressing/set-chain-head! ctx nil)

          ;; Second call - should use cache (not rebuild mode)
          (let [t2 (make-spin)]
            (is (= 99 @t2))
            ;; Counter should NOT increment (cache hit)
            (is (= 1 @call-counter) "Cache should be used in normal mode")))
        (finally
          (ctx/stop-context! ctx))))))
