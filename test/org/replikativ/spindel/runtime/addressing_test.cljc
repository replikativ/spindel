(ns org.replikativ.spindel.runtime.addressing-test
  "Tests for deterministic address generation (hash-chain addressing).

  The addressing system is critical infrastructure that generates unique,
  deterministic spin IDs based on source location and execution order.

  This test file focuses on the concurrent access scenario that caused
  our semaphore test failures (race condition in next-address!)."
  (:require #?(:clj [clojure.test :refer [deftest is testing]])
            #?(:cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.runtime.context :as ctx]
            [org.replikativ.spindel.runtime.core :as rtc]
            [org.replikativ.spindel.runtime.addressing :as addressing]))

;; =============================================================================
;; Concurrent Address Generation Tests
;; =============================================================================

#?(:clj
   (deftest test-concurrent-next-address-uniqueness
     (testing "Concurrent next-address! calls from same source location generate unique IDs"
       (let [ctx (ctx/create-execution-context)
             n-threads 50
             n-calls-per-thread 100
             all-ids (atom #{})
             source-loc [:test :concurrent-location]]

         ;; Run many threads concurrently, all calling next-address!
         ;; from the SAME source location (this was the semaphore bug scenario)
         (let [futures (repeatedly n-threads
                         (fn []
                           (future
                             (binding [rtc/*execution-context* ctx]
                               (dotimes [_ n-calls-per-thread]
                                 ;; Same source location across all threads
                                 (let [id (addressing/next-address! ctx "test" source-loc)]
                                   (swap! all-ids conj id)))))))]

           ;; Wait for all threads to complete
           (doseq [f futures]
             (deref f 10000 :timeout))

           ;; Critical assertion: ALL IDs should be unique
           ;; Before the fix, duplicate IDs would be generated when multiple threads
           ;; read the same chain-head value before any updated it
           (is (= (* n-threads n-calls-per-thread) (count @all-ids))
               "All generated IDs should be unique - no duplicates from race condition")

           ;; Additional check: verify we actually generated the expected number
           (is (= 5000 (count @all-ids))
               "Should have generated exactly 5000 unique IDs"))))))

#?(:clj
   (deftest test-concurrent-next-address-from-different-sources
     (testing "Concurrent calls from different source locations also generate unique IDs"
       (let [ctx (ctx/create-execution-context)
             n-threads 20
             all-ids (atom #{})]

         ;; Each thread uses a different source location
         (let [futures (mapv
                         (fn [thread-id]
                           (future
                             (binding [rtc/*execution-context* ctx]
                               (dotimes [i 50]
                                 (let [source-loc [:thread thread-id :call i]
                                       id (addressing/next-address! ctx "test" source-loc)]
                                   (swap! all-ids conj id))))))
                         (range n-threads))]

           ;; Wait for completion
           (doseq [f futures]
             (deref f 10000 :timeout))

           ;; All should be unique
           (is (= (* n-threads 50) (count @all-ids))
               "IDs from different source locations should all be unique")

           (is (= 1000 (count @all-ids))
               "Should have generated exactly 1000 unique IDs"))))))

;; =============================================================================
;; Determinism Tests
;; =============================================================================

(deftest test-deterministic-address-generation
  (testing "Same source location sequence generates same IDs after reset"
    (let [ctx (ctx/create-execution-context)
          source-locs [[:file1 :line10]
                       [:file1 :line20]
                       [:file2 :line5]
                       [:file1 :line10]  ; Repeat
                       [:file2 :line15]]
          ids-run-1 (atom [])
          ids-run-2 (atom [])]

      (binding [rtc/*execution-context* ctx]
        ;; First run
        (doseq [loc source-locs]
          (swap! ids-run-1 conj (addressing/next-address! ctx "test" loc)))

        ;; Reset chain head
        (addressing/set-chain-head! ctx nil)

        ;; Second run with same sequence
        (doseq [loc source-locs]
          (swap! ids-run-2 conj (addressing/next-address! ctx "test" loc)))

        ;; Should get identical ID sequences
        (is (= @ids-run-1 @ids-run-2)
            "Same source location sequence should generate same IDs after reset")))))

(deftest test-different-sequences-different-ids
  (testing "Different source location sequences generate different IDs"
    (let [ctx (ctx/create-execution-context)
          ids-1 (atom [])
          ids-2 (atom [])]

      (binding [rtc/*execution-context* ctx]
        ;; Sequence 1
        (swap! ids-1 conj (addressing/next-address! ctx "test" [:a]))
        (swap! ids-1 conj (addressing/next-address! ctx "test" [:b]))

        ;; Reset
        (addressing/set-chain-head! ctx nil)

        ;; Sequence 2 (different order)
        (swap! ids-2 conj (addressing/next-address! ctx "test" [:b]))
        (swap! ids-2 conj (addressing/next-address! ctx "test" [:a]))

        ;; Different sequences → different IDs
        (is (not= @ids-1 @ids-2)
            "Different source location sequences should generate different ID sequences")))))

;; =============================================================================
;; Chain Head Manipulation Tests
;; =============================================================================

(deftest test-chain-head-get-set
  (testing "Chain head can be get and set"
    (let [ctx (ctx/create-execution-context)]
      (binding [rtc/*execution-context* ctx]
        ;; Initially nil
        (is (nil? (addressing/get-chain-head ctx)))

        ;; Generate an ID - chain head should be set
        (let [id (addressing/next-address! ctx "test" [:test])]
          (is (= id (addressing/get-chain-head ctx)))

          ;; Reset to nil
          (addressing/set-chain-head! ctx nil)
          (is (nil? (addressing/get-chain-head ctx)))

          ;; Generate again - should get same ID (same source, nil chain)
          (let [id2 (addressing/next-address! ctx "test" [:test])]
            (is (= id id2)
                "Same source location from nil chain should generate same ID")))))))

(deftest test-branch-head-computation
  (testing "Branch head computation is deterministic"
    (let [base-chain-head :some-chain-head
          ;; Same base + same index → same branch head
          branch-0-a (addressing/branch-head base-chain-head 0)
          branch-0-b (addressing/branch-head base-chain-head 0)
          branch-1-a (addressing/branch-head base-chain-head 1)
          branch-1-b (addressing/branch-head base-chain-head 1)]

      ;; Same parameters → same result
      (is (= branch-0-a branch-0-b)
          "Same base and index should produce same branch head")
      (is (= branch-1-a branch-1-b)
          "Same base and index should produce same branch head")

      ;; Different index → different result
      (is (not= branch-0-a branch-1-a)
          "Different branch indices should produce different branch heads")

      ;; All should be keywords
      (is (keyword? branch-0-a))
      (is (keyword? branch-1-a)))))

;; =============================================================================
;; Edge Cases
;; =============================================================================

(deftest test-very-long-address-chain
  (testing "Long address chains maintain uniqueness"
    (let [ctx (ctx/create-execution-context)
          n 1000
          ids (atom #{})]

      (binding [rtc/*execution-context* ctx]
        (dotimes [i n]
          (swap! ids conj
                 (addressing/next-address! ctx "test" [:long-chain i])))

        ;; All should be unique
        (is (= n (count @ids))
            "All IDs in long chain should be unique")))))

(deftest test-empty-source-location
  (testing "Empty source location is valid"
    (let [ctx (ctx/create-execution-context)]
      (binding [rtc/*execution-context* ctx]
        (let [id (addressing/next-address! ctx "test" [])]
          (is (keyword? id))
          (is (not (nil? id))))))))
