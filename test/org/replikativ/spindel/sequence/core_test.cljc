(ns org.replikativ.spindel.sequence.core-test
  "Tests for async sequence generation with yield.

  Cross-platform tests using async/done pattern."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.sequence.core :as seq-core]
            [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [is.simm.partial-cps.sequence :refer [anext]]))

;; =============================================================================
;; Helper to run anext with callbacks
;; =============================================================================

(defn run-anext!
  "Run anext on a generator and call on-result with the result.
   Result is [value rest-gen] or nil if exhausted."
  [gen on-result on-error]
  (let [async-expr (anext gen)]
    (async-expr on-result on-error)))

;; =============================================================================
;; Basic Sequence Tests
;; =============================================================================

(deftest test-gen-aseq-simple
  (testing "Simple sequence generation with multiple yields"
    (async done
      (with-ctx [_ctx]
        (let [gen (seq-core/gen-aseq
                   (seq-core/yield 1)
                   (seq-core/yield 2)
                   (seq-core/yield 3))]
          ;; First anext should return [1 rest-gen]
          (run-anext! gen
            (fn [result1]
              (is (vector? result1))
              (is (= 1 (first result1)))
              ;; Second anext should return [2 rest-gen]
              (run-anext! (second result1)
                (fn [result2]
                  (is (vector? result2))
                  (is (= 2 (first result2)))
                  ;; Third anext should return [3 rest-gen]
                  (run-anext! (second result2)
                    (fn [result3]
                      (is (vector? result3))
                      (is (= 3 (first result3)))
                      ;; Fourth anext should return nil (exhausted)
                      (run-anext! (second result3)
                        (fn [result4]
                          (is (nil? result4))
                          (done))
                        (fn [e] (is false (str "error: " e)) (done))))
                    (fn [e] (is false (str "error: " e)) (done))))
                (fn [e] (is false (str "error: " e)) (done))))
            (fn [e] (is false (str "error: " e)) (done))))))))

(deftest test-gen-aseq-empty
  (testing "Empty sequence (no yields)"
    (async done
      (with-ctx [_ctx]
        (let [gen (seq-core/gen-aseq
                   nil)]
          ;; First anext should return nil immediately
          (run-anext! gen
            (fn [result]
              (is (nil? result))
              (done))
            (fn [e] (is false (str "error: " e)) (done))))))))

(deftest test-gen-aseq-with-computation
  (testing "Sequence with computation between yields"
    (async done
      (with-ctx [_ctx]
        (let [gen (seq-core/gen-aseq
                   (let [x (* 2 3)]
                     (seq-core/yield x)
                     (let [y (+ x 4)]
                       (seq-core/yield y)
                       (let [z (* y 2)]
                         (seq-core/yield z)))))]
          ;; Should yield 6, 10, 20
          (run-anext! gen
            (fn [result1]
              (is (= 6 (first result1)))
              (run-anext! (second result1)
                (fn [result2]
                  (is (= 10 (first result2)))
                  (run-anext! (second result2)
                    (fn [result3]
                      (is (= 20 (first result3)))
                      (run-anext! (second result3)
                        (fn [result4]
                          (is (nil? result4))
                          (done))
                        (fn [e] (is false (str "error: " e)) (done))))
                    (fn [e] (is false (str "error: " e)) (done))))
                (fn [e] (is false (str "error: " e)) (done))))
            (fn [e] (is false (str "error: " e)) (done))))))))

(deftest test-gen-aseq-error-handling
  (testing "Error propagation in generators"
    (async done
      (with-ctx [_ctx]
        (let [gen (seq-core/gen-aseq
                   (seq-core/yield 1)
                   (throw (ex-info "Test error" {}))
                   (seq-core/yield 2))]
          ;; First yield should work
          (run-anext! gen
            (fn [result1]
              (is (= 1 (first result1)))
              ;; Second anext should propagate the error
              (run-anext! (second result1)
                (fn [_result2]
                  (is false "Expected error but got result")
                  (done))
                (fn [error]
                  (is (= "Test error" (ex-message error)))
                  (done))))
            (fn [e] (is false (str "first yield error: " e)) (done))))))))

(deftest test-yield-outside-gen-aseq-throws
  (testing "Calling yield outside gen-aseq throws"
    (is (thrown? #?(:clj Exception :cljs js/Error)
                 (seq-core/yield 42)))))

;; =============================================================================
;; Loop/Recur Tests
;; =============================================================================

(deftest test-gen-aseq-with-loop
  (testing "Sequence generation with loop/recur"
    (async done
      (with-ctx [_ctx]
        (let [gen (seq-core/gen-aseq
                   (loop [n 0]
                     (when (< n 5)
                       (seq-core/yield n)
                       (recur (inc n)))))]
          ;; Collect all values using recursive callback
          (letfn [(collect [current-gen values]
                    (run-anext! current-gen
                      (fn [result]
                        (if (nil? result)
                          ;; Sequence exhausted
                          (do
                            (is (= [0 1 2 3 4] values))
                            (done))
                          ;; Got [value rest-gen]
                          (collect (second result) (conj values (first result)))))
                      (fn [e] (is false (str "error: " e)) (done))))]
            (collect gen [])))))))

;; =============================================================================
;; Cold Semantics Test
;; =============================================================================

(deftest test-gen-aseq-cold-semantics
  (testing "Cold semantics - each anext creates new execution context"
    (async done
      (with-ctx [_ctx]
        (let [call-count (atom 0)
              gen (seq-core/gen-aseq
                   (swap! call-count inc)
                   (seq-core/yield @call-count)
                   (swap! call-count inc)
                   (seq-core/yield @call-count))]
          ;; First consumer
          (run-anext! gen
            (fn [result1]
              (is (= 1 (first result1)))
              ;; Call count should be 1 (only first swap executed)
              ;; Note: This tests cold semantics - each anext starts fresh
              (is (= 1 @call-count))
              (done))
            (fn [e] (is false (str "error: " e)) (done))))))))

;; =============================================================================
;; Spin Integration Tests
;; =============================================================================

(deftest test-gen-aseq-with-await-in-loop
  (testing "gen-aseq with await inside loop/recur"
    (async done
      (with-ctx [_ctx]
        (let [make-spin (fn [n]
                          (spin
                           (let [result (* n 2)]
                             result)))
              gen (seq-core/gen-aseq
                   (loop [n 0]
                     (when (< n 3)
                       (let [t (make-spin n)
                             doubled (await t)]
                         (seq-core/yield doubled)
                         (recur (inc n))))))]
          ;; Should yield 0, 2, 4
          (run-anext! gen
            (fn [result1]
              (is (= 0 (first result1)))
              (run-anext! (second result1)
                (fn [result2]
                  (is (= 2 (first result2)))
                  (run-anext! (second result2)
                    (fn [result3]
                      (is (= 4 (first result3)))
                      (run-anext! (second result3)
                        (fn [result4]
                          (is (nil? result4))
                          (done))
                        (fn [e] (is false (str "error: " e)) (done))))
                    (fn [e] (is false (str "error: " e)) (done))))
                (fn [e] (is false (str "error: " e)) (done))))
            (fn [e] (is false (str "error: " e)) (done))))))))

(deftest test-spin-consuming-aseq-with-loop
  (testing "Spin that consumes async sequence with loop/recur"
    (async done
      (with-ctx [_ctx]
        (let [gen (seq-core/gen-aseq
                   (seq-core/yield 10)
                   (seq-core/yield 20)
                   (seq-core/yield 30))
              consumer-spin (spin
                             (loop [s gen
                                    acc 0]
                               (let [t (anext s)
                                     result (await t)]
                                 (if result
                                   (let [[v rest-s] result]
                                     (recur rest-s (+ acc v)))
                                   acc))))]
          ;; Should sum to 60
          (run-spin! consumer-spin
                     (fn [result]
                       (is (= 60 result))
                       (done))
                     (fn [e]
                       (is false (str "error: " e))
                       (done))))))))
