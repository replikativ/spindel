(ns org.replikativ.spindel.v2.port.spin-error-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task await track]]
            [org.replikativ.spindel.v2.combinators :as comb :refer [parallel]]
            [org.replikativ.spindel.v2.port.support :refer
             [checking vworld with-world outcome check-result observed-value wait-until required-api]]))

(use-fixtures :each checking)

(deftest test-spin-throws-exception
  (with-world [w]
    (let [[tag e] (outcome (spin (throw (ex-info "Test error" {:code 42}))))]
      (is (= :err tag))
      (is (= "Test error" (ex-message e)))
      (is (= {:code 42} (ex-data e))))))

(deftest test-error-is-cached
  (with-world [w]
    (let [executions (atom 0)
          c (spin (let [n (swap! executions inc)]
                    (throw (ex-info "Cached error" {:attempt n}))))]
      (dotimes [_ 2]
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Cached error"
                              (v2/value c 2000 ::timeout)))
        (is (= 1 @executions))))))

(deftest test-error-propagates-through-await
  (with-world [w]
    (let [a (spin (throw (ex-info "Upstream error" {})))
          b (spin (* 2 (await a)))]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Upstream error"
                            (v2/value b 2000 ::timeout))))))

(deftest test-error-propagates-through-chain
  (with-world [w]
    (let [a (spin 10) b (spin (throw (ex-info "Spin2 error" {})))
          c (spin (+ (await a) (await b)))]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Spin2 error"
                            (v2/value c 2000 ::timeout))))))

(deftest test-partial-chain-success
  (with-world [w]
    (let [a (spin (+ 1 2)) b (spin (* 2 (await a)))
          c (spin (throw (ex-info "Spin3 error" {})))
          d (spin (+ (await b) (await c)))]
      (is (= [:ok 3] (outcome a)))
      (is (= [:ok 6] (outcome b)))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Spin3 error" (v2/value c 2000 ::timeout)))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Spin3 error" (v2/value d 2000 ::timeout))))))

(deftest test-error-preserves-message
  (with-world [w]
    (let [[tag e] (outcome (spin (throw (ex-info "Specific error message" {:x 1}))))]
      (is (= :err tag))
      (is (= "Specific error message" (ex-message e))))))

(deftest test-error-preserves-ex-data
  (with-world [w]
    (let [data {:error-code 500 :context "test"}
          [tag e] (outcome (spin (throw (ex-info "Error" data))))]
      (is (= :err tag))
      (is (= data (ex-data e))))))

(deftest test-error-cache-stores-correct-error
  (with-world [w]
    (let [original (ex-info "Original" {:data 123}) c (spin (throw original))]
      (dotimes [_ 2]
        (let [[tag e] (outcome c)]
          (is (= :err tag))
          (is (identical? original e))
          (is (= "Original" (ex-message e)))
          (is (= {:data 123} (ex-data e))))))))

(deftest test-error-with-cause
  (with-world [w]
    (let [cause (Exception. "Root cause")
          wrapped (ex-info "Wrapped" {:wrapped true} cause)
          [tag e] (outcome (spin (throw wrapped)))]
      (is (= :err tag))
      (is (= "Wrapped" (ex-message e)))
      (is (= {:wrapped true} (ex-data e)))
      (is (identical? cause (ex-cause e)))
      (is (= "Root cause" (ex-message (ex-cause e)))))))

(deftest test-spin-error-then-signal-change
  (with-world [w]
    (let [divisor (v2/signal 0) c (spin (/ 100 (:new (track divisor))))]
      (is (thrown? ArithmeticException (v2/value c 2000 ::timeout)))
      (reset! divisor 10)
      (is (= [:ok 10] (outcome c))))))

(deftest test-retry-with-success
  (with-world [w]
    (let [attempt (v2/signal 1)
          c (spin (let [n (:new (track attempt))]
                    (if (< n 3) (throw (ex-info "Not ready" {:attempt n})) (* 2 n))))]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Not ready" (v2/value c 2000 ::timeout)))
      (reset! attempt 2)
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Not ready" (v2/value c 2000 ::timeout)))
      (reset! attempt 3)
      (is (= [:ok 6] (outcome c))))))

(deftest test-successful-spin-then-error
  (with-world [w]
    (let [x (v2/signal 10)
          c (spin (let [n (:new (track x))]
                    (when (< n 0) (throw (ex-info "Negative value" {:val n}))) (* 2 n)))]
      (is (= [:ok 20] (outcome c)))
      (reset! x -5)
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Negative value" (v2/value c 2000 ::timeout))))))

(deftest test-error-then-success
  (with-world [w]
    (let [x (v2/signal -5)
          c (spin (let [n (:new (track x))]
                    (when (< n 0) (throw (ex-info "Must be positive" {:val n}))) (* 2 n)))]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Must be positive" (v2/value c 2000 ::timeout)))
      (reset! x 10)
      (is (= [:ok 20] (outcome c))))))

(deftest test-spin-division-by-zero
  (with-world [w]
    (is (thrown? ArithmeticException (v2/value (spin (/ 1 0)) 2000 ::timeout)))))

(deftest test-spin-null-pointer
  (with-world [w]
    (is (thrown? NullPointerException (v2/value (spin (.toString nil)) 2000 ::timeout)))))

(deftest test-runtime-exception
  (with-world [w]
    (is (thrown? RuntimeException (v2/value (spin (throw (RuntimeException. "Runtime error"))) 2000 ::timeout)))))

(deftest test-illegal-argument-exception
  (with-world [w]
    (is (thrown? IllegalArgumentException (v2/value (spin (throw (IllegalArgumentException. "Invalid argument"))) 2000 ::timeout)))))

(deftest test-assertion-error
  (with-world [w]
    (is (thrown? AssertionError (v2/value (spin (assert false "Assertion failed")) 2000 ::timeout)))))

(deftest ^:gap test-attempt-captures-ok
  (with-world [w]
    (let [c (spin (let [f (await ((required-api 'attempt) (spin 42)))] (f)))]
      (is (= [:ok 42] (outcome c))))))

(deftest ^:gap test-attempt-captures-error
  (with-world [w]
    (let [risky (spin (throw (ex-info "boom" {:x 1})))
          c (spin (let [f (await ((required-api 'attempt) risky))]
                    (try (f) :no-throw (catch Throwable e [:caught (ex-message e)]))))]
      (is (= [:ok [:caught "boom"]] (outcome c))))))

(deftest ^:gap test-absolve-unwraps-ok
  (with-world [w]
    (let [wrapped (spin (fn [] 99))
          c (spin (await ((required-api 'absolve) wrapped)))]
      (is (= [:ok 99] (outcome c))))))

(deftest ^:gap test-absolve-rethrows-error
  (with-world [w]
    (let [wrapped (spin (fn [] (throw (ex-info "kaboom" {}))))
          c (spin (await ((required-api 'absolve) wrapped)))]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"kaboom" (v2/value c 2000 ::timeout))))))

(deftest ^:gap test-attempt-absolve-roundtrip
  (with-world [w]
    (let [c (spin (await ((required-api 'absolve) ((required-api 'attempt) (spin 7)))))]
      (is (= [:ok 7] (outcome c))))))
