(ns org.replikativ.spindel.spin.result-test
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.spin.core :as spin-core]))

(deftest test-ok-construction
  (testing "ok creates success result"
    (let [r (spin-core/ok 42)]
      (is (spin-core/ok? r))
      (is (not (spin-core/error? r)))
      (is (= 42 (spin-core/unwrap r)))))

  (testing "ok with nil value"
    (let [r (spin-core/ok nil)]
      (is (spin-core/ok? r))
      (is (not (spin-core/error? r)))
      (is (nil? (spin-core/unwrap r)))))

  (testing "ok with complex value"
    (let [r (spin-core/ok {:a 1 :b [2 3]})]
      (is (spin-core/ok? r))
      (is (= {:a 1 :b [2 3]} (spin-core/unwrap r))))))

(deftest test-error-construction
  (testing "error creates error result"
    (let [ex (ex-info "test error" {})
          r (spin-core/error ex)]
      (is (spin-core/error? r))
      (is (not (spin-core/ok? r)))
      (is (thrown? #?(:clj clojure.lang.ExceptionInfo :cljs ExceptionInfo) (spin-core/unwrap r)))))

  (testing "error unwrap throws original exception"
    (let [ex (ex-info "test error" {:data 123})
          r (spin-core/error ex)]
      (try
        (spin-core/unwrap r)
        (is false "Should have thrown")
        (catch #?(:clj clojure.lang.ExceptionInfo :cljs ExceptionInfo) e
          (is (= "test error" (ex-message e)))
          (is (= {:data 123} (ex-data e))))))))

(deftest test-match
  (testing "match calls ok-fn on success"
    (let [r (spin-core/ok 42)
          result (spin-core/match r
                   (fn [v] [:ok v])
                   (fn [e] [:error e]))]
      (is (= [:ok 42] result))))

  (testing "match calls error-fn on error"
    (let [ex (ex-info "test error" {})
          r (spin-core/error ex)
          result (spin-core/match r
                   (fn [v] [:ok v])
                   (fn [e] [:error e]))]
      (is (= [:error ex] result))))

  (testing "match with nil value"
    (let [r (spin-core/ok nil)
          result (spin-core/match r
                   (fn [v] [:ok v])
                   (fn [e] [:error e]))]
      (is (= [:ok nil] result))))

  (testing "match allows side effects"
    (let [called (atom nil)
          r (spin-core/ok 42)]
      (spin-core/match r
        (fn [v] (reset! called [:ok v]))
        (fn [e] (reset! called [:error e])))
      (is (= [:ok 42] @called)))))

(deftest test-result-equality
  (testing "ok results with same value are equal"
    (is (= (spin-core/ok 42) (spin-core/ok 42))))

  (testing "ok results with different values are not equal"
    (is (not= (spin-core/ok 42) (spin-core/ok 43))))

  (testing "ok and error are never equal"
    (let [ex (ex-info "test" {})]
      (is (not= (spin-core/ok 42) (spin-core/error ex)))))

  (testing "error results with same exception are equal"
    (let [ex (ex-info "test" {})]
      (is (= (spin-core/error ex) (spin-core/error ex)))))

  (testing "nil values are properly handled in equality"
    (is (= (spin-core/ok nil) (spin-core/ok nil)))
    (is (not= (spin-core/ok nil) (spin-core/ok 0)))))

(deftest test-result-predicates
  (testing "ok? and error? are mutually exclusive"
    (let [ok-result (spin-core/ok 42)
          error-result (spin-core/error (ex-info "test" {}))]
      (is (and (spin-core/ok? ok-result)
               (not (spin-core/error? ok-result))))
      (is (and (spin-core/error? error-result)
               (not (spin-core/ok? error-result)))))))

(deftest test-result-protocol-implementation
  (testing "Result implements PResult"
    (let [r (spin-core/ok 42)]
      (is (satisfies? spin-core/PResult r))))

  (testing "All protocol methods work"
    (let [ok-r (spin-core/ok 42)
          err-r (spin-core/error (ex-info "test" {}))]
      (is (boolean? (spin-core/ok? ok-r)))
      (is (boolean? (spin-core/error? ok-r)))
      (is (number? (spin-core/unwrap ok-r)))
      (is (some? (spin-core/match ok-r identity (constantly nil)))))))
