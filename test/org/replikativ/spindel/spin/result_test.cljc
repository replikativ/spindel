(ns org.replikativ.spindel.spin.result-test
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.spin.result :as result]))

(deftest test-ok-construction
  (testing "ok creates success result"
    (let [r (result/ok 42)]
      (is (result/ok? r))
      (is (not (result/error? r)))
      (is (= 42 (result/unwrap r)))))

  (testing "ok with nil value"
    (let [r (result/ok nil)]
      (is (result/ok? r))
      (is (not (result/error? r)))
      (is (nil? (result/unwrap r)))))

  (testing "ok with complex value"
    (let [r (result/ok {:a 1 :b [2 3]})]
      (is (result/ok? r))
      (is (= {:a 1 :b [2 3]} (result/unwrap r))))))

(deftest test-error-construction
  (testing "error creates error result"
    (let [ex (ex-info "test error" {})
          r (result/error ex)]
      (is (result/error? r))
      (is (not (result/ok? r)))
      (is (thrown? #?(:clj clojure.lang.ExceptionInfo :cljs ExceptionInfo) (result/unwrap r)))))

  (testing "error unwrap throws original exception"
    (let [ex (ex-info "test error" {:data 123})
          r (result/error ex)]
      (try
        (result/unwrap r)
        (is false "Should have thrown")
        (catch #?(:clj clojure.lang.ExceptionInfo :cljs ExceptionInfo) e
          (is (= "test error" (ex-message e)))
          (is (= {:data 123} (ex-data e))))))))

(deftest test-match
  (testing "match calls ok-fn on success"
    (let [r (result/ok 42)
          result (result/match r
                   (fn [v] [:ok v])
                   (fn [e] [:error e]))]
      (is (= [:ok 42] result))))

  (testing "match calls error-fn on error"
    (let [ex (ex-info "test error" {})
          r (result/error ex)
          result (result/match r
                   (fn [v] [:ok v])
                   (fn [e] [:error e]))]
      (is (= [:error ex] result))))

  (testing "match with nil value"
    (let [r (result/ok nil)
          result (result/match r
                   (fn [v] [:ok v])
                   (fn [e] [:error e]))]
      (is (= [:ok nil] result))))

  (testing "match allows side effects"
    (let [called (atom nil)
          r (result/ok 42)]
      (result/match r
        (fn [v] (reset! called [:ok v]))
        (fn [e] (reset! called [:error e])))
      (is (= [:ok 42] @called)))))

(deftest test-result-equality
  (testing "ok results with same value are equal"
    (is (= (result/ok 42) (result/ok 42))))

  (testing "ok results with different values are not equal"
    (is (not= (result/ok 42) (result/ok 43))))

  (testing "ok and error are never equal"
    (let [ex (ex-info "test" {})]
      (is (not= (result/ok 42) (result/error ex)))))

  (testing "error results with same exception are equal"
    (let [ex (ex-info "test" {})]
      (is (= (result/error ex) (result/error ex)))))

  (testing "nil values are properly handled in equality"
    (is (= (result/ok nil) (result/ok nil)))
    (is (not= (result/ok nil) (result/ok 0)))))

(deftest test-result-predicates
  (testing "ok? and error? are mutually exclusive"
    (let [ok-result (result/ok 42)
          error-result (result/error (ex-info "test" {}))]
      (is (and (result/ok? ok-result)
               (not (result/error? ok-result))))
      (is (and (result/error? error-result)
               (not (result/ok? error-result)))))))

(deftest test-result-protocol-implementation
  (testing "Result implements PResult"
    (let [r (result/ok 42)]
      (is (satisfies? result/PResult r))))

  (testing "All protocol methods work"
    (let [ok-r (result/ok 42)
          err-r (result/error (ex-info "test" {}))]
      (is (boolean? (result/ok? ok-r)))
      (is (boolean? (result/error? ok-r)))
      (is (number? (result/unwrap ok-r)))
      (is (some? (result/match ok-r identity (constantly nil)))))))
