(ns org.replikativ.spindel.v2.port.result-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task await track]]
            [org.replikativ.spindel.v2.combinators :as comb :refer [parallel]]
            [org.replikativ.spindel.v2.port.support :refer
             [checking vworld with-world outcome check-result observed-value wait-until required-api]]))

(use-fixtures :each checking)

(deftest test-ok-construction
  (testing "ok creates success result"
    (let [r ((required-api 'ok) 42)]
      (is ((required-api 'ok?) r))
      (is (not ((required-api 'error?) r)))
      (is (= 42 ((required-api 'unwrap) r)))))

  (testing "ok with nil value"
    (let [r ((required-api 'ok) nil)]
      (is ((required-api 'ok?) r))
      (is (not ((required-api 'error?) r)))
      (is (nil? ((required-api 'unwrap) r)))))

  (testing "ok with complex value"
    (let [r ((required-api 'ok) {:a 1 :b [2 3]})]
      (is ((required-api 'ok?) r))
      (is (= {:a 1 :b [2 3]} ((required-api 'unwrap) r))))))

(deftest test-error-construction
  (testing "error creates error result"
    (let [ex (ex-info "test error" {})
          r ((required-api 'error) ex)]
      (is ((required-api 'error?) r))
      (is (not ((required-api 'ok?) r)))
      (is (thrown? clojure.lang.ExceptionInfo ((required-api 'unwrap) r)))))

  (testing "error unwrap throws original exception"
    (let [ex (ex-info "test error" {:data 123})
          r ((required-api 'error) ex)]
      (try
        ((required-api 'unwrap) r)
        (is false "Should have thrown")
        (catch clojure.lang.ExceptionInfo e
          (is (= "test error" (ex-message e)))
          (is (= {:data 123} (ex-data e))))))))

(deftest test-match
  (testing "match calls ok-fn on success"
    (let [r ((required-api 'ok) 42)
          result ((required-api 'match) r
                                        (fn [v] [:ok v])
                                        (fn [e] [:error e]))]
      (is (= [:ok 42] result))))

  (testing "match calls error-fn on error"
    (let [ex (ex-info "test error" {})
          r ((required-api 'error) ex)
          result ((required-api 'match) r
                                        (fn [v] [:ok v])
                                        (fn [e] [:error e]))]
      (is (= [:error ex] result))))

  (testing "match with nil value"
    (let [r ((required-api 'ok) nil)
          result ((required-api 'match) r
                                        (fn [v] [:ok v])
                                        (fn [e] [:error e]))]
      (is (= [:ok nil] result))))

  (testing "match allows side effects"
    (let [called (atom nil)
          r ((required-api 'ok) 42)]
      ((required-api 'match) r
                             (fn [v] (reset! called [:ok v]))
                             (fn [e] (reset! called [:error e])))
      (is (= [:ok 42] @called)))))

(deftest test-result-equality
  (testing "ok results with same value are equal"
    (is (= ((required-api 'ok) 42) ((required-api 'ok) 42))))

  (testing "ok results with different values are not equal"
    (is (not= ((required-api 'ok) 42) ((required-api 'ok) 43))))

  (testing "ok and error are never equal"
    (let [ex (ex-info "test" {})]
      (is (not= ((required-api 'ok) 42) ((required-api 'error) ex)))))

  (testing "error results with same exception are equal"
    (let [ex (ex-info "test" {})]
      (is (= ((required-api 'error) ex) ((required-api 'error) ex)))))

  (testing "nil values are properly handled in equality"
    (is (= ((required-api 'ok) nil) ((required-api 'ok) nil)))
    (is (not= ((required-api 'ok) nil) ((required-api 'ok) 0)))))

(deftest test-result-predicates
  (testing "ok? and error? are mutually exclusive"
    (let [ok-result ((required-api 'ok) 42)
          error-result ((required-api 'error) (ex-info "test" {}))]
      (is (and ((required-api 'ok?) ok-result)
               (not ((required-api 'error?) ok-result))))
      (is (and ((required-api 'error?) error-result)
               (not ((required-api 'ok?) error-result)))))))
