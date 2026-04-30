(ns org.replikativ.spindel.distributed.bridge-test
  "Unit tests for spindel/core.async bridge functions."
  (:require #?(:clj [clojure.test :refer [deftest is testing use-fixtures]]
               :cljs [cljs.test :refer [deftest is testing] :include-macros true])
            [org.replikativ.spindel.distributed.core :as dist]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.executor :as scheduler]
            #?(:clj [org.replikativ.spindel.spin.cps :refer [spin]])
            [org.replikativ.spindel.effects.await :refer [await]]
            #?(:clj [clojure.core.async :as a :refer [go <! >! chan close! put! take!]]
               :cljs [cljs.core.async :as a :refer [chan close! put! take!]]))
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]]
                            [cljs.core.async.macros :refer [go]]
                            [cljs.test :refer [use-fixtures async]])))

;; =============================================================================
;; Test Fixtures
;; =============================================================================

(def ^:dynamic *test-runtime* nil)

(defn with-runtime [f]
  (let [executor (scheduler/default-executor)
        rt (ctx/create-execution-context :executor executor)]
    ;; Register context for remote spin lookup
    (dist/register-context! :default rt)
    (try
      (binding [*test-runtime* rt
                ec/*execution-context* rt]
        (f))
      (finally
        (dist/unregister-context! :default)
        (ctx/stop-context! rt)))))

(use-fixtures :each with-runtime)

;; =============================================================================
;; spin->chan Tests
;; =============================================================================

;; Helper: take from a channel into a promise so the test can deterministically
;; wait for the value to land instead of guessing at a Thread/sleep duration.
;; Cross-platform: on JVM we use a Clojure promise; on JS we use cljs.test/async
;; in the call sites that need it.
(defn- chan->promise [ch]
  #?(:clj  (let [p (promise)]
             (take! ch (fn [v] (deliver p v)))
             p)
     :cljs (let [p (atom nil)]
             (take! ch (fn [v] (reset! p v)))
             p)))

(deftest test-spin->chan-success
  (testing "spin->chan delivers success value to channel"
    (let [t (spin 42)
          ch (dist/spin->chan t)
          p (chan->promise ch)]
      #?(:clj (is (= 42 (deref p 1000 :timeout)))
         :cljs (is (= 42 @p))))))

(deftest test-spin->chan-nil-value
  (testing "spin->chan handles nil values via sentinel"
    (let [t (spin nil)
          ch (dist/spin->chan t)
          p (chan->promise ch)]
      #?(:clj (is (= :org.replikativ.spindel.distributed.core/nil-value
                     (deref p 1000 :timeout)))
         :cljs (is (= :org.replikativ.spindel.distributed.core/nil-value @p))))))

(deftest test-spin->chan-error
  (testing "spin->chan delivers errors to channel"
    (let [t (spin (throw (ex-info "test error" {:code 123})))
          ch (dist/spin->chan t)
          p (chan->promise ch)]
      #?(:clj (let [v (deref p 1000 :timeout)]
                (is (instance? Throwable v))
                (is (= "test error" (ex-message v))))
         :cljs (do (is (instance? js/Error @p))
                   (is (= "test error" (ex-message @p))))))))

(deftest test-spin->chan-computed-value
  (testing "spin->chan works with computed values"
    (let [t (spin (+ 1 2 3 4 5))
          ch (dist/spin->chan t)
          p (chan->promise ch)]
      #?(:clj (is (= 15 (deref p 1000 :timeout)))
         :cljs (is (= 15 @p))))))

;; =============================================================================
;; chan->spin Tests (CLJ only - requires blocking deref)
;; =============================================================================

#?(:clj
   (deftest test-chan->spin-success
     (testing "chan->spin resolves with channel value"
       (let [ch (chan 1)
             t (dist/chan->spin ch)
             ;; Put value on channel
             _ (put! ch 42)
             ;; Await in spin context
             result @(spin (await t))]
         (is (= 42 result))))))

#?(:clj
   (deftest test-chan->spin-nil
     (testing "chan->spin handles nil via sentinel"
       (let [ch (chan 1)
             t (dist/chan->spin ch)
             _ (put! ch :org.replikativ.spindel.distributed.core/nil-value)
             result @(spin (await t))]
         (is (nil? result))))))

#?(:clj
   (deftest test-chan->spin-error
     (testing "chan->spin rejects with error from channel"
       (let [ch (chan 1)
             t (dist/chan->spin ch)
             test-error (ex-info "remote error" {:code 500})
             _ (put! ch test-error)]
         (is (thrown-with-msg? clojure.lang.ExceptionInfo #"remote error"
               @(spin (await t))))))))

;; =============================================================================
;; Round-trip Tests (CLJ only)
;; =============================================================================

#?(:clj
   (deftest test-spin-chan-round-trip
     (testing "spin -> channel -> spin round trip"
       (let [original-value {:data [1 2 3] :nested {:a "b"}}
             t1 (spin original-value)
             ch (dist/spin->chan t1)
             t2 (dist/chan->spin ch)
             result @(spin (await t2))]
         (is (= original-value result))))))

#?(:clj
   (deftest test-spin-chan-round-trip-computed
     (testing "computed spin -> channel -> spin round trip"
       (let [t1 (spin
                  (let [x 10
                        y 20]
                    {:sum (+ x y) :product (* x y)}))
             ch (dist/spin->chan t1)
             t2 (dist/chan->spin ch)
             result @(spin (await t2))]
         (is (= {:sum 30 :product 200} result))))))

#?(:clj
   (deftest test-nested-await-round-trip
     (testing "nested await through channel round trip"
       (let [inner-spin (spin 100)
             outer-spin (spin
                          (let [inner-result (await inner-spin)]
                            (* inner-result 2)))
             ch (dist/spin->chan outer-spin)
             t2 (dist/chan->spin ch)
             result @(spin (await t2))]
         (is (= 200 result))))))

;; =============================================================================
;; Registry Tests
;; =============================================================================

(deftest test-remote-spin-registry
  (testing "register and lookup remote spins"
    ;; Register a spin factory
    (dist/register-remote-spin!
      'test.ns/my-func
      (fn [{:keys [x]}]
        (let [ch (chan 1)]
          (put! ch (* x 2))
          ch)))

    ;; Lookup should succeed
    (is (some? (dist/get-remote-spin 'test.ns/my-func)))

    ;; Unknown lookup returns nil
    (is (nil? (dist/get-remote-spin 'test.ns/unknown)))))

(deftest test-response-handler-lifecycle
  (testing "response handler registration and dispatch"
    (let [request-id (random-uuid)
          received (atom nil)]
      ;; Register handler
      (dist/register-response-handler!
        request-id
        (fn [response] (reset! received response)))

      ;; Handler should exist
      (is (some? (dist/get-response-handler request-id)))

      ;; Dispatch response
      (dist/handle-response! {:request-id request-id :result 42})

      ;; Should have received
      (is (= {:request-id request-id :result 42} @received))

      ;; Handler should be cleaned up
      (is (nil? (dist/get-response-handler request-id))))))

;; =============================================================================
;; Utility Tests
;; =============================================================================

(deftest test-throwable-detection
  (testing "throwable? correctly identifies errors"
    (is (dist/throwable? (ex-info "test" {})))
    (is (dist/throwable? #?(:clj (Exception. "test")
                            :cljs (js/Error. "test"))))
    (is (not (dist/throwable? "not an error")))
    (is (not (dist/throwable? {:type :error})))
    (is (not (dist/throwable? nil)))))
