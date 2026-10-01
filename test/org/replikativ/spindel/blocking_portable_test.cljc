(ns org.replikativ.spindel.blocking-portable-test
  "`blocking` on both platforms: its value, its throw."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.blocking :as blocking]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]])
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]])))

(deftest blocking-resolves-with-the-value-of-f
  (async done
         (with-ctx [_ctx]
           (run-spin! (spin (inc (await (blocking/blocking (fn [] 41)))))
                      (fn [v] (is (= 42 v)) (done))
                      (fn [e] (is false (str "rejected: " (ex-message e))) (done))))))

(deftest blocking-rejects-with-the-throw-of-f
  (async done
         (with-ctx [_ctx]
           (run-spin! (spin (await (blocking/blocking (fn [] (throw (ex-info "boom" {:code 7}))))))
                      (fn [_] (is false "should reject") (done))
                      (fn [e] (is (= 7 (:code (ex-data e)))) (done))))))
