(ns org.replikativ.spindel.v2.case-dispatch-test
  "Consumer regression for partial-cps keyword-case dispatch across registered
   breakpoints. All eleven ordinary branches complete; ordinary effects in
   finalizers still fail with the cleanup admission error."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [task await]]))

(def selectors [:await :track :external :sleep :spawn :spin :fork :savepoint :scope :custom :custom-helper])

(defn- ordinary-case [selector ready]
  (task
   (case selector
     :await (await ready)
     :track (await ready)
     :external (await ready)
     :sleep (await ready)
     :spawn (await ready)
     :spin (await ready)
     :fork (await ready)
     :savepoint (await ready)
     :scope (await ready)
     :custom (await ready)
     :custom-helper (await ready))))

(defn- finalizer-case [selector ready]
  (task
   (try :body
        (finally
          (case selector
            :await (await ready)
            :track (await ready)
            :external (await ready)
            :sleep (await ready)
            :spawn (await ready)
            :spin (await ready)
            :fork (await ready)
            :savepoint (await ready)
            :scope (await ready)
            :custom (await ready)
            :custom-helper (await ready))))))

(deftest keyword-case-keeps-every-suspending-branch
  (let [w (v2/world)]
    (binding [v2/*world* w]
      (let [ready (v2/deferred)]
        (v2/deliver! ready :ok)
        (doseq [selector selectors]
          (testing (str selector)
            (let [out (atom nil)]
              (v2/value-async (ordinary-case selector ready)
                              (fn [value failed?]
                                (reset! out [(if failed? (ex-message value) value) failed?])))
              (is (= [:ok false] @out)))
            (let [out (atom nil)]
              (v2/value-async (finalizer-case selector ready)
                              (fn [value _failed?]
                                (reset! out (:spindel/invalid
                                             (ex-data (first (:spindel/cleanup-failures (ex-data value))))))))
              (is (= :finalizer-effect @out))))))
      (v2/release-world! w))))
