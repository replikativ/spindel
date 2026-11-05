(ns org.replikativ.spindel.v2.case-dispatch-gap-test
  "Known partial-cps 0.1.72 keyword-case emission defect. Must close before
   Foerster compiler acceptance; cleanup admission tests use cond independently.
   The dependency's CLJ case* emitter rebuilds a sorted dispatch table as {}.
   More than eight keyword entries then misdispatch. Ordinary task and standalone
   async reproductions are preserved in .internal/validation/case-repro.clj.
   Upstream original local commit c4d2dd2 fixes both emitters via (empty imap);
   adopting/pinning that fix requires the separate dependency checkpoint."
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

(deftest ^:gap keyword-case-keeps-every-suspending-branch
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
