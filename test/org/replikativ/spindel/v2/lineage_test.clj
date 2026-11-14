(ns org.replikativ.spindel.v2.lineage-test
  "§8.1: a world reaches only rows it inherited: created by itself, or by an
   ancestor before the fork that leads to it."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.port.helpers :refer [checked-fixture]]))

(use-fixtures :each checked-fixture)

(defn- lineage? [t] (= :lineage (:spindel/invalid (ex-data t))))

(defmacro refused? [form]
  `(try ~form false (catch clojure.lang.ExceptionInfo t# (lineage? t#))))

(deftest a-row-from-before-the-fork-is-inherited
  (let [root v2/*world* s (v2/signal 1) c (v2/fork! root)]
    (try
      (is (= 1 @(v2/in-world c s)))
      (finally (v2/release-world! c)))))

(deftest a-row-created-after-the-fork-is-not
  (let [root v2/*world* c (v2/fork! root) s (v2/signal 1)]
    (try
      (is (refused? (v2/in-world c s)))
      (finally (v2/release-world! c)))))

(deftest a-grandchild-inherits-from-every-ancestor-up-to-its-forks
  (let [root v2/*world* a (v2/signal :a) c (v2/fork! root)
        b (binding [v2/*world* c] (v2/signal :b))
        g (v2/fork! c)
        late (binding [v2/*world* c] (v2/signal :late))]
    (try
      (is (= :a @(v2/in-world g a)))
      (is (= :b @(v2/in-world g b)))
      (is (refused? (v2/in-world g late)))
      (finally (v2/release-world! g) (v2/release-world! c)))))

(deftest a-siblings-row-older-than-the-fork-is-not-inherited
  (let [root v2/*world* left (v2/fork! root)
        d (binding [v2/*world* left] (v2/deferred))
        right (v2/fork! root)]
    (try
      (is (refused? (v2/in-world right d)) "d is older than right's fork point but was never in root")
      (finally (v2/release-world! left) (v2/release-world! right)))))

(deftest a-foreign-handle-is-refused-where-it-is-used
  (let [root v2/*world* c (v2/fork! root) s (v2/signal 0)]
    (try
      (is (refused? (v2/host-call! c #(v2/row-of s))))
      (finally (v2/release-world! c)))))
