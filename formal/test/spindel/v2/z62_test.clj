(ns spindel.v2.z62-test
  "Z#62: a semaphore's maximum is its permit count at creation (`SourceRow.max`); a release at the
  maximum is refused (engine `sem-release!`). Pins on tasks (engine `kind-ok?` :pin): a pinned task
  is a retention root."
  (:require [clojure.test :refer [deftest is testing]]
            [spindel.v2.state :as s]
            [spindel.v2.engine :as en]
            [spindel.v2.retain :as r]
            [spindel.v2.oracle :as o]))

(defn- it [tag & fields] (into [(o/ctor-idx tag)] fields))
(defn- row [w t id] (some #(when (= id (:id %)) %) (get w t)))
(defn- step [w item] (en/world-step w item))
(defn- set-state [w id v] (update w :sources (fn [xs] (map #(if (= id (:id %)) (assoc % :state v) %) xs))))

(deftest semaphore-max
  (let [w0 s/empty-world
        x (:next-id w0)
        o1 (step w0 (it :create-source-top 2 s/sk-semaphore 2 x))
        w1 (:world o1)]
    (is (true? (:accepted o1)))
    (is (= [2 2] ((juxt :state :max) (row w1 :sources x))) "created with its permits, maximum = permits")
    (testing "a release at the maximum is refused and changes nothing"
      (let [o (step w1 (it :release x))]
        (is (false? (:accepted o)))
        (is (= w1 (:world o)))))
    (testing "below the maximum a release returns a permit"
      (let [w2 (set-state w1 x 1)
            o (step w2 (it :release x))]
        (is (true? (:accepted o)))
        (is (= [2 2] ((juxt :state :max) (row (:world o) :sources x))))
        (is (false? (:accepted (step (:world o) (it :release x)))) "the second release is at the maximum")))
    (testing "other kinds keep refusing release"
      (let [y (:next-id w1)
            w3 (:world (step w1 (it :create-source-top 2 s/sk-signal 5 y)))]
        (is (false? (:accepted (step w3 (it :release y)))))))))

(deftest pin-a-task
  (let [w0 s/empty-world
        k (:next-id w0)
        o1 (step w0 (it :spawn-top 2 7 k [] false))
        w1 (:world o1)]
    (is (true? (:accepted o1)))
    (is (some? (row w1 :tasks k)))
    (let [o (step w1 (it :pin k))]
      (is (true? (:accepted o)) "a task can be pinned")
      (is (= [k] (vec (:pins (:world o)))))
      (is (some #{k} (r/roots (:world o))) "a pinned task is a retention root"))
    (is (false? (:accepted (step w1 (it :pin 999)))) "an unknown id is refused")))
