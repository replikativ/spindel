(ns org.replikativ.spindel.v2.census-test
  "Census gate (§0): retained rows stay bounded under churn, including the
   pattern that leaked in the old engine (a long-lived body awaiting a fresh
   child per iteration, the dvergr :await-conts growth)."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await take!]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.verify :as verify]
            [org.replikativ.spindel.incremental.interval :as iv]))

(defn- census [w]
  (verify/gc-settle! w)
  (v2/call-in! w #(frequencies (map (fn [r] (aget ^objects r rw/TYPE)) (vals (aget ^objects w rw/W-REG))))))

(defn- total [c] (reduce + (vals c)))

(deftest long-lived-task-awaiting-fresh-children
  (let [w (v2/world {:verify? true})]
    (binding [v2/*world* w]
      (let [mb (v2/mailbox)
            n 300
            done (v2/deferred)
            loop-task (task (loop [i 0 acc 0]
                              (let [m (take! mb)]
                                (if (= m :stop)
                                  (do (v2/deliver! done acc) acc)
                                  (recur (inc i) (+ acc (await (spin (* 2 m)))))))))
            before (atom nil)]
        (dotimes [i 10] (v2/post! mb i))
        (reset! before (total (census w)))
        (dotimes [i n] (v2/post! mb i))
        (let [after (total (census w))]
          (is (<= after (+ @before 2)) (str "rows grew from " @before " to " after)))
        (v2/post! mb :stop)
        (is (= (* 2 (+ (reduce + (range 10)) (reduce + (range n)))) (v2/value done 5000 ::timeout)))))))

(deftest observed-computation-with-child-per-run
  (let [w (v2/world {:verify? true})]
    (binding [v2/*world* w]
      (let [x (v2/signal 0)
            parent (spin (let [v (iv/get-new (track x))]
                           (await (spin (inc v)))))
            u (v2/observe! parent (fn [_ _]))]
        (dotimes [i 10] (v2/write! x i))
        (let [before (total (census w))]
          (dotimes [i 1000] (v2/write! x i))
          (is (<= (total (census w)) before)))
        (u)
        (let [c (census w)]
          (is (zero? (get c rw/T-EDGE 0)))
          (is (zero? (get c rw/T-RUN 0))))))))

(deftest unobserved-graph-is-reclaimed
  (let [w (v2/world {:verify? true})]
    (binding [v2/*world* w]
      (let [x (v2/signal 0)]
        (dotimes [_ 50]
          (let [a (spin (iv/get-new (track x)))
                b (spin (* 2 (await a)))
                u (v2/observe! b (fn [_ _]))]
            (v2/write! x 1)
            (u)))
        (let [c (census w)]
          (is (<= (get c rw/T-COMP 0) 2) (str "census " c))
          (is (zero? (get c rw/T-EDGE 0)) (str "census " c)))))))
