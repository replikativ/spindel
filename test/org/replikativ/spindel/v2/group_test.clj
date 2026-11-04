(ns org.replikativ.spindel.v2.group-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await await-all await-any]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.verify :as verify]
            [org.replikativ.spindel.incremental.interval :as iv]))

(def ^:dynamic *divergences* nil)

(defn- vworld []
  (v2/world {:verify? true :hook (verify/checking-hook *divergences*)}))

(defmacro checked [& body]
  `(binding [*divergences* (atom [])]
     ~@body
     (is (empty? @*divergences*) (str "Rule R divergences: " (vec (take 3 @*divergences*))))))

(defn- census [w]
  (let [fr (v2/call-in! w #(frequencies (map (fn [r] (aget ^objects r rw/TYPE)) (vals (aget ^objects w rw/W-REG)))))]
    {:comps (get fr rw/T-COMP 0) :tasks (get fr rw/T-TASK 0) :runs (get fr rw/T-RUN 0)
     :edges (get fr rw/T-EDGE 0) :acts (get fr rw/T-ACT 0)}))

(defn- outcome [h]
  (try (let [v (v2/value h 100 ::pending)] (if (= ::pending v) [:pending] [:ok v]))
       (catch Exception e [:err e])))

(deftest task-await-all
  (checked
    (let [w (vworld)]
      (binding [v2/*world* w]
        (let [x (v2/signal 2)
              c (spin (* 10 (iv/get-new (track x))))
              d (v2/deferred)
              t (task (await-all [c d c]))]
          (is (= :pending (first (outcome t))))
          (v2/deliver! d :d)
          (is (= [20 :d 20] (v2/value t)))
          (is (= 0 (:edges (census w)))))))))

(deftest task-await-any-cancels-losers
  (checked
    (let [w (vworld)]
      (binding [v2/*world* w]
        (let [d1 (v2/deferred)
              d2 (v2/deferred)
              loser (atom nil)
              t (task (await-any [(task (await d1)) (reset! loser (task (await d2)))]))]
          (v2/deliver! d1 :one)
          (is (= :one (v2/value t)))
          (is (= :err (first (outcome @loser))) "the losing child was cancelled")
          (is (= 0 (:edges (census w))))
          (is (= 0 (:runs (census w)))))))))

(deftest computation-await-all-restarts
  (checked
    (let [w (vworld)]
      (binding [v2/*world* w]
        (let [x (v2/signal 1)
              y (v2/signal 2)
              a (spin (iv/get-new (track x)))
              b (spin (iv/get-new (track y)))
              c (spin (let [[p q] (await-all [a b])] (+ p q)))
              seen (atom [])
              u (v2/observe! c (fn [v _] (swap! seen conj v)))]
          (v2/write! y 5)
          (v2/write! x 10)
          (is (= [3 6 15] @seen))
          (u)
          (is (= 0 (:edges (census w)))))))))

(deftest blocked-debtor-does-not-deadlock
  ;; §4.5.6 (X#8): D waits on task K, which waits on deferred P; C delivers P
  ;; once X is 1 and then awaits D.
  (checked
    (let [w (vworld)]
      (binding [v2/*world* w]
        (let [x (v2/signal 0)
              p (v2/deferred)
              k (task (await p))
              dd (spin (let [v (iv/get-new (track x))] (if (zero? v) 0 (await k))))
              c (spin (let [v (iv/get-new (track x))]
                        (when (= v 1) (v2/deliver! p :go))
                        (await dd)))
              seen (atom [])
              u (v2/observe! c (fn [v _] (swap! seen conj v)))]
          (is (= [0] @seen))
          (v2/write! x 1)
          (is (= [0 :go] @seen))
          (u))))))

(deftest dependency-cycle-is-refused
  ;; I12: an await that would close a computation cycle fails with ::cycle.
  (checked
    (let [w (vworld)]
      (binding [v2/*world* w]
        (let [x (v2/signal 0)
              cell (atom nil)
              a (spin (if (pos? (iv/get-new (track x)))
                        (try (await @cell) (catch Exception e (if (:spindel/cycle (ex-data e)) :cycle (throw e))))
                        :base))
              b (spin [:b (await a)])
              _ (reset! cell b)
              seen (atom [])
              u (v2/observe! b (fn [v _] (swap! seen conj v)))]
          (v2/write! x 1)
          (is (= [[:b :base] [:b :cycle]] @seen))
          (u))))))
