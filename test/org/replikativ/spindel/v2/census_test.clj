(ns org.replikativ.spindel.v2.census-test
  "Census gate (§0): retained rows stay bounded under churn, including the
   pattern that leaked in the old engine (a long-lived body awaiting a fresh
   child per iteration, the dvergr :await-conts growth)."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await take!]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.combinators :as comb]
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

(deftest release-world-reclaims-everything
  (let [w (v2/world {:verify? true})
        released (atom [])]
    (binding [v2/*world* w]
      (let [x (v2/signal 0)
            c (spin (* 2 (iv/get-new (track x))))
            u (v2/observe! c (fn [v err?] (when err? (swap! released conj v))))
            d (v2/deferred)
            t (task (try (await d) (finally nil)))
            left (v2/release-world! w)]
        (is (= 1 (count @released)) "the observer was told")
        (is (:spindel/released (ex-data (first @released))))
        (is (thrown? Exception (v2/write! x 1)) "host operations fail after release")
        (System/gc)
        (is (<= (left) 4) (str "rows left: " (left) " (root scope and handle-held rows)"))))))

(deftest task-loop-with-deferreds-and-timers
  ;; §0 census: a dvergr-style loop creating a fresh computation, a deferred
  ;; and a timer per iteration stays at a constant row count.
  (let [w (v2/world {:verify? true})]
    (binding [v2/*world* w]
      (let [mb (v2/mailbox)
            loop-task (task (loop [acc 0]
                              (let [m (take! mb)]
                                (if (= m :stop)
                                  acc
                                  (let [d (v2/deferred)
                                        k (task (v2/sleep 0) (v2/deliver! d m))
                                        c (spin (* 2 m))]
                                    (recur (+ acc (await c) (await d))))))))]
        (dotimes [i 20] (v2/post! mb i))
        (Thread/sleep 100)
        (let [before (total (census w))]
          (dotimes [i 300] (v2/post! mb i))
          ;; settles once the in-flight iterations finish; a leak never does
          (let [after (loop [n 0]
                        (let [t (total (census w))]
                          (if (or (<= t (+ before 3)) (> n 100)) t (do (Thread/sleep 50) (recur (inc n))))))]
            (is (<= after (+ before 3)) (str "rows grew from " before " to " after))))
        (v2/post! mb :stop)
        (is (number? (v2/value loop-task 5000 ::timeout)))))))

(deftest opaque-collections-preserve-equality-without-retaining-handles
  (let [w (v2/world {:verify? true})
        refs (v2/call-in! w
                          (fn []
                            (let [h (v2/deferred w)
                                  intern #(v2/intern-opaque! w %)
                                  a (intern {:nested [#{h} (list h)]})]
                              (is (= a (intern {:nested (list #{h} [h])})))
                              (is (not= (intern [h]) (intern #{h})))
                              (is (not= (intern {h :value}) (intern {:value h})))
                              (is (= (intern [:metadata])
                                     (intern (with-meta [:metadata] {:handle h}))))
                              (is (= 0 (intern nil)))
                              (is (= 1 (intern :org.replikativ.spindel.v2.core/cancelled)))
                              (is (= 2 (intern :org.replikativ.spindel.v2.core/closed)))
                              [(java.lang.ref.WeakReference. h)])))]
    (verify/gc-settle! w)
    (is (every? #(nil? (.get ^java.lang.ref.WeakReference %)) refs))
    (is (= {rw/T-SCOPE 1} (census w)))))

(deftest combinator-captures-are-reclaimed
  (doseq [kind [:parallel :race :timeout]]
    (testing (name kind)
      (let [w (v2/world {:verify? true})]
        (binding [v2/*world* w]
          (dotimes [i 30]
            (case kind
              :parallel (v2/value (comb/parallel (spin i) (spin :b)) 1000 ::timeout)
              :race (v2/value (comb/race (spin i) (spin :b)) 1000 ::timeout)
              :timeout (v2/value (comb/timeout (comb/never) 0 :fallback) 1000 ::timeout))))
        (is (= {rw/T-SCOPE 1} (census w)))))))

(deftest refused-payloads-are-interned-and-reclaimed
  (let [w (v2/world {:verify? true})
        d (v2/deferred w)
        ref (v2/call-in! w
                         (fn []
                           (let [h (v2/deferred w)]
                             (v2/deliver! d :first)
                             (v2/deliver! d {:nested [h]})
                             (java.lang.ref.WeakReference. h))))]
    (let [entry (last (filter #(false? (:accepted %)) (verify/log w)))]
      (is (= :deliver (first (:item entry))))
      (is (true? (integer? (last (:item entry))))))
    (verify/gc-settle! w)
    (is (nil? (.get ^java.lang.ref.WeakReference ref)))
    (is (= :first (v2/value d)))))
