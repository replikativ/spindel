(ns org.replikativ.spindel.v2.mvcc-test
  "MVCC forks (v2-fork-memory-design): the owner changes its rows in place and
   saves versions only for forks that can still read them; forks read the
   state at their fork through their lineage."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [task await track]]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.host :as hs]))

(defn- row [h] (aget ^objects (.-cell ^org.replikativ.spindel.v2.core.Handle h) 0))

(defn- eventually [f]
  (loop [n 0]
    (cond (f) true
          (> n 50) false
          :else (do (System/gc) (Thread/sleep 20) (recur (inc n))))))

(deftest the-owner-keeps-its-rows-and-no-forward-map
  (let [w (v2/world)]
    (binding [v2/*world* w]
      (let [x (v2/signal 0)
            r (row x)
            forks (vec (repeatedly 10 #(v2/fork! w)))]
        (dotimes [i 10] (v2/write! x i))
        (is (identical? r (row x)) "the handle still names the same row")
        (is (empty? (aget ^objects w rw/W-FWD)) "a root world forwards nothing")
        (is (= 9 (v2/value x)))
        (is (every? #(zero? (v2/value (v2/in-world % x))) forks) "each fork sees the state at its fork")
        (run! v2/release-world! forks)))
    (v2/release-world! w)))

(defn- fork-write-release
  "Forks w, writes x (saving its old state for the fork), releases the fork;
   returns a weak reference to it."
  [w x v]
  (let [c (v2/fork! w)]
    (v2/write! x v)
    (v2/release-world! c)
    (hs/weak c)))

(deftest versions-are-kept-only-while-a-fork-can-read-them
  (let [w (v2/world)]
    (binding [v2/*world* w]
      (let [x (v2/signal 0)
            r (row x)
            wc (fork-write-release w x 1)]
        (is (= 1 (count (rw/versions r))) "a fork that can read x: its old state is saved")
        (is (eventually #(nil? (hs/deref-weak wc))) "the released fork is collected")
        (System/gc)
        (let [d (v2/fork! w)]
          (v2/write! x 2)
          (is (= 1 (count (rw/versions r))) "the collected fork's version is pruned, d's is saved")
          (is (= 1 (v2/value (v2/in-world d x))))
          (v2/release-world! d))))
    (v2/release-world! w)))

(deftest a-grandchild-reads-through-a-released-intermediate-fork
  (let [w (v2/world)]
    (binding [v2/*world* w]
      (let [x (v2/signal :root)
            y (v2/signal :root)
            b (v2/fork! w)
            _ (v2/write! (v2/in-world b y) :b)        ; b's own copy of y
            c (v2/fork! b {:owner w})            ; c outlives b
            cx (v2/in-world c x) cy (v2/in-world c y)]
        (v2/release-world! b)
        (System/gc)
        (v2/write! x :later)
        (v2/write! y :later)
        (is (= :root (v2/value cx)) "w's row at b's fork")
        (is (= :b (v2/value cy)) "b's copy at c's fork")
        (is (= :later (v2/value x)))
        (v2/release-world! c)))
    (v2/release-world! w)))

(deftest an-instance-reads-its-basis-after-the-owner-moves-on
  (let [w (v2/world) pubs (atom [])]
    (v2/install-handlers! w {:s (fn [p] (swap! pubs conj p))})
    (binding [v2/*world* w]
      (let [x (v2/signal 1)
            t (task (let [v (v2/savepoint :s nil)] (+ v (iv/get-new (track x)))))]
        (Thread/sleep 50)
        (v2/write! x 10)                       ; the owner moves on after the savepoint
        (let [p (first @pubs)
              i (doto (v2/instantiate p) (v2/activate! 5))]
          (is (= 6 (v2/value (v2/in-world i t) 1000 ::timeout)) "the instance sees x at the savepoint")
          (v2/resume! p 5)
          (is (= 15 (v2/value t 1000 ::timeout)) "the owner sees its own write")
          (v2/release-world! i)
          (v2/dispose! p))))
    (v2/release-world! w)))

(deftest a-finished-fork-needs-no-versions
  (let [w (v2/world)]
    (binding [v2/*world* w]
      (let [x (v2/signal 0)
            r (row x)
            c (v2/fork! w)]
        (v2/release-world! c)
        (Thread/sleep 50)                       ; its cleanup is done
        (v2/write! x 1)
        (is (empty? (rw/versions r)) "a finished fork that nothing derived from ends at once")
        (let [d (v2/fork! w)
              e (v2/fork! d {:owner w})]        ; derived from d: d's token is shared
          (v2/release-world! d)
          (Thread/sleep 50)
          (v2/write! x 2)
          (is (= 1 (count (rw/versions r))) "a shared token lives as long as its descendants")
          (is (= 1 (v2/value (v2/in-world e x))))
          (v2/release-world! e))))
    (v2/release-world! w)))
