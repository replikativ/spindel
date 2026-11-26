(ns org.replikativ.spindel.v2.callback-budget-test
  "H2: host callbacks count against the turn budget. A source write queues
   its observers' callbacks directly, and a write from a callback runs in
   the held gate without starting a turn, so an observer that writes its
   own source again keeps a turn busy. The turn must still end after the
   budget and hand the rest to the drainer, dropping and reordering
   nothing. The loops here are finite, well above the budget, so a turn
   that never yields shows up as one turn doing all of it. A batch larger
   than the budget splits at a callback boundary: its rest runs in order,
   after the next turn's ingress. The time slice is checked between
   callbacks as between other units."
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing async]])
            [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.host :as hs]))

(def ^:private budget 16)
(def ^:private n 1000)

(defn- self-writer
  "An observer callback of `s` (a volatile, set after the source exists)
   that writes `(inc v)` back into it until `limit`, recording
   `[(turn) v]`."
  [s limit seen turn]
  (fn [v err?]
    (swap! seen conj [(turn) v])
    (when (and (not err?) (< v limit))
      (v2/write! @s (inc v)))))

#?(:clj
   (defn- manual-executor
     "An executor that keeps its runnables until the test runs them."
     []
     (let [q (java.util.concurrent.LinkedBlockingQueue.)]
       [(reify java.util.concurrent.Executor
          (execute [_ r] (.add q r)))
        q])))

#?(:clj
   (deftest a-self-writing-observer-yields-after-the-budget
     (let [[ex ^java.util.concurrent.LinkedBlockingQueue q] (manual-executor)
           w (v2/world {:budget budget :executor ex})
           lk (aget ^objects w rw/W-LOCK)
           turn (atom 0)
           held (atom true)
           seen (atom [])
           s (volatile! nil)
           cb (let [f (self-writer s n seen #(deref turn))]
                (fn [v err?]
                  (swap! held #(and % (hs/held? lk)))
                  (f v err?)))]
       (vreset! s (v2/signal w 0))
       ;; the registration delivers 0 at once; every callback writes the next value
       (v2/observe! @s cb)
       (testing "the caller's own turn"
         (is (<= (count @seen) budget)
             (str "the inline turn ran " (count @seen) " callbacks with a budget of " budget))
         (is (= 1 (.size q)) "work remains: the drainer is scheduled")
         (is (not (.isLocked ^java.util.concurrent.locks.ReentrantLock lk))
             "the gate is released while work remains"))
       ;; the drainer's turns, one runnable each
       (loop [k 0]
         (when-let [r (.poll q)]
           (when (< k (* 2 n))
             (swap! turn inc)
             (.run ^Runnable r)
             (recur (inc k)))))
       (testing "every turn stays within the budget, and nothing is dropped or reordered"
         (is (= (range (inc n)) (map second @seen)))
         (is (every? #(<= % budget) (vals (frequencies (map first @seen))))
             (str "callbacks per turn: " (sort-by key (frequencies (map first @seen)))))
         (is (<= (quot (+ n budget) budget) (inc @turn))
             "the n + 1 callbacks took at least ceil((n + 1) / budget) turns")
         (is (true? @held) "each callback ran inside the gate")
         (is (zero? (.size q)) "no work is left"))
       (v2/release-world! w)
       (loop [] (when-let [r (.poll q)] (.run ^Runnable r) (recur))))))

#?(:clj
   (deftest a-batch-splits-at-a-callback-boundary-when-the-budget-runs-out
     ;; One write queues a batch of budget + 4 callbacks. The caller's turn
     ;; runs the first `budget` of them; the rest stay queued, in order,
     ;; ahead of later callbacks. The next turn takes its ingress first, so an
     ;; item queued meanwhile (here from the batch's first callback, as a DOM
     ;; flush would be) commits at the split point, before the batch's rest.
     (let [[ex ^java.util.concurrent.LinkedBlockingQueue q] (manual-executor)
           w (v2/world {:budget budget :executor ex})
           log (atom [])
           s (v2/signal w 0)
           k (+ budget 4)
           flush! #(v2/no-inline (v2/host! w (fn [] (swap! log conj :flush))))]
       (dotimes [i k]
         (v2/observe! s (fn [v _]
                          (when (= 1 v)
                            (swap! log conj i)
                            (when (zero? i) @(future (flush!)))))))
       (v2/write! s 1)
       (is (= (range budget) @log) "the caller's turn ran a budget's worth of the batch")
       (is (= 1 (.size q)) "the rest is handed to the drainer")
       (loop [] (when-let [r (.poll q)] (.run ^Runnable r) (recur)))
       (is (= (concat (range budget) [:flush] (range budget k)) @log)
           "the queued item commits at the split; the batch's rest follows in order")
       (v2/release-world! w)
       (loop [] (when-let [r (.poll q)] (.run ^Runnable r) (recur))))))

(defn- busy-ms!
  "Keeps the thread busy for `ms` milliseconds of the turn clock."
  [ms]
  (let [t (hs/now) d (hs/ms->ticks ms)]
    (while (< (- (hs/now) t) d))))

(defn- slow-observers!
  "`k` observers of `s`, each recording its index on value 1 and then
   taking 3 ms, three times a 1 ms time slice."
  [s k log]
  (dotimes [i k]
    (v2/observe! s (fn [v _]
                     (when (= 1 v)
                       (swap! log conj i)
                       (busy-ms! 3))))))

#?(:clj
   (deftest callbacks-count-toward-the-time-slice
     ;; A batch of slow callbacks within the budget: the time slice, checked
     ;; between callbacks as between other units, ends each turn after one.
     (let [[ex ^java.util.concurrent.LinkedBlockingQueue q] (manual-executor)
           w (v2/world {:budget 4096 :slice-ms 1 :executor ex})
           log (atom [])
           s (v2/signal w 0)
           k 5]
       (slow-observers! s k log)
       (v2/write! s 1)
       (is (= [0] @log) "the caller's turn ended after one slow callback")
       (is (= 1 (.size q)) "the rest is handed to the drainer")
       (let [per-turn (loop [acc []]
                        (if-let [r (.poll q)]
                          (let [before (count @log)]
                            (.run ^Runnable r)
                            (recur (conj acc (- (count @log) before))))
                          acc))]
         (is (= (range k) @log) "nothing dropped or reordered")
         (is (= (repeat (dec k) 1) per-turn) "one slow callback per drainer turn"))
       (v2/release-world! w)
       (loop [] (when-let [r (.poll q)] (.run ^Runnable r) (recur))))))

#?(:cljs
   (deftest callbacks-count-toward-the-time-slice
     (async done
            (let [w (v2/world {:budget 4096 :slice-ms 1})
                  log (atom [])
                  s (v2/signal w 0)
                  k 5
                  deadline (+ (hs/now) 5000)]
              (slow-observers! s k log)
              (v2/write! s 1)
              (is (= [0] @log) "the caller's turn ended after one slow callback")
              (letfn [(check []
                        (cond
                          (= k (count @log))
                          (do (is (= (range k) @log) "the drainer delivered the rest, in order")
                              (v2/release-world! w)
                              (done))
                          (< deadline (hs/now))
                          (do (is false (str "only " (count @log) " callbacks before the deadline"))
                              (v2/release-world! w)
                              (done))
                          :else (js/setTimeout check 1)))]
                (check))))))

#?(:clj
   (deftest a-callback-that-writes-once-is-delivered-in-the-same-turn
     (let [[ex ^java.util.concurrent.LinkedBlockingQueue q] (manual-executor)
           w (v2/world {:budget budget :slice-ms nil :executor ex})
           seen (atom [])
           s (volatile! nil)]
       (vreset! s (v2/signal w 0))
       (v2/observe! @s (self-writer s 1 seen (constantly 0)))
       (is (= [[0 0] [0 1]] @seen) "the write from the callback is observed")
       (v2/write! @s 5)
       (is (= [[0 0] [0 1] [0 5]] @seen))
       (is (zero? (.size q)) "nothing was handed off")
       (v2/release-world! w)
       (loop [] (when-let [r (.poll q)] (.run ^Runnable r) (recur))))))

#?(:cljs
   (deftest a-self-writing-observer-yields-after-the-budget
     (async done
            (let [w (v2/world {:budget budget})
                  seen (atom [])
                  s (volatile! nil)
                  deadline (+ (hs/now-ms) 5000)]
              (vreset! s (v2/signal w 0))
              (v2/observe! @s (self-writer s n seen (constantly 0)))
              (is (<= (count @seen) budget)
                  (str "the inline turn ran " (count @seen) " callbacks with a budget of " budget))
              (letfn [(check []
                        (cond
                          (= (inc n) (count @seen))
                          (do (is (= (range (inc n)) (map second @seen))
                                  "the drainer delivered the rest, in order")
                              (v2/release-world! w)
                              (done))
                          (< deadline (hs/now-ms))
                          (do (is false (str "only " (count @seen) " callbacks before the deadline"))
                              (v2/release-world! w)
                              (done))
                          :else (js/setTimeout check 1)))]
                (check))))))

#?(:cljs
   (deftest a-callback-that-writes-once-is-delivered-in-the-same-turn
     (let [w (v2/world {:budget budget :slice-ms nil})
           seen (atom [])
           s (volatile! nil)]
       (vreset! s (v2/signal w 0))
       (v2/observe! @s (self-writer s 1 seen (constantly 0)))
       (is (= [[0 0] [0 1]] @seen) "the write from the callback is observed")
       (v2/write! @s 5)
       (is (= [[0 0] [0 1] [0 5]] @seen))
       (v2/release-world! w))))
