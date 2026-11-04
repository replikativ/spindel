(ns org.replikativ.spindel.v2.fork-test
  "M5 stage 1b: copy-on-write forks (§8.1, design v3)."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await]]
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

(defn- wait-until [f]
  (loop [n 0] (cond (f) true (> n 500) false :else (do (Thread/sleep 5) (recur (inc n))))))

(deftest fork-isolation
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [x (v2/signal 1)
             c (spin (* 10 (iv/get-new (track x))))
             seen-p (atom [])
             _ (v2/observe! c (fn [v _] (swap! seen-p conj v)))
             child (v2/fork! w)
             cx (v2/in-world child x)
             cc (v2/in-world child c)
             seen-c (atom [])
             _ (v2/observe! cc (fn [v _] (swap! seen-c conj v)))]
         (is (= [10] @seen-p))
         (is (= [10] @seen-c) "the child sees the fork-time state")
         (v2/write! cx 2)
         (is (= [10 20] @seen-c) "the child recomputes on its own write")
         (is (= [10] @seen-p) "the parent's observer is not called by the child (Z#45)")
         (is (= 10 (v2/value c)) "the parent is unchanged")
         (v2/write! x 3)
         (is (= [10 30] @seen-p))
         (is (= 20 (v2/value cc)) "the child is unchanged by the parent's write"))))))

(deftest repeated-forks
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [x (v2/signal 1)
             c (spin (+ 100 (iv/get-new (track x))))
             _ (v2/observe! c (fn [_ _]))
             a (v2/fork! w)
             _ (v2/write! (v2/in-world a x) 2)
             b (v2/fork! a)
             _ (v2/write! (v2/in-world b x) 3)]
         (is (= 101 (v2/value c)))
         (is (= 102 (v2/value (v2/in-world a c))))
         (is (= 103 (v2/value (v2/in-world b c))))
         (v2/write! (v2/in-world a x) 4)
         (is (= 104 (v2/value (v2/in-world a c))))
         (is (= 103 (v2/value (v2/in-world b c))) "a grandchild is isolated from its parent's later writes"))))))

(deftest parked-task-forks
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [d (v2/deferred)
             t (task (* 2 (await d)))
             child (v2/fork! w)]
         (v2/deliver! (v2/in-world child d) 21)
         (is (= 42 (v2/value (v2/in-world child t) 1000 ::timeout)) "the child's copy of the task resumes")
         (is (= ::pending (v2/value t 50 ::pending)) "the parent's task still waits")
         (v2/deliver! d 5)
         (is (= 10 (v2/value t 1000 ::timeout))))))))

(deftest fork-churn-leaves-the-parent-alone
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [x (v2/signal 0)
             c (spin (iv/get-new (track x)))
             _ (v2/observe! c (fn [_ _]))
             before (count (vals (aget ^objects w rw/W-REG)))]
         (dotimes [i 200]
           (let [f (v2/fork! w)]
             (v2/write! (v2/in-world f x) i)
             (assert (= i (v2/value (v2/in-world f c))))))
         (is (= before (count (vals (aget ^objects w rw/W-REG)))) "forks never add rows to the parent")
         (is (= 0 (v2/value c))))))))

(deftest fork-effect-in-a-task
  ;; D3/Q4: the parent continues with [:parent child]; the child's copy of
  ;; the run resumes at the effect with [:child nil].
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [x (v2/signal 1)
             out (promise)
             gate (v2/deferred)
             t (task (let [[side child] (v2/fork)]
                       (v2/write! x (if (= side :child) 20 10))
                       (when (= side :parent) (deliver out child))
                       (when (= side :parent) (await gate))
                       side))
             child (deref out 1000 nil)]
         (is (some? child))
         (is (= 10 (v2/value x)) "the parent wrote 10")
         (is (= :child (v2/value (v2/in-world child t) 1000 ::timeout))
             "the child's copy resumed with the child-side result")
         (is (= 20 (v2/value (v2/in-world child x))) "and wrote in the child")
         (v2/deliver! gate :done)
         (is (= :parent (v2/value t 1000 ::timeout)))
          ;; F2: the fork is owned by the task's run scope, released when it retires
         (is (wait-until #(aget ^objects child rw/W-RELEASED)) "the task's end releases its fork"))))))

(deftest dormant-resources-in-a-fork
  ;; §8.1: a timer re-arms in the fork; an offload fails with err ::forked.
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [release (promise)
             sleeper (task (v2/sleep 50) :woke)
             waiter (task (try (v2/offload #(deref release 5000 :late))
                               (catch Exception e (if (:spindel/forked (ex-data e)) :forked (throw e)))))
             child (v2/fork! w)]
         (is (= :woke (v2/value (v2/in-world child sleeper) 2000 ::timeout)) "the timer re-armed in the child")
         (is (= :forked (v2/value (v2/in-world child waiter) 2000 ::timeout)) "the offload has no counterpart in the child")
         (is (= :woke (v2/value sleeper 2000 ::timeout)))
         (deliver release :done)
         (is (= :done (v2/value waiter 2000 ::timeout)) "the parent's offload is unaffected"))))))

(deftest idle-validity-reads-the-child-copy
  ;; reactivation compares each validity version against this world's copy of
  ;; the debtor, not the frozen basis row
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [x (v2/signal 1)
             c (spin (* 10 (iv/get-new (track x))))
             unobserve (v2/observe! c (fn [_ _]))]
         (unobserve)                                   ; c is idle with validity [x 1]
         (let [child (v2/fork! w)
               cx (v2/in-world child x)
               cc (v2/in-world child c)
               seen (atom [])]
           (v2/write! cx 2)
           (v2/observe! cc (fn [v _] (swap! seen conj v)))
           (is (= [20] @seen) "the child's write invalidates the idle result")
           (is (= 10 (v2/value c)) "the parent keeps its own")))))))
