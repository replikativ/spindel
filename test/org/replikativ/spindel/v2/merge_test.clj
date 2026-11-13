(ns org.replikativ.spindel.v2.merge-test
  "L12 `merge!`: a mergeable fork's writes to inherited signals are adopted by its parent as host
  writes, all or none; the child is released by a merge and untouched by a refusal."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin track]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.verify :as verify]
            [org.replikativ.spindel.incremental.interval :as iv]))

(def ^:dynamic *divergences* nil)

(defn- vworld [] (v2/world {:verify? true :hook (verify/checking-hook *divergences*)}))

(defmacro checked [& body]
  `(binding [*divergences* (atom [])]
     ~@body
     (is (empty? @*divergences*) (str "Rule R divergences: " (vec (take 3 @*divergences*))))))

(defn- wait-until [f] (loop [n 200] (or (f) (when (pos? n) (Thread/sleep 5) (recur (dec n))))))
(defn- released? [w] (aget ^objects w rw/W-RELEASED))

(deftest merge-adopts-the-childs-writes
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [s (v2/signal 1) t (v2/signal 2) u (v2/signal 3)
             c (spin (+ (iv/get-new (track s)) (iv/get-new (track t))))
             seen (atom [])
             stop (v2/observe! c (fn [v _] (swap! seen conj v)))
             child (v2/fork! w {:mergeable? true})
             made (binding [v2/*world* child] (v2/signal 100))]
         (v2/write! (v2/in-world child s) 10)
         (v2/write! (v2/in-world child s) 11)
         (is (= 3 (v2/value (v2/in-world child u))) "read in the child, not written")
         (v2/write! made 101)
         (v2/write! u 30)
         (is (= 1 (v2/value s)) "isolated before the merge")
         (is (true? (v2/merge! w child)))
         (is (= [11 2 30] (mapv v2/value [s t u])) "the child's last value of s; t and the parent's own write to u are kept")
         (is (= 13 (v2/value c 1000 ::timeout)) "dependents recompute")
         ;; the child inherited this observe edge too: its release reports to the same callback
         (is (= 13 (last (filter number? @seen))) "and observers are told")
         (is (= 2 (count (filter #(= :write (first (:item %))) (verify/log w))))
             "one host write in the parent, after its own")
         (is (wait-until #(released? child)) "the merged child is released")
         (is (false? (v2/merge! w child)) "at most once")
         (stop))))))

(deftest a-conflict-refuses-the-whole-merge
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [s (v2/signal 1) t (v2/signal 2)
             child (v2/fork! w {:mergeable? true})]
         (v2/write! (v2/in-world child s) 10)
         (v2/write! (v2/in-world child t) 20)
         (v2/write! t 21)
         (is (false? (v2/merge! w child)) "the parent wrote t since the fork")
         (is (= [1 21] (mapv v2/value [s t])) "nothing is adopted, not even s")
         (is (not (released? child)))
         (is (= [10 20] (mapv #(v2/value (v2/in-world child %)) [s t])) "the child is untouched and usable"))))))

(deftest only-mergeable-forks-of-the-parent
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [s (v2/signal 1)
             plain (v2/fork! w)
             child (v2/fork! w {:mergeable? true})
             grand (v2/fork! child {:mergeable? true})]
         (v2/write! (v2/in-world plain s) 5)
         (v2/write! (v2/in-world grand s) 7)
         (is (false? (v2/merge! w plain)) "not created mergeable")
         (is (false? (v2/merge! w grand)) "its parent is the child")
         (is (false? (v2/merge! w w)))
         (is (= 1 (v2/value s)))
         (is (true? (v2/merge! child grand)) "a fork merges into its own parent")
         (is (= 7 (v2/value (v2/in-world child s))))
         (is (true? (v2/merge! w child)) "and the result merges on")
         (is (= 7 (v2/value s))))))))

(deftest a-changed-source-that-is-not-a-signal-refuses
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [s (v2/signal 1) d (v2/deferred)
             child (v2/fork! w {:mergeable? true})]
         (v2/write! (v2/in-world child s) 10)
         (v2/deliver! (v2/in-world child d) :x)
         (is (false? (v2/merge! w child)) "a delivery is not a write")
         (is (= 1 (v2/value s))))))))

(deftest a-merge-with-no-writes-releases-the-child
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [s (v2/signal 1)
             child (v2/fork! w {:mergeable? true})]
         (is (= 1 (v2/value (v2/in-world child s))))
         (is (true? (v2/merge! w child)))
         (is (= 1 (v2/value s)))
         (is (wait-until #(released? child))))))))
