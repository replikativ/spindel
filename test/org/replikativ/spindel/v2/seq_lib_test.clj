(ns org.replikativ.spindel.v2.seq-lib-test
  "C0 library: state-passing sequence combinators and pub/sub over streams."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [task await]]
            [org.replikativ.spindel.v2.seq :as as]
            [org.replikativ.spindel.v2.pubsub :as ps]))

(defmacro in-world [& body]
  `(let [w# (v2/world)]
     (try (binding [v2/*world* w#] ~@body)
          (finally (v2/release-world! w#)))))

(defn- all [src] (v2/value (as/into [] src) 3000 ::timeout))

(deftest pull-combinators
  (in-world
   (let [xs (as/from-coll (range 10))]
     (is (= (range 10) (all xs)))
     (is (= [0 2 4 6 8] (all (as/afilter even? xs))))
     (is (= [1 2 3] (all (as/take 3 (as/amap inc xs)))))
     (is (= [7 8 9] (all (as/drop 7 xs))))
     (is (= [0 1 2] (all (as/take-while #(< % 3) xs))))
     (is (= [[0 1 2 3] [4 5 6 7] [8 9]] (all (as/partition-all 4 xs))))
     (is (= [1 2 3 1] (all (as/dedupe (as/from-coll [1 1 2 3 3 3 1])))))
     (is (= [0 1 3 6] (all (as/take 4 (as/scan + 0 xs)))))
     (is (= [:a :a :b :b] (all (as/amapcat #(repeat 2 %) (as/from-coll [:a :b])))))
     (is (= [:x 1 2] (all (as/concat (as/from-coll [:x]) (as/from-coll []) (as/from-coll [1 2])))))
     (is (= ["0" "2"] (all (as/akeep #(when (even? %) (str %)) (as/take 3 xs)))))
     (is (= 45 (v2/value (as/reduce + 0 xs) 3000 ::timeout)))
     (is (= (range 10) (all xs)) "the source was never consumed"))))

(deftest merge-by-readiness
  (in-world
   (let [a (v2/stream) b (v2/stream)
         m (as/merge (v2/position a) (v2/position b))
         r (as/into [] m)]
     (v2/append! a 1) (v2/append! b :x) (v2/append! a 2)
     (v2/close! a) (v2/append! b :y) (v2/close! b)
     (let [res (v2/value r 3000 ::timeout)]
       (is (= #{1 2 :x :y} (set res)))
       (is (= [1 2] (filter number? res)) "per-source order is kept")))))

(deftest latest-skips-to-the-newest
  (in-world
   (let [s (v2/stream) p (v2/position s)]
     (dotimes [i 5] (v2/append! s i))
     (let [[v nx] (v2/value (as/latest p) 3000 ::timeout)]
       (is (= 4 v))
       (v2/append! s 5) (v2/append! s 6)
       (is (= 6 (first (v2/value nx 3000 ::timeout)))))
     (is (= [4 5 6] (first (v2/value (as/take-latest 3 p) 3000 ::timeout)))))))

(deftest pub-routes-by-topic
  (in-world
   (let [bus (v2/stream)
         by-type (ps/pub (v2/position bus) :type)
         by-to (ps/pub (v2/position bus) :to {:multi true})
         msgs (v2/value (ps/sub by-type :msg) 3000 ::timeout)
         alice (v2/value (ps/sub by-to :alice) 3000 ::timeout)
         bob (v2/value (ps/sub by-to :bob) 3000 ::timeout)
         ra (as/into [] alice) rb (as/into [] bob) rm (as/into [] (as/amap :n msgs))]
     (v2/append! bus {:type :msg :to #{:alice} :n 1})
     (v2/append! bus {:type :tick :to #{} :n 2})
     (v2/append! bus {:type :msg :to #{:alice :bob} :n 3})
     (v2/close! bus)
     (is (= [1 3] (v2/value rm 3000 ::timeout)))
     (is (= [1 3] (mapv :n (v2/value ra 3000 ::timeout))))
     (is (= [3] (mapv :n (v2/value rb 3000 ::timeout))))
     (is (nil? (v2/value (v2/value (ps/sub by-type :late) 3000 ::timeout) 3000 ::timeout))
         "a topic subscribed after the source ended is ended"))))

(deftest a-subscriber-task-in-a-body
  (in-world
   (let [bus (v2/stream)
         p (ps/pub (v2/position bus) first)
         got (v2/deferred)
         subscriber (task (let [pos (await (ps/sub p :a))]
                            (v2/deliver! got :subscribed)
                            (loop [pos pos acc []]
                              (if-let [[v nx] (await pos)] (recur nx (conj acc (second v))) acc))))]
     (is (= :subscribed (v2/value got 3000 ::timeout)))
     (v2/append! bus [:a 1]) (v2/append! bus [:b 2]) (v2/append! bus [:a 3])
     (v2/close! bus)
     (is (= [1 3] (v2/value subscriber 3000 ::timeout))))))

;; ---------------------------------------------------------------------------
;; Review findings (c0-review-sol.md)

(defn- weak-row [h] (java.lang.ref.WeakReference. (aget ^objects (.-cell ^org.replikativ.spindel.v2.core.Handle h) 0)))

(defn- collected? [^java.lang.ref.WeakReference r]
  (loop [n 0] (cond (nil? (.get r)) true (> n 50) false :else (do (System/gc) (Thread/sleep 10) (recur (inc n))))))

(deftest a-sub-before-the-router-starts-is-served
  (in-world
   (let [s (v2/stream)
         t (task (let [p (ps/pub (v2/position s) identity)] (await (ps/sub p :a))))]
     (is (v2/handle? (v2/value t 2000 ::timeout))))))

(deftest a-long-running-task-does-not-retain-the-head-it-captured
  (in-world
   (let [s (v2/stream)
         head (v2/position s)
         first-row (weak-row head)
         seen (atom 0)
         reader (task (loop [p head] (when-let [[_ nx] (await p)] (swap! seen inc) (recur nx))))]
     (dotimes [i 100] (v2/append! s i))
     (is (= 100 @seen))
     (is (collected? first-row) "the task's captures go once its body has started")
     (v2/close! s)
     (v2/value reader 2000 ::timeout))))

(deftest the-pub-router-keeps-only-tails
  (in-world
   (let [s (v2/stream)
         head (v2/position s)
         first-row (weak-row head)
         p (ps/pub head :t)
         a (v2/value (ps/sub p :a) 2000 ::timeout)
         r (as/into [] a)]
     (dotimes [i 100] (v2/append! s {:t :a :i i}))
     (v2/close! s)
     (is (= 100 (count (v2/value r 2000 ::timeout))))
     (is (collected? first-row) "the router does not hold the source history"))))

(deftest markers-never-collide-with-elements
  (in-world
   (is (= [[:org.replikativ.spindel.v2.seq/end :ok] 1]
          (all (as/merge (as/from-coll [[:org.replikativ.spindel.v2.seq/end :ok] 1])))))
   (is (= [:org.replikativ.spindel.v2.seq/none 1]
          (all (as/dedupe (as/from-coll [:org.replikativ.spindel.v2.seq/none 1])))))
   (let [bus (v2/stream)
         p (ps/pub (v2/position bus) (constantly :all))
         r (as/into [] (v2/value (ps/sub p :all) 2000 ::timeout))]
     (v2/append! bus :org.replikativ.spindel.v2.pubsub/end)
     (v2/append! bus :after)
     (v2/close! bus)
     (is (= [:org.replikativ.spindel.v2.pubsub/end :after] (v2/value r 2000 ::timeout))))))

(deftest sliding-reads-keep-their-values-before-a-failure
  (in-world
   (let [s (v2/stream) pos (v2/position s)]
     (v2/append! s 1) (v2/append! s 2)
     (v2/close! s (ex-info "bad" {}))
     (let [[v nx] (v2/value (as/latest pos) 2000 ::timeout)]
       (is (= 2 v))
       (is (thrown-with-msg? Exception #"bad" (v2/value nx 2000 ::timeout)) "the error is the next read"))
     (is (= [1 2] (first (v2/value (as/take-latest 2 pos) 2000 ::timeout)))))))
