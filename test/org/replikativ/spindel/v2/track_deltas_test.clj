(ns org.replikativ.spindel.v2.track-deltas-test
  "§4.4: track delivers the composed deltas of a signal since the site's
   baseline, or nil when they are unknown (a plain write, truncation)."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin track]]
            [org.replikativ.spindel.v2.port.helpers :refer [checked-fixture hot-spin]]))

(use-fixtures :each checked-fixture)

(defn- tracker [s] (hot-spin (let [i (track s)] [(:old i) (:new i) (:deltas i)])))

(deftest swap-records-deltas-and-stores-the-plain-value
  (let [s (v2/signal []) t (tracker s)]
    (is (= [nil [] nil] @t) "a first track has no deltas")
    (swap! s conj :a)
    (is (= [[] [:a] [{:delta :add :path [0] :value :a}]] @t))
    (is (= [:a] @s))
    (is (= (hash [:a]) (hash @s)) "the stored value is a plain vector")
    (is (= clojure.lang.PersistentVector (type @s)))))

(defn- observed
  "An observed computation of the deltas `s` delivers; returns [last stop]."
  [s]
  (let [res (atom ::none)
        c (spin (:deltas (track s)))]
    [res (v2/observe! c (fn [v _] (reset! res v)))]))

(deftest deltas-compose-across-writes-between-deliveries
  ;; two writes in one host item: the computation runs once, after both
  (let [s (v2/signal {}) [res stop] (observed s)]
    (try
      (v2/host-call! v2/*world* #(do (swap! s assoc :x 1) (swap! s assoc :y 2)))
      (is (= [{:delta :add :path [:x] :value 1} {:delta :add :path [:y] :value 2}] @res))
      (finally (stop)))))

(deftest an-unobserved-computation-has-no-baseline
  ;; lazy invalidation: no armed edge between host reads, so each read is a
  ;; first track (old nil, deltas nil)
  (let [s (v2/signal []) c (spin (let [i (track s)] [(:old i) (:deltas i)]))]
    (is (= [nil nil] @c))
    (swap! s conj :a)
    (is (= [nil nil] @c))))

(deftest a-plain-write-makes-the-deltas-unknown
  (let [s (v2/signal []) t (tracker s)]
    @t
    (reset! s [:z])
    (is (= [[] [:z] nil] @t))
    (swap! s conj :b)
    (is (= [[:z] [:z :b] [{:delta :add :path [1] :value :b}]] @t) "a later swap is known again")))

(deftest truncation-beyond-the-bound-gives-nil
  (let [s (v2/signal []) [res stop] (observed s)]
    (try
      (v2/host-call! v2/*world* #(dotimes [i 40] (swap! s conj i)))
      (is (nil? @res) "40 writes since the baseline exceed the bound")
      (swap! s conj :next)
      (is (= [{:delta :add :path [40] :value :next}] @res) "the next delivery is known again")
      (finally (stop)))))

(deftest scalars-and-compare-and-set-carry-no-deltas
  (let [s (v2/signal 0) t (tracker s)]
    @t
    (swap! s inc)
    (is (= [0 1 nil] @t))
    (is (compare-and-set! s 1 2))
    (is (= [1 2 nil] @t))))
