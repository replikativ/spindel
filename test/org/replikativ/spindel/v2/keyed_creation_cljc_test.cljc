(ns org.replikativ.spindel.v2.keyed-creation-cljc-test
  "E1 keyed creation on both platforms (phase-d design §1.13: K1-K3, K5, K6,
   K10, K18): keys compare by value, so freshly allocated equal keys find
   their predecessor on CLJS too."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await await-all]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.incremental.interval :as iv]
            #?(:clj [org.replikativ.spindel.v2.port.helpers :refer [checked-fixture]])))

(use-fixtures :each
  #?(:clj checked-fixture
     :cljs (fn [f] (let [w (v2/world)]
                     (try (binding [v2/*world* w] (f)) (finally (v2/release-world! w)))))))

(v2/defeffect frame-here [_ ctx] [:value [(:frame ctx) (:key ctx)]])

(defn- now
  "The settled value of `h`. CLJS inline worlds settle synchronously."
  [h]
  #?(:clj (v2/value h 2000 ::timeout)
     :cljs (let [a (atom ::pending)]
             (v2/value-async h (fn [v _err?] (reset! a v)))
             @a)))

(defn- rid [x] (aget ^objects (v2/row-of x) rw/ID))

(defn- keyed-parent
  "Tracks `items` and creates one child computation per item under the key
   `(key-of item)`; records each run's [item id] pairs in `ids` and each
   child run in `runs`."
  [items key-of runs ids]
  (spin (let [xs (iv/get-new (track items))
              hs (loop [xs xs acc []]
                   (if-let [x (first xs)]
                     (recur (rest xs)
                            (conj acc (v2/with-key (key-of x) (spin (swap! runs update x (fnil inc 0)) (* 10 x)))))
                     acc))]
          (swap! ids conj (into {} (map (fn [x hd] [x (rid hd)]) xs hs)))
          (await-all hs))))

(deftest k1-reorder
  (let [items (v2/signal [1 2 3 4 5])
        runs (atom {}) ids (atom [])
        c (keyed-parent items identity runs ids)
        u (v2/observe! c (fn [_ _]))]
    (is (= [10 20 30 40 50] (now c)))
    (v2/write! items [5 4 3 2 1])
    (is (= [50 40 30 20 10] (now c)))
    (is (= {1 1 2 1 3 1 4 1 5 1} @runs) "no child reruns")
    (is (apply = @ids) "every key keeps its computation")
    (u)))

(deftest k2-insert
  (let [items (v2/signal [1 2 4 5])
        runs (atom {}) ids (atom [])
        c (keyed-parent items identity runs ids)
        u (v2/observe! c (fn [_ _]))]
    (is (= [10 20 40 50] (now c)))
    (v2/write! items [1 2 3 4 5])
    (is (= [10 20 30 40 50] (now c)))
    (is (= {1 1 2 1 3 1 4 1 5 1} @runs) "only the new child runs")
    (let [[a b] @ids] (is (= a (dissoc b 3))))
    (u)))

(deftest k3-remove-cancels-the-keyed-task
  (let [items (v2/signal [1 2 3])
        never (v2/deferred)
        log (atom [])
        c (spin (let [xs (iv/get-new (track items))
                      hs (loop [xs xs acc []]
                           (if-let [x (first xs)]
                             (recur (rest xs)
                                    (conj acc (v2/with-key x
                                                (task (try (await never) (finally (swap! log conj x)))))))
                             acc))]
                  (count hs)))
        u (v2/observe! c (fn [_ _]))]
    (is (= 3 (now c)))
    (v2/write! items [1 3])
    (is (= 2 (now c)))
    #?(:clj (loop [i 0] (when (and (empty? @log) (< i 400)) (Thread/sleep 5) (recur (inc i)))))
    (is (= [2] @log) "the removed key's task is cancelled at the parent's completion")
    (u)))

(deftest k5-duplicates
  (let [items (v2/signal [[:a 1] [:a 2]])
        runs (atom []) ids (atom [])
        c (spin (let [xs (iv/get-new (track items))
                      hs (loop [xs xs acc []]
                           (if-let [[k v] (first xs)]
                             (recur (rest xs) (conj acc (v2/with-key k (spin (swap! runs conj v) v))))
                             acc))]
                  (swap! ids conj (mapv rid hs))
                  (await-all hs)))
        u (v2/observe! c (fn [_ _]))]
    (is (= [1 2] (now c)))
    (is (= 2 (count (set (first @ids)))))
    (v2/write! items [[:a 2] [:a 1]])
    (is (= [2 1] (now c)))
    (is (= #{1 2} (set (drop 2 @runs))) "both rerun")
    (is (apply = @ids))
    (u)))

(deftest k6-nested-keys
  (let [c (spin (await (v2/with-key :a (v2/with-key :b (spin (frame-here))))))
        [frame _] (now c)
        [_ ks n] (peek frame)]
    (is (= [:a :b] ks))
    (is (= 0 n))))

(deftest k10-resume-between-keyed-creations
  (let [mid (v2/signal 0)
        runs (atom [])
        ids (atom [])
        c (spin (loop [i 0 acc []]
                  (if (= i 2)
                    (do (swap! ids conj (mapv rid acc)) (await-all acc))
                    (do (when (= i 1) (track mid))
                        (recur (inc i) (conj acc (v2/with-key :k (spin (swap! runs conj i) i))))))))
        u (v2/observe! c (fn [_ _]))]
    (is (= [0 1] (now c)))
    (v2/write! mid 1)
    (is (= [0 1] (now c)))
    (is (apply = @ids))
    (is (= 2 (count (set (first @ids)))))
    (is (= [0 1] @runs))
    (u)))

(deftest k18-fresh-equal-keys-match
  (doseq [[label key-of] [[:string #(str "k" %)]
                          [:uuid #(parse-uuid (str "00000000-0000-0000-0000-00000000000" %))]
                          [:vector #(vector % :item)]
                          [:map #(hash-map :id %)]]]
    (testing (name label)
      (let [items (v2/signal [1 2 3])
            runs (atom {}) ids (atom [])
            c (keyed-parent items key-of runs ids)
            u (v2/observe! c (fn [_ _]))]
        (is (= [10 20 30] (now c)))
        (v2/write! items [3 1 2])
        (is (= [30 10 20] (now c)))
        (is (= {1 1 2 1 3 1} @runs) "readopted across a rerun")
        (let [child (v2/fork! v2/*world*)
              cc (v2/in-world child c)
              uc (v2/observe! cc (fn [_ _]))]
          (v2/write! (v2/in-world child items) [2 3 1])
          (is (= [20 30 10] (now cc)))
          (is (= {1 1 2 1 3 1} @runs) "and in a fork")
          (is (apply = @ids))
          (uc)
          (v2/release-world! child))
        (u)))))
