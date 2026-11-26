(ns org.replikativ.spindel.v2.keyed-creation-cljc-test
  "E1 keyed creation on both platforms (phase-d design §1.13: K1-K3, K5, K6,
   K10, K18): keys compare by value, so freshly allocated equal keys find
   their predecessor on CLJS too. Every read waits for the settled value:
   JVM by blocking, CLJS by the value callback (no assumption that a
   budgeted drain finishes synchronously)."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is async]])
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await await-all]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.incremental.interval :as iv]
            #?(:clj [org.replikativ.spindel.v2.verify :as verify])))

(v2/defeffect frame-here [_ ctx] [:value [(:frame ctx) (:key ctx)]])

(defn- then
  "Calls `(k v)` with `h`'s settled value (`[:err e]` for an error)."
  [h k]
  #?(:clj (k (try (v2/value h 2000 ::timeout) (catch Exception e [:err e])))
     :cljs (v2/value-async h (fn [v err?] (k (if err? [:err v] v))))))

(defn- in-world
  "Runs `(f done)` with a fresh world bound; the test ends at `(done)`. JVM:
   a checked world (Rule R compared after every commit), waited for here."
  [f]
  #?(:clj (let [acc (atom [])
                w (v2/world {:verify? true :hook (verify/checking-hook acc)})
                p (promise)]
            (try (binding [v2/*world* w] (f #(deliver p true)))
                 (is (true? (deref p 5000 false)) "the test completes")
                 (finally (v2/release-world! w)))
            (is (empty? @acc) (str "Rule R divergences: " (vec (take 3 @acc)))))
     :cljs (async done
                  (let [w (v2/world)
                        over (atom false)
                        end (fn [] (when (compare-and-set! over false true)
                                     (v2/release-world! w) (js/setTimeout done 0)))
                        t (js/setTimeout #(when-not @over (is false "the test completes") (end)) 5000)]
                    (binding [v2/*world* w]
                      (f (fn [] (js/clearTimeout t) (end))))))))

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
  (in-world
   (fn [done]
     (let [items (v2/signal [1 2 3 4 5])
           runs (atom {}) ids (atom [])
           c (keyed-parent items identity runs ids)
           u (v2/observe! c (fn [_ _]))]
       (then c (fn [v]
                 (is (= [10 20 30 40 50] v))
                 (v2/write! items [5 4 3 2 1])
                 (then c (fn [v]
                           (is (= [50 40 30 20 10] v))
                           (is (= {1 1 2 1 3 1 4 1 5 1} @runs) "no child reruns")
                           (is (apply = @ids) "every key keeps its computation")
                           (u) (done)))))))))

(deftest k2-insert
  (in-world
   (fn [done]
     (let [items (v2/signal [1 2 4 5])
           runs (atom {}) ids (atom [])
           c (keyed-parent items identity runs ids)
           u (v2/observe! c (fn [_ _]))]
       (then c (fn [v]
                 (is (= [10 20 40 50] v))
                 (v2/write! items [1 2 3 4 5])
                 (then c (fn [v]
                           (is (= [10 20 30 40 50] v))
                           (is (= {1 1 2 1 3 1 4 1 5 1} @runs) "only the new child runs")
                           (let [[a b] @ids] (is (= a (dissoc b 3))))
                           (u) (done)))))))))

(deftest k3-remove-cancels-the-keyed-task
  (in-world
   (fn [done]
     (let [items (v2/signal [1 2 3])
           never (v2/deferred)
           log (atom [])
           tasks (atom {})
           c (spin (let [xs (iv/get-new (track items))
                         hs (loop [xs xs acc []]
                              (if-let [x (first xs)]
                                (recur (rest xs)
                                       (conj acc (v2/with-key x
                                                   (task (try (await never) (finally (swap! log conj x)))))))
                                acc))]
                     (swap! tasks merge (zipmap xs hs))
                     (count hs)))
           u (v2/observe! c (fn [_ _]))]
       (then c (fn [v]
                 (is (= 3 v))
                 (v2/write! items [1 3])
                 (then c (fn [v]
                           (is (= 2 v))
                           ;; the removed key's task settles once its cancellation unwound
                           (then (get @tasks 2)
                                 (fn [r]
                                   (is (= :err (first r)))
                                   (is (= [2] @log) "the removed key's task is cancelled at the parent's completion")
                                   (u) (done)))))))))))

(deftest k5-duplicates
  (in-world
   (fn [done]
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
       (then c (fn [v]
                 (is (= [1 2] v))
                 (is (= 2 (count (set (first @ids)))))
                 (v2/write! items [[:a 2] [:a 1]])
                 (then c (fn [v]
                           (is (= [2 1] v))
                           (is (= #{1 2} (set (drop 2 @runs))) "both rerun")
                           (is (apply = @ids))
                           (u) (done)))))))))

(deftest k6-nested-keys
  (in-world
   (fn [done]
     (then (spin (await (v2/with-key :a (v2/with-key :b (spin (frame-here))))))
           (fn [[frame _]]
             (let [[_ ks n] (peek frame)]
               (is (= [:a :b] ks))
               (is (= 0 n)))
             (done))))))

(deftest k10-resume-between-keyed-creations
  (in-world
   (fn [done]
     (let [mid (v2/signal 0)
           runs (atom [])
           ids (atom [])
           c (spin (loop [i 0 acc []]
                     (if (= i 2)
                       (do (swap! ids conj (mapv rid acc)) (await-all acc))
                       (do (when (= i 1) (track mid))
                           (recur (inc i) (conj acc (v2/with-key :k (spin (swap! runs conj i) i))))))))
           u (v2/observe! c (fn [_ _]))]
       (then c (fn [v]
                 (is (= [0 1] v))
                 (v2/write! mid 1)
                 (then c (fn [v]
                           (is (= [0 1] v))
                           (is (apply = @ids))
                           (is (= 2 (count (set (first @ids)))))
                           (is (= [0 1] @runs))
                           (u) (done)))))))))

(defn- k18-case
  "Fresh equal keys from `key-of` readopt across a rerun and in a fork."
  [w key-of k]
  (let [items (binding [v2/*world* w] (v2/signal [1 2 3]))
        runs (atom {}) ids (atom [])
        c (binding [v2/*world* w] (keyed-parent items key-of runs ids))
        u (v2/observe! c (fn [_ _]))]
    (then c (fn [v]
              (is (= [10 20 30] v))
              (v2/write! items [3 1 2])
              (then c (fn [v]
                        (is (= [30 10 20] v))
                        (is (= {1 1 2 1 3 1} @runs) "readopted across a rerun")
                        (let [child (v2/fork! w)
                              cc (v2/in-world child c)
                              uc (v2/observe! cc (fn [_ _]))]
                          (v2/write! (v2/in-world child items) [2 3 1])
                          (then cc (fn [v]
                                     (is (= [20 30 10] v))
                                     (is (= {1 1 2 1 3 1} @runs) "and in a fork")
                                     (is (apply = @ids))
                                     (uc)
                                     (v2/release-world! child)
                                     (u)
                                     (k))))))))))

(deftest k18-fresh-equal-keys-match
  (in-world
   (fn [done]
     (let [w v2/*world*
           cases [#(str "k" %)
                  #(parse-uuid (str "00000000-0000-0000-0000-00000000000" %))
                  #(vector % :item)
                  #(hash-map :id %)]
           step (fn step [cs]
                  (if (empty? cs)
                    (done)
                    (k18-case w (first cs) #(step (rest cs)))))]
       (step cases)))))

(deftest a-restart-readopts-keyed-prefix-creations
  ;; T11: the item tracks `sel` and reruns on its own; the list's await-all
  ;; stores no continuation, so the list restarts from its body and readopts
  ;; the items, created before the fired edge, by key. Each item counts its
  ;; runs before its track: a resume there does not count, a new row does.
  (in-world
   (fn [done]
     (let [sel (v2/signal 1)
           runs (atom {}) ids (atom [])
           c (spin (let [hs (loop [xs [1 2 3] acc []]
                              (if-let [x (first xs)]
                                (recur (rest xs)
                                       (conj acc (v2/with-key x (spin (swap! runs update x (fnil inc 0))
                                                                      [x (= x (iv/get-new (track sel)))]))))
                                acc))]
                     (swap! ids conj (mapv rid hs))
                     (await-all hs)))
           u (v2/observe! c (fn [_ _]))]
       (then c (fn [v]
                 (is (= [[1 true] [2 false] [3 false]] v))
                 (v2/write! sel 2)
                 (then c (fn [v]
                           (is (= [[1 false] [2 true] [3 false]] v))
                           (is (= 2 (count @ids)) "the item's change restarted the list")
                           (is (apply = @ids) "every key keeps its row")
                           (is (= {1 1 2 1 3 1} @runs) "no item body runs again from its start")
                           (u) (done)))))))))
