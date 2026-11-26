(ns org.replikativ.spindel.v2.incremental.for-keyed-test
  "`for-keyed` and the combinators inside computations (phase-d design
   §4.2-§4.3). `for-keyed` creates one computation per item under
   `v2/with-key`: a later run adopts each item's computation by its key, in
   any order, and only an item whose captures changed reruns. This is the
   port of the old `for-each*` memoisation case, now by keyed adoption
   instead of a per-call-site cache. C1 in a world: a captured threshold
   changes while the tracked source does not."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.v2.core :as v2 :refer [spin track]]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.incremental :as ic :refer [for-keyed]]
            [org.replikativ.spindel.v2.dom.render-fixture :as fx]))

(defn- item [id v] {:id id :v v})

(defn- counted
  "A root mapping the items of `items` to `[id v]` with for-keyed, counting
   item body runs per id in `runs`."
  [items runs]
  (spin (for-keyed [x (track items) :key :id]
                   (swap! runs update (:id x) (fnil inc 0))
                   [(:id x) (:v x)])))

(defn- delta
  "The item runs since `before`, ids with no run left out."
  [runs before]
  (into {} (keep (fn [[k n]] (let [d (- n (get before k 0))] (when (pos? d) [k d])))) runs))

(deftest for-keyed-runs-each-item-once-and-adopts-by-key
  (fx/each-world
   (fn [env]
     (let [a (item 1 "a") b (item 2 "b") c (item 3 "c") d (item 4 "d")
           items (v2/signal [a b])
           runs (atom {})
           root (counted items runs)
           u (v2/observe! root (fn [_ _]))]
       (is (= [[1 "a"] [2 "b"]] (fx/read! env root)) "results in coll order")
       (is (= {1 1 2 1} @runs))
       (testing "append: only the new item runs (the old for-each* memo case)"
         (let [before @runs]
           (fx/write! env items [a b c])
           (is (= [[1 "a"] [2 "b"] [3 "c"]] (fx/read! env root)))
           (is (= {3 1} (delta @runs before)))))
       (testing "reverse: no item runs"
         (let [before @runs]
           (fx/write! env items [c b a])
           (is (= [[3 "c"] [2 "b"] [1 "a"]] (fx/read! env root)))
           (is (= {} (delta @runs before)))))
       (testing "insert at the head: one item runs"
         (let [before @runs]
           (fx/write! env items [d c b a])
           (is (= [[4 "d"] [3 "c"] [2 "b"] [1 "a"]] (fx/read! env root)))
           (is (= {4 1} (delta @runs before)))))
       (testing "change one item: only it runs (the others are the same objects)"
         (let [before @runs]
           (fx/write! env items [d c (item 2 "B") a])
           (is (= [[4 "d"] [3 "c"] [2 "B"] [1 "a"]] (fx/read! env root)))
           (is (= {2 1} (delta @runs before)))))
       (u)))))

(deftest two-sites-do-not-share-items
  (fx/each-world
   (fn [env]
     (let [items (v2/signal [(item 1 "a")])
           runs (atom {})
           root (spin (let [xs (track items)]
                        [(for-keyed [x xs :key :id] (swap! runs update [:one (:id x)] (fnil inc 0)) (:v x))
                         (for-keyed [x xs :key :id] (swap! runs update [:two (:id x)] (fnil inc 0)) (:v x))]))
           u (v2/observe! root (fn [_ _]))]
       (is (= [["a"] ["a"]] (fx/read! env root)))
       (is (= {[:one 1] 1 [:two 1] 1} @runs) "one computation per site and key")
       (u)))))

(deftest combinators-inside-a-computation
  (fx/each-world
   (fn [env]
     (let [xs (v2/signal [1 2 3 4])
           root (spin (let [iv (track xs)
                            evens (ic/ifilter even? iv)]
                        {:sum (iv/get-new (ic/ireduce + 0 evens))
                         :old (iv/get-old evens)
                         :new (iv/get-new (ic/imap inc evens))}))
           u (v2/observe! root (fn [_ _]))]
       (is (= {:sum 6 :old nil :new [3 5]} (fx/read! env root)) "the first run tracks no old value")
       (fx/write! env xs [1 2 3 4 5 6])
       (is (= {:sum 12 :old [2 4] :new [3 5 7]} (fx/read! env root)) ":old from the tracked old value")
       (u)))))

(deftest c1-a-captured-threshold-changes-in-a-world
  (fx/each-world
   (fn [env]
     (let [xs (v2/signal [1 2 3 4 5])
           t (v2/signal 2)
           root (spin (let [th (iv/get-new (track t))
                            r (ic/ifilter #(> % th) (track xs))]
                        [(iv/get-old r) (iv/get-new r)]))
           u (v2/observe! root (fn [_ _]))
           [_ new1] (fx/read! env root)]
       (is (= [3 4 5] new1))
       (fx/write! env t 4)
       (let [[old2 new2] (fx/read! env root)]
         (is (= [5] new2))
         (is (= [5] old2) "the source's old filtered by the new threshold")
         (is (not= new1 old2) "not the previous output: :old is advisory when a parameter changes"))
       (u)))))
