(ns org.replikativ.spindel.v2.keyed-creation-test
  "E1 keyed creation (spec §5.2 Z#82; phase-d design §1.3-§1.13, K1-K17): a
   creation inside `with-key` has the creation key [site K n]; a computation
   run adopts the predecessor with that key from its adoption basis, in any
   order."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await await-all aseq]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.verify :as verify]
            [org.replikativ.spindel.v2.port.helpers :as h :refer [checked-fixture]]
            [org.replikativ.spindel.incremental.interval :as iv]))

(use-fixtures :each checked-fixture)

(v2/register-effect! `frame-here (fn [_ ctx] [:value [(:frame ctx) (:key ctx)]]))
(defn frame-here [] (throw (ex-info "frame-here outside a body" {})))

(defn- rid
  "The row ID behind handle `x`, inside a body or a world item."
  [x] (aget ^objects (v2/row-of x) rw/ID))

(defn- hid [w x] (v2/call-in! w #(rid x)))

(defn- proj [w] (v2/call-in! w #(verify/projection w)))

(defn- adoption
  "C's basis and adoption basis, as ID sets."
  [w c]
  (let [p (get-in (proj w) [:comps (hid w c)])]
    {:basis (set (map first (:basis p)))
     :adopt (set (get-in p [:adoption :basis]))}))

(defn- now [h] (v2/value h 2000 ::timeout))

(defn- created-ids
  "The child ids named by the `:create-comp` items of `w`'s log."
  [w]
  (keep #(when (= :create-comp (first (:item %))) (nth (:item %) 2)) (verify/log w)))

(defn- keyed-parent
  "Tracks `items` (a vector of keys) and creates one keyed child computation
   per key; records each run's [key id] pairs in `ids` and each child run
   in `runs`."
  [items runs ids]
  (spin (let [xs (iv/get-new (track items))
              hs (loop [xs xs acc []]
                   (if-let [x (first xs)]
                     (recur (rest xs)
                            (conj acc (v2/with-key x (spin (swap! runs update x (fnil inc 0)) (* 10 x)))))
                     acc))]
          (swap! ids conj (mapv (fn [x hd] [x (rid hd)]) xs hs))
          (await-all hs))))

;; ---------------------------------------------------------------------------
;; K1-K5: reorder, insert, remove, changed captures, duplicates

(deftest k1-reorder-readopts-every-child
  (let [w v2/*world*
        items (v2/signal [1 2 3 4 5])
        runs (atom {}) ids (atom [])
        c (keyed-parent items runs ids)
        u (v2/observe! c (fn [_ _]))]
    (is (= [10 20 30 40 50] (now c)))
    (let [first-ids (set (created-ids w))]
      (v2/write! items [5 4 3 2 1])
      (is (= [50 40 30 20 10] (now c)))
      (is (= {1 1 2 1 3 1 4 1 5 1} @runs) "no child reruns")
      (let [[a b] @ids]
        (is (= (into {} a) (into {} b)) "every key keeps its computation"))
      (is (= 10 (count (created-ids w))))
      (is (= first-ids (set (created-ids w))) "the reorder's create-comp items name the old ids"))
    (u)))

(deftest k2-insert-in-the-middle
  (let [items (v2/signal [1 2 4 5])
        runs (atom {}) ids (atom [])
        c (keyed-parent items runs ids)
        u (v2/observe! c (fn [_ _]))]
    (is (= [10 20 40 50] (now c)))
    (v2/write! items [1 2 3 4 5])
    (is (= [10 20 30 40 50] (now c)))
    (is (= {1 1 2 1 3 1 4 1 5 1} @runs) "only the new child runs")
    (let [[a b] (map #(into {} %) @ids)]
      (is (= a (dissoc b 3)) "the others keep their computations")
      (is (not (contains? (set (vals a)) (b 3)))))
    (u)))

(deftest k3-remove
  (let [w v2/*world*
        items (v2/signal [1 2 3])
        never (v2/deferred)
        log (atom [])
        ids (atom [])
        c (spin (let [xs (iv/get-new (track items))
                      hs (loop [xs xs acc []]
                           (if-let [x (first xs)]
                             (recur (rest xs)
                                    (conj acc (v2/with-key x
                                                [(spin (* 10 x))
                                                 (task (try (await never) (finally (swap! log conj x))))])))
                             acc))]
                  (swap! ids conj (into {} (map (fn [x [cx kx]] [x [(rid cx) (rid kx)]]) xs hs)))
                  (await-all (mapv first hs))))
        u (v2/observe! c (fn [_ _]))]
    (is (= [10 20 30] (now c)))
    (v2/write! items [1 3])
    (is (= [10 30] (now c)))
    (is (h/wait-until #(= [2] @log)) "the removed key's task is cancelled at the parent's completion")
    (let [[before after] @ids
          [c2 k2] (before 2)
          a (adoption w c)]
      (is (= (dissoc before 2) after) "the other keys keep their rows")
      (is (not-any? #{c2 k2} (concat (:basis a) (:adopt a))) "T12 released the removed key's rows")
      (verify/gc-settle! w)
      (is (nil? (get-in (proj w) [:comps c2])) "its computation is gone"))
    (u)))

(deftest k4-changed-captures-rerun-only-that-key
  (let [items (v2/signal [[1 :a] [2 :b] [3 :c]])
        runs (atom {}) ids (atom [])
        c (spin (let [xs (iv/get-new (track items))
                      hs (loop [xs xs acc []]
                           (if-let [[k v] (first xs)]
                             (recur (rest xs) (conj acc (v2/with-key k (spin (swap! runs update k (fnil inc 0)) [k v]))))
                             acc))]
                  (swap! ids conj (mapv rid hs))
                  (await-all hs)))
        u (v2/observe! c (fn [_ _]))]
    (is (= [[1 :a] [2 :b] [3 :c]] (now c)))
    (v2/write! items [[1 :a] [2 :B] [3 :c]])
    (is (= [[1 :a] [2 :B] [3 :c]] (now c)))
    (is (= {1 1 2 2 3 1} @runs) "only key 2 reruns")
    (is (apply = @ids) "at the same ids")
    (u)))

(deftest k5-duplicate-keys-are-positional-within-the-key
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
    (is (= 2 (count (set (first @ids)))) "both duplicates exist")
    (v2/write! items [[:a 2] [:a 1]])
    (is (= [2 1] (now c)))
    (is (= #{1 2} (set (drop 2 @runs))) "swapping their captures reruns both")
    (is (apply = @ids) "each occurrence keeps its row")
    (u)))

;; ---------------------------------------------------------------------------
;; K6-K9: nesting, outside a body, key evaluation, the synchronous body

(deftest k6-nested-keys-append
  (let [c (spin (await (v2/with-key :a (v2/with-key :b (spin (frame-here))))))
        [frame key] (now c)
        [site ks n] (peek frame)]
    (is (= [:a :b] ks) "K is the active keys, outermost first")
    (is (= 0 n))
    (is (integer? site))
    (is (integer? key) "the effect's own key stays positional")))

(deftest k7-outside-a-body-runs-unkeyed
  (is (= 3 (v2/with-key :a (+ 1 2))))
  (let [c (v2/with-key :a (spin (frame-here)))]
    (is (= [] (first (now c))) "a host creation: an empty frame")))

(deftest k8-the-key-is-evaluated-once-in-the-caller
  (let [evals (atom 0)
        c (spin (await (v2/with-key (do (swap! evals inc) :k) (spin (frame-here)))))]
    (is (= [:k] (second (peek (first (now c))))))
    (is (= 1 @evals))))

(deftest k9-an-effect-in-the-body-is-a-compile-error
  (let [e (try (eval `(let [d# nil] (spin (v2/with-key 1 (await d#))))) nil
               (catch Throwable t t))]
    (is (some? e) "await directly in a with-key body does not compile")
    (is (re-find #"opaque closure" (str (some-> e ex-cause ex-message)))))
  (let [d (v2/deferred)
        c (spin (await (v2/with-key 1 (spin (await d)))))]
    (v2/deliver! d :ok)
    (is (= :ok (now c)) "an await in a nested spin of the body works")))

;; ---------------------------------------------------------------------------
;; K10-K12: resume between keyed creations, tasks, sources and sequences

(deftest k10-resume-between-keyed-creations-continues-the-counts
  (let [mid (v2/signal 0)
        runs (atom [])
        ids (atom [])
        c (spin (loop [i 0 acc []]
                  (if (= i 2)
                    (do (swap! ids conj (mapv rid acc)) (await-all acc))
                    (do (when (= i 1) (track mid))
                        ;; one site and one key: told apart by n
                        (recur (inc i) (conj acc (v2/with-key :k (spin (swap! runs conj i) i))))))))
        u (v2/observe! c (fn [_ _]))]
    (is (= [0 1] (now c)))
    (v2/write! mid 1)              ; re-enters at the track, keeps child 0
    (is (= [0 1] (now c)))
    (let [[a b] @ids]
      (is (= 2 (count (set a))))
      (is (= a b) "child 1 is readopted, not confused with child 0"))
    (is (= [0 1] @runs) "no child reruns")
    (u)))

(deftest k11-keyed-tasks
  (let [w v2/*world*
        items (v2/signal [[1 :a] [2 :b]])
        never (v2/deferred)
        log (atom [])
        ids (atom [])
        c (spin (let [xs (iv/get-new (track items))
                      hs (loop [xs xs acc []]
                           (if-let [[k v] (first xs)]
                             (recur (rest xs)
                                    (conj acc (v2/with-key k (task (try (await never) (finally (swap! log conj [k v])))))))
                             acc))]
                  (swap! ids conj (mapv rid hs))
                  (count hs)))
        u (v2/observe! c (fn [_ _]))]
    (is (= 2 (now c)))
    (v2/write! items [[2 :b] [1 :a]])
    (is (= 2 (now c)))
    (is (= (first @ids) (vec (reverse (second @ids)))) "equal captures keep each task")
    (is (= [] @log))
    (v2/write! items [[2 :B] [1 :a]])
    (is (= 2 (now c)))
    (let [[_ [k1 k2] [k1' k2']] @ids]
      (is (= k2 k2') "key 1 keeps its task")
      (is (not= k1 k1') "key 2's changed captures replace its task"))
    (is (h/wait-until #(= [[2 :b]] @log)) "T12 cancels the replaced task")
    (is (empty? (:adopt (adoption w c))))
    (u)))

(deftest k12-keyed-sources-and-sequences
  (testing "a source is readopted by key only with the same kind"
    (let [s (v2/signal 0)
          seen (atom [])
          c (spin (let [v (iv/get-new (track s))
                        xs (loop [ks [:b :a] acc {}]
                             (if-let [k (first ks)]
                               (recur (rest ks)
                                      (assoc acc k (v2/with-key k (if (and (= k :a) (= v 1)) (v2/mailbox) (v2/signal k)))))
                               acc))]
                    (swap! seen conj (update-vals xs rid))
                    v))
          u (v2/observe! c (fn [_ _]))]
      (is (= 0 (now c)))
      (v2/write! s 1)
      (is (= 1 (now c)))
      (v2/write! s 2)
      (is (= 2 (now c)))
      (let [[r0 r1 r2] @seen]
        (is (= (:b r0) (:b r1) (:b r2)) "the other key keeps its signal")
        (is (not= (:a r0) (:a r1)) "a mailbox under :a is a new source")
        (is (not= (:a r1) (:a r2)) "a signal again is a new source")
        (is (not= (:a r0) (:a r2)) "the rejected signal was released at T12, not readopted"))
      (u)))
  (testing "a sequence is readopted by key only with the same initial state"
    (let [s (v2/signal [[:a 0] [:b 0]])
          seen (atom [])
          c (spin (let [ps (iv/get-new (track s))
                        xs (loop [ps ps acc {}]
                             (if-let [[k init] (first ps)]
                               (recur (rest ps) (assoc acc k (v2/with-key k (aseq [n init] [n (inc n)]))))
                               acc))]
                    (swap! seen conj (update-vals xs rid))
                    (count xs)))
          u (v2/observe! c (fn [_ _]))]
      (is (= 2 (now c)))
      (v2/write! s [[:b 0] [:a 0]])
      (is (= 2 (now c)))
      (v2/write! s [[:b 5] [:a 0]])
      (is (= 2 (now c)))
      (let [[r0 r1 r2] @seen]
        (is (= r0 r1) "a reorder keeps both sequences")
        (is (= (:a r1) (:a r2)))
        (is (not= (:b r1) (:b r2)) "a changed initial state is a new sequence"))
      (u))))

;; ---------------------------------------------------------------------------
;; K13-K15: forks, savepoint instances, registered effects

(deftest k13-a-fork-reorders-independently
  (let [w v2/*world*
        items (v2/signal [1 2 3])
        runs (atom {}) ids (atom [])
        c (keyed-parent items runs ids)
        u (v2/observe! c (fn [_ _]))
        _ (is (= [10 20 30] (now c)))
        frozen (v2/fork! w)
        child (v2/fork! w)
        cc (v2/in-world child c)
        uc (v2/observe! cc (fn [_ _]))
        by-key #(into {} (peek @ids))
        orig (by-key)]
    (v2/write! (v2/in-world child items) [3 1 2])
    (is (= [30 10 20] (now cc)))
    (is (= orig (by-key)) "the fork readopts by key in its own copy")
    (v2/write! items [2 3 1])
    (is (= [20 30 10] (now c)))
    (is (= orig (by-key)) "the parent readopts by key")
    (is (= [30 10 20] (now cc)) "the fork is untouched by the parent")
    (is (= {1 1 2 1 3 1} @runs) "no child reruns in either world")
    (is (= [10 20 30] (now (v2/in-world frozen c))) "the frozen fork kept its state across the parent's rerun")
    (v2/write! (v2/in-world frozen items) [3 2 1])
    (is (= [30 20 10] (now (v2/in-world frozen c))))
    (is (= orig (by-key)) "and readopts by key from it")
    (uc) (u)
    (v2/release-world! child)
    (v2/release-world! frozen)))

(deftest k14-a-savepoint-instance-continues-the-counts
  (let [w v2/*world* pubs (atom [])]
    (v2/install-handlers! w {:s (fn [p] (swap! pubs conj p))})
    (let [t (task (loop [i 0 acc []]
                    (if (= i 2)
                      (loop [hs acc out []]
                        (if-let [hd (first hs)] (recur (rest hs) (conj out (await hd))) out))
                      (do (when (= i 1) (v2/savepoint :s nil))
                          (recur (inc i) (conj acc (v2/with-key :k (spin (frame-here)))))))))
          ns-of (fn [r] (mapv (fn [[frame _]] (nth (peek frame) 2)) r))]
      (is (h/wait-until #(seq @pubs)))
      (let [i (doto (v2/instantiate (first @pubs)) (v2/activate! nil))]
        (is (= [0 1] (ns-of (now (v2/in-world i t)))) "the instance continues the count of the run it copies")
        (v2/resume! (first @pubs) nil)
        (is (= [0 1] (ns-of (now t))))
        (v2/release-world! i)))))

(deftest k15-registered-effects-stay-positional
  (let [c (spin (let [a (v2/with-key "k" (spin [(frame-here) (frame-here)]))]
                  (await a)))
        [[f1 k1] [f2 k2]] (now c)
        [site ks n] (peek f1)]
    (is (= ["k"] ks))
    (is (= 0 n))
    (is (integer? site))
    (is (= f1 f2) "the keyed child's effects see its keyed creation key in their frame")
    (is (and (integer? k1) (integer? k2) (not= k1 k2)) "their own keys are positional")))

;; ---------------------------------------------------------------------------
;; K16, K17: helper call sites, keyed sub-models

(defmacro ^:private keyed-each
  "A test stand-in for P5's `for-keyed` (§4.3): one keyed computation per
   element, the generated `spin` carrying the call site's metadata (§2.6)."
  [[x xs] & body]
  (let [spin-form (with-meta `(spin ~@body) (meta &form))]
    `(await-all (mapv (fn [~x] (v2/with-key ~x ~spin-form)) ~xs))))

(deftest k16-helper-call-sites-keep-their-own-rows
  (testing "two call sites of one keyed macro, overlapping keys"
    (let [l (v2/signal [1 2 3])
          r (v2/signal [2 3 4])
          runs (atom {})
          c (spin (let [as (iv/get-new (track l))
                        bs (iv/get-new (track r))]
                    [(keyed-each [x as] (swap! runs update [:l x] (fnil inc 0)) [:l x])
                     (keyed-each [x bs] (swap! runs update [:r x] (fnil inc 0)) [:r x])]))
          u (v2/observe! c (fn [_ _]))]
      (is (= [[[:l 1] [:l 2] [:l 3]] [[:r 2] [:r 3] [:r 4]]] (now c)))
      (v2/write! l [3 2 1])
      (is (= [[[:l 3] [:l 2] [:l 1]] [[:r 2] [:r 3] [:r 4]]] (now c)) "each site keeps its own rows")
      (is (= 6 (count @runs)) "the sites do not share rows")
      (is (every? #{1} (vals @runs)) "no child reruns on the reorder")
      (u)))
  (testing "two calls of one helper computation, overlapping keys"
    (let [runs (atom {})
          view (fn [tag xs] (spin (keyed-each [x xs] (swap! runs update [tag x] (fnil inc 0)) [tag x])))
          l (v2/signal [1 2 3])
          c (spin (let [as (iv/get-new (track l))]
                    [(await (view :l as)) (await (view :r [2 3 4]))]))
          u (v2/observe! c (fn [_ _]))]
      (is (= [[[:l 1] [:l 2] [:l 3]] [[:r 2] [:r 3] [:r 4]]] (now c)))
      (v2/write! l [3 2 1])
      (is (= [[[:l 3] [:l 2] [:l 1]] [[:r 2] [:r 3] [:r 4]]] (now c)))
      (is (every? #{1} (vals @runs)) "each helper adopts only its own children")
      (is (= 6 (count @runs)))
      (u))))

(deftest k17-keyed-sub-models
  ;; a foerster-style model: a sub-model per named site, its parameters an
  ;; input; changing one site's parameter reruns only that sub-model
  (let [params (v2/signal {:mu 0.0 :sigma 1.0 :tau 2.0})
        runs (atom {})
        model (spin (let [ps (iv/get-new (track params))
                          subs (loop [ks (sort (keys ps)) acc []]
                                 (if-let [k (first ks)]
                                   (recur (rest ks)
                                          (conj acc (v2/with-key k
                                                      (let [p (get ps k)]
                                                        (spin (swap! runs update k (fnil inc 0))
                                                              (* p p))))))
                                   acc))]
                      (reduce + (await-all subs))))
        u (v2/observe! model (fn [_ _]))]
    (is (= 5.0 (now model)))
    (v2/write! params {:mu 0.0 :sigma 3.0 :tau 2.0})
    (is (= 13.0 (now model)))
    (is (= {:mu 1 :sigma 2 :tau 1} @runs))
    (v2/write! params {:mu 0.0 :sigma 3.0 :tau 2.0 :nu 1.0})
    (is (= 14.0 (now model)))
    (is (= {:mu 1 :sigma 2 :tau 1 :nu 1} @runs) "a new site runs alone")
    (u)))

;; ---------------------------------------------------------------------------
;; The positional ordinal limit (§1.2: an ordinal at 2^20 would spill into the site)

(defn- invalid-of [e]
  (some #(:spindel/invalid (ex-data %)) (take-while some? (iterate ex-cause e))))

(deftest positional-ordinals-are-limited
  ;; a plain world: 2^20 creations
  (let [w (v2/world)]
    (try
      (binding [v2/*world* w]
        (let [t (task (loop [i 0] (if (< i 1048577) (do (spin nil) (recur (inc i))) i)))
              e (try (v2/value t 60000 ::timeout) (catch Throwable e e))]
          (is (= ::v2/too-many-creations (invalid-of e)) (str e))
          (is (= 1048577 (v2/value (task (loop [i 0] (if (< i 1048577) (do (v2/with-key :k (spin nil)) (recur (inc i))) i)))
                                   60000 ::timeout))
              "a keyed count is not packed into a long, so it is not bound")))
      (finally (v2/release-world! w)))))
