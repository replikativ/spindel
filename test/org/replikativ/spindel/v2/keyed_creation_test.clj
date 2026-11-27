(ns org.replikativ.spindel.v2.keyed-creation-test
  "E1 keyed creation (spec §5.2 Z#82; phase-d design §1.3-§1.13, K1-K17): a
   creation inside `with-key` has the creation key [site K n]; a computation
   run adopts the predecessor with that key from its adoption basis, in any
   order."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await await-all await-any aseq take!]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.host :as hs]
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

;; ---------------------------------------------------------------------------
;; Limits. Counts are seeded near 2^20 in the running run (test-only access
;; to its R-ORD / R-KORD) instead of making a million rows.

(def ^:private M 1048576)

(defn- creation-key-of
  "The creation key of the row behind `h`: the last frame entry of a
   computation or task, the KEY of a source or sequence."
  [h]
  (let [^objects x (v2/row-of h)
        t (long (aget x rw/TYPE))]
    (cond (== t rw/T-COMP) (peek (aget x rw/C-FRAME))
          (== t rw/T-TASK) (peek (aget x rw/K-FRAME))
          :else (aget x rw/KEY))))

(defn- site-of-key [k] (Math/floorDiv (long k) (long M)))

(defn- seed-ordinal!
  "Inside a body: the running run's next positional ordinal at `site` is `n`."
  [site n]
  (let [^objects r (v2/active-run)]
    (when-not (aget r rw/R-ORD) (aset r rw/R-ORD (hs/vmap)))
    (hs/mput! (aget r rw/R-ORD) site n)))

(defn- registered [] (count (aget ^objects (#'v2/cw) rw/W-REG)))

(defn- at-the-limit
  "Inside a body: one creation with `make` gives its site; with the site's
   count seeded at 2^20 the next one is rejected. Returns the rejection's
   kind and what the rejection changed: the run's effect index and the
   number of registered rows."
  [make]
  (let [^objects r (v2/active-run)
        site (site-of-key (creation-key-of (make)))
        _ (seed-ordinal! site M)
        eidx (long (aget r rw/R-EIDX))
        n (registered)
        e (try (make) nil (catch Throwable e e))]
    [(invalid-of e) (- (long (aget r rw/R-EIDX)) eidx) (- (registered) n)]))

(deftest positional-ordinals-are-limited
  (let [t (task (let [mk (fn [] (spin nil))
                      site (site-of-key (creation-key-of (mk)))]
                  (seed-ordinal! site (dec M))
                  (let [last-ok (creation-key-of (mk))
                        e (try (mk) nil (catch Throwable e e))]
                    (aset ^objects (v2/active-run) rw/R-KORD {[site [:k]] (+ M 5)})
                    [site last-ok (invalid-of e) (creation-key-of (v2/with-key :k (mk)))])))
        [site last-ok kind keyed] (now t)]
    (is (= (+ (* site M) (dec M)) last-ok) "ordinal 2^20 - 1 is a valid creation")
    (is (= ::v2/too-many-creations kind) "ordinal 2^20 is rejected")
    (is (= [site [:k] (+ M 5)] keyed) "a keyed count is not packed into a long, so it is not bound")))

(deftest a-creation-at-the-limit-changes-nothing
  ;; the rejection precedes the effect index, the id allocation and the
  ;; registration, in every creation path; the run continues consistently
  ;; (the checked fixture compares Rule R after every commit)
  (let [ok [::v2/too-many-creations 0 0]
        t (task (let [r [(at-the-limit (fn [] (spin nil)))
                         (at-the-limit (fn [] (task nil)))]]
                  (await (spin :after))
                  r))
        c (spin (let [r [(at-the-limit (fn [] (v2/signal 0)))
                         (at-the-limit (fn [] (aseq [n 0] [n (inc n)])))
                         (at-the-limit (fn [] (spin nil)))
                         (at-the-limit (fn [] (task nil)))]]
                  (await (spin :after))
                  r))]
    (is (= [ok ok] (now t)) "task-owned computation and task")
    (is (= [ok ok ok ok] (now c)) "computation-owned source, sequence, computation and task")
    (let [w v2/*world*
          p (proj w)
          created (set (keep #(when (#{:create-comp :create-comp-top :spawn :spawn-top :create-source :create-link}
                                     (first (:item %)))
                                (case (first (:item %))
                                  (:spawn :spawn-top) (nth (:item %) 3)
                                  :create-source (nth (:item %) 4)
                                  (:create-link) (nth (:item %) 2)
                                  (nth (:item %) 2)))
                             (verify/log w)))]
      (is (every? created (concat (keys (:comps p)) (keys (:tasks p))))
          "every computation and task has its creation item"))))

;; ---------------------------------------------------------------------------
;; Registered-effect keys stay injective past 2^20 occurrences of one site

(v2/register-effect! `key-here (fn [_ ctx] [:value [(:site ctx) (:key ctx)]]))
(defn key-here [] (throw (ex-info "key-here outside a body" {})))

(deftest effect-keys-past-2-20-do-not-collide
  (let [t (task (loop [i 0 acc []]
                  (if (= i 2)
                    (let [[[s _]] acc]
                      ;; site s + 1's first occurrence, from the same counter map
                      (conj acc [(inc s) (#'v2/effect-key! (v2/active-run) (inc s))]))
                    (let [[site key] (key-here)]
                      (when (zero? i) (seed-ordinal! site M))
                      (recur (inc i) (conj acc [site key]))))))
        [[s k0] [_ k1] [_ next-first]] (now t)]
    (is (= (* s M) k0) "below 2^20 the key stays the packed long")
    (is (= (* (inc s) M) next-first))
    (is (not= k1 next-first) "ordinal 2^20 at site s is not site s+1's first occurrence")
    (is (= [s M] k1))))

;; ---------------------------------------------------------------------------
;; Review cases (sol, PR #359)

(deftest mixed-keyed-and-positional-suffixes-through-repeated-cuts
  ;; no run completes (each parks on an empty mailbox): every write is a cut.
  ;; Runs 0 and 1 create a positional and a keyed child, run 2 nothing (an
  ;; empty suffix), run 3 both again.
  (let [w v2/*world*
        s (v2/signal 0)
        mb (v2/mailbox)
        runs (atom [])
        c (spin (let [v (iv/get-new (track s))]
                  (swap! runs conj (when-not (= v 2)
                                     (let [p (rid (spin :p)) a (rid (v2/with-key :a (spin :a)))]
                                       {:p p :a a})))
                  (take! mb)))
        u (v2/observe! c (fn [_ _]))
        adopt #(:adopt (adoption w c))]
    (is (h/wait-until #(= 1 (count @runs))))
    (v2/write! s 1)
    (is (h/wait-until #(= 2 (count @runs))))
    (let [[r0 r1] @runs]
      (is (= r0 r1) "both kinds are readopted at the cut")
      (is (= #{} (adopt))))
    (v2/write! s 2)
    (is (h/wait-until #(= 3 (count @runs))))
    (is (= (set (vals (first @runs))) (adopt)) "the empty run's adoption basis is the previous suffix")
    (v2/write! s 3)
    (is (h/wait-until #(= 4 (count @runs))))
    (let [[r0 _ _ r3] @runs]
      (is (not-any? (set (vals r0)) (vals r3)) "after the empty suffix both are created afresh")
      (is (= #{} (adopt)) "the empty suffix replaced the adoption basis")
      (verify/gc-settle! w)
      (is (not-any? (set (keys (:comps (proj w)))) (vals r0)) "the superseded children are gone"))
    (u)))

(deftest keyed-superseded-tasks-at-the-cut
  (testing "a keyed task nothing else retains is cancelled at the second cut"
    (let [w v2/*world*
          s (v2/signal 0)
          never (v2/deferred)
          log (atom [])
          ks (atom [])
          c (spin (let [v (iv/get-new (track s))]
                    (when (zero? v)
                      (swap! ks conj (rid (v2/with-key :k
                                            (task (try (loop [] (v2/sleep 20) (recur))
                                                       (finally (swap! log conj :fin))))))))
                    (await never)))
          u (v2/observe! c (fn [_ _]))
          [k] @ks]
      (v2/write! s 1)
      (is (= #{k} (:adopt (adoption w c))) "the first cut keeps it in the keyed adoption basis")
      (is (= [] @log))
      (v2/write! s 2)
      (is (h/wait-until #(= [:fin] @log)) "the next cut drops it: cancelled")
      (is (empty? (:adopt (adoption w c))))
      (verify/gc-settle! w)
      (is (nil? (get-in (proj w) [:tasks k])))
      (u)))
  (testing "a keyed task another live computation awaits keeps running"
    (let [w v2/*world*
          s (v2/signal 0)
          never (v2/deferred)
          fin (v2/deferred)
          held (atom nil)
          c (spin (let [v (iv/get-new (track s))]
                    (when (zero? v) (reset! held (v2/with-key :k (task (await fin)))))
                    (await never)))
          u (v2/observe! c (fn [_ _]))
          k0 @held
          o (spin (await k0))
          seen (atom [])
          uo (v2/observe! o (fn [v _] (swap! seen conj v)))]
      (v2/write! s 1)
      (v2/write! s 2)
      (is (empty? (:adopt (adoption w c))))
      (is (some? (get-in (proj w) [:tasks (hid w k0) :run])) "it keeps running")
      (v2/deliver! fin :done)
      (is (h/wait-until #(= [:done] @seen)))
      (uo) (u))))

(deftest a-fork-adopts-and-drops-from-its-copy-of-the-keyed-adoption-basis
  ;; the run after the cut parks before creating, so C-ADOPT-K holds :a and
  ;; :b at the fork; the parent then adopts :a and drops :b, the fork adopts
  ;; :b and drops :a
  (let [w v2/*world*
        s (v2/signal 0)
        mb (v2/mailbox)
        c (spin (let [_ (iv/get-new (track s))
                      ks (take! mb)
                      m (loop [ks ks m {}]
                          (if-let [k (first ks)]
                            (recur (rest ks) (assoc m k (rid (v2/with-key k (spin k)))))
                            m))]
                  m))
        u (v2/observe! c (fn [_ _]))
        _ (v2/post! mb [:a :b])
        orig (now c)
        _ (v2/write! s 1)
        _ (is (= (set (vals orig)) (:adopt (adoption w c))) "parked with both in the keyed adoption basis")
        child (v2/fork! w)
        cc (v2/in-world child c)
        uc (v2/observe! cc (fn [_ _]))]
    (v2/post! mb [:a])
    (is (= (select-keys orig [:a]) (now c)) "the parent adopts :a")
    (v2/post! (v2/in-world child mb) [:b])
    (is (= (select-keys orig [:b]) (now cc)) "the fork adopts :b from its own copy")
    (let [a (adoption w c)
          ca (let [p (v2/call-in! child #(verify/projection child))
                   x (get-in p [:comps (hid w c)])]
               {:basis (set (map first (:basis x))) :adopt (set (get-in x [:adoption :basis]))})]
      (is (= #{(:a orig)} (:basis a)))
      (is (empty? (:adopt a)) "T12 dropped :b in the parent")
      (is (= #{(:b orig)} (:basis ca)))
      (is (empty? (:adopt ca)) "and :a in the fork"))
    (uc) (u)
    (v2/release-world! child)))

(deftest the-key-scope-is-restored-after-a-caught-throw
  (let [c (spin (let [_ (try (v2/with-key :a (throw (ex-info "x" {}))) (catch Exception _ nil))
                      a (spin (frame-here))
                      b (v2/with-key :o
                          (try (v2/with-key :i (throw (ex-info "y" {}))) (catch Exception _ nil))
                          (spin (frame-here)))]
                  [(await a) (await b)]))
        [[fa] [fb]] (now c)]
    (is (integer? (peek fa)) "after the caught throw the creation is positional again")
    (is (= [:o] (second (peek fb))) "the inner key is gone, the outer one stays")))

(deftest nil-and-false-are-keys
  (let [items (v2/signal [[nil 1] [false 2] [:x 3]])
        runs (atom {}) ids (atom [])
        c (spin (let [xs (iv/get-new (track items))
                      hs (loop [xs xs acc []]
                           (if-let [[k v] (first xs)]
                             (recur (rest xs) (conj acc (v2/with-key k (spin (swap! runs update v (fnil inc 0)) v))))
                             acc))]
                  (swap! ids conj (into {} (map (fn [[k _] hd] [k (rid hd)]) xs hs)))
                  (await-all hs)))
        u (v2/observe! c (fn [_ _]))]
    (is (= [1 2 3] (now c)))
    (v2/write! items [[:x 3] [false 2] [nil 1]])
    (is (= [3 2 1] (now c)))
    (is (= {1 1 2 1 3 1} @runs) "readopted by key")
    (is (apply = @ids))
    (is (= 3 (count (set (vals (first @ids))))) "nil, false and :x are three keys")
    (u)))

(deftest keyed-task-path-and-sequence-capture-replacement
  (let [w v2/*world*
        s (v2/signal [:p 0])
        never (v2/deferred)
        log (atom [])
        seen (atom [])
        gates {1 (v2/deferred) 2 (v2/deferred) 3 (v2/deferred)}
        c (spin (let [[p x] (iv/get-new (track s))
                      k (v2/with-path [p] (v2/with-key :k (task (try (await never) (finally (swap! log conj :fin))))))
                      q (v2/with-key :k (aseq [n 0] [(+ n x) (inc n)]))]
                  (swap! seen conj [(rid k) (rid q)])
                  (await (get gates (count @seen)))
                  p))
        u (v2/observe! c (fn [_ _]))]
    (v2/write! s [:q 0])
    (is (h/wait-until #(= 2 (count @seen))))
    (let [[[k0 q0] [k1 q1]] @seen
          a (adoption w c)]
      (is (not= k0 k1) "a changed path replaces the keyed task")
      (is (= q0 q1) "equal captures keep the keyed sequence")
      (is (contains? (:adopt a) k0) "the replaced task stays in the adoption basis")
      (is (= [] @log)))
    (v2/write! s [:q 1])
    (is (h/wait-until #(= 3 (count @seen))))
    (let [[_ [k1 q1] [k2 q2]] @seen
          a (adoption w c)]
      (is (= k1 k2))
      (is (not= q1 q2) "changed captures replace the keyed sequence")
      (is (contains? (:adopt a) q1) "the replaced sequence stays in the adoption basis"))
    (v2/deliver! (gates 3) :go)
    (is (= :q (now c)))
    (is (h/wait-until #(= [:fin] @log)) "the replaced task is cancelled once no adoption basis holds it")
    (is (empty? (:adopt (adoption w c))))
    (u)))

(deftest the-verify-hook-checks-creation-key-uniqueness
  ;; P3: checked after every commit, for the basis and the adoption basis
  ;; separately (duplicates are injected and removed inside one world item)
  (let [kv (or (ns-resolve 'org.replikativ.spindel.v2.verify 'key-violations) (constantly ::missing))
        w v2/*world*
        c (spin (let [a (spin 1) b (spin 2)] (+ (await a) (await b))))
        u (v2/observe! c (fn [_ _]))
        _ (is (= 3 (now c)))
        found (fn [i]
                (v2/call-in! w (fn []
                                 (let [^objects x (v2/row-of c)
                                       ^java.util.List l (or (aget x i) (let [l (java.util.ArrayList.)] (aset x i l) l))
                                       first-row (.get ^java.util.List (aget x rw/C-BASIS) 0)]
                                   (.add l first-row) (.add l first-row)
                                   (let [v (kv w)]
                                     (.remove l (int (dec (.size l)))) (.remove l (int (dec (.size l))))
                                     (set (map :container v)))))))]
    (is (= [] (v2/call-in! w #(kv w))))
    (is (= #{:basis :rows} (found rw/C-BASIS)))
    (is (= #{:adoption :rows} (found rw/C-ADOPT)))
    (is (= [{:container :kept :key [0 [:x] 0] :comp (hid w c)} {:container :kept :completed true :comp (hid w c)}]
           (v2/call-in! w (fn []
                            (let [^objects x (v2/row-of c)]
                              ;; a basis row under another key, left by a completed run
                              (aset x rw/C-KEPT-K {[0 [:x] 0] (.get ^java.util.List (aget x rw/C-BASIS) 0)})
                              (let [v (kv w)] (aset x rw/C-KEPT-K nil) v)))))
        "the kept keyed prefix of a restart (T11)")
    (is (= [] (v2/call-in! w #(kv w))) "restored")
    (u)))

;; ---------------------------------------------------------------------------
;; T11 restart from the body: a group await stores no continuation, so a fired
;; edge at it restarts the run from its body. The creations before that edge
;; stay in the basis for adoption (spec T11), keyed ones included. Item
;; bodies count their runs before their track: a resume at the track does not
;; count, a new computation (or a rerun from its body) does.

(defn- selected
  "One keyed item per element of `xs`; each counts its runs in `runs` and
   tracks `sel`."
  [xs sel runs]
  (loop [xs xs acc []]
    (if-let [x (first xs)]
      (recur (rest xs)
             (conj acc (v2/with-key x (spin (swap! runs update x (fnil inc 0))
                                            [x (= x (iv/get-new (track sel)))]))))
      acc)))

(deftest a-restart-readopts-keyed-prefix-creations
  (let [w v2/*world*
        sel (v2/signal 1)
        runs (atom {}) ids (atom [])
        c (spin (let [p (spin (swap! runs update :p (fnil inc 0)) :p)
                      hs (selected [1 2 3] sel runs)]
                  (swap! ids conj (mapv rid (into [p] hs)))
                  (await-all (into [p] hs))))
        u (v2/observe! c (fn [_ _]))]
    (is (= [:p [1 true] [2 false] [3 false]] (now c)))
    (v2/write! sel 2)
    (is (= [:p [1 false] [2 true] [3 false]] (now c)))
    (is (= 2 (count @ids)) "the item's change restarted the list")
    (is (apply = @ids) "the positional and the keyed creations keep their rows")
    (is (= {:p 1 1 1 2 1 3 1} @runs) "no item body runs again from its start")
    (is (= 4 (count (:basis (adoption w c)))) "each creation is in the basis once")
    (u)))

(deftest a-restart-reruns-a-keyed-prefix-row-whose-captures-changed
  ;; the captures come from a host atom the list does not track
  (let [sel (v2/signal 1)
        gen (atom 0)
        runs (atom {}) ids (atom [])
        c (spin (let [g (deref gen)
                      hs (loop [xs [1 2] acc []]
                           (if-let [x (first xs)]
                             (recur (rest xs)
                                    (conj acc (v2/with-key x (spin (swap! runs update x (fnil inc 0))
                                                                   [g x (= x (iv/get-new (track sel)))]))))
                             acc))]
                  (swap! ids conj (mapv rid hs))
                  (await-all hs)))
        u (v2/observe! c (fn [_ _]))]
    (is (= [[0 1 true] [0 2 false]] (now c)))
    (reset! gen 1)
    (v2/write! sel 2)
    (is (= [[1 1 false] [1 2 true]] (now c)))
    (is (apply = @ids) "readopted at the same rows")
    (is (= {1 2 2 2} @runs) "the changed captures rerun each item from its body (W#5)")
    (u)))

(deftest a-restart-readopts-keyed-tasks-sources-and-sequences
  (let [w v2/*world*
        sel (v2/signal 1)
        never (v2/deferred)
        log (atom [])
        seen (atom [])
        c (spin (let [k (v2/with-key :t (task (swap! log conj :start)
                                              (try (await never) (finally (swap! log conj :fin)))))
                      s (v2/with-key :s (v2/signal 0))
                      q (v2/with-key :q (aseq [n 0] [n (inc n)]))
                      i (v2/with-key :i (spin (iv/get-new (track sel))))]
                  (swap! seen conj (mapv rid [k s q i]))
                  (await-all [i])))
        u (v2/observe! c (fn [_ _]))]
    (is (= [1] (now c)))
    (is (h/wait-until #(= [:start] @log)))
    (v2/write! sel 2)
    (is (= [2] (now c)))
    (is (= 2 (count @seen)) "the item's change restarted the list")
    (is (apply = @seen) "the task, the source and the sequence keep their rows")
    (is (= 4 (count (:basis (adoption w c)))))
    (is (= [:start] @log) "the task keeps running: neither cancelled nor started again")
    (u)))

(deftest an-await-any-restart-readopts-keyed-prefix-creations
  (let [sel (v2/signal 1)
        runs (atom {}) ids (atom [])
        c (spin (let [hs (selected [1 2] sel runs)]
                  (swap! ids conj (mapv rid hs))
                  (await-any hs)))
        u (v2/observe! c (fn [_ _]))]
    (is (= [1 true] (now c)))
    ;; the loser's first settle fires its edge too: a restart before the write
    (let [n (count @ids)]
      (v2/write! sel 2)
      (is (= [1 false] (now c)))
      (is (= (inc n) (count @ids)) "the winner's change restarted the list"))
    (is (apply = @ids))
    (is (= {1 1 2 1} @runs))
    (u)))

(deftest a-fail-fast-await-all-restart-readopts-keyed-prefix-creations
  ;; :a fails, so the group resumes at once; :b's edge stays with the list,
  ;; and when :b settles it fires and restarts the list from its body
  (let [gate (v2/deferred)
        runs (atom {}) ids (atom [])
        c (spin (let [a (v2/with-key :a (spin (swap! runs update :a (fnil inc 0)) (throw (ex-info "a" {}))))
                      b (v2/with-key :b (spin (swap! runs update :b (fnil inc 0)) (await gate)))]
                  (swap! ids conj (mapv rid [a b]))
                  (try (await-all [a b]) (catch Exception e (ex-message e)))))
        u (v2/observe! c (fn [_ _]))]
    (is (= "a" (now c)))
    (v2/deliver! gate :go)
    (is (h/wait-until #(= 2 (count @ids))) "the loser's settle restarted the list")
    (is (= "a" (now c)))
    (is (apply = @ids))
    (is (= {:a 1 :b 1} @runs))
    (u)))

(deftest a-key-missing-from-the-restarted-run-stays-a-prefix-creation
  ;; the keys come from a host atom the list does not track. Model B11: T12
  ;; releases only the adoption basis; prefix creations stay in the basis
  (let [w v2/*world*
        ks (atom [1 2 3])
        sel (v2/signal 1)
        runs (atom {}) ids (atom [])
        c (spin (let [xs (vec (deref ks))
                      hs (selected xs sel runs)]
                  (swap! ids conj (into {} (map (fn [x hd] [x (rid hd)]) xs hs)))
                  (await-all hs)))
        u (v2/observe! c (fn [_ _]))]
    (is (= [[1 true] [2 false] [3 false]] (now c)))
    (reset! ks [3 1])
    (v2/write! sel 3)
    (is (= [[3 true] [1 false]] (now c)))
    (let [[before after] @ids
          a (adoption w c)]
      (is (= (dissoc before 2) after) "the remaining keys keep their rows")
      (is (= {1 1 2 1 3 1} @runs))
      (is (= (set (vals before)) (:basis a)) "the missing key's row stays in the basis, once")
      (is (empty? (:adopt a))))
    (u)))

(deftest a-fork-adopts-keyed-prefix-creations-from-its-copy
  ;; the restarted run parks on the take between its two keyed creations: :a
  ;; is readopted, :b still waits for its readoption when the world forks
  (let [w v2/*world*
        sel (v2/signal :a)
        mb (v2/mailbox)
        ids (atom [])
        c (spin (let [a (v2/with-key :a (spin (= :a (iv/get-new (track sel)))))
                      _ (take! mb)
                      b (v2/with-key :b (spin (= :b (iv/get-new (track sel)))))]
                  (swap! ids conj [(rid a) (rid b)])
                  (await-all [a b])))
        u (v2/observe! c (fn [_ _]))]
    (v2/post! mb :go)
    (is (= [true false] (now c)))
    (v2/write! sel :b)
    (let [child (v2/fork! w)
          cc (v2/in-world child c)
          uc (v2/observe! cc (fn [_ _]))]
      (v2/post! mb :go)
      (is (= [false true] (now c)))
      (v2/post! (v2/in-world child mb) :go)
      (is (= [false true] (now cc)))
      (is (= 3 (count @ids)) "the first run, the parent's restart and the fork's")
      (is (apply = @ids) "each world readopts :b from its own copy")
      (is (= (set (first @ids)) (:basis (adoption w c))))
      (is (= [] (v2/call-in! child #(verify/key-violations child))))
      (uc)
      (v2/release-world! child))
    (u)))

;; ---------------------------------------------------------------------------
;; Z#83: a creation that rejects a predecessor kept in the basis by a restart
;; from the body moves it to the adoption basis: the run's completion releases
;; it, the next cut drops it. A fresh non-scalar capture is never identical,
;; so such a creation rejects its predecessor on every restart.

(defn- rejecting
  "A list that creates one entity with `(make v)`, `v` = `(capture)` taken in
   each run (a fresh vector, or a changed scalar: each run rejects the last
   run's entity), then a keyed item tracking `sel`, and awaits the item (a
   group await: a change of the item restarts the list from its body).
   Records the entity ids in `made`."
  [sel capture made make]
  (spin (let [v (capture)
              e (make v)
              i (v2/with-key :i (spin (iv/get-new (track sel))))]
          (swap! made conj (rid e))
          (await-all [i]))))

(defn- fin-task
  "A task that captures `v`, parks forever and counts its finalizer in `fins`."
  [v never fins]
  (task (try (identity v) (await never) (finally (swap! fins inc)))))

(defn- rows-of
  "The ids in `ids` that still have a row in `w`."
  [w ids]
  (let [p (proj w)]
    (vec (filter #(or (get-in p [:tasks %]) (get-in p [:sources %]) (get-in p [:comps %])) ids))))

(deftest a-rejected-prefix-predecessor-is-released-at-the-completion
  (doseq [[label make tasks? captures] [["keyed task" (fn [v never fins] (v2/with-key :t (fin-task v never fins))) true [:fresh :scalar]]
                                        ["positional task" (fn [v never fins] (fin-task v never fins)) true [:fresh :scalar]]
                                        ["keyed sequence" (fn [v _ _] (v2/with-key :q (aseq [n 0] [v (inc n)]))) false [:fresh :scalar]]
                                        ["keyed source of another kind"
                                         (fn [v _ _] (v2/with-key :s (if (odd? v) (v2/mailbox) (v2/signal 0)))) false [:scalar]]]
          capture captures]
    (testing (str label ", " (name capture) " capture")
      (let [w v2/*world*
            sel (v2/signal 1)
            never (v2/deferred)
            gen (atom 0) made (atom []) fins (atom 0)
            c (rejecting sel (if (= capture :fresh) #(vector 1) #(swap! gen inc)) made #(make % never fins))
            u (v2/observe! c (fn [_ _]))]
        (is (= [1] (now c)))
        (v2/write! sel 2)
        (is (= [2] (now c)))
        (let [[e1 e2] @made]
          (is (not= e1 e2) "the restart rejected the predecessor")
          (when tasks? (is (h/wait-until #(= 1 @fins)) "the completion cancelled it"))
          (verify/gc-settle! w)
          (is (= [e2] (rows-of w [e1 e2])) "and released it")
          (is (= #{} (:adopt (adoption w c)))))
        (v2/rerun! c)
        (is (= [2] (now c)))
        (when tasks? (is (h/wait-until #(= 2 @fins)) "the full rerun's completion cancelled the next one"))
        (u)
        (when tasks? (is (h/wait-until #(= 3 @fins)) "unobserved: the last one is cancelled"))
        (verify/gc-settle! w)
        (is (= [] (rows-of w @made)) "nothing is left")))))

(deftest a-cut-during-the-restarted-run-drops-the-rejected-predecessor
  ;; the restarted run parks on the take after rejecting; rerun! cuts it
  (let [w v2/*world*
        sel (v2/signal 1)
        never (v2/deferred)
        mb (v2/mailbox)
        made (atom []) fins (atom 0)
        c (spin (let [cfg (vector 1)
                      t (v2/with-key :t (fin-task cfg never fins))
                      i (v2/with-key :i (spin (iv/get-new (track sel))))]
                  (swap! made conj (rid t))
                  (take! mb)
                  (await-all [i])))
        u (v2/observe! c (fn [_ _]))]
    (v2/post! mb :go)
    (is (= [1] (now c)))
    (v2/write! sel 2)
    (is (h/wait-until #(= 2 (count @made))) "the restart rejected the predecessor and parked")
    (is (= #{(first @made)} (:adopt (adoption w c))) "the rejected predecessor is in the adoption basis")
    (v2/rerun! c)
    (is (h/wait-until #(= 3 (count @made))))
    (is (h/wait-until #(= 1 @fins)) "the cut dropped it: cancelled")
    (v2/post! mb :go)
    (is (= [2] (now c)))
    (is (h/wait-until #(= 2 @fins)) "the completion released the parked run's task")
    (u)
    (is (h/wait-until #(= 3 @fins)))
    (verify/gc-settle! w)
    (is (= [] (rows-of w @made)))))

(deftest repeated-restarts-keep-one-generation-running
  (doseq [keyed? [true false]]
    (testing (if keyed? "keyed" "positional")
      (let [sel (v2/signal 0)
            never (v2/deferred)
            made (atom []) fins (atom 0)
            c (rejecting sel #(vector 1) made #(if keyed? (v2/with-key :t (fin-task % never fins)) (fin-task % never fins)))
            u (v2/observe! c (fn [_ _]))]
        (is (= [0] (now c)))
        (doseq [k (range 1 6)]
          (v2/write! sel k)
          (is (= [k] (now c))))
        (is (= 6 (count (set @made))))
        (is (h/wait-until #(= 5 @fins)) "each completion cancelled the rejected generation")
        (u)
        (is (h/wait-until #(= 6 @fins)))))))

(deftest a-fork-releases-its-copy-of-a-rejected-predecessor
  ;; the world forks while the restarted run is parked after the rejection
  ;; (the keyed predecessor still waits to leave the basis)
  (let [w v2/*world*
        sel (v2/signal 1)
        never (v2/deferred)
        mb (v2/mailbox)
        made (atom []) fins (atom 0)
        c (spin (let [cfg (vector 1)
                      t (v2/with-key :t (fin-task cfg never fins))
                      i (v2/with-key :i (spin (iv/get-new (track sel))))]
                  (swap! made conj (rid t))
                  (take! mb)
                  (await-all [i])))
        u (v2/observe! c (fn [_ _]))]
    (v2/post! mb :go)
    (is (= [1] (now c)))
    (v2/write! sel 2)
    (is (h/wait-until #(= 2 (count @made))))
    (let [[t1 t2] @made
          child (v2/fork! w)
          cc (v2/in-world child c)
          uc (v2/observe! cc (fn [_ _]))
          cadoption #(let [x (get-in (v2/call-in! child (fn [] (verify/projection child))) [:comps (hid w c)])]
                       {:basis (set (map first (:basis x))) :adopt (set (get-in x [:adoption :basis]))})]
      (is (contains? (:adopt (cadoption)) t1) "the fork inherits it in the adoption basis")
      (is (not (contains? (:basis (cadoption)) t1)))
      (is (contains? (:basis (cadoption)) t2))
      (v2/post! (v2/in-world child mb) :go)
      (is (= [2] (now cc)))
      (is (not (contains? (:basis (cadoption)) t1)) "the fork's completion released it")
      (is (= #{} (:adopt (cadoption))))
      (is (= [] (v2/call-in! child #(verify/key-violations child))))
      (is (contains? (:adopt (adoption w c)) t1) "the parent's copy still waits")
      (v2/post! mb :go)
      (is (= [2] (now c)))
      (is (= #{} (:adopt (adoption w c))))
      (is (not (contains? (:basis (adoption w c)) t1)))
      (uc)
      (v2/release-world! child))
    (u)))

(deftest a-restart-readopts-duplicate-keys-by-their-counts
  ;; sol: n = 0 and 1 of one (site, K) in the kept prefix
  (let [sel (v2/signal 1)
        runs (atom []) ids (atom [])
        c (spin (let [hs (loop [i 0 acc []]
                           (if (= i 2)
                             acc
                             (recur (inc i) (conj acc (v2/with-key :k (spin (swap! runs conj i) i))))))
                      s (v2/with-key :s (spin (iv/get-new (track sel))))]
                  (swap! ids conj (mapv rid hs))
                  (await-all (conj hs s))))
        u (v2/observe! c (fn [_ _]))]
    (is (= [0 1 1] (now c)))
    (v2/write! sel 2)
    (is (= [0 1 2] (now c)))
    (is (= 2 (count @ids)) "the restart")
    (is (apply = @ids) "n = 0 and n = 1 readopt their own rows")
    (is (= 2 (count (set (first @ids)))))
    (is (= [0 1] @runs))
    (u)))
