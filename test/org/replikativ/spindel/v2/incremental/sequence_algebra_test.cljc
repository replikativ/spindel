(ns org.replikativ.spindel.v2.incremental.sequence-algebra-test
  "Property tests for `SequenceAlgebra`. Pins all four monoid laws plus
   the state-diff round-trip and the `empty-deltas?` predicate.

   See `algebra_test.cljc` for the same tests applied to ScalarAlgebra.
   Every future algebra instance should reuse this skeleton."
  #?(:clj
     (:require [clojure.test :refer [deftest is testing]]
               [clojure.test.check.clojure-test :refer [defspec]]
               [clojure.test.check.generators :as gen]
               [clojure.test.check.properties :as prop]
               [org.replikativ.spindel.incremental.algebra :as a]
               [org.replikativ.spindel.incremental.sequence-algebra :as sa])
     :cljs
     (:require [cljs.test :refer-macros [deftest is testing]]
               [clojure.test.check.clojure-test :refer-macros [defspec]]
               [clojure.test.check.generators :as gen]
               [clojure.test.check.properties :as prop :include-macros true]
               [org.replikativ.spindel.incremental.algebra :as a]
               [org.replikativ.spindel.incremental.sequence-algebra :as sa])))

(def ^:private alg sa/sequence-algebra)

;; =============================================================================
;; Hand-written sanity checks
;; =============================================================================

(deftest apply-basics
  (testing "Identity diff is a no-op"
    (is (= [:a :b :c]
           (a/apply-deltas alg [:a :b :c] (a/empty-deltas alg {:size 3})))))
  (testing "Grow + change populates the tail"
    (is (= [:a :b :c :tail]
           (a/apply-deltas alg [:a :b :c]
                           (sa/diff {:degree 4 :grow 1 :change {3 :tail}})))))
  (testing "Shrink drops the tail"
    (is (= [:a :b]
           (a/apply-deltas alg [:a :b :c]
                           (sa/diff {:degree 3 :shrink 1})))))
  (testing "Permutation reorders"
    ;; rotation 0 → 2 on [:a :b :c] yields [:b :c :a]
    (is (= [:b :c :a]
           (a/apply-deltas alg [:a :b :c]
                           (sa/diff {:degree 3
                                     :permutation {0 2, 1 0, 2 1}})))))
  (testing "Insert at head via grow + perm + change"
    (is (= [:NEW :a :b :c]
           (a/apply-deltas alg [:a :b :c]
                           (sa/diff {:degree 4 :grow 1
                                     :permutation {3 0, 0 1, 1 2, 2 3}
                                     :change {0 :NEW}}))))))

(deftest state-diff-shapes
  (testing "Identical vectors → empty diff"
    (let [d (a/state-diff alg [:a :b :c] [:a :b :c])]
      (is (a/empty-deltas? alg d))))
  (testing "Append → grow + change, no permutation needed"
    (let [d (a/state-diff alg [:a :b :c] [:a :b :c :d])]
      (is (= 1 (:grow d)))
      (is (zero? (:shrink d)))
      (is (empty? (:permutation d)))
      (is (= {3 :d} (:change d)))))
  (testing "Remove from tail → shrink, empty perm"
    (let [d (a/state-diff alg [:a :b :c :d] [:a :b :c])]
      (is (= 1 (:shrink d)))
      (is (zero? (:grow d)))
      (is (empty? (:permutation d)))))
  (testing "Remove entire vector → full shrink"
    (let [d (a/state-diff alg [:a :b :c] [])]
      (is (= 3 (:shrink d)))
      (is (= 0 (:grow d)))
      ;; After the canonicalisation fix: doomed items map src=i → tgt=i
      ;; (all fixed points), so the permutation is empty.
      (is (empty? (:permutation d))))))

;; =============================================================================
;; Generators
;; =============================================================================

(defn- gen-perm-of [n]
  (if (zero? n)
    (gen/return {})
    (gen/let [shuf (gen/shuffle (range n))]
      (into {} (remove (fn [[k v]] (= k v))) (map vector (range n) shuf)))))

(defn- gen-diff-for-size [size-in]
  (gen/let [grow   (gen/choose 0 4)
            shrink (gen/choose 0 (+ size-in grow))
            perm   (gen-perm-of (+ size-in grow))]
    (let [size-after (- (+ size-in grow) shrink)]
      (gen/let [ch-keys (if (zero? size-after)
                          (gen/return #{})
                          (gen/set (gen/choose 0 (dec size-after))))
                ch-vals (gen/vector gen/keyword (count ch-keys))
                fz      (if (zero? size-after)
                          (gen/return #{})
                          (gen/set (gen/choose 0 (dec size-after))))]
        (sa/diff {:degree      (+ size-in grow)
                  :grow        grow
                  :shrink      shrink
                  :permutation perm
                  :change      (zipmap ch-keys ch-vals)
                  :freeze      fz})))))

(def gen-pair
  "A starting vector + two composable diffs."
  (gen/let [n-A (gen/choose 0 6)
            v   (gen/vector gen/keyword n-A)
            d1  (gen-diff-for-size n-A)
            d2  (gen-diff-for-size (- (:degree d1) (:shrink d1)))]
    [v d1 d2]))

(def gen-triple
  "A starting vector + three composable diffs."
  (gen/let [n-A (gen/choose 0 5)
            v   (gen/vector gen/keyword n-A)
            d1  (gen-diff-for-size n-A)
            d2  (gen-diff-for-size (- (:degree d1) (:shrink d1)))
            d3  (gen-diff-for-size (- (:degree d2) (:shrink d2)))]
    [v d1 d2 d3]))

;; =============================================================================
;; Monoid laws — the four invariants from the conceptual design doc.
;;
;; Every algebra instance must satisfy these. The combinator-level
;; correctness theorems (in the conceptual doc §6) reduce to these.
;; =============================================================================

(defspec apply-identity 300
  ;; Law 1: apply(t, id) = t for all t.
  (prop/for-all [v (gen/vector gen/keyword 0 10)]
                (= v (a/apply-deltas alg v (a/empty-deltas alg {:size (count v)})))))

(def ^:private gen-single-diff
  (gen/let [n-A (gen/choose 0 6)
            d   (gen-diff-for-size n-A)]
    d))

(defspec compose-identity-right 300
  ;; Law: compose(d, id_after) = d.
  (prop/for-all [d gen-single-diff]
                (let [size-after (- (:degree d) (:shrink d))]
                  (= d (a/compose-deltas alg d (a/empty-deltas alg {:size size-after}))))))

(defspec compose-identity-left 300
  ;; Law: compose(id_before, d) = d.
  (prop/for-all [d gen-single-diff]
                (let [size-before (- (:degree d) (:grow d))]
                  (= d (a/compose-deltas alg (a/empty-deltas alg {:size size-before}) d)))))

(defspec apply-composition 500
  ;; Law: apply(v, compose(d1, d2)) = apply(apply(v, d1), d2).
  ;; This is the crucial one — it's what makes deltas a valid
  ;; representation of state transitions.
  (prop/for-all [[v d1 d2] gen-pair]
                (= (a/apply-deltas alg (a/apply-deltas alg v d1) d2)
                   (a/apply-deltas alg v (a/compose-deltas alg d1 d2)))))

(defspec compose-associative-by-effect 500
  ;; Law: compose is associative — at minimum, by effect on any
  ;; starting vector. (Syntactic associativity follows from a
  ;; canonical normal form, which we don't yet enforce post-compose.)
  (prop/for-all [[v d1 d2 d3] gen-triple]
                (= (a/apply-deltas alg v (a/compose-deltas alg (a/compose-deltas alg d1 d2) d3))
                   (a/apply-deltas alg v (a/compose-deltas alg d1 (a/compose-deltas alg d2 d3))))))

(defspec state-diff-round-trip 1000
  ;; Law: apply(a, state-diff(a, b)) = b for all vectors a, b.
  ;; Makes state-diff a section of apply — given any two states, we
  ;; can recover deltas that produce one from the other.
  (prop/for-all [a-v (gen/vector gen/keyword 0 8)
                 b-v (gen/vector gen/keyword 0 8)]
                (= b-v (a/apply-deltas alg a-v (a/state-diff alg a-v b-v)))))

(defspec empty?-detection 200
  ;; Law: empty-deltas? returns true exactly for the algebra's
  ;; identity element at the given size.
  (prop/for-all [n (gen/choose 0 10)]
                (and (a/empty-deltas? alg (a/empty-deltas alg {:size n}))
                     (not (a/empty-deltas? alg (if (pos? n)
                                                 (sa/diff {:degree n :change {0 :x}})
                                                 (sa/diff {:degree 1 :grow 1
                                                           :change {0 :x}})))))))

;; =============================================================================
;; Composition law cases (phase D review): delete→insert, move→delete,
;; change→move, and size-changing compositions.
;;
;; Each case is a chain of states s0 → s1 → s2 (→ s3). Every step's diff
;; must take its state to the next, and the composed diff must take s0 to
;; the last state directly. Diffs come from both producers: `keyed-seq-diff`
;; (identity by key, so moves are permutations) and `state-diff` (identity
;; by value, so a move may come out as changes — correct, not minimal).
;;
;; States are vectors of [key value] items; a "change" keeps the key and
;; replaces the value.
;; =============================================================================

(defn- keyed-diff
  "keyed-seq-diff between two states of [key value] items, or the identity
   diff when nothing changed (keyed-seq-diff returns nil then)."
  [prev new]
  (or (sa/keyed-seq-diff (mapv first new) (mapv first prev)
                         (into {} (map (juxt first identity)) new)
                         (into {} (map (juxt first identity)) prev)
                         =)
      (a/empty-deltas alg {:size (count prev)})))

(defn- value-diff [prev new]
  (a/state-diff alg prev new))

(defn- chain-holds?
  "True when every step diff of `states` (made by `diff-fn`) takes its state
   to the next, the left- and right-folded compositions both take the first
   state to the last, and composition with the identity on either side
   changes nothing."
  [diff-fn states]
  (let [steps (mapv diff-fn states (rest states))
        s0 (first states)
        sn (peek states)
        left (reduce #(a/compose-deltas alg %1 %2) steps)
        right (reduce #(a/compose-deltas alg %2 %1) (rseq steps))]
    (and (every? true? (map (fn [s d s'] (= s' (a/apply-deltas alg s d)))
                            states steps (rest states)))
         (= sn (a/apply-deltas alg s0 left))
         (= sn (a/apply-deltas alg s0 right))
         (= (count s0) (sa/size-before left))
         (= (count sn) (sa/size-after left))
         (= sn (a/apply-deltas alg s0 (a/compose-deltas
                                       alg (a/empty-deltas alg {:size (count s0)}) left)))
         (= sn (a/apply-deltas alg s0 (a/compose-deltas
                                       alg left (a/empty-deltas alg {:size (count sn)})))))))

(defn- items [& kvs] (mapv vec (partition 2 kvs)))

(def ^:private law-cases
  {"delete -> insert, middle"
   [(items :a 1 :b 2 :c 3 :d 4) (items :a 1 :c 3 :d 4) (items :a 1 :x 9 :c 3 :d 4)]
   "delete at head -> insert at tail"
   [(items :a 1 :b 2 :c 3) (items :b 2 :c 3) (items :b 2 :c 3 :x 9)]
   "delete at tail -> insert at head (grow after a shrink region)"
   [(items :a 1 :b 2 :c 3) (items :a 1 :b 2) (items :x 9 :a 1 :b 2)]
   "delete -> re-insert the same key elsewhere"
   [(items :a 1 :b 2 :c 3) (items :a 1 :c 3) (items :a 1 :c 3 :b 2)]
   "move -> delete the moved item"
   [(items :a 1 :b 2 :c 3 :d 4) (items :b 2 :c 3 :d 4 :a 1) (items :b 2 :c 3 :d 4)]
   "move -> delete another item"
   [(items :a 1 :b 2 :c 3 :d 4) (items :b 2 :c 3 :d 4 :a 1) (items :b 2 :d 4 :a 1)]
   "reverse -> delete head"
   [(items :a 1 :b 2 :c 3) (items :c 3 :b 2 :a 1) (items :b 2 :a 1)]
   "change -> move the changed item"
   [(items :a 1 :b 2 :c 3) (items :a 1 :b 20 :c 3) (items :b 20 :a 1 :c 3)]
   "change -> move another item"
   [(items :a 1 :b 2 :c 3) (items :a 10 :b 2 :c 3) (items :b 2 :c 3 :a 10)]
   "change -> swap two changed items"
   [(items :a 1 :b 2) (items :a 10 :b 20) (items :b 20 :a 10)]
   "grow -> shrink past the grown items"
   [(items :a 1 :b 2) (items :a 1 :b 2 :c 3 :d 4) (items :a 1)]
   "shrink to empty -> grow from empty"
   [(items :a 1 :b 2 :c 3) [] (items :x 9 :y 8)]
   "grow from empty -> shrink to empty"
   [[] (items :a 1 :b 2) []]
   "insert -> delete -> insert, net size change"
   [(items :a 1 :b 2) (items :a 1 :x 9 :b 2) (items :x 9 :b 2) (items :x 9 :b 2 :y 8 :z 7)]
   "delete two -> insert one -> move -> change"
   [(items :a 1 :b 2 :c 3 :d 4) (items :a 1 :d 4) (items :a 1 :x 9 :d 4)
    (items :d 4 :a 1 :x 9) (items :d 4 :a 1 :x 90)]})

(deftest composition-law-cases
  (doseq [[label states] law-cases]
    (testing label
      (is (chain-holds? keyed-diff states) "keyed-seq-diff")
      (is (chain-holds? value-diff states) "state-diff"))))

(deftest keyed-moves-are-permutations
  (testing "keyed-seq-diff expresses a move as a permutation alone: no grow,
            no shrink, no change. state-diff only promises a correct diff,
            not a minimal one, so it is not held to this."
    (let [s0 (items :a 1 :b 2 :c 3 :d 4)
          s1 (items :b 2 :c 3 :d 4 :a 1)
          d (keyed-diff s0 s1)]
      (is (zero? (:grow d)))
      (is (zero? (:shrink d)))
      (is (empty? (:change d)))
      (is (seq (:permutation d)))
      (is (= s1 (a/apply-deltas alg s0 (value-diff s0 s1)))))))

(def ^:private gen-keyed-state
  "A vector of [key value] items with distinct keys from a small pool and
   values from a small set, so consecutive states share keys and values."
  (gen/let [ks (gen/shuffle (range 6))
            n (gen/choose 0 6)
            vs (gen/vector (gen/elements [:p :q]) 6)]
    (mapv vector (take n ks) vs)))

(defspec keyed-diff-chain-composition 300
  ;; Arbitrary mixes of delete, insert, move and change across three steps.
  (prop/for-all [states (gen/vector gen-keyed-state 2 4)]
                (and (chain-holds? keyed-diff states)
                     (chain-holds? value-diff states))))

;; =============================================================================
;; nil and false keys (phase D decision: reject them)
;;
;; keyed-seq-diff assigns grown and doomed slots with `(filterv added
;; order)` and `(filterv removed prev-order)`: the key sets are the
;; predicates, so a nil or false key is a member that tests falsy and gets
;; no slot. The diff's permutation is then not a bijection. Phase D does not
;; teach the algebra these keys; callers reject them before diffing
;; (`ifor-each` throws ::invalid-key). These cases pin the edge: if
;; keyed-seq-diff ever handles them, revisit that decision.
;; =============================================================================

(defn- self-keyed-diff
  "keyed-seq-diff between two vectors of keys, each key its own value."
  [prev new]
  (sa/keyed-seq-diff new prev (zipmap new new) (zipmap prev prev) =))

(defn- bijective?
  "A sparse permutation (fixed points omitted) is a bijection exactly when
   it moves a set of positions onto itself."
  [perm]
  (= (set (keys perm)) (set (vals perm))))

(deftest nil-and-false-keys-are-outside-keyed-seq-diff
  (doseq [k [nil false]]
    (testing (str "key " (pr-str k) " added")
      (is (bijective? (:permutation (self-keyed-diff [:a :b] [:a :k :b])))
          "control: a truthy key")
      (is (not (bijective? (:permutation (self-keyed-diff [:a :b] [:a k :b]))))))
    (testing (str "key " (pr-str k) " removed")
      (is (bijective? (:permutation (self-keyed-diff [:a :k :b] [:a :b])))
          "control: a truthy key")
      (is (not (bijective? (:permutation (self-keyed-diff [:a k :b] [:a :b]))))))))
