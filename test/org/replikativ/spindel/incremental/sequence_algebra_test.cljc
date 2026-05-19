(ns org.replikativ.spindel.incremental.sequence-algebra-test
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
