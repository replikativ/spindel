(ns org.replikativ.spindel.incremental.algebra-test
  "Property-based tests for the typed-delta-algebra foundation.

   Covers:
   - Algebra laws (identity, associativity, application-soundness)
     applied to ScalarAlgebra.
   - State-diff round-trip: `(apply a (state-diff a b)) = b`.
   - Merge-states default behaviour.

   These tests are the *acceptance suite* for every future algebra
   instance (sequence, set, map, counter, LWW). When you add a new
   algebra, copy the four `defspec` skeletons below and instantiate
   them for that algebra. If the new algebra fails any property, it
   doesn't satisfy the monoid laws and shouldn't be used."
  #?(:clj
     (:require [clojure.test :refer [deftest is testing]]
               [clojure.test.check :as tc]
               [clojure.test.check.clojure-test :refer [defspec]]
               [clojure.test.check.generators :as gen]
               [clojure.test.check.properties :as prop]
               [org.replikativ.spindel.incremental.algebra :as a])
     :cljs
     (:require [cljs.test :refer-macros [deftest is testing]]
               [clojure.test.check :as tc]
               [clojure.test.check.clojure-test :refer-macros [defspec]]
               [clojure.test.check.generators :as gen]
               [clojure.test.check.properties :as prop :include-macros true]
               [org.replikativ.spindel.incremental.algebra :as a])))

;; =============================================================================
;; ScalarAlgebra: hand-written sanity tests
;; =============================================================================

(deftest scalar-apply-basics
  (testing "apply-deltas on no-change returns old"
    (is (= 42 (a/apply-deltas a/scalar-algebra 42 (a/empty-deltas a/scalar-algebra)))))
  (testing "apply-deltas on replace returns new"
    (is (= :bar (a/apply-deltas a/scalar-algebra :foo (a/scalar-replace :bar)))))
  (testing "apply-deltas on invalid delta throws"
    (is (thrown? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
                 (a/apply-deltas a/scalar-algebra :foo {:malformed true})))))

(deftest scalar-compose-basics
  (let [a a/scalar-algebra
        nc (a/empty-deltas a)]
    (testing "compose with empty is identity (left and right)"
      (let [d (a/scalar-replace :x)]
        (is (= d (a/compose-deltas a d nc)))
        (is (= d (a/compose-deltas a nc d)))))
    (testing "compose of two replaces takes the later one"
      (is (= (a/scalar-replace :b)
             (a/compose-deltas a (a/scalar-replace :a) (a/scalar-replace :b)))))
    (testing "compose with no args returns empty"
      (is (= nc (a/compose-deltas a))))
    (testing "variadic compose left-folds"
      (is (= (a/scalar-replace :c)
             (a/compose-deltas a
                               (a/scalar-replace :a)
                               (a/scalar-replace :b)
                               (a/scalar-replace :c)))))))

(deftest scalar-empty?-basics
  (let [a a/scalar-algebra]
    (is (a/empty-deltas? a (a/empty-deltas a)))
    (is (not (a/empty-deltas? a (a/scalar-replace :x))))))

(deftest scalar-state-diff-basics
  (let [a a/scalar-algebra]
    (testing "equal states → no-change"
      (is (a/empty-deltas? a (a/state-diff a 42 42))))
    (testing "different states → replace delta"
      (is (= (a/scalar-replace :b) (a/state-diff a :a :b))))
    (testing "custom :eq-fn"
      ;; treat strings case-insensitively
      (let [eq-ci (fn [x y] (= (clojure.string/lower-case x)
                               (clojure.string/lower-case y)))]
        (is (a/empty-deltas? a (a/state-diff a "FOO" "foo" {:eq-fn eq-ci})))
        (is (not (a/empty-deltas? a (a/state-diff a "FOO" "bar" {:eq-fn eq-ci}))))))))

(deftest scalar-merge-basics
  (let [a a/scalar-algebra]
    ;; Scalar merge is last-write-wins on the second argument.
    (is (= :b (a/merge-states a :a :b)))
    (is (= :a (a/merge-states a :b :a)))))

;; =============================================================================
;; Generators
;; =============================================================================

(def gen-scalar
  "Arbitrary scalar values for property tests. Includes nil, bools,
   keywords, strings, numbers — small set, hashable, comparable."
  (gen/one-of [gen/small-integer
               gen/string-alphanumeric
               gen/keyword
               (gen/return nil)
               (gen/return true)
               (gen/return false)]))

(def gen-scalar-delta
  "A scalar delta is either no-change or a `[::replace v]` carrying any
   scalar value."
  (gen/one-of [(gen/return (a/empty-deltas a/scalar-algebra))
               (gen/fmap a/scalar-replace gen-scalar)]))

;; =============================================================================
;; Algebra laws — ScalarAlgebra
;;
;; These four properties are what makes a delta algebra correct. Every
;; future algebra instance gets the same four (parameterised by their
;; generator + value type). The combinator-level invariants from the
;; conceptual doc reduce to these algebra laws.
;; =============================================================================

(defspec scalar-apply-identity 200
  ;; Law 1: apply(t, id) = t for all t
  (prop/for-all [v gen-scalar]
                (= v (a/apply-deltas a/scalar-algebra v (a/empty-deltas a/scalar-algebra)))))

(defspec scalar-compose-identity 200
  ;; Law: compose(d, id) = d  and  compose(id, d) = d
  (prop/for-all [d gen-scalar-delta]
                (and (= d (a/compose-deltas a/scalar-algebra d (a/empty-deltas a/scalar-algebra)))
                     (= d (a/compose-deltas a/scalar-algebra (a/empty-deltas a/scalar-algebra) d)))))

(defspec scalar-compose-associativity 200
  ;; Law: compose(compose(a, b), c) = compose(a, compose(b, c))
  (prop/for-all [d1 gen-scalar-delta
                 d2 gen-scalar-delta
                 d3 gen-scalar-delta]
                (= (a/compose-deltas a/scalar-algebra (a/compose-deltas a/scalar-algebra d1 d2) d3)
                   (a/compose-deltas a/scalar-algebra d1 (a/compose-deltas a/scalar-algebra d2 d3)))))

(defspec scalar-apply-composition 200
  ;; Law: apply(t, compose(d1, d2)) = apply(apply(t, d1), d2)
  ;; This is the *crucial* property — it's what makes deltas a valid
  ;; representation of state transitions.
  (prop/for-all [v gen-scalar
                 d1 gen-scalar-delta
                 d2 gen-scalar-delta]
                (= (a/apply-deltas a/scalar-algebra v (a/compose-deltas a/scalar-algebra d1 d2))
                   (a/apply-deltas a/scalar-algebra
                                   (a/apply-deltas a/scalar-algebra v d1)
                                   d2))))

(defspec scalar-state-diff-round-trip 200
  ;; Law: apply(a, state-diff(a, b)) = b for all a, b
  ;; This makes state-diff a section of apply — given any two states,
  ;; we can always recover a delta that takes us from one to the other.
  (prop/for-all [a-val gen-scalar
                 b-val gen-scalar]
                (= b-val (a/apply-deltas a/scalar-algebra
                                         a-val
                                         (a/state-diff a/scalar-algebra a-val b-val)))))

(defspec scalar-empty?-detection 200
  ;; Law: empty-deltas? detects exactly the identity element.
  ;; Anything constructed by compose-deltas of all-empty inputs is
  ;; itself empty; any explicit replace delta is not.
  (prop/for-all [d gen-scalar-delta]
                (let [is-empty? (a/empty-deltas? a/scalar-algebra d)
                      equal-to-empty? (= d (a/empty-deltas a/scalar-algebra))]
                  (= is-empty? equal-to-empty?))))
