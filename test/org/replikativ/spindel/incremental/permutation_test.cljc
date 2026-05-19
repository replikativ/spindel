(ns org.replikativ.spindel.incremental.permutation-test
  "Property tests for the symmetric-group operations on permutations.

   These tests pin the four group laws (closure, associativity,
   identity, inverse) plus the action `arrange` on vectors. The
   sparse-map representation in `permutation.cljc` is correct iff all
   of these hold."
  (:refer-clojure :exclude [cycle])
  #?(:clj
     (:require [clojure.test :refer [deftest is testing]]
               [clojure.test.check.clojure-test :refer [defspec]]
               [clojure.test.check.generators :as gen]
               [clojure.test.check.properties :as prop]
               [org.replikativ.spindel.incremental.permutation :as p])
     :cljs
     (:require [cljs.test :refer-macros [deftest is testing]]
               [clojure.test.check.clojure-test :refer-macros [defspec]]
               [clojure.test.check.generators :as gen]
               [clojure.test.check.properties :as prop :include-macros true]
               [org.replikativ.spindel.incremental.permutation :as p])))

;; =============================================================================
;; Hand-written sanity tests
;; =============================================================================

(deftest constructors
  (testing "identity-perm? recognises the identity"
    (is (p/identity-perm? {}))
    (is (p/identity-perm? nil))
    (is (not (p/identity-perm? {0 1, 1 0}))))
  (testing "transposition"
    (is (= {} (p/transposition 3 3)))
    (is (= {0 1, 1 0} (p/transposition 0 1))))
  (testing "rotation"
    ;; move element at position 0 to position 2 — the rest shift back
    (is (= {0 2, 1 0, 2 1} (p/rotation 0 2)))
    ;; move element at position 2 to position 0 — the rest shift forward
    (is (= {2 0, 0 1, 1 2} (p/rotation 2 0)))
    (is (= {} (p/rotation 5 5))))
  (testing "split-swap"
    ;; Swap two adjacent ranges [0,2) and [2,5): first slides up by 3,
    ;; second slides down by 2.
    (is (= {0 3, 1 4, 2 0, 3 1, 4 2} (p/split-swap 0 2 3)))
    (is (= {} (p/split-swap 0 0 5)))
    (is (= {} (p/split-swap 0 5 0))))
  (testing "cycle"
    (is (= {} (p/cycle)))
    (is (= {} (p/cycle 5)))
    (is (= {0 1, 1 0} (p/cycle 0 1)))
    ;; cycle 0→1→2→0 means: position 0's element goes to 1, 1's to 2, 2's to 0
    (is (= {0 1, 1 2, 2 0} (p/cycle 0 1 2)))))

(deftest arrange-basics
  (testing "arrange on identity is no-op"
    (is (= [:a :b :c] (p/arrange {} [:a :b :c])))
    (is (= [:a :b :c] (p/arrange nil [:a :b :c]))))
  (testing "arrange swap"
    (is (= [:b :a :c] (p/arrange (p/transposition 0 1) [:a :b :c]))))
  (testing "arrange rotation"
    ;; move element at 0 to position 2: result is [b c a d]
    (is (= [:b :c :a :d] (p/arrange (p/rotation 0 2) [:a :b :c :d])))))

(deftest decompose-cycles
  (is (= [] (p/decompose-cycles {})))
  (testing "single transposition"
    (let [cs (p/decompose-cycles (p/transposition 0 1))]
      ;; cycle starting from 0: 0 → 1 → (back to 0). length 2.
      (is (= 1 (count cs)))
      (is (= #{0 1} (set (first cs))))))
  (testing "rotation as one cycle"
    (let [cs (p/decompose-cycles (p/rotation 0 2))]
      (is (= 1 (count cs)))
      (is (= #{0 1 2} (set (first cs))))))
  (testing "two disjoint transpositions decompose to two cycles"
    (let [perm (merge (p/transposition 0 1) (p/transposition 5 6))
          cs   (p/decompose-cycles perm)]
      (is (= 2 (count cs)))
      (is (= #{#{0 1} #{5 6}} (into #{} (map set) cs))))))

;; =============================================================================
;; Generator
;; =============================================================================

(def gen-perm
  "Generate a random permutation on `[0, n)` for small n, in sparse-map
   canonical form (fixed points omitted)."
  (gen/let [n    (gen/choose 0 12)
            shuf (gen/shuffle (range n))]
    (let [m (into {} (map vector (range n) shuf))]
      (into {} (remove (fn [[k v]] (= k v))) m))))

;; =============================================================================
;; Group laws — every property below pins one law of the symmetric group
;; =============================================================================

(defspec compose-closure 200
  ;; Closure: composing two permutations yields a permutation in
  ;; canonical form. Since we omit fixed points, "canonical" means no
  ;; (k, k) entries.
  (prop/for-all [a gen-perm
                 b gen-perm]
                (every? (fn [[k v]] (not= k v)) (p/compose a b))))

(defspec compose-associative 200
  (prop/for-all [a gen-perm
                 b gen-perm
                 c gen-perm]
                (= (p/compose (p/compose a b) c)
                   (p/compose a (p/compose b c)))))

(defspec compose-identity-left 200
  (prop/for-all [perm gen-perm]
                (= perm (p/compose {} perm))))

(defspec compose-identity-right 200
  (prop/for-all [perm gen-perm]
                (= perm (p/compose perm {}))))

(defspec inverse-is-group-inverse 200
  (prop/for-all [perm gen-perm]
                (and (= {} (p/compose perm (p/inverse perm)))
                     (= {} (p/compose (p/inverse perm) perm)))))

;; =============================================================================
;; Action on vectors
;; =============================================================================

(defspec arrange-then-inverse-is-id 200
  ;; The group action: `arrange (inverse p) (arrange p v) = v`.
  ;; Establishes that the permutation acts correctly on concrete vectors.
  (prop/for-all [perm gen-perm]
                (let [bound (if (empty? perm) 0 (apply max (concat (keys perm) (vals perm))))
                      v     (vec (range (inc bound)))]
                  (= v (p/arrange (p/inverse perm) (p/arrange perm v))))))

(defspec arrange-respects-compose 200
  ;; Functorality: `arrange (compose p q) v = arrange p (arrange q v)`.
  ;; This is the *crucial* property — it's the bridge between the
  ;; algebra (compose) and the action (arrange).
  (prop/for-all [a gen-perm
                 b gen-perm]
                (let [bound (max (if (empty? a) 0 (apply max (concat (keys a) (vals a))))
                                 (if (empty? b) 0 (apply max (concat (keys b) (vals b)))))
                      v     (vec (range (inc bound)))]
                  (= (p/arrange (p/compose a b) v)
                     (p/arrange a (p/arrange b v))))))
