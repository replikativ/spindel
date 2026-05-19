(ns org.replikativ.spindel.incremental.map-algebra-test
  "Property tests for MapAlgebra plus lift/lower from `algebra.cljc`.
   Pins the four monoid laws, state-diff round-trip (both with and
   without `:value-algebra` relations), and the lift/lower inversion."
  #?(:clj
     (:require [clojure.set :as set]
               [clojure.test :refer [deftest is testing]]
               [clojure.test.check.clojure-test :refer [defspec]]
               [clojure.test.check.generators :as gen]
               [clojure.test.check.properties :as prop]
               [org.replikativ.spindel.incremental.algebra :as a]
               [org.replikativ.spindel.incremental.map-algebra :as ma])
     :cljs
     (:require [clojure.set :as set]
               [cljs.test :refer-macros [deftest is testing]]
               [clojure.test.check.clojure-test :refer-macros [defspec]]
               [clojure.test.check.generators :as gen]
               [clojure.test.check.properties :as prop :include-macros true]
               [org.replikativ.spindel.incremental.algebra :as a]
               [org.replikativ.spindel.incremental.map-algebra :as ma])))

(def ^:private alg ma/map-algebra)

;; =============================================================================
;; Hand-written sanity tests
;; =============================================================================

(deftest apply-pipeline-tests
  (testing "Empty delta is the identity"
    (is (= {:a 1 :b 2}
           (a/apply-deltas alg {:a 1 :b 2} (a/empty-deltas alg)))))
  (testing "Application order: dissoc → assoc → update"
    ;; Same key in dissoc and assoc: dissoc happens first, assoc replaces.
    (is (= {:a 99}
           (a/apply-deltas alg {:a 1}
                           (ma/diff {:dissoc #{:a} :assoc {:a 99}})))))
  (testing "Update on missing key is a no-op"
    (is (= {}
           (a/apply-deltas alg {}
                           (ma/diff {:update {:k (ma/nested-entry a/scalar-algebra
                                                                  (a/scalar-replace 1))}})))))
  (testing "Update modifies an existing value via the inner algebra"
    (is (= {:a 99}
           (a/apply-deltas alg {:a 1}
                           (ma/diff {:update {:a (ma/nested-entry a/scalar-algebra
                                                                  (a/scalar-replace 99))}}))))))

(deftest compose-canonicalisation
  (testing "compose folds (assoc k v1) then (update k inner) into (assoc k inner-of-v1)"
    (let [d1 (ma/diff {:assoc {:a 1}})
          d2 (ma/diff {:update {:a (ma/nested-entry a/scalar-algebra (a/scalar-replace 99))}})
          c (a/compose-deltas alg d1 d2)]
      (is (= {:a 99} (:assoc c)))
      (is (empty? (:update c)))))
  (testing "compose preserves d1's dissoc when d2 tries to update the same key"
    (let [d1 (ma/diff {:dissoc #{:x}})
          d2 (ma/diff {:update {:x (ma/nested-entry a/scalar-algebra (a/scalar-replace 1))}})
          c (a/compose-deltas alg d1 d2)]
      (is (contains? (:dissoc c) :x)
          "the key must stay gone after composition")
      (is (not (contains? (:update c) :x)))))
  (testing "compose collapses (dissoc k) then (assoc k v) into (assoc k v)"
    (let [d1 (ma/diff {:dissoc #{:x}})
          d2 (ma/diff {:assoc {:x 7}})
          c (a/compose-deltas alg d1 d2)]
      (is (= 7 (get-in c [:assoc :x])))
      (is (not (contains? (:dissoc c) :x))))))

(deftest state-diff-tests
  (testing "Identical maps yield empty delta"
    (is (a/empty-deltas? alg (a/state-diff alg {:a 1} {:a 1}))))
  (testing "Added key yields :assoc"
    (let [d (a/state-diff alg {:a 1} {:a 1 :b 2})]
      (is (= {:b 2} (:assoc d)))))
  (testing "Removed key yields :dissoc"
    (let [d (a/state-diff alg {:a 1 :b 2} {:a 1})]
      (is (= #{:b} (:dissoc d)))))
  (testing "Changed key yields :assoc (without value-algebra)"
    (let [d (a/state-diff alg {:a 1} {:a 2})]
      (is (= {:a 2} (:assoc d)))))
  (testing "Changed key with :value-algebra yields :update with inner delta"
    (let [d (a/state-diff alg {:a 1} {:a 2} {:value-algebra a/scalar-algebra})]
      (is (contains? (:update d) :a))
      (is (= (a/scalar-replace 2) (:delta (get (:update d) :a)))))))

(deftest lift-lower-tests
  (testing "lift produces nested :update envelopes"
    (let [d (a/lift [:users :admin :name] ma/map-algebra a/scalar-algebra
                    (a/scalar-replace :Z))
          ;; Walk one level deep manually.
          users-entry (get-in d [:update :users])
          admin-entry (get-in users-entry [:delta :update :admin])
          name-entry  (get-in admin-entry [:delta :update :name])]
      (is (identical? ma/map-algebra (:algebra users-entry)))
      (is (identical? ma/map-algebra (:algebra admin-entry)))
      (is (identical? a/scalar-algebra (:algebra name-entry)))
      (is (= (a/scalar-replace :Z) (:delta name-entry)))))
  (testing "lower is the inverse of lift"
    (let [delta (a/scalar-replace :Z)
          lifted (a/lift [:users :admin :name] ma/map-algebra a/scalar-algebra delta)
          [out-alg out-delta] (a/lower [:users :admin :name] lifted)]
      (is (identical? a/scalar-algebra out-alg))
      (is (= delta out-delta))))
  (testing "lower returns nil when the path is not present in the delta"
    (is (nil? (a/lower [:absent] (ma/diff {:assoc {:other 1}}))))
    (is (nil? (a/lower [:k :missing-inner]
                       (a/lift [:k] ma/map-algebra a/scalar-algebra
                               (a/scalar-replace 1)))))))

;; =============================================================================
;; Generators
;; =============================================================================

(def ^:private small-key (gen/elements [:a :b :c :d :e]))
(def ^:private gen-val gen/small-integer)
(def ^:private gen-map (gen/map small-key gen-val {:max-elements 4}))

(def ^:private gen-mdiff
  "Generate a *valid* map delta where the three fields don't conflict
   on the same key. This is what producers should emit; pathological
   diffs (same key in assoc + update) aren't part of the contract."
  (gen/let [k-assoc (gen/set small-key {:max-elements 3})
            v-assoc (gen/vector gen-val (count k-assoc))
            k-dissoc-raw (gen/set small-key {:max-elements 2})
            k-update-raw (gen/set small-key {:max-elements 2})
            v-update (gen/vector gen-val (count k-update-raw))]
    (let [assoc-map (zipmap k-assoc v-assoc)
          ;; Subtract assoc keys from both dissoc and update so the
          ;; fields are disjoint.
          dissoc-set (set/difference k-dissoc-raw k-assoc)
          update-keys (set/difference k-update-raw k-assoc dissoc-set)
          update-map (into {} (for [[k v] (map vector update-keys v-update)]
                                [k (ma/nested-entry a/scalar-algebra
                                                    (a/scalar-replace v))]))]
      (ma/diff {:assoc assoc-map :dissoc dissoc-set :update update-map}))))

;; =============================================================================
;; Monoid laws
;; =============================================================================

(defspec map-apply-identity 200
  (prop/for-all [m gen-map]
                (= m (a/apply-deltas alg m (a/empty-deltas alg)))))

(defspec map-compose-identity-right 200
  (prop/for-all [d gen-mdiff]
                (= d (a/compose-deltas alg d (a/empty-deltas alg)))))

(defspec map-compose-identity-left 200
  (prop/for-all [d gen-mdiff]
                (= d (a/compose-deltas alg (a/empty-deltas alg) d))))

(defspec map-apply-composition 500
  ;; The crucial property: applying d1 then d2 is the same as applying
  ;; the composed delta.
  (prop/for-all [m gen-map
                 d1 gen-mdiff
                 d2 gen-mdiff]
                (= (a/apply-deltas alg (a/apply-deltas alg m d1) d2)
                   (a/apply-deltas alg m (a/compose-deltas alg d1 d2)))))

(defspec map-compose-associative-by-effect 500
  (prop/for-all [m gen-map
                 d1 gen-mdiff
                 d2 gen-mdiff
                 d3 gen-mdiff]
                (= (a/apply-deltas alg m (a/compose-deltas alg (a/compose-deltas alg d1 d2) d3))
                   (a/apply-deltas alg m (a/compose-deltas alg d1 (a/compose-deltas alg d2 d3))))))

;; =============================================================================
;; state-diff
;; =============================================================================

(defspec map-state-diff-round-trip 500
  ;; apply(a, state-diff(a, b)) = b for any maps a, b.
  (prop/for-all [a-m gen-map
                 b-m gen-map]
                (= b-m (a/apply-deltas alg a-m (a/state-diff alg a-m b-m)))))

(defspec map-state-diff-nested-round-trip 200
  ;; Same property with a value-algebra in the relations map.
  (prop/for-all [a-m gen-map
                 b-m gen-map]
                (= b-m (a/apply-deltas alg a-m
                                       (a/state-diff alg a-m b-m
                                                     {:value-algebra a/scalar-algebra})))))

;; =============================================================================
;; lift/lower
;; =============================================================================

(defspec lift-lower-inverse 200
  ;; (lower p (lift p map-alg leaf-alg Δ)) = [leaf-alg Δ]
  (prop/for-all [path (gen/vector (gen/elements [:x :y :z]) 1 4)
                 v gen-val]
                (let [delta (a/scalar-replace v)
                      lifted (a/lift path ma/map-algebra a/scalar-algebra delta)
                      [out-alg out-delta] (a/lower path lifted)]
                  (and (identical? a/scalar-algebra out-alg)
                       (= delta out-delta)))))

(defspec lift-applies-as-update-in 200
  ;; Lifting a scalar delta and applying it to a map is observably the
  ;; same as `(update-in m path #(apply-deltas scalar-alg % Δ))`. This
  ;; is the lift's contract from algebra.cljc.
  (prop/for-all [path (gen/vector (gen/elements [:x :y :z]) 1 3)
                 old-val gen-val
                 new-val gen-val]
                (let [m (assoc-in {} path old-val)
                      delta (a/scalar-replace new-val)
                      lifted (a/lift path ma/map-algebra a/scalar-algebra delta)
                      result (a/apply-deltas alg m lifted)]
                  (= new-val (get-in result path)))))
