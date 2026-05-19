(ns org.replikativ.spindel.incremental.map-algebra
  "Delta algebra for keyed maps.

   A map delta is a single record with three fields:

     {:assoc  {k v   …}  ;; key → whole new value (no inner delta)
      :dissoc #{k    …}  ;; key removed
      :update {k {:algebra A_inner :delta Δ_inner} …}}

   Each field describes one kind of change to the map at the key level.

   Application order — fixed and load-bearing:

       dissoc → assoc → update

   Reasoning:
     - `dissoc` removes keys first. A subsequent `assoc` at the same key
       is a fresh put (the prior value was already gone).
     - `assoc` places whole new values. Cheap, no inner-algebra
       dispatch.
     - `update` modifies existing values via an inner-algebra delta.
       The inner value must already be present (i.e. the key wasn't
       dissoc'd in this same delta, and an `assoc` at the same key
       would have replaced it — see canonicalisation in compose).

   Algebraic structure
   -------------------
   The map deltas under composition form a monoid: associative,
   identity = `empty-deltas`, no inverse (`:dissoc` is irreversible
   without prior state).

   The carrier is non-free: many syntactically distinct deltas have
   the same observable effect (e.g. `{:dissoc #{k} :assoc {k v}}` ≡
   `{:assoc {k v}}`). `compose-deltas` produces a canonical form via
   per-key folding; equality of canonical deltas is decidable by
   Clojure map equality.

   Inner-delta semantics
   ---------------------
   The `:update` field's value `{:algebra A :delta Δ}` carries the
   inner algebra inline (the nested-deltas encoding). Composition
   recurses one level into the inner algebra's `compose-deltas` when
   the same key is `:update`d twice; application recurses one level
   into the inner algebra's `apply-deltas`.

   Element relations (`state-diff`, `merge`) accept a `:value-algebra`
   in the relations map that names the algebra to use for inner values
   when diffing or merging. Without it, the algebra defaults to
   scalar-algebra (whole-value replacement). With it, the diff
   produces `:update` entries with proper inner deltas."
  (:require [clojure.set :as set]
            [org.replikativ.spindel.incremental.algebra :as a]))

;; =============================================================================
;; Construction helpers
;; =============================================================================

(defn diff
  "Build a map delta. All fields optional; defaults are the identity
   for each. Producers should use this rather than constructing the map
   literal directly so that absent fields are always normalised to
   their empty values."
  [{:keys [assoc dissoc update]
    :or   {assoc {} dissoc #{} update {}}}]
  {:assoc assoc :dissoc dissoc :update update})

(defn nested-entry
  "Build an `:update` entry: `{:algebra A :delta Δ}`."
  [algebra delta]
  {:algebra algebra :delta delta})

(defn- empty-diff [] {:assoc {} :dissoc #{} :update {}})

(defn- empty-diff? [d]
  (and (zero? (count (:assoc d)))
       (zero? (count (:dissoc d)))
       (zero? (count (:update d)))))

;; =============================================================================
;; Apply
;; =============================================================================

(defn- apply-pipeline [m d]
  (let [m1 (reduce (fn [acc k] (dissoc acc k)) m (:dissoc d))
        m2 (reduce-kv (fn [acc k v] (assoc acc k v)) m1 (:assoc d))
        m3 (reduce-kv
            (fn [acc k inner]
              (let [inner-alg (:algebra inner)
                    inner-delta (:delta inner)]
                (if-some [current (get acc k)]
                  (assoc acc k (a/apply-deltas inner-alg current inner-delta))
                  ;; Updating a missing key is a noop in this design.
                  ;; Producers should never emit such a delta; the
                  ;; conservative response is to skip rather than throw.
                  acc)))
            m2 (:update d))]
    m3))

;; =============================================================================
;; Compose
;;
;; Given d1 (m → m') and d2 (m' → m''), produce d (m → m'') in canonical form.
;; Per-key case analysis is exhaustive across the cross product of
;; {assoc, dissoc, update, absent} for d1 × d2.
;; =============================================================================

(defn- compose-pair [d1 d2]
  (let [a1 (:assoc d1) a2 (:assoc d2)
        d1-dissoc (:dissoc d1) d2-dissoc (:dissoc d2)
        u1 (:update d1) u2 (:update d2)
        ;; All keys touched by either side. Iterating once over this
        ;; set is enough to canonicalise.
        keys-touched (-> #{}
                         (into (keys a1)) (into (keys a2))
                         (into d1-dissoc) (into d2-dissoc)
                         (into (keys u1)) (into (keys u2)))]
    (reduce
     (fn [acc k]
       (cond
         ;; d2 dissoc wins: key is dropped regardless of what d1 did.
         (contains? d2-dissoc k)
         (-> acc
             (update :dissoc conj k)
             (update :assoc dissoc k)
             (update :update dissoc k))

         ;; d2 assoc wins: key now has d2's value. Any d1 dissoc/update is
         ;; superseded; any d1 assoc is overwritten.
         (contains? a2 k)
         (-> acc
             (update :assoc assoc k (a2 k))
             (update :dissoc disj k)
             (update :update dissoc k))

         ;; d2 update on this key.
         (contains? u2 k)
         (let [{a-inner :algebra d-inner :delta} (u2 k)]
           (cond
             ;; d1 had an assoc on k: fold update into a new assoc by
             ;; applying the inner delta to d1's asserted value.
             (contains? a1 k)
             (update acc :assoc assoc k
                     (a/apply-deltas a-inner (a1 k) d-inner))

             ;; d1 had an update on k with the same inner algebra:
             ;; compose the inner deltas.
             (and (contains? u1 k)
                  (identical? (:algebra (u1 k)) a-inner))
             (update acc :update assoc k
                     (nested-entry a-inner
                                   (a/compose-deltas a-inner
                                                     (:delta (u1 k))
                                                     d-inner)))

             ;; d1 had an update with a DIFFERENT algebra — invalid
             ;; composition. Keep d2's update as the canonical answer
             ;; (last writer wins on inner-algebra disagreement); the
             ;; condition in practice indicates a producer bug and
             ;; will surface in property tests.
             (contains? u1 k)
             (update acc :update assoc k (u2 k))

             ;; d1 dissoc'd this key — update is meaningless on a
             ;; removed key. Drop d2's update but preserve d1's dissoc;
             ;; the key has to stay gone after composition.
             (contains? d1-dissoc k)
             (update acc :dissoc conj k)

             ;; d1 did nothing on k: pass d2's update through.
             :else
             (update acc :update assoc k (u2 k))))

         ;; d2 did nothing on k: pass d1's action through.
         :else
         (cond
           (contains? a1 k)        (update acc :assoc assoc k (a1 k))
           (contains? d1-dissoc k) (update acc :dissoc conj k)
           (contains? u1 k)        (update acc :update assoc k (u1 k))
           :else                   acc)))
     (empty-diff)
     keys-touched)))

;; =============================================================================
;; State diff
;; =============================================================================

(defn- state-diff-naive
  "First-tier state-diff: per-key analysis. Without a `:value-algebra` in
   relations, every changed key becomes an `:assoc` (atomic put).
   With a `:value-algebra` (the algebra that should be used for inner
   values), changed keys that already exist on both sides become
   `:update` entries with inner-state-diff'd deltas."
  [a b relations]
  (let [a-keys (set (keys a))
        b-keys (set (keys b))
        removed (set/difference a-keys b-keys)
        added   (set/difference b-keys a-keys)
        common  (set/intersection a-keys b-keys)
        value-alg (:value-algebra relations)
        eq-fn (get relations :eq-fn =)
        assoc-from-added (into {} (map (fn [k] [k (b k)])) added)
        ;; For keys present in both: either skip (equal), produce :update
        ;; (when a value-algebra is supplied), or produce :assoc (no value
        ;; algebra → atomic replacement).
        [assoc-from-changed update-from-changed]
        (reduce
         (fn [[a-acc u-acc] k]
           (let [va (a k) vb (b k)]
             (cond
               (eq-fn va vb)        [a-acc u-acc]
               (some? value-alg)    [a-acc (assoc u-acc k
                                                  (nested-entry
                                                   value-alg
                                                   (a/state-diff value-alg va vb relations)))]
               :else                [(assoc a-acc k vb) u-acc])))
         [{} {}] common)]
    {:assoc  (merge assoc-from-added assoc-from-changed)
     :dissoc removed
     :update update-from-changed}))

;; =============================================================================
;; Algebra instance
;; =============================================================================

(defrecord MapAlgebra []
  a/DeltaAlgebra
  (-apply-deltas [_ m d] (apply-pipeline m d))
  (-compose-deltas [_ d1 d2] (compose-pair d1 d2))
  (-empty-deltas [_ _context] (empty-diff))

  a/DeltaAlgebraEmpty?
  (-empty-deltas? [_ d] (empty-diff? d))

  a/StateDiffable
  (-state-diff [_ a b relations] (state-diff-naive a b relations))

  a/Mergeable
  (-merge-states [_ a b _relations]
    ;; Last-write-wins union at the key level. CRDT-shaped maps (OR-Map
    ;; with per-key tombstones) plug in via their own algebra; this is
    ;; the structural baseline.
    (merge a b)))

(def map-algebra
  "Singleton `MapAlgebra` instance. Use as the algebra for any reactive
   value that is a Clojure map at the level of structural change."
  (->MapAlgebra))
