(ns org.replikativ.spindel.incremental.algebra
  "Typed delta algebras for incremental computation.

   A `DeltaAlgebra` is a *structural* description of how deltas compose
   and apply for a given value type. Each algebra forms a monoid:

     (D, ·, id)  with operations
       -apply-deltas    : T × D → T
       -compose-deltas  : D × D → D     (associative)
       -empty-deltas    :     → D       (identity for ·)

   subject to three laws:

     (Identity)     apply(t, id) = t
     (Application) apply(t, d₁ · d₂) = apply(apply(t, d₁), d₂)
     (Associativity) (d₁ · d₂) · d₃ = d₁ · (d₂ · d₃)

   This protocol is *purely structural* — it knows about positions,
   sizes, and deltas but nothing about element equality, identity, or
   ordering. Operations that need element-level semantics
   (`state-diff`, `merge-states`) are *separate* protocols whose methods
   accept an optional `relations` map ({:eq-fn :key-fn :tie-break …})
   carrying the element-relations.

   The three-state contract from `interval.cljc` continues to apply:

     :deltas nil        — \"I don't know what changed.\" Consumer recomputes.
     :deltas <empty-T>  — \"I verified no change.\" The algebra's identity
                          element, checked via `empty-deltas?`.
     :deltas <Δ…>       — \"These changes happened.\" Subject to the
                          delta-soundness invariant
                          `(apply old Δ) = new`.

   See the namespace docstrings of `sequence_algebra.cljc` and
   `map_algebra.cljc` for the concrete algebras and their delta shapes."
  (:refer-clojure :exclude [merge]))

;; =============================================================================
;; Core protocol: structural delta algebra
;; =============================================================================

(defprotocol DeltaAlgebra
  "Three methods that every delta algebra must implement. Element-level
   semantics live elsewhere — see `StateDiffable` and `Mergeable`."

  (-apply-deltas [algebra old deltas]
    "Apply `deltas` to `old`, returning the resulting value.

     Must satisfy the three laws stated in the namespace docstring.
     For verified-no-change input the result is `old` unchanged.")

  (-compose-deltas [algebra d1 d2]
    "Return a single delta equivalent to applying d1 then d2.

     Must be associative. Composing with the algebra's empty element
     (in either position) is the identity:
       (compose-deltas a (empty-deltas a (size-after d1))) = d1
       (compose-deltas a (empty-deltas a (size-before d2)) d2) = d2")

  (-empty-deltas [algebra context]
    "Return the algebra's identity element. `context` is an opaque map
     that algebras may consult — sequence reads `:size`; scalar and
     set ignore it. The minimum useful context is `{}`."))

(defprotocol DeltaAlgebraEmpty?
  "Predicate for the identity-element of a delta algebra. Kept as its
   own protocol (rather than derived from `compose-deltas`) for clarity
   and dispatch speed. An implementor must guarantee:
     (-empty-deltas? algebra (-empty-deltas algebra anything)) → true"

  (-empty-deltas? [algebra deltas]
    "True iff `deltas` is the algebra's identity element."))

;; =============================================================================
;; Optional protocols: element-relation-dependent operations
;; =============================================================================

(defprotocol StateDiffable
  "Algebras that can derive deltas from two states. Implementations may
   accept element relations via the `relations` map; absence means
   defaults (= for equality, identity for keys)."

  (-state-diff [algebra a b relations]
    "Return deltas d such that `(apply-deltas algebra a d) = b`.
     The result is best-effort: a correct but possibly verbose delta
     (e.g. `{:change {0 …, 1 …, …}}` for a sequence) is acceptable;
     implementations may use the relations map to produce a more
     precise diff."))

(defprotocol Mergeable
  "Algebras whose value type is a CRDT — i.e. forms a join-semilattice.
   Implementations must satisfy commutativity, associativity, and
   idempotence:
     (merge-states a x y) = (merge-states a y x)
     (merge-states a (merge-states a x y) z)
        = (merge-states a x (merge-states a y z))
     (merge-states a x x) = x"

  (-merge-states [algebra a b relations]
    "Semilattice join of states a and b. Throws for algebras whose
     value type is not a CRDT."))

;; =============================================================================
;; Top-level dispatch functions
;; =============================================================================

(defn apply-deltas
  "Apply `deltas` to `old` under the given `algebra`. See
   `DeltaAlgebra/-apply-deltas`."
  [algebra old deltas]
  (-apply-deltas algebra old deltas))

(defn compose-deltas
  "Compose two deltas under the given `algebra`. Associative; identity
   element is `(empty-deltas algebra …)`. Variadic for convenience:
   `(compose-deltas a)` is the empty delta; `(compose-deltas a d)` is `d`;
   `(compose-deltas a d1 d2 d3 …)` left-folds."
  ([algebra]
   (-empty-deltas algebra {}))
  ([_algebra d]
   d)
  ([algebra d1 d2]
   (-compose-deltas algebra d1 d2))
  ([algebra d1 d2 & more]
   (reduce #(-compose-deltas algebra %1 %2) (-compose-deltas algebra d1 d2) more)))

(defn empty-deltas
  "Return the identity element of `algebra` at the given context.
   `context` defaults to `{}` for algebras that don't care."
  ([algebra]
   (-empty-deltas algebra {}))
  ([algebra context]
   (-empty-deltas algebra context)))

(defn empty-deltas?
  "True iff `deltas` is the identity element of `algebra`."
  [algebra deltas]
  (-empty-deltas? algebra deltas))

(defn state-diff
  "Derive a delta that takes `a` to `b` under `algebra`. Optional
   `relations` map carries element-relations (`:eq-fn`, `:key-fn`).
   When omitted, defaults are: `:eq-fn` = `=`, `:key-fn` = `identity`.

   The result d satisfies `(apply-deltas algebra a d) = b`."
  ([algebra a b]
   (state-diff algebra a b nil))
  ([algebra a b relations]
   (-state-diff algebra a b (or relations {}))))

(defn merge-states
  "Semilattice join of `a` and `b` under `algebra`. Optional `relations`
   map carries element-relations (`:tie-break` for LWW-style joins,
   `:eq-fn`, …). Throws for algebras whose value type is not a CRDT."
  ([algebra a b]
   (merge-states algebra a b nil))
  ([algebra a b relations]
   (-merge-states algebra a b (or relations {}))))

;; =============================================================================
;; Scalar algebra
;; =============================================================================

;; A scalar delta is one of:
;;   ::no-change            — the identity element (verified no change)
;;   [::replace v]          — the new value replaces the old wholesale
;;
;; This vocabulary is the simplest non-trivial algebra. Most non-
;; collection combinator outputs (notably reducers) use it.
;;
;; The `::replace` tag is needed so that the wrapped value can itself
;; be `::no-change` without confusion — `[::replace ::no-change]` is
;; semantically distinct from `::no-change`. Equality across two
;; replace-deltas is decided by Clojure equality of their wrapped
;; values.

(def ^:private no-change ::no-change)

(defn- replace? [d]
  (and (vector? d)
       (= 2 (count d))
       (= ::replace (nth d 0))))

(defrecord ScalarAlgebra []
  DeltaAlgebra
  (-apply-deltas [_ old deltas]
    (cond
      (= no-change deltas) old
      (replace? deltas)    (nth deltas 1)
      :else (throw (ex-info "Invalid scalar delta"
                            {:deltas deltas :algebra :scalar}))))

  (-compose-deltas [_ d1 d2]
    ;; Last-write-wins: if d2 is no-change, d1 stands; otherwise d2.
    ;; Both no-change → no-change.
    (cond
      (= no-change d2) d1
      :else            d2))

  (-empty-deltas [_ _context] no-change)

  DeltaAlgebraEmpty?
  (-empty-deltas? [_ deltas] (= no-change deltas))

  StateDiffable
  (-state-diff [_ a b relations]
    (let [eq-fn (get relations :eq-fn =)]
      (if (eq-fn a b)
        no-change
        [::replace b])))

  Mergeable
  (-merge-states [_ _a b _relations]
    ;; Scalar merge is last-write-wins on the second argument. This is
    ;; *not* commutative in general — scalar isn't a CRDT — but we
    ;; provide it as a fallback so consumers can call `merge-states`
    ;; uniformly. CRDT-typed algebras (LWW-Register, GCounter) override
    ;; with proper commutative merges.
    b))

(def scalar-algebra
  "Singleton instance of `ScalarAlgebra`. Use this as the algebra for
   any reactive value with no internal structure (scalars, opaque
   records, anything where 'changed' is binary)."
  (->ScalarAlgebra))

;; =============================================================================
;; Helpers for testing and bridging
;; =============================================================================

(defn scalar-noop?
  "True iff `d` is the scalar algebra's identity element. Exposed for
   tests and for legacy code that needs to detect scalar no-change
   without going through the protocol."
  [d]
  (= no-change d))

(defn scalar-replace
  "Construct a scalar `::replace` delta carrying `v`. Exposed so test
   code and combinators can build deltas without knowing the encoding."
  [v]
  [::replace v])

;; =============================================================================
;; Path operations: lift and lower
;;
;; A *path* is a non-empty vector of keys descending through one or
;; more map-algebra levels. `lift` wraps an inner-algebra delta in a
;; series of map-algebra `:update` envelopes; `lower` navigates a
;; map-algebra delta back to a specific path.
;;
;; These are pure top-level functions (not protocol methods) because
;; the algebra at each *intermediate* level of a nested path is
;; map-algebra by construction — the only thing that varies is the
;; leaf inner-algebra. The path itself contains no algebra
;; information; the leaf algebra is supplied as a parameter to lift
;; and is reported back as the first element of lower's result.
;;
;; Sequence-nested paths (e.g. `[:users 3 :name]` where 3 is an index
;; into a sequence) are *not* handled here. Sequence-algebra's
;; `:change` field's values would need to gain a `(:nested algebra
;; delta)` variant before sequence-nested lift/lower works. That
;; widening is deferred. This file's lift/lower handles map-only
;; paths today.
;;
;; The map-algebra reference is supplied as a parameter so this file
;; does not need to require map_algebra.cljc (which would create a
;; cycle). Callers pass `map-algebra/map-algebra` as the
;; `map-alg` argument.
;; =============================================================================

(defn lift
  "Wrap `inner-delta` in `:update` envelopes for each key in `path`.

   path        — non-empty vector of map keys, root-to-leaf order
   map-alg     — the map algebra to use for intermediate levels
   leaf-alg    — the algebra of the deepest (leaf) inner-delta
   inner-delta — the delta at the leaf, in leaf-alg's vocabulary

   Returns a map-algebra delta in canonical form.

   Invariants (verified by property test):
     (apply-deltas map-alg m (lift p map-alg leaf-alg Δ))
       = (update-in m p #(apply-deltas leaf-alg % Δ))

     (lower p (lift p map-alg leaf-alg Δ)) = [leaf-alg Δ]"
  [path map-alg leaf-alg inner-delta]
  {:pre [(seq path)]}
  (let [last-key (peek path)
        leaf-update {:assoc {} :dissoc #{}
                     :update {last-key {:algebra leaf-alg :delta inner-delta}}}]
    ;; Walk outward from the leaf: at each step, wrap the current diff
    ;; in a map-algebra :update envelope keyed by the next-up path
    ;; element. The intermediate algebra at every step is map-alg.
    (loop [acc leaf-update
           remaining (pop path)]
      (if (empty? remaining)
        acc
        (recur {:assoc {} :dissoc #{}
                :update {(peek remaining) {:algebra map-alg :delta acc}}}
               (pop remaining))))))

(defn lower
  "Navigate a map-algebra delta to the inner delta at `path`.

   Returns `[leaf-alg inner-delta]` when the path resolves to an
   `:update` chain ending at a leaf. Returns `nil` when:
     - any step of the path is missing from the corresponding level's
       `:update` field (i.e. no incremental delta at that path)
     - any step encounters an `:assoc` or `:dissoc` instead of an
       `:update` (the sub-tree was wholesale replaced or removed; the
       caller can choose to reconstruct via state-diff)

   Inverse of `lift` for any path produced by `lift`:
     (lower p (lift p map-alg leaf-alg Δ)) = [leaf-alg Δ]"
  [path delta]
  {:pre [(seq path)]}
  (loop [d delta
         remaining path]
    (let [k (first remaining)
          rest-path (rest remaining)]
      (cond
        (nil? d) nil
        (contains? (:update d) k)
        (let [entry (get (:update d) k)
              inner-alg (:algebra entry)
              inner-d (:delta entry)]
          (if (empty? rest-path)
            [inner-alg inner-d]
            (recur inner-d rest-path)))

        :else nil))))
