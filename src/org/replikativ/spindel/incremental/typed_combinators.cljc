(ns org.replikativ.spindel.incremental.typed-combinators
  "New combinators built directly on top of the typed delta algebra
   (`algebra.cljc`, `sequence_algebra.cljc`). These complement the
   list-comprehension primitives in `combinators.cljc` with two
   missing algebraic shapes:

   - `izip*`  — applicative product: combine N independent reactive
                values pointwise via a function. Without this,
                downstream consumers re-track every dependency inside
                their body, defeating fine-grained reactivity.
   - `iflat-map*` — monadic flatten: each source element expands to a
                sub-sequence; output is the concatenation. Without
                this, recursive-rendering use cases (tree-of-blocks
                etc.) flatten the tree externally and lose
                per-subtree incrementality.

   Both combinators consume *and* produce typed intervals — Clojure
   maps with `{:algebra :old :new :deltas}` keys. Maps interoperate
   with the existing `iv/Interval` deftype via `clojure.lang.ILookup`,
   so consumers reading `(iv/get-new …)` etc. work unchanged.

   Deltas under these combinators follow the new typed-algebra
   contract:
     - `izip*` emits scalar-algebra deltas (`::no-change` or
       `[::replace v]`).
     - `iflat-map*` emits sequence-algebra deltas (the 5-field
       `{:degree :grow :shrink :permutation :change :freeze}` map)
       computed via `state-diff` against the previous cached
       output's value.

   Caching pattern matches the existing `with-incremental-cache` in
   `combinators.cljc`: per source-loc address, the engine state holds
   the previous typed interval, and the new value is recomputed from
   source + cache."
  (:require [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.incremental.algebra :as a]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.incremental.sequence-algebra :as sa]))

;; =============================================================================
;; Caching scaffold (parallel to combinators.cljc but at a different key
;; prefix so the two namespaces don't collide on the same source-loc).
;; =============================================================================

(defn- typed-address
  "Stable address for a typed combinator. Keyed under `:typed-incremental`
   in the engine state so it doesn't collide with the legacy combinators'
   `:incremental` keyspace."
  [source-loc]
  (keyword (str "typed-" (:file source-loc) "-" (:line source-loc)
                "-" (:column source-loc))))

(defn- get-prev-output [addr]
  (ec/get-state [:typed-incremental addr]))

(defn- store-output! [addr output]
  (ec/swap-state! [:typed-incremental addr] (constantly output))
  output)

(defn- with-cache
  [source-loc compute-fn]
  (let [addr (typed-address source-loc)
        prev (get-prev-output addr)
        out  (compute-fn prev)]
    (store-output! addr out)
    out))

;; =============================================================================
;; izip*
;;
;; Applicative product over N scalar intervals. Given sources `[s₁ … sₙ]` and a
;; function `f`, produces a scalar interval whose `:new` is `(apply f (mapv
;; iv/get-new sources))`. Re-computes on every call (no per-source dedup), but
;; emits `::no-change` deltas if every source explicitly declares no-change AND
;; the cached output matches.
;; =============================================================================

(defn izip*
  "Internal implementation; see `izip` macro."
  [source-loc f sources]
  (with-cache source-loc
    (fn [prev-output]
      (let [ivs (mapv iv/as-interval sources)
            news (mapv iv/get-new ivs)
            new-val (apply f news)
            ;; prev-output is a typed-interval map (our own shape) — read
            ;; its `:new` directly. iv/get-new would hit the Object
            ;; extension and return the entire map back to us.
            prev-val (:new prev-output)
            all-no-change? (and prev-output
                                (every? iv/no-change? ivs))]
        (cond
          ;; All sources verified no-change → output is verified no-change.
          all-no-change?
          {:algebra a/scalar-algebra
           :old     prev-val
           :new     prev-val
           :deltas  (a/empty-deltas a/scalar-algebra)}

          ;; First run with no cached prev: emit a value with nil deltas
          ;; (consumer must recompute from :new).
          (nil? prev-output)
          {:algebra a/scalar-algebra :old nil :new new-val :deltas nil}

          ;; Value didn't actually change despite some source claiming a delta:
          ;; emit verified no-change (scalar empty).
          (= prev-val new-val)
          {:algebra a/scalar-algebra
           :old     prev-val
           :new     prev-val
           :deltas  (a/empty-deltas a/scalar-algebra)}

          ;; Real change: emit a scalar replace.
          :else
          {:algebra a/scalar-algebra
           :old     prev-val
           :new     new-val
           :deltas  (a/scalar-replace new-val)})))))

;; =============================================================================
;; iflat-map*
;;
;; Monadic flatten on sequences. `(iflat-map* sl body source)` where `body` is
;; `T → Seq U` produces an interval over the concatenation. First cut: compute
;; `:new` functionally (`(into [] (mapcat body) source-new)`), derive deltas via
;; `sequence-algebra/state-diff` against the cached `prev-new`. This is correct
;; and self-checking; per-element body memoisation is a future optimisation.
;;
;; Short-circuit: when the source declares verified no-change AND we have a
;; cached output, emit a sequence-algebra empty diff with `:old = :new` and
;; skip the body invocations.
;; =============================================================================

(defn iflat-map*
  "Internal implementation; see `iflat-map` macro."
  [source-loc body source]
  (with-cache source-loc
    (fn [prev-output]
      (let [source-iv (iv/as-interval source)
            source-new (iv/get-new source-iv)
            ;; Internal read of our typed-interval map — see comment in izip*.
            prev-new (:new prev-output)]
        (cond
          ;; Source verified no-change AND we have a cached output.
          ;; Verified-no-change downstream.
          (and prev-output (iv/no-change? source-iv))
          {:algebra sa/sequence-algebra
           :old     prev-new
           :new     prev-new
           :deltas  (a/empty-deltas sa/sequence-algebra
                                    {:size (count prev-new)})}

          :else
          (let [new-value (into [] (mapcat body) source-new)
                deltas (when prev-new
                         (a/state-diff sa/sequence-algebra prev-new new-value))]
            {:algebra sa/sequence-algebra
             :old     prev-new
             :new     new-value
             :deltas  deltas}))))))

;; =============================================================================
;; Macros — capture source-loc from caller for stable per-call-site addressing.
;; Mirrors the `imap`/`ifilter` pattern in `combinators.cljc` so users have
;; consistent ergonomics across the legacy and typed combinator surfaces.
;; =============================================================================

#?(:clj
   (defmacro izip
     "Applicative N-ary product over scalar reactive sources.

      Usage:
        (izip f source-1 source-2 …)
        (izip f sources-vec)   ; explicit vector form

      Each `source-i` is a scalar interval (or a plain value coerced via
      `as-interval`). Returns a scalar typed interval whose `:new` is
      `(f (:new source-1) (:new source-2) …)`. Emits scalar-algebra
      `::no-change` deltas when every source declares verified no-change."
     [f & sources]
     (let [meta-form (or (meta &form) {})
           source-loc {:file (or *file* "unknown")
                       :line (:line meta-form 0)
                       :column (:column meta-form 0)}
           sources-form (if (and (= 1 (count sources))
                                 (vector? (first sources)))
                          (first sources)
                          (vec sources))]
       `(izip* ~source-loc ~f ~sources-form))))

#?(:clj
   (defmacro iflat-map
     "Monadic flatten on a sequence reactive source.

      Usage:
        (iflat-map (fn [t] body…) source)

      `body` returns a vector / seq of zero or more output items per
      input. Output is the concatenation. Returns a sequence typed
      interval whose `:new` is `(into [] (mapcat body) (iv/get-new
      source))`. Deltas are derived via `state-diff` of the new value
      against the cached previous output."
     [body source]
     (let [meta-form (or (meta &form) {})
           source-loc {:file (or *file* "unknown")
                       :line (:line meta-form 0)
                       :column (:column meta-form 0)}]
       `(iflat-map* ~source-loc ~body ~source))))
