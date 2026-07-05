(ns org.replikativ.spindel.incremental.interval
  "Interval abstraction for incremental computation.

   An interval represents a segment of change with:
   - old: Value at start of interval (baseline)
   - new: Value at end of interval (current)
   - deltas: Structural changes during the interval

   This is the core abstraction for incremental/reactive programming.
   Combinators consume intervals and produce intervals, enabling
   O(delta) computation through the pipeline.

   Key concepts:
   - Signals produce intervals on each change
   - Combinators transform intervals incrementally
   - commit: End current interval, new becomes old, deltas cleared

   The interval abstraction unifies:
   - SignalDeltaView (old/new/delta from signals)
   - DeltaableVector/Map/Set (collections with deltas)
   - Plain values (wrapped with nil old/deltas = static)

   Usage:
     (let [todos (track todos-signal)]  ; Returns interval
       (->> todos
            (filter active?)             ; Interval -> Interval
            (map :hours)                 ; Interval -> Interval
            (reduce + 0)))               ; Interval -> scalar

   Delta contract — three states for `:deltas`
   --------------------------------------------

   Every producer that emits an interval must distinguish three cases:

     :deltas nil  — \"I don't know what changed; treat `new` as opaque\"
                    Consumers fall back to full recompute.

     :deltas []   — \"I verified — nothing changed\"
                    Consumers skip work and keep their cached output.
                    Use `unchanged` to construct, `no-change?` to test.

     :deltas […]  — \"These specific things changed\"
                    Consumers apply only those deltas.

   `nil` vs `[]` is a real semantic distinction — `nil` is uncertainty,
   `[]` is a definitive empty answer. Combinators MUST NOT conflate
   them via `(seq deltas)` alone; check explicitly with `no-change?`
   when you want to short-circuit. Producers that have verified there
   are no changes (e.g. by diffing) should emit `[]`, not `nil`."
  (:require [org.replikativ.spindel.incremental.deltaable :as d]
            [org.replikativ.spindel.incremental.algebra :as a]))

;; =============================================================================
;; Protocol: Interval (old/new/deltas unified abstraction)
;; =============================================================================

(defprotocol PInterval
  "Protocol for interval values that expose old, new, and deltas.

   This is the core abstraction for incremental computation.
   Every value in the reactive pipeline can implement this protocol."

  (get-old [this]
    "Returns the value at the start of this interval (baseline).
     nil for initial values or static values.")

  (get-new [this]
    "Returns the current value (end of interval).")

  (get-deltas [this]
    "Returns sequence of structural deltas during this interval.
     nil or [] for no changes.")

  (has-deltas? [this]
    "Returns true if there are pending deltas.")

  (commit [this]
    "End the current interval: new becomes old, deltas are cleared.
     Returns a new interval representing the committed state."))

;; =============================================================================
;; Interval Record - Explicit interval wrapper
;; =============================================================================

;; Note: We don't use defrecord because we need custom ILookup behavior
;; for :old, :new, :deltas keys (not the field names old-value, new-value, deltas)
(deftype Interval [old-value new-value deltas]
  PInterval
  (get-old [_] old-value)
  (get-new [_] new-value)
  (get-deltas [_] deltas)
  (has-deltas? [_] (boolean (seq deltas)))
  (commit [_]
    (Interval. new-value new-value nil))

  #?(:clj clojure.lang.IDeref :cljs IDeref)
  (#?(:clj deref :cljs -deref) [_]
    new-value)

  #?(:clj clojure.lang.ILookup :cljs ILookup)
  (#?(:clj valAt :cljs -lookup) [_ k]
    (case k
      :old old-value
      :new new-value
      :delta deltas
      :deltas deltas
      nil))
  (#?(:clj valAt :cljs -lookup) [_ k not-found]
    (case k
      :old old-value
      :new new-value
      :delta deltas
      :deltas deltas
      not-found))

  ;; Support sequential destructuring: [new old deltas]
  ;; This enables backward compatibility with old combinator tests
  #?(:clj clojure.lang.Indexed :cljs IIndexed)
  (#?(:clj nth :cljs -nth) [_ i]
    (case (int i)
      0 new-value
      1 old-value
      2 deltas
      (throw (#?(:clj IndexOutOfBoundsException. :cljs js/Error.)
              (str "Index " i " out of bounds for Interval (0-2)")))))
  (#?(:clj nth :cljs -nth) [_ i not-found]
    (case (int i)
      0 new-value
      1 old-value
      2 deltas
      not-found))

  #?(:clj clojure.lang.Counted :cljs ICounted)
  (#?(:clj count :cljs -count) [_] 3)

  Object
  (toString [_]
    (str "#Interval{:old " (pr-str old-value)
         " :new " (pr-str new-value)
         " :deltas " (pr-str deltas) "}"))
  (equals [_ other]
    (and (instance? Interval other)
         (= old-value (.-old-value ^Interval other))
         (= new-value (.-new-value ^Interval other))
         (= deltas (.-deltas ^Interval other))))
  (hashCode [_]
    (hash [old-value new-value deltas])))

;; =============================================================================
;; Constructor Functions
;; =============================================================================

(defn interval
  "Create an interval with old, new, and deltas.

   Examples:
     (interval nil [1 2 3] nil)           ; Initial value, no old
     (interval [1 2] [1 2 3] [{:delta :add :value 3}])  ; With change"
  ([new-value]
   (->Interval nil new-value nil))
  ([old-value new-value]
   (->Interval old-value new-value nil))
  ([old-value new-value deltas]
   (->Interval old-value new-value deltas)))

(defn interval?
  "Returns true if x implements PInterval."
  [x]
  (satisfies? PInterval x))

;; =============================================================================
;; Delta contract helpers
;; =============================================================================

(defn typed-interval-map?
  "True when `x` is a Clojure map carrying the typed-interval shape
   (`:algebra`, `:old`, `:new`, `:deltas`). Typed-interval maps are
   produced by the new combinators (`map*`, `filter*`, …) and by
   typed_combinators.cljc (`izip*`, `iflat-map*`). They satisfy
   `PInterval` via the map extension below — so consumers reading via
   `get-new` / `get-old` / `get-deltas` work uniformly across the
   legacy `Interval` deftype and the new typed maps.

   Records are excluded: typed-interval maps are plain maps, and
   records may not implement `-contains-key?` (datahike's CLJS AsOfDB
   throws on it — probing a record here rejected the consuming spin and
   froze the UI at the last resolved frame)."
  [x]
  (and (map? x) (not (record? x)) (contains? x :algebra)))

(defn no-change?
  "True when this interval explicitly reports 'nothing changed'.

   Two cases:

   1. **Typed interval** (`(typed-interval-map? iv)` is true): we ask
      the interval's algebra whether its deltas are the algebra's
      identity element. If so AND `:old = :new`, the interval is
      verified-no-change.

   2. **Legacy interval / deltaable**: the historical convention is
      `:deltas []` AND `:old = :new`. The two-part check
      disambiguates verified-no-change from \"I happen to have no
      deltas right now\" (which an `as-interval`-coerced freshly-
      cleared collection can produce).

   Use this in combinators to short-circuit: when input is
   `no-change?`, the consumer can return its cached output unchanged.
   See the namespace doc for the full three-state delta contract."
  [iv]
  (let [old (get-old iv)
        new (get-new iv)
        d (get-deltas iv)]
    (and (= old new)
         (cond
           ;; Typed interval: dispatch through the algebra's empty?
           ;; predicate. No cycle: algebra.cljc has no requires, so
           ;; interval → algebra is a clean forward edge.
           (typed-interval-map? iv)
           (boolean (a/empty-deltas? (:algebra iv) d))

           ;; Legacy: deltas must be a non-nil empty sequential.
           :else
           (and (some? d) (not (seq d)))))))

(defn unchanged
  "Construct an interval declaring 'nothing changed' — `:old = :new = value`,
   `:deltas = []` (the empty-deltas form of the contract).

   This is the canonical 'no-op' interval. Combinators receiving it
   should keep their cached output and emit another `unchanged` (or
   equivalent) downstream so the no-change signal propagates."
  [value]
  (->Interval value value []))

;; =============================================================================
;; Coercion: Make any value usable as an interval
;; =============================================================================

(defn as-interval
  "Coerce a value to an interval.

   - Interval type: returned as-is
   - Typed-interval map (has :algebra): returned as-is — its
     IPersistentMap extension of PInterval already exposes
     get-old/get-new/get-deltas.
   - Deltaable collections: wrapped with old=nil, deltas from collection
   - Plain values: wrapped with old=nil, no deltas (static)

   This enables natural Clojure-like code where plain values
   are automatically usable in incremental pipelines."
  [x]
  (cond
    ;; Already an Interval type (not just satisfies PInterval, since Object extends it)
    (instance? Interval x)
    x

    ;; Typed-interval map produced by the new combinators — already
    ;; satisfies PInterval via the IPersistentMap extension. Pass
    ;; through unchanged. (Record guard lives in the predicate — see
    ;; typed-interval-map?.)
    (typed-interval-map? x)
    x

    ;; Deltaable collection - extract its deltas
    ;; Check this BEFORE Object-based PInterval extension kicks in
    (d/deltaable? x)
    (->Interval nil @x (d/get-deltas x))

    ;; Plain value - wrap as static (no old, no deltas)
    :else
    (->Interval nil x nil)))

(defn as-interval-with-old
  "Coerce a value to an interval, using prev as the old value.

   This is used when we have a previous result to compare against.

   Args:
     prev - Previous interval (or nil for initial)
     current - Current value (any type)"
  [prev current]
  (let [old-val (when prev (get-new prev))
        new-val (if (satisfies? PInterval current)
                  (get-new current)
                  current)
        deltas (cond
                 ;; Current has its own deltas
                 (and (satisfies? PInterval current) (has-deltas? current))
                 (get-deltas current)

                 ;; Deltaable with deltas
                 (and (d/deltaable? current) (d/has-deltas? current))
                 (d/get-deltas current)

                 ;; Compute diff if old != new
                 (and old-val (not= old-val new-val))
                 [{:delta :replace :old-value old-val :value new-val}]

                 ;; No change
                 :else
                 nil)]
    (->Interval old-val new-val deltas)))

;; =============================================================================
;; Extend PInterval to existing types
;; =============================================================================

;; Extend to DeltaableVector - use its deltas, derive old from deref
;; Note: DeltaableVector doesn't track old internally, so old is nil
;; The spin/signal system provides old via as-interval-with-old

#?(:clj
   (extend-protocol PInterval
     ;; Maps with an `:algebra` key are typed intervals; read their
     ;; fields directly. Plain maps (no `:algebra`) fall through to
     ;; the Object extension as a static value.
     clojure.lang.IPersistentMap
     (get-old [this] (if (contains? this :algebra) (:old this) this))
     (get-new [this] (if (contains? this :algebra) (:new this) this))
     (get-deltas [this] (when (contains? this :algebra) (:deltas this)))
     (has-deltas? [this] (and (contains? this :algebra)
                              (boolean (seq (:deltas this)))))
     (commit [this]
       (if (contains? this :algebra)
         (assoc this :old (:new this) :deltas nil)
         this))

     ;; Default for all objects - treat as static value
     Object
     (get-old [_] nil)
     (get-new [this] this)
     (get-deltas [_] nil)
     (has-deltas? [_] false)
     (commit [this] this)

     nil
     (get-old [_] nil)
     (get-new [_] nil)
     (get-deltas [_] nil)
     (has-deltas? [_] false)
     (commit [_] nil)))

#?(:cljs
   (extend-protocol PInterval
     PersistentArrayMap
     (get-old [this] (if (contains? this :algebra) (:old this) this))
     (get-new [this] (if (contains? this :algebra) (:new this) this))
     (get-deltas [this] (when (contains? this :algebra) (:deltas this)))
     (has-deltas? [this] (and (contains? this :algebra)
                              (boolean (seq (:deltas this)))))
     (commit [this]
       (if (contains? this :algebra)
         (assoc this :old (:new this) :deltas nil)
         this))

     PersistentHashMap
     (get-old [this] (if (contains? this :algebra) (:old this) this))
     (get-new [this] (if (contains? this :algebra) (:new this) this))
     (get-deltas [this] (when (contains? this :algebra) (:deltas this)))
     (has-deltas? [this] (and (contains? this :algebra)
                              (boolean (seq (:deltas this)))))
     (commit [this]
       (if (contains? this :algebra)
         (assoc this :old (:new this) :deltas nil)
         this))

     default
     (get-old [_] nil)
     (get-new [this] this)
     (get-deltas [_] nil)
     (has-deltas? [_] false)
     (commit [this] this)

     nil
     (get-old [_] nil)
     (get-new [_] nil)
     (get-deltas [_] nil)
     (has-deltas? [_] false)
     (commit [_] nil)))

;; =============================================================================
;; Interval Operations
;; =============================================================================

(defn changed?
  "Returns true if the interval represents a change (has old and differs from new)."
  [interval]
  (let [old (get-old interval)
        new (get-new interval)]
    (and (some? old)
         (not= old new))))

(defn static?
  "Returns true if the interval is static (no old, no deltas)."
  [interval]
  (and (nil? (get-old interval))
       (not (has-deltas? interval))))

(defn derive-interval
  "Create a derived interval for combinator output.

   Given the previous output (from spin cache) and the new computed value,
   creates an interval where:
   - old = prev.new (what we computed last time)
   - new = computed value
   - deltas = provided deltas or computed from diff

   Args:
     prev-output - Previous interval (from spin cache), or nil
     new-value - Newly computed value
     deltas - Explicit deltas, or nil to compute from diff"
  [prev-output new-value deltas]
  (let [old-val (when prev-output (get-new prev-output))]
    (->Interval old-val new-value deltas)))

;; =============================================================================
;; Interval Merging (CRDT-like Associative Operation)
;; =============================================================================

(defn merge-intervals
  "Merge two intervals, preserving full delta history.

   This is an associative semigroup operation for intervals:
   - old: Use first interval's old (preserved even if nil - represents baseline)
   - new: Use newest new (second interval's new)
   - deltas: Concatenate and compact both delta sequences

   This enables accumulating intervals during rate-controlled observation.
   When a signal changes faster than an observer can process, intermediate
   deltas can be accumulated using this function.

   Associativity: merge(merge(a, b), c) = merge(a, merge(b, c))

   Args:
     acc-interval - Accumulated interval (or nil for first value)
     new-interval - New interval to merge

   Returns: Merged interval with combined deltas

   Example:
     ;; Signal changes A→B→C before observer runs
     ;; Interval 1: {:old A :new B :deltas [A→B]}
     ;; Interval 2: {:old B :new C :deltas [B→C]}
     ;; Merged:     {:old A :new C :deltas [A→B B→C]} (compacted)"
  [acc-interval new-interval]
  (if (nil? acc-interval)
    new-interval
    (let [;; Always use acc-interval's old - it's the original baseline
          ;; (nil is a valid old value meaning "no previous state")
          old-val (get-old acc-interval)
          new-val (get-new new-interval)
          acc-deltas (get-deltas acc-interval)
          new-deltas (get-deltas new-interval)
          ;; Merge deltas: concatenate and compact to remove redundant ops
          merged-deltas (when (or acc-deltas new-deltas)
                          (d/compact-deltas
                           (concat acc-deltas new-deltas)))]
      (->Interval old-val new-val merged-deltas))))
