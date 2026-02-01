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
            (reduce + 0)))               ; Interval -> scalar"
  (:require [org.replikativ.spindel.incremental.deltaable :as d]))

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
;; Coercion: Make any value usable as an interval
;; =============================================================================

(defn as-interval
  "Coerce a value to an interval.

   - Interval type: returned as-is
   - Deltaable collections: wrapped with old=nil, deltas from collection
   - Plain values: wrapped with old=nil, no deltas (static)

   This enables natural Clojure-like code where plain values
   are automatically usable in incremental pipelines."
  [x]
  (cond
    ;; Already an Interval type (not just satisfies PInterval, since Object extends it)
    (instance? Interval x)
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
