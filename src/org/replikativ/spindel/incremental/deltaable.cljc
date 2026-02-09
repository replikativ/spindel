(ns org.replikativ.spindel.incremental.deltaable
  "Deltaable collections for incremental computation with SHALLOW wrapping.

   This namespace provides collections that track TOP-LEVEL changes as deltas:
   - IDeltaable: Protocol for delta tracking
   - IUnwrapDeltaable: Protocol for unwrapping deltaables to plain collections
   - DeltaableVector/Map/Set: Top-level wrappers with delta tracking
   - DeltaableValue: Simple value wrapper (no structural deltas)

   **IMPORTANT**: Deltaables only track TOP-LEVEL operations!
   - Nested collections remain plain (no deep wrapping)
   - For fine-grained tracking, use separate signals

   Note: This namespace defines delta transducer functions (map, filter, etc.)
   that shadow clojure.core functions. These are intended to transform delta
   streams, not regular collections. Use with namespace qualification: (d/map f)

   Usage:

   (let [dm (deltaable-map {:a 1 :users []})]
     (-> dm
         (assoc :b 2)              ; :add delta for :b
         (update :users conj \"Alice\"))  ; :update delta for :users (NOT for conj)
     (get-deltas dm))  ; => [{:delta :add :path [:b] :value 2}
                       ;;     {:delta :update :path [:users] :value [\"Alice\"] :old-value []}]"
  (:refer-clojure :exclude [map filter remove keep transduce])
  (:require [org.replikativ.spindel.incremental.deltaable.protocols :as proto]
            [org.replikativ.spindel.incremental.deltaable.vector :as dvec]
            [org.replikativ.spindel.incremental.deltaable.map :as dmap]
            [org.replikativ.spindel.incremental.deltaable.set :as dset])
  #?(:clj (:import [org.replikativ.spindel.incremental.deltaable.vector DeltaableVector]
                    [org.replikativ.spindel.incremental.deltaable.map DeltaableMap]
                    [org.replikativ.spindel.incremental.deltaable.set DeltaableSet])))

;; =============================================================================
;; Re-export protocols from deltaable.protocols
;; =============================================================================

(def PDeltaable proto/PDeltaable)
(def PWrapDeltaable proto/PWrapDeltaable)
(def PUnwrapDeltaable proto/PUnwrapDeltaable)

;; =============================================================================
;; Re-export constructors and helpers from sub-namespaces
;; =============================================================================

(def deltaable-vector dvec/deltaable-vector)
(def remove-at dvec/remove-at)
(def insert-at dvec/insert-at)
(def move-to dvec/move-to)
(def filter-vec dvec/filter-vec)
(def find-index dvec/find-index)
(def update-first-where dvec/update-first-where)
(def update-by-key dvec/update-by-key)
(def deltaable-map dmap/deltaable-map)
(def deltaable-map-with-deltas dmap/deltaable-map-with-deltas)
(def deltaable-set dset/deltaable-set)

;; =============================================================================
;; Simple Value Wrapper (No Structural Deltas)
;; =============================================================================

#?(:clj
   (defrecord DeltaableValue [v]
     proto/PDeltaable
     (get-deltas [_]
       "Simple values have no structural deltas"
       nil)
     (deltaable? [_]
       "DeltaableValue is not a deltaable collection"
       false)

     clojure.lang.IDeref
     (deref [_]
       "Deref returns the wrapped value"
       v))

   :cljs
   (defrecord DeltaableValue [v]
     proto/PDeltaable
     (get-deltas [_]
       "Simple values have no structural deltas"
       nil)
     (deltaable? [_]
       "DeltaableValue is not a deltaable collection"
       false)

     IDeref
     (-deref [_]
       "Deref returns the wrapped value"
       v)))

(defn deltaable-value
  "Create a DeltaableValue wrapper for simple values.

   This is used for numbers, strings, keywords, etc. that don't have
   structural deltas but need to be treated uniformly with collections."
  [v]
  (->DeltaableValue v))

;; Extend protocol to everything for uniform interface

(extend-protocol proto/PDeltaable
  #?(:clj Object :cljs default)
  (get-deltas [_]
    "Non-deltaable values return nil (no structural changes)"
    nil)
  (deltaable? [_]
    "Default: not a deltaable collection"
    false)

  nil
  (get-deltas [_]
    "nil has no deltas"
    nil)
  (deltaable? [_]
    "nil is not deltaable"
    false))

;; Helper Functions

(defn has-deltas?
  "Returns true if value has non-empty structural deltas.

   Returns false for:
   - nil
   - Non-deltaable values
   - Deltaable values with empty delta vector"
  [x]
  (seq (proto/get-deltas x)))

(defn unwrap
  "Unwrap a deltaable value to get the raw value.

   For DeltaableValue: returns the wrapped value
   For DeltaableVector/Map/Set: returns the collection itself
   For other values: returns as-is

  Note: SignalDeltaView unwrapping is handled by signal.cljc"
  [x]
  (cond
    (instance? DeltaableValue x) (.-v x)
    :else x))

;; =============================================================================
;; Print methods - avoid multimethod dispatch ambiguity
;; =============================================================================

#?(:clj
   (do
     (defmethod print-method DeltaableVector [dv ^java.io.Writer w]
       (.write w (str (.-v ^DeltaableVector dv))))
     (defmethod print-method DeltaableMap [dm ^java.io.Writer w]
       (.write w (str (.-m ^DeltaableMap dm))))
     (defmethod print-method DeltaableSet [ds ^java.io.Writer w]
       (.write w (str (.-s ^DeltaableSet ds))))))

;; =============================================================================
;; wrap-deltaable - Extend PWrapDeltaable for all types
;; =============================================================================

(extend-protocol proto/PWrapDeltaable
  ;; Deltaable collections return themselves unchanged
  #?(:clj DeltaableVector :cljs dvec/DeltaableVector)
  (wrap-deltaable [x] x)

  #?(:clj DeltaableMap :cljs dmap/DeltaableMap)
  (wrap-deltaable [x] x)

  #?(:clj DeltaableSet :cljs dset/DeltaableSet)
  (wrap-deltaable [x] x)

  #?@(:clj
      [;; Records: pass through unchanged (they may implement custom protocols)
       ;; IMPORTANT: This must come before IPersistentMap since records implement it
       clojure.lang.IRecord
       (wrap-deltaable [x] x)

       ;; Plain vectors: wrap shallowly (NO nested wrapping)
       clojure.lang.IPersistentVector
       (wrap-deltaable [x]
         (DeltaableVector. x [] nil))

       ;; Plain maps: wrap shallowly (NO nested wrapping)
       ;; Note: Records don't match this due to IRecord extension above
       clojure.lang.IPersistentMap
       (wrap-deltaable [x]
         (DeltaableMap. x [] nil))

       ;; Plain sets: wrap shallowly (NO nested wrapping)
       clojure.lang.IPersistentSet
       (wrap-deltaable [x]
         (DeltaableSet. x [] nil))]

      :cljs
      [;; Plain vectors: wrap shallowly (NO nested wrapping)
       cljs.core/PersistentVector
       (wrap-deltaable [x]
         (dvec/DeltaableVector. x [] nil))

       ;; Plain maps: wrap shallowly (NO nested wrapping)
       cljs.core/PersistentArrayMap
       (wrap-deltaable [x]
         (dmap/DeltaableMap. x [] nil))

       cljs.core/PersistentHashMap
       (wrap-deltaable [x]
         (dmap/DeltaableMap. x [] nil))

       ;; Plain sets: wrap shallowly (NO nested wrapping)
       cljs.core/PersistentHashSet
       (wrap-deltaable [x]
         (dset/DeltaableSet. x [] nil))])

  ;; Default: return unchanged (scalars, records, etc.)
  #?(:clj Object :cljs default)
  (wrap-deltaable [x] x)

  nil
  (wrap-deltaable [_] nil))

(defn wrap-nested
  "DEPRECATED: Shallow wrapping doesn't need wrap-nested anymore.

   This function is kept for backwards compatibility but now just
   calls wrap-deltaable without path parameter.

   With shallow wrapping architecture, nested collections are NOT wrapped.
   Only use this if you explicitly want to wrap a value as top-level deltaable."
  [x path]
  (proto/wrap-deltaable x))

(defn clear-deltas
  "Return a copy of deltaable collection with deltas cleared (O(1) operation).

   This creates a new deltaable with the same inner value but empty delta vector.
   Since we use shallow wrapping, this is O(1) - just creates new wrapper.
   Used by the runtime after propagating deltas to observers."
  [deltaable]
  (cond
    (instance? #?(:clj DeltaableVector :cljs dvec/DeltaableVector) deltaable)
    #?(:clj  (DeltaableVector. (.-v ^DeltaableVector deltaable) [] (.-_meta ^DeltaableVector deltaable))
       :cljs (dvec/DeltaableVector. (.-v deltaable) [] (.-_meta deltaable)))

    (instance? #?(:clj DeltaableMap :cljs dmap/DeltaableMap) deltaable)
    #?(:clj  (DeltaableMap. (.-m ^DeltaableMap deltaable) [] (.-_meta ^DeltaableMap deltaable))
       :cljs (dmap/DeltaableMap. (.-m deltaable) [] (.-_meta deltaable)))

    (instance? #?(:clj DeltaableSet :cljs dset/DeltaableSet) deltaable)
    #?(:clj  (DeltaableSet. (.-s ^DeltaableSet deltaable) [] (.-_meta ^DeltaableSet deltaable))
       :cljs (dset/DeltaableSet. (.-s deltaable) [] (.-_meta deltaable)))

    :else
    deltaable))

;; =============================================================================
;; IUnwrapDeltaable Protocol Implementations
;; =============================================================================

;; Deltaable collections unwrap recursively
(extend-protocol proto/PUnwrapDeltaable
  #?(:clj DeltaableVector :cljs dvec/DeltaableVector)
  (unwrap-deltaable [x]
    (mapv proto/unwrap-deltaable #?(:clj (.deref x) :cljs (-deref x))))

  #?(:clj DeltaableMap :cljs dmap/DeltaableMap)
  (unwrap-deltaable [x]
    (into {} (clojure.core/map (fn [[k v]] [k (proto/unwrap-deltaable v)]))
          #?(:clj (.deref x) :cljs (-deref x))))

  #?(:clj DeltaableSet :cljs dset/DeltaableSet)
  (unwrap-deltaable [x]
    (into #{} (clojure.core/map proto/unwrap-deltaable)
          #?(:clj (.deref x) :cljs (-deref x))))

  ;; Default: plain values pass through unchanged
  #?(:clj Object :cljs default)
  (unwrap-deltaable [x] x)

  ;; Handle nil explicitly
  nil
  (unwrap-deltaable [_] nil))

;; =============================================================================
;; Delta Transducers - Transform delta streams
;; =============================================================================

(defn map
  "Delta transducer that transforms values in deltas.

   Applies f to:
   - :add delta: transforms :value
   - :update delta: transforms both :value and :old-value
   - :remove delta: passes through unchanged (no value to transform)

   Works with standard transducer composition:
     (transduce (comp (d/map inc) (d/filter even?)) ...)

   Example:
     (d/map inc) transforms:
     {:delta :add :path [0] :value 1}
     => {:delta :add :path [0] :value 2}"
  [f]
  (fn [rf]
    (fn
      ([] (rf))
      ([result] (rf result))
      ([result delta]
       (rf result
           (case (:delta delta)
             :add (update delta :value f)
             :update (-> delta
                        (update :value f)
                        (update :old-value f))
             :remove delta))))))

(defn filter
  "Delta transducer that filters deltas with enter/exit semantics.

   Uses :old-value to determine if items entered or exited the filter:
   - Old passed, new passed: :update (stay in)
   - Old didn't pass, new passed: :add (entered)
   - Old passed, new didn't pass: :remove (exited)
   - Neither passed: filter out entirely

   For :add deltas (no old-value): treat as entering if pred passes
   For :remove deltas: treat as exiting if value would have passed

   Example with (d/filter even?):
     {:delta :update :value 4 :old-value 3}
     => {:delta :add :value 4}  ; entered the filter

     {:delta :update :value 3 :old-value 4}
     => {:delta :remove :value 4}  ; exited the filter

     {:delta :update :value 6 :old-value 4}
     => {:delta :update :value 6 :old-value 4}  ; stayed in"
  [pred]
  (fn [rf]
    (fn
      ([] (rf))
      ([result] (rf result))
      ([result delta]
       (case (:delta delta)
         :add
         (if (pred (:value delta))
           (rf result delta)
           result)

         :remove
         ;; For remove, we don't have access to the value
         ;; Pass through - caller needs to handle
         (rf result delta)

         :update
         (let [old-pass? (pred (:old-value delta))
               new-pass? (pred (:value delta))]
           (cond
             ;; Both pass: update (stay in filter)
             (and old-pass? new-pass?)
             (rf result delta)

             ;; Entered filter: change to :add
             (and (not old-pass?) new-pass?)
             (rf result (-> delta
                           (assoc :delta :add)
                           (dissoc :old-value)))

             ;; Exited filter: change to :remove
             (and old-pass? (not new-pass?))
             (rf result (-> delta
                           (assoc :delta :remove)
                           (dissoc :old-value)))

             ;; Neither pass: filter out
             :else
             result)))))))

(defn remove
  "Delta transducer that removes deltas - inverse of filter.

   Equivalent to (d/filter (complement pred))

   Example:
     (d/remove odd?) removes odd numbers from the delta stream"
  [pred]
  (filter (complement pred)))

(defn keep
  "Delta transducer that transforms and filters in one step.

   Applies f to values, keeps only non-nil results.
   Similar semantics to filter but with transformation.

   Example:
     (d/keep #(when (even? %) (* 2 %)))
     Keeps only even numbers and doubles them"
  [f]
  (fn [rf]
    (fn
      ([] (rf))
      ([result] (rf result))
      ([result delta]
       (case (:delta delta)
         :add
         (let [new-val (f (:value delta))]
           (if (some? new-val)
             (rf result (assoc delta :value new-val))
             result))

         :update
         (let [old-val (f (:old-value delta))
               new-val (f (:value delta))
               old-some? (some? old-val)
               new-some? (some? new-val)]
           (cond
             ;; Both some: update
             (and old-some? new-some?)
             (rf result (-> delta
                           (assoc :value new-val)
                           (assoc :old-value old-val)))

             ;; Entered: change to :add
             (and (not old-some?) new-some?)
             (rf result (-> delta
                           (assoc :delta :add)
                           (assoc :value new-val)
                           (dissoc :old-value)))

             ;; Exited: change to :remove
             (and old-some? (not new-some?))
             (rf result (-> delta
                           (assoc :delta :remove)
                           (dissoc :old-value)))

             ;; Neither: filter out
             :else
             result))

         :remove
         (rf result delta))))))

;; =============================================================================
;; Delta Application - Apply deltas to collections
;; =============================================================================

(defn apply-delta
  "Reducing function that applies a delta to a collection.

   Supports:
   - Plain collections (vectors, maps, sets)
   - DeltaableVector/Map/Set (preserves delta tracking)
   - Nested paths (uses assoc-in/update-in semantics)

   Delta formats:
   {:delta :add/:remove/:update
    :path [0] or [:users 0 :name]
    :value new-value
    :old-value old-value}  ; For :update/:remove

   {:delta :move
    :from-path [from-idx]
    :to-path [to-idx]
    :value element}  ; For vector reordering

   Example:
     (reduce d/apply-delta [] deltas)
     (reduce d/apply-delta (d/deltaable-vector []) deltas)"
  ([] [])  ; 0-arity: init
  ([coll] coll)  ; 1-arity: completion (identity)
  ([coll delta]  ; 2-arity: step
  (let [path (:path delta)
        value (:value delta)]
    (case (:delta delta)
      :add
      (if (empty? path)
        ;; Top-level add (conj)
        (conj coll value)
        ;; Nested add
        (if (= 1 (count path))
          ;; Single level
          (let [k (first path)]
            (if (vector? coll)
              ;; Vector: always add at end (conj), ignore path index
              ;; (path is just metadata from source, not target position)
              (conj coll value)
              ;; Map/Set: use key from path
              (assoc coll k value)))
          ;; Multi-level: use assoc-in
          (assoc-in coll path value)))

      :update
      (if (empty? path)
        ;; Top-level update (replace entire collection)
        value
        ;; Nested update
        (if (= 1 (count path))
          ;; Single level: use assoc
          (assoc coll (first path) value)
          ;; Multi-level: use assoc-in
          (assoc-in coll path value)))

      :remove
      (if (empty? path)
        ;; Top-level remove (clear collection)
        (empty coll)
        ;; Nested remove
        (if (= 1 (count path))
          ;; Single level: remove by index/key
          (cond
            (vector? coll)
            ;; Vector: remove by creating new vector without item
            (vec (concat (subvec coll 0 (first path))
                         (subvec coll (inc (first path)))))

            (map? coll)
            (dissoc coll (first path))

            (set? coll)
            (disj coll (first path))

            :else coll)
          ;; Multi-level: use update-in with recursive remove
          (update-in coll (butlast path)
                     (fn [parent]
                       (let [k (last path)]
                         (cond
                           (vector? parent)
                           (vec (concat (subvec parent 0 k)
                                        (subvec parent (inc k))))
                           (map? parent) (dissoc parent k)
                           (set? parent) (disj parent k)
                           :else parent))))))

      :move
      ;; Move element within a vector from from-path to to-path
      (let [from-idx (first (:from-path delta))
            to-idx (first (:to-path delta))]
        (if (vector? coll)
          (let [element (nth coll from-idx)
                ;; Remove from original position
                without-elem (into (subvec coll 0 from-idx) (subvec coll (inc from-idx)))
                ;; Insert at new position
                result (into (conj (subvec without-elem 0 to-idx) element)
                             (subvec without-elem to-idx))]
            result)
          ;; Non-vector: ignore move (doesn't make sense for maps/sets)
          coll))

      ;; Unknown delta type - return unchanged
      coll))))  ; Close 2-arity body

(defn transduce
  "Transduce deltas through xf and apply to initial collection.

   Like clojure.core/transduce but specialized for delta streams:
   - xf: delta transducer (d/map, d/filter, etc.)
   - init: initial collection (plain or deltaable)
   - deltas: sequence of delta maps

   Example:
     ;; Process only completed todos
     (d/transduce (d/filter :completed) [] deltas)

     ;; Transform and filter
     (d/transduce (comp (d/map inc) (d/filter even?))
                  []
                  deltas)"
  ([xf init deltas]
   (clojure.core/transduce xf apply-delta init deltas))
  ([xf init]
   (fn [deltas]
     (transduce xf init deltas))))

(defn merge-deltas
  "Merge multiple delta sequences into one.

   Concatenates delta sequences in order. Useful for combining
   deltas from multiple sources or time periods.

   Example:
     (d/merge-deltas deltas1 deltas2 deltas3)"
  [& delta-seqs]
  (apply concat delta-seqs))

(defn compact-deltas
  "Compact a sequence of deltas by removing redundant operations.

   Optimizations:
   - Multiple updates to same path: keep only last
   - Add followed by remove: cancel out
   - Remove followed by add: convert to update

   Note: Preserves order within non-redundant operations.

   Example:
     [{:delta :add :path [0] :value 1}
      {:delta :update :path [0] :value 2}
      {:delta :update :path [0] :value 3}]
     =>
     [{:delta :add :path [0] :value 3}]"
  [deltas]
  (let [;; Group by path
        by-path (group-by :path deltas)]
    ;; For each path, compact the operations
    (vec
     (mapcat
      (fn [[path ops]]
        (loop [result []
               [op & rest] ops]
          (if-not op
            result
            (let [last-op (peek result)]
              (cond
                ;; First operation for this path
                (nil? last-op)
                (recur (conj result op) rest)

                ;; add + remove = cancel
                (and (= :add (:delta last-op))
                     (= :remove (:delta op)))
                (recur (pop result) rest)

                ;; remove + add = update
                (and (= :remove (:delta last-op))
                     (= :add (:delta op)))
                (recur (conj (pop result)
                             (assoc op :delta :update
                                    :old-value nil))
                       rest)

                ;; Multiple updates = keep last
                (and (= :update (:delta last-op))
                     (= :update (:delta op)))
                (recur (conj (pop result)
                             (assoc op :old-value (:old-value last-op)))
                       rest)

                ;; add + update = add with new value
                (and (= :add (:delta last-op))
                     (= :update (:delta op)))
                (recur (conj (pop result)
                             (assoc last-op :value (:value op)))
                       rest)

                ;; update + remove = remove
                (and (= :update (:delta last-op))
                     (= :remove (:delta op)))
                (recur (conj (pop result) op) rest)

                ;; Otherwise keep both
                :else
                (recur (conj result op) rest))))))
      by-path))))

;; =============================================================================
;; Protocol function re-exports (MUST be after all extend-protocol calls)
;; =============================================================================
;; extend-protocol creates new function objects, so re-exports must capture
;; the final versions. Using wrapper fns ensures dispatch goes through vars.

(defn get-deltas
  "Returns sequence of deltas. See PDeltaable."
  [x]
  (proto/get-deltas x))

(defn deltaable?
  "Returns true if x is a deltaable collection. See PDeltaable."
  [x]
  (proto/deltaable? x))

(defn wrap-deltaable
  "Wrap x as a deltaable collection. See PWrapDeltaable."
  [x]
  (proto/wrap-deltaable x))

(defn unwrap-deltaable
  "Unwrap deltaable to plain collection. See PUnwrapDeltaable."
  [x]
  (proto/unwrap-deltaable x))
