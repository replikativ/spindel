(ns org.replikativ.spindel.incremental.combinators
  "Interval-based incremental combinators.

   These combinators operate on intervals (old/new/deltas) and produce intervals.
   They are designed to be used inside spins, where each combinator's previous
   result is stored by address for incremental updates.

   Key concepts:
   - Each combinator call has a unique address (from source location + chain)
   - Previous results are stored at [:incremental address] in runtime
   - On re-execution, prev.new becomes our 'old'

   Usage:
     (spin
       (let [todos (track todos-signal)]
         (->> todos
              (ifilter active?)   ; address A - stores its result
              (imap :hours)       ; address B - stores its result
              (ireduce + 0))))    ; address C - stores its result

   Each combinator:
   1. Gets its address from current execution context
   2. Retrieves previous output from [:incremental address]
   3. Processes input interval incrementally
   4. Stores new output at [:incremental address]
   5. Returns interval for downstream"
  (:refer-clojure :exclude [filter map reduce])
  (:require [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.runtime.core :as rtc]))

;; =============================================================================
;; Helper: Address-based result storage
;; =============================================================================

(defn- get-combinator-address
  "Generate a stable address for this combinator call.

   Uses the source location directly as the address key.
   This is deterministic: same source-loc -> same address.

   Note: The source-loc should be unique per call site.
   In production, this would come from macro expansion capturing &form metadata."
  [source-loc]
  ;; Use source-loc directly as address key
  ;; Coerce to keyword for consistent storage
  (keyword (str "comb-" (:file source-loc) "-" (:line source-loc) "-" (:column source-loc))))

(defn- get-prev-result
  "Get the previous result for a combinator at the given address."
  [address]
  (rtc/get-state [:incremental address]))

(defn- store-result!
  "Store the combinator's result at the given address."
  [address result]
  (rtc/swap-state! [:incremental address] (constantly result))
  result)

(defn- with-incremental-cache
  "Execute combinator body with address-based caching.

   Gets previous result, executes computation, stores new result.
   Returns the new result (an interval)."
  [source-loc compute-fn]
  (let [address (get-combinator-address source-loc)
        prev-result (get-prev-result address)
        new-result (compute-fn prev-result)]
    (store-result! address new-result)
    new-result))

;; =============================================================================
;; Filter Combinator
;; =============================================================================

(defn filter*
  "Internal filter implementation.

   Takes source-loc for addressing, predicate, and source interval."
  [source-loc pred source]
  (with-incremental-cache source-loc
    (fn [prev-output]
      (let [;; Coerce source to interval if needed
            source-iv (iv/as-interval source)
            source-new (iv/get-new source-iv)
            source-deltas (iv/get-deltas source-iv)

            ;; Our 'old' comes from previous output's 'new'
            our-old (when prev-output (iv/get-new prev-output))

            ;; Predicate is a plain function - treat as static
            pred-fn pred

            ;; Always compute what the filtered result SHOULD be
            ;; This is needed to detect stale deltas
            expected-filtered (filterv pred-fn source-new)

            ;; Detect stale deltas: if our-old already equals expected result,
            ;; the deltas are stale (already processed in a previous execution)
            stale-deltas? (and our-old (seq source-deltas) (= our-old expected-filtered))]

        (if (and our-old (seq source-deltas) (not stale-deltas?))
          ;; Incremental: process deltas with enter/exit semantics
          (let [out-deltas
                (into []
                      (keep
                        (fn [delta]
                          (case (:delta delta)
                            :add
                            (when (pred-fn (:value delta))
                              delta)

                            :remove
                            (when (pred-fn (:value delta))
                              delta)

                            :update
                            (let [old-val (:old-value delta)
                                  new-val (:value delta)
                                  old-match? (pred-fn old-val)
                                  new-match? (pred-fn new-val)]
                              (cond
                                (and old-match? new-match?)
                                delta  ; Still in filter, pass through

                                (and old-match? (not new-match?))
                                {:delta :remove :value old-val}  ; Exit filter

                                (and (not old-match?) new-match?)
                                {:delta :add :value new-val}  ; Enter filter

                                :else
                                nil))  ; Not in filter before or after

                            ;; Unknown delta type
                            nil)))
                      source-deltas)

                ;; Apply deltas to old result
                computed-result (clojure.core/reduce
                                  (fn [acc delta]
                                    (case (:delta delta)
                                      :add (conj acc (:value delta))
                                      :remove (filterv #(not= % (:value delta)) acc)
                                      :update (mapv #(if (= % (:old-value delta))
                                                       (:value delta)
                                                       %)
                                                   acc)
                                      acc))
                                  (vec our-old)
                                  out-deltas)

                ;; CRITICAL: Verify computed result matches expected
                ;; If they differ, our-old was stale and we need to use expected
                ;; Use expected if computed doesn't match (stale our-old)
                new-result (if (= computed-result expected-filtered)
                             computed-result
                             expected-filtered)

                ;; If we had to correct, clear deltas (full recompute scenario)
                final-deltas (if (= computed-result expected-filtered)
                               out-deltas
                               nil)]
            (iv/->Interval our-old new-result final-deltas))

          ;; Full recompute: no previous result, no deltas, or stale deltas
          ;; Use expected-filtered which was already computed
          (iv/->Interval our-old expected-filtered nil))))))

(defn filter
  "Incremental filter using interval abstraction.

   Takes a predicate and a source (any value, coerced to interval).
   Returns an interval with filtered values.

   Incremental behavior:
   - If predicate is a static function and source has deltas:
     Only processes the deltas (O(delta))
   - If predicate changed or no previous result:
     Full recompute (O(n))

   Usage:
     (filter active? todos-interval)
     (filter (fn [x] (> (:hours x) 5)) tasks)

   Note: For proper addressing, use the filter macro which captures source location."
  [pred source]
  ;; Without macro, use a placeholder source-loc
  ;; In production, this would be a macro that captures &form metadata
  (filter* {:file "unknown" :line 0 :column 0} pred source))

;; =============================================================================
;; Map Combinator
;; =============================================================================

(defn map*
  "Internal map implementation."
  [source-loc f source]
  (with-incremental-cache source-loc
    (fn [prev-output]
      (let [source-iv (iv/as-interval source)
            source-new (iv/get-new source-iv)
            source-deltas (iv/get-deltas source-iv)

            our-old (when prev-output (iv/get-new prev-output))
            map-fn f]

        (if (and our-old (seq source-deltas))
          ;; Incremental: map deltas
          (let [out-deltas
                (mapv
                  (fn [delta]
                    (case (:delta delta)
                      :add
                      {:delta :add :value (map-fn (:value delta))}

                      :remove
                      {:delta :remove :value (map-fn (:value delta))}

                      :update
                      {:delta :update
                       :value (map-fn (:value delta))
                       :old-value (map-fn (:old-value delta))}

                      delta))
                  source-deltas)

                ;; Apply deltas to old result
                new-result (clojure.core/reduce
                             (fn [acc delta]
                               (case (:delta delta)
                                 :add (conj acc (:value delta))
                                 :remove (filterv #(not= % (:value delta)) acc)
                                 :update (mapv #(if (= % (:old-value delta))
                                                  (:value delta)
                                                  %)
                                              acc)
                                 acc))
                             (vec our-old)
                             out-deltas)]
            (iv/->Interval our-old new-result out-deltas))

          ;; Full recompute
          (let [mapped (mapv map-fn source-new)]
            (iv/->Interval our-old mapped nil)))))))

(defn map
  "Incremental map using interval abstraction.

   Takes a function and a source interval.
   Returns an interval with mapped values.

   Incremental behavior:
   - If source has deltas: Only maps delta values (O(delta))
   - Otherwise: Full recompute (O(n))

   Usage:
     (map :hours tasks-interval)
     (map (fn [x] (* 2 x)) numbers)"
  [f source]
  (map* {:file "unknown" :line 0 :column 0} f source))

;; =============================================================================
;; Reduce Combinator (Terminal)
;; =============================================================================

(defn reduce*
  "Internal reduce implementation."
  [source-loc rf init enter-fn exit-fn source]
  (with-incremental-cache source-loc
    (fn [prev-output]
      (let [source-iv (iv/as-interval source)
            source-new (iv/get-new source-iv)
            source-deltas (iv/get-deltas source-iv)

            ;; For reduce, the previous result IS the accumulated value
            ;; We wrap it in an interval for consistency
            prev-value (when prev-output (iv/get-new prev-output))]

        (if (and prev-value (seq source-deltas))
          ;; Incremental: apply enter/exit
          (let [new-value (clojure.core/reduce
                            (fn [acc delta]
                              (case (:delta delta)
                                :add (enter-fn acc (:value delta))
                                :remove (exit-fn acc (:value delta))
                                :update (-> acc
                                            (exit-fn (:old-value delta))
                                            (enter-fn (:value delta)))
                                acc))
                            prev-value
                            source-deltas)]
            ;; Return as interval for consistency
            (iv/->Interval prev-value new-value nil))

          ;; Full recompute
          (let [result (clojure.core/reduce rf init source-new)]
            (iv/->Interval nil result nil)))))))

(defn reduce
  "Incremental reduce using interval abstraction.

   Takes a reducing function, initial value, and source interval.
   Returns an interval wrapping the scalar result.

   For incremental updates, uses enter/exit semantics:
   - enter-fn: Applied when item enters (default: rf)
   - exit-fn: Applied when item exits (must undo rf)

   For +, the exit-fn is -.
   For *, the exit-fn would be /.

   Usage:
     (reduce + 0 numbers-interval)  ; Sum
     (reduce + 0 - numbers-interval)  ; Sum with explicit exit

   Returns interval so you can get the value with (iv/get-new result)
   or use @result for convenience."
  ([rf init source]
   (reduce rf init rf (fn [acc x] (- acc x)) source))

  ([rf init enter-fn exit-fn source]
   (reduce* {:file "unknown" :line 0 :column 0} rf init enter-fn exit-fn source)))

;; =============================================================================
;; For-Each Combinator (Keyed transformation)
;; =============================================================================

(defn for-each*
  "Internal for-each implementation."
  [source-loc key-fn transform-fn source]
  (with-incremental-cache source-loc
    (fn [prev-output]
      (let [source-iv (iv/as-interval source)
            source-new (iv/get-new source-iv)
            source-deltas (iv/get-deltas source-iv)

            our-old (when prev-output (iv/get-new prev-output))

            ;; Build key->transformed cache from previous output
            ;; This is O(n) but only needed when we have deltas to process
            old-by-key (when (and our-old (seq source-deltas))
                         (into {} (clojure.core/map (fn [item] [(key-fn item) item]) our-old)))]

        (if (and our-old (seq source-deltas))
          ;; Incremental: only transform changed items
          (let [out-deltas
                (into []
                      (keep
                        (fn [delta]
                          (case (:delta delta)
                            :add
                            (let [item (:value delta)
                                  k (when item (key-fn item))]
                              (when k
                                {:delta :add :value (transform-fn item)}))

                            :remove
                            ;; Remove deltas may have item in :old-value (from slice*)
                            ;; or :value (from other sources like filter*)
                            (let [item (or (:old-value delta) (:value delta))
                                  k (when item (key-fn item))]
                              (when k
                                {:delta :remove :value (get old-by-key k)}))

                            :update
                            (let [item (:value delta)
                                  k (when item (key-fn item))]
                              (when k
                                {:delta :update
                                 :value (transform-fn item)
                                 :old-value (get old-by-key k)}))

                            nil)))
                      source-deltas)

                ;; Apply deltas to old result
                new-result (clojure.core/reduce
                             (fn [acc delta]
                               (case (:delta delta)
                                 :add (conj acc (:value delta))
                                 :remove (filterv #(not= % (:value delta)) acc)
                                 :update (mapv #(if (= % (:old-value delta))
                                                  (:value delta)
                                                  %)
                                              acc)
                                 acc))
                             (vec our-old)
                             out-deltas)]
            (iv/->Interval our-old new-result out-deltas))

          ;; Full recompute: transform all items
          (let [transformed (mapv transform-fn source-new)]
            (iv/->Interval our-old transformed nil)))))))

(defn for-each
  "Incremental for-each using interval abstraction.

   Like map, but maintains a cache keyed by key-fn for efficient updates.
   Only re-transforms items that actually changed.

   Usage:
     (for-each :id render-todo todos-interval)"
  [key-fn transform-fn source]
  (for-each* {:file "unknown" :line 0 :column 0} key-fn transform-fn source))

;; =============================================================================
;; Slice Combinator (Window-based positional filtering for infinite scroll)
;; =============================================================================

(defn- subvec-safe
  "Safe subvec that clamps to valid bounds."
  [v start end]
  (let [len (count v)
        s (max 0 (min start len))
        e (max s (min end len))]
    (if (= s e)
      []
      (subvec v s e))))

(defn- compute-window-slide-deltas
  "Compute deltas when window slides from old-window to new-window.

  Optimized O(delta) implementation that directly computes exit/enter ranges
  without iterating over entire windows.

  When window slides right (new-start > old-start):
  - Items [old-start, new-start) exit from front
  - Items [old-end, new-end) enter at back

  When window slides left (new-start < old-start):
  - Items [new-end, old-end) exit from back
  - Items [new-start, old-start) enter at front

  Returns vector of deltas ordered for correct application:
  - Removes processed from high index to low (so indices remain valid)
  - Adds processed from low index to high"
  [{old-start :start old-end :end}
   {new-start :start new-end :end}
   source-items]
  (let [source-len (count source-items)

        ;; Clamp windows to source bounds
        old-start (max 0 (min old-start source-len))
        old-end (max old-start (min old-end source-len))
        new-start (max 0 (min new-start source-len))
        new-end (max new-start (min new-end source-len))

        ;; Compute overlap region
        overlap-start (max old-start new-start)
        overlap-end (min old-end new-end)
        has-overlap? (< overlap-start overlap-end)

        ;; Exit regions: parts of old window not in new window
        ;; Left exit: [old-start, min(old-end, new-start))
        ;; Right exit: [max(old-start, new-end), old-end)
        left-exit-start old-start
        left-exit-end (min old-end new-start)
        right-exit-start (max old-start new-end)
        right-exit-end old-end

        ;; Enter regions: parts of new window not in old window
        ;; Left enter: [new-start, min(new-end, old-start))
        ;; Right enter: [max(new-start, old-end), new-end)
        left-enter-start new-start
        left-enter-end (min new-end old-start)
        right-enter-start (max new-start old-end)
        right-enter-end new-end

        ;; Build exit deltas (high to low for stable removal)
        exit-deltas
        (persistent!
          (clojure.core/reduce
            (fn [acc src-idx]
              (conj! acc {:delta :remove
                          :path [(- src-idx old-start)]
                          :old-value (get source-items src-idx)}))
            (transient [])
            ;; Right exits first (higher indices), then left exits
            (concat
              (when (< right-exit-start right-exit-end)
                (range (dec right-exit-end) (dec right-exit-start) -1))
              (when (< left-exit-start left-exit-end)
                (range (dec left-exit-end) (dec left-exit-start) -1)))))

        ;; Build enter deltas (low to high for stable insertion)
        enter-deltas
        (persistent!
          (clojure.core/reduce
            (fn [acc src-idx]
              (conj! acc {:delta :add
                          :path [(- src-idx new-start)]
                          :value (get source-items src-idx)}))
            (transient [])
            ;; Left enters first (lower indices), then right enters
            (concat
              (when (< left-enter-start left-enter-end)
                (range left-enter-start left-enter-end))
              (when (< right-enter-start right-enter-end)
                (range right-enter-start right-enter-end)))))]

    ;; Removes first, then adds
    (into exit-deltas enter-deltas)))

(defn- compute-source-deltas-in-window
  "Compute output deltas when source changes within a fixed window.

  For each source delta, determine if it affects the window:
  - :add at index i: if i < end, items shift; if i in window, it enters
  - :remove at index i: if i < end, items shift; if i was in window, it exits
  - :update at index i: if i in window, pass through"
  [{:keys [start end]} source-deltas prev-source new-source]
  (let [window-size (- end start)]
    ;; For now, if source structure changes (add/remove), do full recompute
    ;; This is conservative but correct. Optimization: track index shifts
    (if (some #(#{:add :remove} (:delta %)) source-deltas)
      ;; Structural change - return nil to trigger full recompute
      nil
      ;; Only updates - check if any are in window
      (let [update-deltas
            (keep (fn [delta]
                    (when (= :update (:delta delta))
                      ;; Find index of updated item in source
                      ;; This requires scanning - could be optimized with indexed source
                      (let [old-val (:old-value delta)
                            new-val (:value delta)
                            ;; Find index in prev-source
                            idx (first (keep-indexed
                                         (fn [i v] (when (= v old-val) i))
                                         prev-source))]
                        (when (and idx (>= idx start) (< idx end))
                          (let [out-pos (- idx start)]
                            {:delta :update
                             :path [out-pos]
                             :old-value old-val
                             :value new-val})))))
                  source-deltas)]
        (when (seq update-deltas)
          (vec update-deltas))))))

(defn slice*
  "Internal slice implementation for window-based positional filtering.

  Takes a window {:start n :end m} and a source collection.
  Returns an interval containing the slice [start, end) with deltas
  for window changes and source changes.

  Key behaviors:
  - Window changes produce :add/:remove deltas for entering/exiting items
  - Source changes within window are propagated
  - Source structural changes outside window may shift indices

  This combinator enables O(delta) infinite scroll:
  - Only items entering/exiting the visible window cause DOM changes
  - Scroll position changes are O(window-delta) not O(n)

  Args:
    source-loc - Source location for address-based caching
    window - Map with :start and :end keys (0-indexed, end exclusive)
    source - Collection interval or plain collection

  Returns: Interval with sliced items and deltas"
  [source-loc window source]
  (let [address (get-combinator-address source-loc)
        prev-cache (get-prev-result address)

        ;; Coerce inputs
        window-new (if (satisfies? iv/PInterval window)
                     (iv/get-new window)
                     window)
        source-iv (iv/as-interval source)
        source-new (iv/get-new source-iv)
        source-deltas (iv/get-deltas source-iv)

        ;; Extract window bounds
        {:keys [start end]} window-new

        ;; Get previous state from cache
        prev-window (:window prev-cache)
        prev-source (:source prev-cache)
        prev-output (:output prev-cache)

        ;; Compute new slice
        new-slice (subvec-safe source-new start end)]

    (cond
      ;; No previous state - initial render
      (nil? prev-cache)
      (let [result (iv/->Interval nil new-slice nil)]
        (store-result! address {:window window-new
                                :source source-new
                                :output new-slice})
        result)

      ;; Window changed - compute window slide deltas
      (not= prev-window window-new)
      (let [deltas (compute-window-slide-deltas prev-window window-new source-new)
            result (iv/->Interval prev-output new-slice (when (seq deltas) deltas))]
        (store-result! address {:window window-new
                                :source source-new
                                :output new-slice})
        result)

      ;; Source changed - compute source change deltas within window
      (seq source-deltas)
      (let [deltas (compute-source-deltas-in-window window-new source-deltas
                                                     prev-source source-new)
            result (iv/->Interval prev-output new-slice deltas)]
        (store-result! address {:window window-new
                                :source source-new
                                :output new-slice})
        result)

      ;; No changes
      :else
      (iv/->Interval prev-output new-slice nil))))

(defn slice
  "Incremental slice for window-based filtering.

  Returns items from source in the range [start, end).
  Produces deltas when window bounds change or source changes.

  Usage:
    (slice {:start 10 :end 30} items)

  For infinite scroll, track a window signal:
    (spin
      (let [items-iv (track items-signal)
            window (track window-signal)]
        (islice window items-iv)))

  Note: For proper addressing, use the islice macro."
  [window source]
  (slice* {:file "unknown" :line 0 :column 0} window source))

;; =============================================================================
;; Macros: Auto-capture source location
;; =============================================================================

#?(:clj
   (defmacro islice
     "Incremental slice macro that captures source location.

      Returns items from source in range [start, end).
      Produces deltas when window or source changes.

      Usage:
        (islice {:start 0 :end 20} items)
        (islice window-signal items-interval)"
     [window source]
     (let [source-loc {:file *file*
                       :line (:line (meta &form))
                       :column (:column (meta &form))}]
       `(slice* ~source-loc ~window ~source))))

#?(:clj
   (defmacro ifilter
     "Incremental filter macro that captures source location.

      Usage:
        (ifilter even? numbers)
        (->> items (ifilter :active))"
     [pred source]
     (let [source-loc {:file *file*
                       :line (:line (meta &form))
                       :column (:column (meta &form))}]
       `(filter* ~source-loc ~pred ~source))))

#?(:clj
   (defmacro imap
     "Incremental map macro that captures source location.

      Usage:
        (imap :hours tasks)
        (->> items (imap #(* 2 %)))"
     [f source]
     (let [source-loc {:file *file*
                       :line (:line (meta &form))
                       :column (:column (meta &form))}]
       `(map* ~source-loc ~f ~source))))

#?(:clj
   (defmacro ireduce
     "Incremental reduce macro that captures source location.

      Usage:
        (ireduce + 0 numbers)
        (ireduce + 0 + - numbers)  ; explicit enter/exit fns"
     ([rf init source]
      (let [source-loc {:file *file*
                        :line (:line (meta &form))
                        :column (:column (meta &form))}]
        `(reduce* ~source-loc ~rf ~init ~rf (fn [acc# x#] (- acc# x#)) ~source)))
     ([rf init enter-fn exit-fn source]
      (let [source-loc {:file *file*
                        :line (:line (meta &form))
                        :column (:column (meta &form))}]
        `(reduce* ~source-loc ~rf ~init ~enter-fn ~exit-fn ~source)))))

#?(:clj
   (defmacro ifor-each
     "Incremental for-each macro that captures source location.

      Usage:
        (ifor-each :id render-fn items)"
     [key-fn transform-fn source]
     (let [source-loc {:file *file*
                       :line (:line (meta &form))
                       :column (:column (meta &form))}]
       `(for-each* ~source-loc ~key-fn ~transform-fn ~source))))

;; =============================================================================
;; Example: Composing combinators
;; =============================================================================

(comment
  ;; This shows how combinators would be used in a spin:
  ;;
  ;; (require '[org.replikativ.spindel.spin.cps :refer [spin]]
  ;;          '[org.replikativ.spindel.effects.track :refer [track]]
  ;;          '[org.replikativ.spindel.signal :as sig])
  ;;
  ;; (def todos (sig/signal []))
  ;;
  ;; ;; Simple pipeline using macros (recommended)
  ;; (def active-hours
  ;;   (spin
  ;;     (let [todos-iv (track todos)]
  ;;       (->> todos-iv
  ;;            (ifilter :active)
  ;;            (imap :hours)
  ;;            (ireduce + 0)))))
  ;;
  ;; When todos changes:
  ;; 1. track returns interval with old/new/deltas from signal
  ;; 2. ifilter processes deltas (enter/exit semantics) - stores at address A
  ;; 3. imap processes filter's output deltas - stores at address B
  ;; 4. ireduce applies enter/exit for final sum - stores at address C
  ;; Total: O(delta) not O(n)
  ;;
  ;; Each combinator:
  ;; - Gets unique address from source location (captured by macro)
  ;; - Retrieves its previous result from [:incremental address]
  ;; - Uses prev.new as 'old' for incremental computation
  ;; - Stores new result for next execution
  ;;
  ;; ;; With rendering
  ;; (def todo-list
  ;;   (spin
  ;;     (let [todos-iv (track todos)]
  ;;       (ifor-each :id (fn [todo] {:tag :li :content (:text todo)}) todos-iv))))
  ;; ;; Only re-renders items that changed
  )
