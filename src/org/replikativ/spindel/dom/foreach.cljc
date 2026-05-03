(ns org.replikativ.spindel.dom.foreach
  "Delta-driven collection rendering for DOM using KeyedFragment.

  **IMPORTANT: Pass intervals to ifor-each for O(delta) updates!**

  When using ifor-each with track, pass the interval directly:

    ;; CORRECT - O(delta) incremental updates:
    (let [items-iv (track items-sig)]
      (ifor-each :id items-iv render-fn))

    ;; SUBOPTIMAL - O(n) comparison each render:
    (let [{:keys [new]} (track items-sig)]
      (ifor-each :id new render-fn))

  The interval carries deltas from signal changes. Without deltas,
  ifor-each must re-render all items and compare vnodes to detect changes.

  The `ifor-each` macro renders a collection to DOM children with true
  O(delta) incremental updates. It returns a KeyedFragment that:
  - Contains rendered vnodes
  - Carries deltas from incremental changes
  - Integrates with slot-based caching in parent elements

  **How it works:**

  1. ifor-each has its own tree address (from source-loc + parent context)
  2. Each item rendered with keyed addressing (parent-addr + item-key)
  3. Previous results cached at [:dom/keyed-cache address]
  4. Only changed items re-rendered
  5. Returns KeyedFragment with items and deltas

  **Spin Support:**

  If render-fn returns spins instead of vnodes, ifor-each will:
  1. Detect spin results during first pass rendering
  2. Return a spin that awaits all child spins using loop/recur
  3. After all spins resolve, build the KeyedFragment with resolved vnodes

  This enables patterns like:
    (ifor-each :id items
      (fn [item]
        (spin
          (el/li {}
            (await (fetch-data (:id item)))))))

  **Defensive Delta Handling:**

  Due to CPS transformation capturing intervals in closures, deltas may be
  stale when a spin resumes from a later continuation. ifor-each defensively
  validates cache consistency before trusting deltas:

  1. source-keys-mismatch?: If keys from source don't match cached keys,
     the source fundamentally changed (e.g., filter switch) - full recompute
  2. stale-deltas?: If deltas describe changes the cache already reflects,
     they're from a previous execution - full recompute
  3. Only takes incremental path when cache is consistent with current source

  **Stale Delta Clearing:**

  Vnodes are cached with their deltas attached. When returning cached vnodes
  on subsequent renders, we must clear their stale deltas. Otherwise,
  collect-nodes-with-deltas will find them and discharge-vnode! will apply
  the same deltas again, causing duplicate DOM children.

  **Integration with parent elements:**

  Parent elements recognize KeyedFragment and:
  1. Store in a :keyed slot (vs :single for regular children)
  2. Propagate fragment's internal deltas with adjusted indices
  3. Flatten items into final children vector

  Usage:
    (spin
      (let [{:keys [new]} (track items)]
        (el/ul {:class \"list\"}
          (ifor-each :id new
            (fn [item]
              (el/li {:key (:id item)} (:text item)))))))

  Or with per-item spins:
    (spin
      (let [{:keys [new]} (track items)]
        (el/ul {:class \"list\"}
          (ifor-each :id new
            (fn [item]
              ;; Each item is a spin with its own reactive scope
              (spin
                (let [extra @(track extra-signal)]
                  (el/li {:key (:id item)} (:text item) extra))))))))

  The render-fn receives each item and should return a vnode or a spin.
  Keys must be unique within the collection."
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.dom.fragment :as frag]
            [org.replikativ.spindel.dom.addressing :as addr]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.incremental.deltaable :as d]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [replikativ.logging :as log])
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]])))

;; =============================================================================
;; VNode Value Comparison
;; =============================================================================

(defn- vnode-value-equal?
  "Compare two vnodes by their semantic value, not object identity.

  This is needed because vnodes contain DeltaableMap/Vector which are
  new objects each render. We compare the dereferenced values instead.

  For performance, we do shallow comparison:
  - Compare :tag directly
  - Compare :key directly
  - Compare dereferenced :attrs
  - Compare dereferenced :children (recursively)
  - Compare :content for text nodes"
  [v1 v2]
  (cond
    ;; Both nil
    (and (nil? v1) (nil? v2)) true
    ;; One nil
    (or (nil? v1) (nil? v2)) false
    ;; Both text nodes
    (and (= :text (:tag v1)) (= :text (:tag v2)))
    (= (:content v1) (:content v2))
    ;; Both element nodes
    (and (:tag v1) (:tag v2))
    (and (= (:tag v1) (:tag v2))
         (= (:key v1) (:key v2))
         ;; Compare dereferenced attrs
         (= (if (d/deltaable? (:attrs v1)) @(:attrs v1) (:attrs v1))
            (if (d/deltaable? (:attrs v2)) @(:attrs v2) (:attrs v2)))
         ;; Compare children count and content
         (let [c1 (if (d/deltaable? (:children v1)) @(:children v1) (:children v1))
               c2 (if (d/deltaable? (:children v2)) @(:children v2) (:children v2))]
           (and (= (count c1) (count c2))
                (every? true? (map vnode-value-equal? c1 c2)))))
    ;; Different types
    :else false))

;; =============================================================================
;; Spin Detection
;; =============================================================================

(defn- spin?
  "Check if x is a Spin."
  [x]
  (instance? org.replikativ.spindel.spin.core.Spin x))

;; =============================================================================
;; Keyed Cache Access
;; =============================================================================

(defn- get-keyed-cache
  "Get cached items for a keyed collection at address.

  Cache structure: {:by-key {key -> rendered-vnode}
                    :order [key1 key2 ...]}"
  [addr]
  (ec/get-state [:dom/keyed-cache addr]))

(defn- set-keyed-cache!
  "Store keyed cache at address."
  [addr cache-data]
  (ec/swap-state! [:dom/keyed-cache addr] (constantly cache-data)))

;; =============================================================================
;; Stale Delta Clearing
;; =============================================================================

(defn- clear-stale-deltas
  "Clear stale deltas from a cached vnode.

  When vnodes are cached, they retain their :deltas field from when they were
  first rendered. On subsequent renders, returning these cached vnodes would
  cause collect-nodes-with-deltas to find them and apply the same deltas again,
  duplicating DOM children.

  This function clears:
  - :deltas field on the vnode itself
  - Recursively clears children's deltas
  - Clears deltas from DeltaableMap attrs"
  [vnode]
  (when vnode
    (cond
      ;; Text nodes have no deltas
      (and (map? vnode) (contains? vnode :content) (not (contains? vnode :tag)))
      vnode

      ;; Element vnode - clear its deltas and recurse
      (and (map? vnode) (contains? vnode :tag))
      (let [cleared (dissoc vnode :deltas)
            ;; Clear attr deltas if attrs is a deltaable map
            cleared (if-let [attrs (:attrs cleared)]
                      (assoc cleared :attrs (d/clear-deltas attrs))
                      cleared)
            ;; Recurse on children
            children (:children cleared)]
        (if children
          (let [child-vec (if (d/deltaable? children) @children children)]
            (assoc cleared :children
                   (d/deltaable-vector
                     (mapv clear-stale-deltas child-vec))))
          cleared))

      ;; Not a vnode - return as-is
      :else vnode)))

;; =============================================================================
;; For-Each Implementation
;; =============================================================================

(defn- build-fragment-result
  "Build the KeyedFragment result from resolved items.

  Shared logic between sync and async paths for full recompute."
  [my-addr resolved-items prev-by-key prev-order]
  (let [by-key (into {} (map (juxt :key :vnode) resolved-items))
        order (mapv :key resolved-items)
        items (mapv :vnode resolved-items)

        ;; Compute deltas by comparing with cached vnodes
        ;; This handles the case where source has no deltas (e.g., using :new instead of interval)
        ;; but items have actually changed
        deltas (cond
                 ;; No previous cache - initial render
                 (empty? prev-by-key)
                 (if (seq items)
                   ;; Produce :add deltas for each item
                   (vec (map-indexed
                          (fn [idx vnode]
                            {:delta :add :path [idx] :value vnode})
                          items))
                   ;; Empty - no deltas
                   nil)

                 ;; Order changed - need structural update
                 (not= order prev-order)
                 [{:delta :replace-all
                   :old-items (mapv #(get prev-by-key %) prev-order)
                   :items items}]

                 ;; Same order - check if any items changed by comparing vnodes
                 :else
                 (let [;; Compare each new vnode with cached vnode using value equality
                       ;; Produce :update deltas only for changed items
                       update-deltas
                       (keep-indexed
                         (fn [idx k]
                           (let [new-vnode (get by-key k)
                                 old-vnode (get prev-by-key k)]
                             ;; Compare vnodes by value - if different, produce update delta
                             (when-not (vnode-value-equal? new-vnode old-vnode)
                               {:delta :update
                                :path [idx]
                                :old-value old-vnode
                                :value new-vnode})))
                         order)]
                   (when (seq update-deltas)
                     (vec update-deltas))))]

    ;; Update cache
    (set-keyed-cache! my-addr {:by-key by-key :order order})

    ;; Return KeyedFragment
    (frag/keyed-fragment items deltas)))

(defn- build-incremental-fragment-result
  "Build the KeyedFragment result from incremental path results.

  Shared logic for the incremental delta processing path."
  [my-addr new-by-key new-order out-deltas has-spins?]
  (if has-spins?
    ;; Return a spin that awaits all spins in by-key
    (spin
      (loop [remaining (seq new-order)
             resolved-by-key {}]
        (if (empty? remaining)
          ;; All resolved - build fragment
          (let [items (mapv #(clear-stale-deltas (get resolved-by-key %)) new-order)]
            (set-keyed-cache! my-addr {:by-key resolved-by-key :order new-order})
            (frag/keyed-fragment items (when (seq out-deltas) out-deltas)))
          ;; Resolve next item
          (let [k (first remaining)
                vnode (get new-by-key k)
                resolved-vnode (if (spin? vnode) (await vnode) vnode)]
            (recur (rest remaining)
                   (assoc resolved-by-key k resolved-vnode))))))
    ;; Sync path - no spins
    (let [items (mapv #(clear-stale-deltas (get new-by-key %)) new-order)]
      (set-keyed-cache! my-addr {:by-key new-by-key :order new-order})
      (frag/keyed-fragment items (when (seq out-deltas) out-deltas)))))

(defn for-each*
  "Internal for-each implementation.

  Renders a collection with keyed addressing, returning a KeyedFragment
  containing the rendered vnodes and any incremental deltas.

  If render-fn returns spins instead of vnodes, for-each* returns a spin
  that awaits all child spins using loop/recur (CPS-safe pattern).

  Args:
    source-loc - Source location map for addressing
    key-fn - Function to extract unique key from each item
    render-fn - Function (item) -> vnode or spin
    source - Collection interval or plain collection

  Returns: KeyedFragment with :items and :deltas, or a spin resolving to one"
  [source-loc key-fn render-fn source]
  (let [;; Compute address for this ifor-each
        my-addr (addr/current-element-address source-loc)

        ;; Check if source is a proper Interval type (not just satisfies PInterval)
        ;; Warn if it's a raw deltaable - passing :new instead of interval loses deltas
        _ (when (and (d/deltaable? source)
                     (not (instance? #?(:clj org.replikativ.spindel.incremental.interval.Interval
                                        :cljs iv/Interval) source)))
            (log/warn ::ifor-each-without-interval "ifor-each received deltaable without interval wrapper. Pass the interval from track directly for O(delta) updates." {:source-type (type source)
                              :has-deltas? (boolean (seq (d/get-deltas source)))}))

        ;; Coerce source to interval
        source-iv (iv/as-interval source)
        source-new (iv/get-new source-iv)
        source-deltas (iv/get-deltas source-iv)

        ;; Get previous cache
        prev-cache (get-keyed-cache my-addr)
        prev-by-key (or (:by-key prev-cache) {})
        prev-order (or (:order prev-cache) [])]

    ;; Extract keys from source-new to check for fundamental changes
    (let [source-keys (set (map key-fn source-new))
          prev-keys (set prev-order)

          ;; Extract keys from deltas
          delta-add-keys (set (keep (fn [d] (when (= :add (:delta d))
                                              (key-fn (:value d))))
                                    source-deltas))
          delta-remove-keys (set (keep (fn [d] (when (= :remove (:delta d))
                                                 (key-fn (or (:old-value d) (:value d)))))
                                       source-deltas))

          ;; Keys that disappeared from cache but aren't in remove deltas
          ;; This indicates a fundamental source change (e.g., filter switch)
          unexplained-missing-keys (clojure.set/difference
                                     (clojure.set/difference prev-keys source-keys)
                                     delta-remove-keys)

          ;; Keys that appeared but aren't in add deltas
          ;; This also indicates a fundamental source change
          unexplained-new-keys (clojure.set/difference
                                 (clojure.set/difference source-keys prev-keys)
                                 delta-add-keys)

          ;; Detect if source fundamentally changed: keys appeared/disappeared
          ;; without corresponding deltas. This happens when switching filters -
          ;; the upstream source changes completely and deltas are meaningless.
          source-keys-mismatch? (and (seq prev-keys)
                                     (or (seq unexplained-missing-keys)
                                         (seq unexplained-new-keys)))

          ;; Detect stale deltas: deltas that were already processed in a previous execution
          ;; A delta is stale if the cache already reflects it:
          ;; - :add delta is stale if key already exists in cache
          ;; - :remove delta is stale if key doesn't exist in cache
          ;; - :update delta is never stale just because key exists (we always need to re-render)
          ;; - :move delta is never stale (we always need to reorder)
          stale-deltas? (and (seq prev-by-key)
                              (seq source-deltas)
                              (every? (fn [delta]
                                        (let [item (or (:value delta) (:old-value delta))
                                              k (key-fn item)]
                                          (case (:delta delta)
                                            :add (contains? prev-by-key k)
                                            :remove (not (contains? prev-by-key k))
                                            :update false  ; update is never stale - we need to re-render
                                            :move false    ; move is never stale - we need to reorder
                                            false)))
                                      source-deltas))

          ;; Only take incremental path if:
          ;; 1. We have previous cache AND source deltas
          ;; 2. Deltas are not stale
          ;; 3. Source keys match cache keys (no fundamental change)
          incremental-path? (and (seq prev-by-key)
                                 (seq source-deltas)
                                 (not stale-deltas?)
                                 (not source-keys-mismatch?))]
      (if incremental-path?
      ;; Incremental: process only deltas
      (let [;; Process each delta to produce output delta and updated cache
            result
            (reduce
              (fn [{:keys [by-key order deltas has-spins]} delta]
                (case (:delta delta)
                  :add
                  (let [item (:value delta)
                        k (key-fn item)
                        ;; Render with keyed context (use function version for runtime call)
                        vnode (addr/with-keyed-context-fn my-addr k
                                #(render-fn item))
                        is-spin (spin? vnode)
                        ;; Use source delta's path for insertion position if available
                        ;; This is important for islice which specifies exact positions
                        requested-idx (or (first (:path delta)) (count order))
                        ;; Actual insertion position - can't insert past end of current order
                        ;; This is crucial: after previous removes, (count order) may be smaller
                        ;; than the requested index, so we clamp to the current size
                        actual-idx (min requested-idx (count order))
                        ;; Insert key at the correct position in order
                        new-order (if (>= actual-idx (count order))
                                    (conj order k)  ; Append if at end
                                    (vec (concat (take actual-idx order)
                                                 [k]
                                                 (drop actual-idx order))))]
                    {:by-key (assoc by-key k vnode)
                     :order new-order
                     :deltas (conj deltas {:delta :add :path [actual-idx] :value vnode})
                     :has-spins (or has-spins is-spin)})

                  :remove
                  (let [;; :remove deltas may have item in :old-value (from DeltaableVector)
                        ;; or :value (from filter* combinator exit)
                        item (or (:old-value delta) (:value delta))
                        k (key-fn item)
                        old-vnode (get by-key k)
                        idx (.indexOf order k)]  ; Find position
                    (if (>= idx 0)
                      {:by-key (dissoc by-key k)
                       :order (into (subvec order 0 idx)
                                    (subvec order (inc idx)))
                       :deltas (conj deltas {:delta :remove :path [idx] :old-value old-vnode})
                       :has-spins has-spins}
                      ;; Key not found - skip this delta (might be stale)
                      {:by-key by-key :order order :deltas deltas :has-spins has-spins}))

                  :update
                  (let [item (:value delta)
                        k (key-fn item)
                        old-vnode (get by-key k)
                        ;; Re-render with keyed context (use function version for runtime call)
                        new-vnode (addr/with-keyed-context-fn my-addr k
                                    #(render-fn item))
                        is-spin (spin? new-vnode)
                        idx (.indexOf order k)]
                    (if (and (not is-spin) (= old-vnode new-vnode))
                      ;; No change to vnode (can't compare if new is spin)
                      {:by-key by-key :order order :deltas deltas :has-spins has-spins}
                      ;; Vnode changed or is a spin
                      {:by-key (assoc by-key k new-vnode)
                       :order order
                       :deltas (conj deltas {:delta :update :path [idx]
                                             :old-value old-vnode :value new-vnode})
                       :has-spins (or has-spins is-spin)}))

                  :move
                  (let [item (:value delta)
                        k (key-fn item)
                        from-idx (first (:from-path delta))
                        to-idx (first (:to-path delta))
                        ;; Get existing vnode (no re-render needed for move)
                        vnode (get by-key k)
                        ;; Update order: remove from old position, insert at new
                        without-item (into (subvec order 0 from-idx)
                                           (subvec order (inc from-idx)))
                        new-order (into (conj (subvec without-item 0 to-idx) k)
                                        (subvec without-item to-idx))]
                    {:by-key by-key  ; vnodes unchanged
                     :order new-order
                     :deltas (conj deltas {:delta :move
                                           :from-path [from-idx]
                                           :to-path [to-idx]
                                           :value vnode})
                     :has-spins has-spins})

                  ;; Unknown delta type - skip
                  {:by-key by-key :order order :deltas deltas :has-spins has-spins}))
              {:by-key prev-by-key :order prev-order :deltas [] :has-spins false}
              source-deltas)]

        ;; Build fragment, handling spins if present
        (build-incremental-fragment-result
          my-addr
          (:by-key result)
          (:order result)
          (:deltas result)
          (:has-spins result)))

      ;; Full recompute: render all items
      (let [items-with-keys
            (mapv (fn [item]
                    (let [k (key-fn item)
                          ;; Use function version for runtime call
                          vnode (addr/with-keyed-context-fn my-addr k
                                  #(render-fn item))]
                      {:key k :vnode vnode}))
                  source-new)

            ;; Check if any results are spins
            has-spins? (some #(spin? (:vnode %)) items-with-keys)]

        (if has-spins?
          ;; Return a spin that awaits all child spins using loop/recur
          ;; This pattern is CPS-safe because partial-cps handles loop/recur correctly
          (spin
            (loop [remaining items-with-keys
                   resolved []]
              (if (empty? remaining)
                ;; All resolved - build cache and fragment
                (build-fragment-result my-addr resolved prev-by-key prev-order)
                ;; Process next item
                (let [{:keys [key vnode]} (first remaining)
                      resolved-vnode (if (spin? vnode) (await vnode) vnode)]
                  (recur (rest remaining)
                         (conj resolved {:key key :vnode resolved-vnode}))))))
          ;; Sync path - no spins, proceed normally
          (build-fragment-result my-addr items-with-keys prev-by-key prev-order)))))))

;; =============================================================================
;; Macro: ifor-each
;; =============================================================================

#?(:clj
   (defmacro ifor-each
     "Incremental for-each macro for DOM rendering.

     Renders a collection to DOM children with true O(delta) updates.
     Returns a KeyedFragment containing rendered vnodes and deltas.

     The macro:
     1. Captures source location for stable addressing
     2. Calls for-each* at runtime with caching

     Args:
       key-fn - Function to extract unique key from each item
       items - Collection (plain or interval)
       render-fn - Function (item) -> vnode

     Usage:
       (ifor-each :id todos
         (fn [todo]
           (el/li {:key (:id todo)} (:text todo))))

     Note: render-fn must be a plain function, not a macro call.
     The render-fn is called with keyed addressing context set.
     Requires an execution context to be bound."
     [key-fn items render-fn]
     (let [source-loc {:file *file*
                       :line (:line (meta &form))
                       :column (:column (meta &form))}]
       `(for-each* ~source-loc ~key-fn ~render-fn ~items))))

