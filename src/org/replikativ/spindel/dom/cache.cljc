(ns org.replikativ.spindel.dom.cache
  "Slot-based caching for DOM elements.

  Each parent element caches its children by slot position. This enables:
  - Stable slot indices (conditionals returning nil don't shift positions)
  - Efficient delta computation (compare prev slot vs new value)
  - KeyedFragment support (keyed lists at a slot position)

  Cache is stored in execution context state at [:dom/cache <address>].

  Slot Types:
  - :nil    - Slot is empty (conditional returned nil)
  - :single - Slot contains one vnode
  - :keyed  - Slot contains KeyedFragment (from ifor-each)"
  (:require [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.dom.core :as core]))

;; Forward declaration for KeyedFragment check
(declare keyed-fragment?)

;; =============================================================================
;; Slot Types
;; =============================================================================

(defn classify-slot
  "Classify a child result into a slot type.

  Returns: :nil, :single, or :keyed"
  [result]
  (cond
    (nil? result) :nil
    (keyed-fragment? result) :keyed
    (core/vnode? result) :single
    ;; Plain vectors treated as keyed (from raw ifor-each without wrapper)
    (vector? result) :keyed
    ;; Anything else treated as single (will be coerced to text node)
    :else :single))

(defn make-slot
  "Create a slot entry from a child result.

  Returns: {:type :nil|:single|:keyed :value <result>}"
  [result]
  {:type (classify-slot result)
   :value result})

;; =============================================================================
;; Cache Access
;; =============================================================================

(defn get-slot-cache
  "Get cached slots for an element address.

  Returns: Vector of slot entries, or nil if not cached."
  [addr]
  (ec/get-state [:dom/cache addr]))

(defn set-slot-cache!
  "Store slot cache for an element address.

  Args:
    addr - Element address (keyword)
    slots - Vector of {:type :value} slot entries"
  [addr slots]
  (ec/swap-state! [:dom/cache addr] (constantly slots)))

;; =============================================================================
;; Attribute Cache Access
;; =============================================================================

(defn get-attr-cache
  "Get cached attrs for an element address.

  Returns: Map of previous attribute values, or nil if not cached."
  [addr]
  (ec/get-state [:dom/attr-cache addr]))

(defn set-attr-cache!
  "Store attr cache for an element address.

  Args:
    addr - Element address (keyword)
    attrs - Map of attribute values"
  [addr attrs]
  (ec/swap-state! [:dom/attr-cache addr] (constantly attrs)))

;; =============================================================================
;; Attribute Reconciliation
;; =============================================================================

(defn reconcile-attrs
  "Reconcile previous attrs with new attrs, producing deltas.

  Args:
    prev-attrs - Previous attribute map (or nil)
    new-attrs - New attribute map

  Returns: Vector of attribute deltas (or nil if no changes)"
  [prev-attrs new-attrs]
  (let [prev-attrs (or prev-attrs {})
        new-attrs (or new-attrs {})
        prev-keys (set (keys prev-attrs))
        new-keys (set (keys new-attrs))

        ;; Keys added (in new but not in prev)
        added-keys (clojure.set/difference new-keys prev-keys)

        ;; Keys removed (in prev but not in new)
        removed-keys (clojure.set/difference prev-keys new-keys)

        ;; Keys that exist in both - check for updates
        common-keys (clojure.set/intersection prev-keys new-keys)
        updated-keys (filter (fn [k]
                               (not= (get prev-attrs k) (get new-attrs k)))
                             common-keys)

        ;; Build deltas
        add-deltas (mapv (fn [k]
                           {:delta :add :path [k] :value (get new-attrs k)})
                         added-keys)
        remove-deltas (mapv (fn [k]
                              {:delta :remove :path [k] :old-value (get prev-attrs k)})
                            removed-keys)
        update-deltas (mapv (fn [k]
                              {:delta :update :path [k]
                               :old-value (get prev-attrs k)
                               :value (get new-attrs k)})
                            updated-keys)

        all-deltas (into [] (concat add-deltas remove-deltas update-deltas))]
    (when (seq all-deltas)
      all-deltas)))

;; =============================================================================
;; Slot Reconciliation
;; =============================================================================

(defn reconcile-slot
  "Reconcile a single slot, comparing prev vs new.

  Args:
    slot-index - Position in parent's children
    prev-slot - Previous slot entry {:type :value} or nil
    new-result - New child result (vnode, nil, or KeyedFragment)

  Returns: {:slot <new-slot-entry> :delta <delta-or-nil>}"
  [slot-index prev-slot new-result]
  (let [new-slot (make-slot new-result)
        prev-type (or (:type prev-slot) :nil)
        new-type (:type new-slot)
        prev-value (:value prev-slot)]

    (case [prev-type new-type]
      ;; nil → nil: no change
      [:nil :nil]
      {:slot new-slot :delta nil}

      ;; nil → single: add
      [:nil :single]
      {:slot new-slot
       :delta {:delta :add :path [slot-index] :value new-result}}

      ;; nil → keyed: add all items (fragment becoming visible)
      [:nil :keyed]
      {:slot new-slot
       :delta {:delta :add-fragment :path [slot-index] :value new-result}}

      ;; single → nil: remove
      [:single :nil]
      {:slot new-slot
       :delta {:delta :remove :path [slot-index] :old-value prev-value}}

      ;; single → single: update if changed
      ;; Compare vnodes semantically:
      ;; - For element vnodes: same tag + same identity (via :key)
      ;;   When unchanged, the child handles its own deltas via discharge-vnode!
      ;; - For text nodes: compare content directly
      ;; - Otherwise: use reference equality
      [:single :single]
      (let [unchanged?
            (cond
              ;; Both are text nodes - compare content
              (and (core/text-node? prev-value) (core/text-node? new-result))
              (= (:content prev-value) (:content new-result))

              ;; Both are element vnodes - check tag and key for identity
              ;; The child element handles its own deltas via discharge-vnode!
              ;; DO NOT check (:deltas new-result) - that would cause parent to
              ;; trigger :update which calls render-initial! and bypasses child deltas
              (and (core/vnode? prev-value) (core/vnode? new-result))
              (let [same-tag? (= (:tag prev-value) (:tag new-result))
                    prev-key (:key prev-value)
                    new-key (:key new-result)
                    ;; Identity check:
                    ;; - If both have explicit keys, they must match
                    ;; - If neither has keys, compare addresses (different source = different element)
                    ;; - If one has key and other doesn't, they're different elements
                    same-identity? (cond
                                     (and prev-key new-key) (= prev-key new-key)
                                     (and (nil? prev-key) (nil? new-key))
                                     (let [prev-addr (:addr prev-value)
                                           new-addr (:addr new-result)]
                                       ;; If both have addresses, they must match
                                       ;; If either is missing addr (legacy), fall back to same
                                       (if (and prev-addr new-addr)
                                         (= prev-addr new-addr)
                                         true))
                                     :else false)]
                (and same-tag? same-identity?))

              ;; Otherwise use reference equality
              :else (= prev-value new-result))]
        (if unchanged?
          {:slot new-slot :delta nil}
          {:slot new-slot
           :delta {:delta :update :path [slot-index]
                   :old-value prev-value :value new-result}}))

      ;; single → keyed: replace with fragment
      [:single :keyed]
      {:slot new-slot
       :delta {:delta :replace-with-fragment :path [slot-index]
               :old-value prev-value :value new-result}}

      ;; keyed → nil: remove all items
      [:keyed :nil]
      {:slot new-slot
       :delta {:delta :remove-fragment :path [slot-index] :old-value prev-value}}

      ;; keyed → single: replace fragment with single
      [:keyed :single]
      {:slot new-slot
       :delta {:delta :replace-fragment-with-single :path [slot-index]
               :old-value prev-value :value new-result}}

      ;; keyed → keyed: propagate fragment's internal deltas
      [:keyed :keyed]
      (let [fragment-deltas (when (keyed-fragment? new-result)
                              (:deltas new-result))]
        {:slot new-slot
         :delta (when (seq fragment-deltas)
                  {:delta :fragment-update :path [slot-index]
                   :deltas fragment-deltas})})

      ;; Fallback: treat as update
      {:slot new-slot
       :delta {:delta :update :path [slot-index]
               :old-value prev-value :value new-result}})))

(defn reconcile-children
  "Reconcile all children against cached slots.

  Args:
    prev-cache - Vector of previous slot entries (or nil)
    new-children - Vector of new child results

  Returns: {:slots <vector-of-slot-entries> :deltas <vector-of-deltas>}"
  [prev-cache new-children]
  (let [prev-cache (or prev-cache [])
        max-slots (max (count prev-cache) (count new-children))
        results (mapv (fn [idx]
                        (let [prev-slot (get prev-cache idx)
                              new-result (get new-children idx)]
                          (reconcile-slot idx prev-slot new-result)))
                      (range max-slots))]
    {:slots (mapv :slot results)
     :deltas (into [] (keep :delta results))}))

;; =============================================================================
;; Flatten Slots to Children
;; =============================================================================

(defn flatten-slot
  "Flatten a slot to its child vnodes.

  Returns: Vector of vnodes (may be empty, single, or multiple)"
  [slot]
  (case (:type slot)
    :nil []
    :single [(:value slot)]
    :keyed (if (keyed-fragment? (:value slot))
             (:items (:value slot))
             (:value slot))
    []))

(defn flatten-slots
  "Flatten all slots to a single children vector.

  This produces the final children for the vnode."
  [slots]
  (into [] (mapcat flatten-slot slots)))

;; =============================================================================
;; Compute Flattened Index
;; =============================================================================

(defn slot-base-index
  "Compute the flattened base index for a slot.

  This is the sum of sizes of all preceding slots."
  [slots slot-index]
  (reduce (fn [acc idx]
            (+ acc (count (flatten-slot (get slots idx)))))
          0
          (range slot-index)))

(defn adjust-delta-paths
  "Adjust delta paths from slot-relative to flattened indices.

  Args:
    slots - Vector of slot entries (for computing base indices)
    deltas - Vector of deltas with slot-relative paths

  Returns: Vector of deltas with absolute flattened indices"
  [slots deltas]
  (mapv (fn [delta]
          (let [slot-idx (first (:path delta))
                base-idx (slot-base-index slots slot-idx)]
            (case (:delta delta)
              ;; Simple deltas: just adjust path
              (:add :remove :update)
              (assoc delta :path [base-idx])

              ;; Fragment deltas: adjust each internal delta's path
              :fragment-update
              (let [internal-deltas (:deltas delta)
                    adjusted-internal (mapv (fn [d]
                                              (update d :path
                                                      (fn [p]
                                                        [(+ base-idx (or (first p) 0))])))
                                            internal-deltas)]
                {:delta :fragment-update
                 :path [slot-idx]
                 :adjusted-deltas adjusted-internal})

              ;; Fragment add/remove: need special handling at render time
              delta)))
        deltas))

;; =============================================================================
;; KeyedFragment Check (defined here to avoid circular deps)
;; =============================================================================

(defn keyed-fragment?
  "Check if x is a KeyedFragment.

  Note: This checks for the expected structure since the record
  is defined in fragment.cljc which may not be loaded yet."
  [x]
  (and (map? x)
       (contains? x :items)
       (contains? x :deltas)
       (vector? (:items x))))
