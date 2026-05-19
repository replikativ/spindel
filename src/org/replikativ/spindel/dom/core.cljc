(ns org.replikativ.spindel.dom.core
  "Core virtual DOM data structures for delta-driven rendering.

  VNodes are IMMUTABLE persistent data structures:
  - :attrs is a DeltaableMap (tracks attribute changes)
  - :children is a DeltaableVector (tracks child add/remove/update)

  The vdom tree should be stored in a runtime signal for fork support.
  Updates produce new vnodes; deltaable collections track the changes.

  Key design principles:
  1. Immutable vnodes - no atoms inside vnodes
  2. Deltaable collections track top-level changes
  3. Path-based updates for efficient tree modification
  4. Addressing for element identity across renders"
  (:require [org.replikativ.spindel.incremental.deltaable :as d]
            [org.replikativ.spindel.engine.hash :as h]))

;; =============================================================================
;; VNode Predicates
;; =============================================================================

(defn vnode?
  "Check if x is a virtual DOM node (map with :tag)."
  [x]
  (and (map? x) (contains? x :tag)))

(defn text-node?
  "Check if x is a text node (has :tag :text)."
  [x]
  (and (map? x) (= (:tag x) :text)))

(defn fragment?
  "Check if x is a fragment (has :tag :fragment)."
  [x]
  (and (map? x) (= (:tag x) :fragment)))

(defn element-node?
  "Check if x is a regular element node (not text or fragment)."
  [x]
  (and (vnode? x)
       (not (text-node? x))
       (not (fragment? x))))

;; =============================================================================
;; VNode Creation
;; =============================================================================

(defn make-vnode
  "Create a new vnode with deltaable attrs and children.

  Args:
    tag: Keyword for HTML tag (e.g. :div, :span)
    attrs: Map of attributes (will be wrapped in deltaable-map)
    children: Optional vector of child vnodes

  Returns: Immutable VNode map with:
    :tag - Element tag keyword
    :key - Explicit key from attrs (for list reconciliation)
    :attrs - DeltaableMap of attributes
    :children - DeltaableVector of child vnodes
    :ref - User's ref callback function (if any)"
  ([tag attrs]
   (make-vnode tag attrs []))
  ([tag attrs children]
   (let [key-val (:key attrs)
         ref-fn (:ref attrs)
         attrs-clean (dissoc attrs :key :ref)]
     (cond-> {:tag tag
              :attrs (d/deltaable-map attrs-clean)
              :children (d/deltaable-vector (vec children))}
       key-val (assoc :key key-val)
       ref-fn (assoc :ref ref-fn)))))

(defn make-text-vnode
  "Create a text vnode. Text nodes are simple strings in the children vector."
  [content]
  {:tag :text
   :content (str content)})

(defn make-fragment-vnode
  "Create a fragment vnode (multiple children without wrapper element)."
  ([]
   (make-fragment-vnode []))
  ([children]
   {:tag :fragment
    :children (d/deltaable-vector (vec children))}))

;; =============================================================================
;; VNode Utilities
;; =============================================================================

(defn ^:no-doc get-key
  "Get the key of a vnode, or nil if not keyed."
  [vnode]
  (:key vnode))

(defn ^:no-doc keyed?
  "Check if a vnode has a key."
  [vnode]
  (some? (get-key vnode)))

(defn ^:no-doc same-key?
  "Check if two vnodes have the same key."
  [a b]
  (let [ka (get-key a)
        kb (get-key b)]
    (and (some? ka) (= ka kb))))

(defn ^:no-doc same-tag?
  "Check if two vnodes have the same tag."
  [a b]
  (= (:tag a) (:tag b)))

(defn ^:no-doc compatible?
  "Check if two vnodes are compatible for update (same tag and key)."
  [a b]
  (and (same-tag? a b)
       (or (and (nil? (get-key a)) (nil? (get-key b)))
           (same-key? a b))))

;; =============================================================================
;; Immutable VNode Updates (return new vnodes)
;; =============================================================================

(defn ^:no-doc update-attrs
  "Return a new vnode with updated attributes.

  The deltaable-map tracks which attrs were added/removed/updated.
  Only actually changed attrs produce deltas."
  [vnode new-attrs]
  (let [attrs (:attrs vnode)
        new-attrs-clean (dissoc new-attrs :key :ref)
        current-attrs @attrs
        ;; Start with current attrs, apply only changes
        updated-attrs (reduce-kv
                       (fn [acc k v]
                          ;; Only assoc if value actually changed
                         (if (= v (get current-attrs k))
                           acc
                           (assoc acc k v)))
                       attrs
                       new-attrs-clean)
        ;; Remove attrs not in new-attrs
        final-attrs (reduce
                     (fn [acc k]
                       (if (contains? new-attrs-clean k)
                         acc
                         (dissoc acc k)))
                     updated-attrs
                     (keys current-attrs))]
    (assoc vnode :attrs final-attrs)))

(defn ^:no-doc append-child
  "Return a new vnode with child appended.

  The deltaable-vector tracks the :add delta."
  [vnode child]
  (update vnode :children conj child))

(defn ^:no-doc update-child
  "Return a new vnode with child at index updated.

  The deltaable-vector tracks the :update delta."
  [vnode index new-child]
  (update vnode :children assoc index new-child))

(defn ^:no-doc remove-child-at
  "Return a new vnode with child at index removed.

  Note: This rebuilds the vector (loses fine-grained delta).
  TODO: Add proper remove-at to deltaable-vector."
  [vnode index]
  (let [children (:children vnode)
        v @children
        n (count v)]
    (if (and (>= index 0) (< index n))
      (let [new-children (into (subvec v 0 index) (subvec v (inc index)))]
        (assoc vnode :children (d/deltaable-vector new-children)))
      vnode)))

(defn ^:no-doc set-children
  "Return a new vnode with children replaced.

  Used when children are completely recomputed."
  [vnode new-children]
  (assoc vnode :children (d/deltaable-vector (vec new-children))))

;; =============================================================================
;; Path-Based Updates (for deep tree modifications)
;; =============================================================================

(defn ^:no-doc get-in-vdom
  "Get vnode at path in vdom tree.

  Path is a sequence of child indices."
  [vdom path]
  (reduce
   (fn [node idx]
     (when node
       (get (:children node) idx)))
   vdom
   path))

(defn ^:no-doc update-in-vdom
  "Update vnode at path in vdom tree.

  Path is a sequence of child indices.
  f is a function (fn [vnode] new-vnode)."
  [vdom path f]
  (if (empty? path)
    (f vdom)
    (let [[idx & rest-path] path
          children (:children vdom)
          child (get children idx)]
      (if child
        (let [new-child (update-in-vdom child rest-path f)]
          (update vdom :children assoc idx new-child))
        vdom))))

(defn ^:no-doc assoc-in-vdom
  "Set vnode at path in vdom tree.

  Path is a sequence of child indices."
  [vdom path new-vnode]
  (update-in-vdom vdom path (constantly new-vnode)))

;; =============================================================================
;; Addressing for Element Identity
;; =============================================================================

(defn ^:no-doc keyed-address
  "Compute address for a keyed element.

  Combines base address with content key for stable identity
  regardless of position in list."
  [base-addr key]
  (keyword (str "keyed-" (h/content-hash [base-addr :keyed key]))))

(defn ^:no-doc derive-child-chain
  "Derive a child chain head from parent address.

  Used for subtree isolation - changes inside a subtree
  don't affect sibling addresses."
  [parent-addr]
  (keyword (str "child-" (h/content-hash [parent-addr :child-chain]))))

(defn ^:no-doc next-address
  "Generate next deterministic address from chain head and source location.

  Returns [new-address new-chain-head]."
  [chain-head prefix source-loc]
  (let [new-uuid (h/content-hash [source-loc chain-head])
        new-addr (keyword (str prefix "-" new-uuid))]
    [new-addr new-addr]))  ; Address becomes new chain head

;; =============================================================================
;; Delta Extraction (for discharge to real DOM)
;; =============================================================================

(defn ^:no-doc get-attr-deltas
  "Get attribute deltas from vnode."
  [vnode]
  (d/get-deltas (:attrs vnode)))

(defn ^:no-doc get-children-deltas
  "Get children deltas from vnode."
  [vnode]
  (d/get-deltas (:children vnode)))

(defn has-deltas?
  "Check if vnode has any pending deltas."
  [vnode]
  (or (d/has-deltas? (:attrs vnode))
      (d/has-deltas? (:children vnode))))

(defn ^:no-doc clear-deltas
  "Return a new vnode with deltas cleared.

  Used after discharge to prepare for next render cycle.
  Clears both DeltaableMap/DeltaableVector deltas and
  the :deltas field from slot reconciliation."
  [vnode]
  (cond-> vnode
    (:attrs vnode) (update :attrs d/clear-deltas)
    (:children vnode) (update :children d/clear-deltas)
    (:deltas vnode) (dissoc :deltas)))

(defn ^:no-doc clear-deltas-deep
  "Recursively clear deltas from vnode and all descendants."
  [vnode]
  (if (or (text-node? vnode) (nil? vnode))
    vnode
    (let [cleared (clear-deltas vnode)
          children (:children cleared)]
      (if children
        (assoc cleared :children
               (d/deltaable-vector
                (mapv clear-deltas-deep @children)))
        cleared))))

;; =============================================================================
;; VNode Comparison (for reconciliation)
;; =============================================================================

(defn ^:no-doc children-by-key
  "Index keyed children by their keys.

  Returns {:by-key {key {:child vnode :index idx}}, :unkeyed [vnodes...]}"
  [children]
  (reduce
   (fn [acc [idx child]]
     (if-let [k (get-key child)]
       (update acc :by-key assoc k {:child child :index idx})
       (update acc :unkeyed conj child)))
   {:by-key {} :unkeyed []}
   (map-indexed vector children)))

(defn ^:no-doc reconcile-children
  "Reconcile old children with new children, producing deltas.

  Uses keys for stable identity when available.
  Returns new children vector (as deltaable) with appropriate deltas."
  [old-children new-children]
  (let [old-by-key (children-by-key old-children)
        result (d/deltaable-vector [])]
    ;; For now, simple implementation - just produce the new children
    ;; The deltaable-vector will track add/update operations
    (reduce
     (fn [acc child]
       (conj acc child))
     result
     new-children)))
