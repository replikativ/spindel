(ns org.replikativ.spindel.dom.fragment
  "KeyedFragment for representing keyed lists in DOM.

  When ifor-each renders a collection, it returns a KeyedFragment
  containing the rendered vnodes and any incremental deltas.

  The parent element recognizes KeyedFragment and:
  1. Stores items in a :keyed slot
  2. Propagates internal deltas with adjusted indices
  3. Flattens items into final children vector

  Usage:
    ;; ifor-each produces KeyedFragment
    (->KeyedFragment
      [<li-1> <li-2> <li-3>]
      [{:delta :add :path [2] :value <li-3>}])

    ;; Parent checks and handles
    (when (keyed-fragment? result)
      (let [{:keys [items deltas]} result]
        ...))")

;; =============================================================================
;; KeyedFragment Record
;; =============================================================================

(defrecord KeyedFragment
           [items   ; Vector of vnodes
            deltas] ; Vector of deltas (internal to this fragment)

  ;; Implement IDeref for convenient access to items
  #?(:clj clojure.lang.IDeref :cljs IDeref)
  (#?(:clj deref :cljs -deref) [_]
    items))

;; =============================================================================
;; Constructors
;; =============================================================================

(defn keyed-fragment
  "Create a KeyedFragment with items and optional deltas.

  Args:
    items - Vector of vnodes
    deltas - Vector of delta maps (default: nil)"
  ([items]
   (->KeyedFragment items nil))
  ([items deltas]
   (->KeyedFragment items deltas)))

(defn keyed-fragment?
  "Check if x is a KeyedFragment."
  [x]
  (instance? KeyedFragment x))

;; =============================================================================
;; Accessors
;; =============================================================================

(defn fragment-items
  "Get the items vector from a KeyedFragment."
  [fragment]
  (:items fragment))

(defn fragment-deltas
  "Get the deltas from a KeyedFragment."
  [fragment]
  (:deltas fragment))

(defn fragment-count
  "Get the number of items in a KeyedFragment."
  [fragment]
  (count (:items fragment)))

;; =============================================================================
;; Operations
;; =============================================================================

(defn with-deltas
  "Return a new KeyedFragment with the given deltas."
  [fragment deltas]
  (->KeyedFragment (:items fragment) deltas))

(defn append-item
  "Append an item to the fragment, producing appropriate delta."
  [fragment item]
  (let [items (:items fragment)
        new-idx (count items)
        new-items (conj items item)
        new-delta {:delta :add :path [new-idx] :value item}
        deltas (conj (or (:deltas fragment) []) new-delta)]
    (->KeyedFragment new-items deltas)))

(defn remove-item-at
  "Remove item at index, producing appropriate delta."
  [fragment index]
  (let [items (:items fragment)
        old-item (get items index)
        new-items (into (subvec items 0 index)
                        (subvec items (inc index)))
        new-delta {:delta :remove :path [index] :old-value old-item}
        deltas (conj (or (:deltas fragment) []) new-delta)]
    (->KeyedFragment new-items deltas)))

(defn update-item-at
  "Update item at index, producing appropriate delta."
  [fragment index new-item]
  (let [items (:items fragment)
        old-item (get items index)
        new-items (assoc items index new-item)
        new-delta {:delta :update :path [index]
                   :old-value old-item :value new-item}
        deltas (conj (or (:deltas fragment) []) new-delta)]
    (->KeyedFragment new-items deltas)))

;; =============================================================================
;; Empty Fragment
;; =============================================================================

(def empty-fragment
  "An empty KeyedFragment."
  (->KeyedFragment [] nil))

(defn empty-fragment?
  "Check if fragment has no items."
  [fragment]
  (empty? (:items fragment)))
