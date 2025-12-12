(ns is.simm.spindel.dom.addressing
  "Tree-based addressing for DOM elements.

  Unlike the chain-based addressing in runtime/addressing.cljc (for spins),
  DOM elements use tree-based addressing where:

  - Each element's address depends on: source-loc + parent-addr + slot-index
  - Siblings are independent (adding one doesn't affect others)
  - Conditionals have stable slot positions
  - Function components inherit parent context

  Address propagation uses ExecutionContext's :bindings map, which is:
  - Fork-safe (inherited by child forks)
  - Thread-safe (immutable per context)

  Usage:
    (let [my-addr (compute-tree-address source-loc parent-addr slot)]
      (with-dom-context my-addr
        (fn [child-ctx]
          ;; Children evaluated here see my-addr as parent
          ...)))"
  (:require [hasch.core :as hc]
            [is.simm.spindel.runtime.core :as rtc]))

;; =============================================================================
;; Tree Address Computation
;; =============================================================================

(defn compute-tree-address
  "Compute a unique address for a DOM element.

  Args:
    source-loc - Map with :file :line :column (captured at macro expansion)
    parent-addr - Parent element's address (keyword or nil for root)
    slot-index - Position in parent's children (integer or nil)

  Returns: Keyword like :el-550e8400-e29b-41d4-a716-446655440000

  Properties:
  - Deterministic: same inputs → same address
  - Unique: different slot positions → different addresses
  - Stable: sibling changes don't affect this element's address"
  [source-loc parent-addr slot-index]
  (let [hash-input [source-loc parent-addr slot-index]
        uuid (hc/uuid hash-input)]
    (keyword (str "el-" uuid))))

(defn keyed-child-address
  "Compute address for a keyed child (inside ifor-each).

  Uses the item's key instead of slot index for stable identity
  across reorderings.

  Args:
    parent-addr - Parent element's address (the ifor-each's address)
    item-key - The key extracted from the item (via key-fn)

  Returns: Keyword address"
  [parent-addr item-key]
  (let [hash-input [parent-addr :keyed item-key]
        uuid (hc/uuid hash-input)]
    (keyword (str "keyed-" uuid))))

;; =============================================================================
;; Context Bindings Access
;; =============================================================================

(defn get-parent-addr
  "Get current parent address from execution context bindings.

  Returns nil if at root level (no parent)."
  []
  (when-let [ctx rtc/*execution-context*]
    (get-in ctx [:bindings :dom/parent-addr])))

(defn get-current-slot
  "Get current slot index from execution context bindings.

  Returns nil if not inside an element's child evaluation."
  []
  (when-let [ctx rtc/*execution-context*]
    (get-in ctx [:bindings :dom/current-slot])))

;; =============================================================================
;; Context Binding Helpers
;; =============================================================================

(defn with-parent-addr
  "Execute thunk with parent-addr set in context bindings.

  Used by elements to set context before evaluating children."
  [parent-addr thunk]
  (if-let [ctx rtc/*execution-context*]
    (let [new-ctx (assoc-in ctx [:bindings :dom/parent-addr] parent-addr)]
      (binding [rtc/*execution-context* new-ctx]
        (thunk)))
    ;; No context - just run thunk (for testing without runtime)
    (thunk)))

(defn with-slot
  "Execute thunk with slot index set in context bindings.

  Used by parent elements for each child position."
  [slot-index thunk]
  (if-let [ctx rtc/*execution-context*]
    (let [new-ctx (assoc-in ctx [:bindings :dom/current-slot] slot-index)]
      (binding [rtc/*execution-context* new-ctx]
        (thunk)))
    ;; No context - just run thunk
    (thunk)))

(defn with-dom-context
  "Execute thunk with both parent-addr and slot set.

  Convenience function combining with-parent-addr and with-slot."
  [parent-addr slot-index thunk]
  (with-parent-addr parent-addr
    (fn []
      (with-slot slot-index thunk))))

(defn with-keyed-context
  "Execute thunk with keyed child context (for ifor-each items).

  Sets parent-addr to the keyed address and slot to 0
  (keyed children typically have single root element)."
  [parent-addr item-key thunk]
  (let [keyed-addr (keyed-child-address parent-addr item-key)]
    (with-dom-context keyed-addr 0 thunk)))

;; =============================================================================
;; Address for Current Element
;; =============================================================================

(defn current-element-address
  "Compute address for an element at current context position.

  Combines source-loc with parent-addr and slot from context bindings."
  [source-loc]
  (compute-tree-address source-loc (get-parent-addr) (get-current-slot)))
