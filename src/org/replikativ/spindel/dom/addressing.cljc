(ns org.replikativ.spindel.dom.addressing
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

  **CPS-Aware Design:**

  The context binding helpers (with-parent-addr, with-slot, with-keyed-context)
  are MACROS that expand to `binding` forms. This is critical for CPS/await
  support in element children:

  - partial-cps handles `binding` forms specially
  - Bindings are captured/restored across await points
  - `await` inside element children works correctly

  Usage:
    (with-parent-addr my-addr
      (let [child-result (await some-spin)]
        (build-element ...)))"
  (:require [org.replikativ.spindel.engine.hash :as h]
            [org.replikativ.spindel.engine.core :as ec])
  #?(:cljs (:require-macros [org.replikativ.spindel.dom.addressing])))

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
        uuid (h/content-hash hash-input)]
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
        uuid (h/content-hash hash-input)]
    (keyword (str "keyed-" uuid))))

;; =============================================================================
;; Context Bindings Access
;; =============================================================================

(defn get-parent-addr
  "Get current parent address from execution context bindings.

  Returns nil if at root level (no parent)."
  []
  (when-let [ctx ec/*execution-context*]
    (get-in ctx [:bindings :dom/parent-addr])))

(defn get-current-slot
  "Get current slot index from execution context bindings.

  Returns nil if not inside an element's child evaluation."
  []
  (when-let [ctx ec/*execution-context*]
    (get-in ctx [:bindings :dom/current-slot])))

;; =============================================================================
;; Context Binding Macros (CPS-Aware)
;; =============================================================================

#?(:clj
   (defmacro with-parent-addr
     "Execute body with parent-addr set in context bindings.

     This is a MACRO that expands to a `binding` form, which partial-cps
     handles specially. Bindings are captured/restored across await points.

     Used by element macros to set context before evaluating children."
     [parent-addr & body]
     `(if-let [ctx# ec/*execution-context*]
        (let [new-ctx# (assoc-in ctx# [:bindings :dom/parent-addr] ~parent-addr)]
          (binding [ec/*execution-context* new-ctx#]
            ~@body))
        ;; No context - just run body (for testing without runtime)
        (do ~@body))))

#?(:clj
   (defmacro with-slot
     "Execute body with slot index set in context bindings.

     This is a MACRO that expands to a `binding` form, which partial-cps
     handles specially. Bindings are captured/restored across await points.

     Used by element macros for each child position."
     [slot-index & body]
     `(if-let [ctx# ec/*execution-context*]
        (let [new-ctx# (assoc-in ctx# [:bindings :dom/current-slot] ~slot-index)]
          (binding [ec/*execution-context* new-ctx#]
            ~@body))
        ;; No context - just run body
        (do ~@body))))

#?(:clj
   (defmacro with-dom-context
     "Execute body with both parent-addr and slot set.

     Convenience macro combining with-parent-addr and with-slot."
     [parent-addr slot-index & body]
     `(with-parent-addr ~parent-addr
        (with-slot ~slot-index
          ~@body))))

#?(:clj
   (defmacro with-keyed-context
     "Execute body with keyed child context (for ifor-each items).

     Sets parent-addr to the keyed address and slot to 0
     (keyed children typically have single root element)."
     [parent-addr item-key & body]
     `(let [keyed-addr# (keyed-child-address ~parent-addr ~item-key)]
        (with-dom-context keyed-addr# 0
          ~@body))))

;; =============================================================================
;; Function Versions (for programmatic/runtime use)
;; =============================================================================

(defn with-parent-addr-fn
  "Function version of with-parent-addr for runtime/programmatic use.

  Executes thunk with parent-addr set. Use the macro version in element
  macros for CPS/await support."
  [parent-addr thunk]
  (if-let [ctx ec/*execution-context*]
    (let [new-ctx (assoc-in ctx [:bindings :dom/parent-addr] parent-addr)]
      (binding [ec/*execution-context* new-ctx]
        (thunk)))
    (thunk)))

(defn with-slot-fn
  "Function version of with-slot for runtime/programmatic use.

  Executes thunk with slot-index set. Use the macro version in element
  macros for CPS/await support."
  [slot-index thunk]
  (if-let [ctx ec/*execution-context*]
    (let [new-ctx (assoc-in ctx [:bindings :dom/current-slot] slot-index)]
      (binding [ec/*execution-context* new-ctx]
        (thunk)))
    (thunk)))

(defn with-keyed-context-fn
  "Function version of with-keyed-context for runtime/programmatic use.

  Executes thunk with keyed child context. Use the macro version in element
  macros for CPS/await support."
  [parent-addr item-key thunk]
  (let [keyed-addr (keyed-child-address parent-addr item-key)]
    (with-parent-addr-fn keyed-addr
      (fn []
        (with-slot-fn 0 thunk)))))

;; =============================================================================
;; Address for Current Element
;; =============================================================================

(defn current-element-address
  "Compute address for an element at current context position.

  Combines source-loc with parent-addr and slot from context bindings."
  [source-loc]
  (compute-tree-address source-loc (get-parent-addr) (get-current-slot)))
