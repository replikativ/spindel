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

  The context binding helpers (with-parent-addr, with-slot, with-dom-context)
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
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.addressing :as eaddr]
            [org.replikativ.spindel.engine.bindings :as bindings])
  #?(:cljs (:require-macros [org.replikativ.spindel.dom.addressing])))

;; =============================================================================
;; Spin scope key registration
;; =============================================================================
;;
;; :dom/parent-addr and :dom/current-slot are lexical scope for element
;; addressing — set by element macros around the point a spin is created.
;; A spin's body must address its elements under that same scope on every
;; re-run. Registering them as spin-scope keys (see engine.bindings) makes
;; the engine snapshot them at spin construction and re-establish them on
;; every body-entry path — without the engine ever naming a :dom/* key.

(bindings/register-spin-scope-key! :dom/parent-addr)
(bindings/register-spin-scope-key! :dom/current-slot)

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
  "Compute address for a keyed child.

  Uses the item's key instead of slot index, so identity is stable
  across reorderings of the surrounding collection.

  Two callers, two roles:
  - `dom/foreach`'s `for-each*` passes the `ifor-each`'s own (stable)
    address as `parent-addr` plus the item key — giving each item true
    position-independent identity.
  - `build-element` passes the element's own structural `my-addr` for a
    keyed element — there the key only disambiguates multiple keyed
    elements at the same source location (e.g. siblings from a `map`); it
    does NOT confer position-independent identity, since `my-addr` itself
    depends on slot. Position-independent identity is `ifor-each`'s job.

  Args:
    parent-addr - Address to scope the key under (see above)
    item-key    - The key extracted from the item (via key-fn)

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

     Used by element macros to set context before evaluating children.
     Requires an execution context to be bound."
     [parent-addr & body]
     `(let [new-ctx# (assoc-in ec/*execution-context* [:bindings :dom/parent-addr] ~parent-addr)]
        (binding [ec/*execution-context* new-ctx#]
          ~@body))))

#?(:clj
   (defmacro with-slot
     "Execute body with slot index set in context bindings.

     This is a MACRO that expands to a `binding` form, which partial-cps
     handles specially. Bindings are captured/restored across await points.

     Used by element macros for each child position.
     Requires an execution context to be bound."
     [slot-index & body]
     `(let [new-ctx# (assoc-in ec/*execution-context* [:bindings :dom/current-slot] ~slot-index)]
        (binding [ec/*execution-context* new-ctx#]
          ~@body))))

#?(:clj
   (defmacro with-dom-context
     "Execute body with both parent-addr and slot set.

     Convenience macro combining with-parent-addr and with-slot."
     [parent-addr slot-index & body]
     `(with-parent-addr ~parent-addr
        (with-slot ~slot-index
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
  "Execute `thunk` with keyed child context — used for ifor-each items.

  Sets :dom/parent-addr to (keyed-child-address parent-addr item-key) and
  :dom/current-slot to 0 (a keyed child is a single root element).

  In addition to the DOM bindings, this also forks the addressing chain-head
  by hashing the item-key into it for the duration of the thunk. That makes
  any spin or runtime address generated INSIDE thunk item-keyed (stable
  across reorderings of the surrounding collection) rather than position-
  keyed off the global sequential chain. Element addresses already use
  keyed-child-address; this aligns spin addresses with the same identity."
  [parent-addr item-key thunk]
  (let [keyed-addr (keyed-child-address parent-addr item-key)
        ctx (ec/current-execution-context)
        prev-head (when ctx (eaddr/get-chain-head ctx))
        ;; Match next-address!'s keyword form so subsequent hashing is identical
        item-head (when ctx
                    (keyword (str "keyed-"
                                  (eaddr/chain-hash {:keyed item-key} prev-head))))]
    (when ctx (eaddr/set-chain-head! ctx item-head))
    (try
      (with-parent-addr-fn keyed-addr
        (fn []
          (with-slot-fn 0 thunk)))
      (finally
        (when ctx (eaddr/set-chain-head! ctx prev-head))))))

;; =============================================================================
;; Address for Current Element
;; =============================================================================

(defn current-element-address
  "Compute address for an element at current context position.

  Combines source-loc with parent-addr and slot from context bindings."
  [source-loc]
  (compute-tree-address source-loc (get-parent-addr) (get-current-slot)))
