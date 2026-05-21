(ns org.replikativ.spindel.engine.addressing
  "Deterministic addressing for spins, elements, and other addressable
  reactive nodes.

  Two addressing schemes coexist here:

  1. **Trace addressing** (currently active for spins). `next-address!`
     mutates a chain-head cursor so each call mints a fresh id, hashing
     `[source-loc, last-address]` to produce the next.

     The chain-head is **per-spin** and stored in execution-context
     state: when `*spin-id*` is bound (i.e. we are inside some spin's
     body), reads and writes go to that spin's
     `[:addressing :chain-heads spin-id]`. When no spin context is
     active, a global slot at `[:addressing :chain-head]` is used as a
     fallback — e.g. for top-level signal/spin construction at app
     boot.

     (The cursor is kept under `:addressing` rather than on the
     `:nodes spin-id` SpinNode because a SpinNode may not exist yet
     when its body first runs — writing to a nested path through a
     missing record would create a plain map and break the PNode
     protocol on later access. `:addressing :chain-heads` is the
     transient addressing-only scratch space and never sees protocol
     dispatch.)

     There is *no* dedicated dynamic var for the chain-head cursor.
     The cursor lives in ctx state so that (a) `*execution-context*`
     remains the single source of truth, (b) the cursor follows the
     fork/snapshot semantics of the rest of the runtime for free, and
     (c) no CLJS-specific dynamic-var leak surface exists. At body
     entry the engine seeds the slot via `set-chain-head!` and at
     suspend the cont-map records the cursor value (under
     `:slice-state :chain-head`) so the engine can restore it at resume.

     Per-spin scoping has two consequences that solve real bugs:

     - Within one body run, the cursor advances monotonically, giving
       B-sites (pump loops, anext, deliver-to-all-taps, defn-spin-remote
       wrappers, …) distinct ids per call exactly like global trace did.
     - Across body re-runs, the cursor resets at body-start (engine
       responsibility — see Spin.invoke). The same code path produces
       the same id sequence each time, so factory functions called from
       a parent body get stable ids → A-site cache reuse, stable
       structural element addresses, no DOM duplication on re-render.

     Two concurrent body slices for the same spin both `swap-state!`
     on the same slot — the swap itself is atomic, and the cancel-token
     gate in the unified-subscription model ensures stale slices' work
     is dropped before it reaches the address site.

  2. **Structural addressing** (used by element macros; available as
     `next-id` / `with-key`). Identity is a pure function of
     `(source-loc, parent-id, key)`. Used by element addressing
     (`compute-tree-address`, `with-keyed-context-fn`). The `next-id`/
     `with-key` helpers below also extend the same model to spin ids,
     available as primitives even though the `spin` macro currently
     uses per-spin trace addressing."
  (:require [org.replikativ.spindel.engine.hash :as h]
            [clojure.string :as str]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.core :as ec])
  #?(:cljs (:require-macros [org.replikativ.spindel.engine.addressing])))

;; =============================================================================
;; Hash-Chain Core
;; =============================================================================

(defn chain-hash
  "Generate content-addressed hash from source-loc and previous address."
  [source-loc last-address]
  (h/content-hash [source-loc last-address]))

(defn body-start-chain-head
  "Compute the chain-head's deterministic starting value at body invocation.

  We can't just use `spin-id` as the starting value: if the parent
  context minted us with `parent-cursor → spin-id` and we then mint a
  child via the *same* source-loc the parent used (common in recursive
  factory code), the child's id collides with the parent's NEXT sibling
  (computed off `spin-id`). By seeding with `hash(spin-id, :body-start)`
  we move our chain off the parent's path so siblings-of-parent and
  first-children-of-first-sibling don't collapse."
  [spin-id]
  (keyword (str "body-start-"
                (h/content-hash [spin-id :body-start]))))

(defn- chain-head-path
  "Path into ctx state where the chain-head cursor for the currently
  active spin lives. When `*spin-id*` is bound the cursor is per-spin
  (`[:addressing :chain-heads spin-id]`); otherwise it's the
  context-global fallback (`[:addressing :chain-head]`) used for
  top-level signal/spin construction at app boot."
  []
  (if-let [sid ec/*spin-id*]
    [:addressing :chain-heads sid]
    [:addressing :chain-head]))

(defn get-chain-head
  "Get the current chain-head cursor from ctx state at the slot
  determined by `*spin-id*` (see `chain-head-path`)."
  [ctx]
  (rtp/get-state ctx (chain-head-path)))

(defn set-chain-head!
  "Set the chain-head cursor in ctx state at the slot determined by
  `*spin-id*`. Atomicity is provided by the state-backend's swap; the
  cancel-token gate in the engine ensures stale slices' writes never
  matter because the slice's resume callback is a no-op by then."
  [ctx new-head]
  (rtp/swap-state! ctx (chain-head-path) (constantly new-head)))

(defn seed-chain-head!
  "Engine-side helper: seed the per-spin chain-head cursor for
  `spin-id` with `new-head`. Used at body entry (with `body-start-…`)
  and at continuation resume (with the suspend-time snapshot)."
  [ctx spin-id new-head]
  (rtp/swap-state! ctx [:addressing :chain-heads spin-id]
                   (constantly new-head)))

(defn seed-body-chain-head!
  "Engine-side helper: seed the per-spin chain-head cursor for `spin-id`
  with its `body-start-chain-head`. Called by the engine at the start
  of every cache-miss / rebuild body invocation; resume paths use
  `seed-chain-head!` with the captured snapshot instead."
  [ctx spin-id]
  (seed-chain-head! ctx spin-id (body-start-chain-head spin-id)))

;; =============================================================================
;; Address Generation
;; =============================================================================

(defn next-address!
  "Generate the next deterministic address in the trace chain.

  Reads + advances the chain-head at the currently active slot
  (see `chain-head-path`).

  This gives B-sites distinct ids per call within one body run (cursor
  advances monotonically) and A-sites stable ids across body re-runs
  (engine resets the per-spin cursor at body-start, so the same call
  sequence produces the same hash chain).

  Args:
    ctx: Execution context (must satisfy PState)
    prefix: String prefix for the address (e.g. 'spin', 'rv', 'signal')
    source-loc: Map with :file, :line, :column (or any identifying data)

  Returns: Keyword like :spin-550e8400-e29b-41d4-a716-446655440000"
  [ctx prefix source-loc]
  (let [last-addr (get-chain-head ctx)
        new-uuid (chain-hash source-loc last-addr)
        new-addr (keyword (str prefix "-" new-uuid))]
    (set-chain-head! ctx new-addr)
    new-addr))

;; =============================================================================
;; Structural addressing (preferred for spins and elements)
;; =============================================================================

(defn next-id
  "Compute a deterministic structural id.

  Identity is a pure function of (prefix, source-loc, parent-id, key) —
  no global mutable cursor, no dependency on evaluation order. Two
  evaluations with the same scope and source-loc produce the same id;
  this is exactly what we want for caching reactive state by id.

  When two evaluations of the same source-loc need different ids
  (loop iterations, repeated component calls in the same parent), the
  caller pushes an `:address/key` binding via `with-key` and the key
  enters the hash.

  Args:
    prefix: String prefix for the address (e.g. \"spin\", \"effect\")
    source-loc: Map with :file, :line, :column
    parent-id: ID of the surrounding spin (or nil at the root)
    key: Optional discriminator (nil if not provided)

  Returns: Keyword like :spin-550e8400-e29b-41d4-a716-446655440000"
  [prefix source-loc parent-id key]
  (keyword (str prefix "-"
                (h/content-hash [source-loc parent-id key]))))

(defn current-key
  "Read the current `:address/key` binding from the execution context.

  Returns nil if no key is set. Used by `next-id` to disambiguate
  repeated evaluations at the same source-loc."
  [ctx]
  (when ctx
    (get-in ctx [:bindings :address/key])))

#?(:clj
   (defmacro with-key
     "Push an `:address/key` binding into the current execution context for
     the duration of body. Used to disambiguate repeated evaluations of the
     same `(spin ...)` or element form — for example, calling the same
     component-function twice in the same parent body, or per-iteration
     identity inside a loop.

     Example:
       (let [a (with-key (:id user-1) (render-user-card user-1))
             b (with-key (:id user-2) (render-user-card user-2))]
         …)

     Inside `render-user-card`'s body, the spin macro reads the key from
     the bindings and incorporates it into the spin id, so the two calls
     produce distinct ids."
     [k & body]
     `(let [cur-ctx# ec/*execution-context*]
        (if cur-ctx#
          (binding [ec/*execution-context*
                    (assoc-in cur-ctx# [:bindings :address/key] ~k)]
            ~@body)
          (do ~@body)))))

;; =============================================================================
;; Source Location Helpers
;; =============================================================================

(defn make-source-loc
  "Create source location map from macro expansion context.

  Used at macro-expansion time to capture file/line/column."
  [file line column]
  {:file file
   :line line
   :column column})

;; =============================================================================
;; Parallel Branching
;; =============================================================================

(defn branch-head
  "Compute the chain-head for a parallel branch.

  Each parallel branch gets a unique chain-head based on:
  - The current chain-head (before branching)
  - The branch index (0, 1, 2, ...)

  This ensures:
  - Different branches get different addresses
  - Same branch index always gets same chain-head (deterministic)
  - Order of parallel execution doesn't matter"
  [base-chain-head branch-index]
  (keyword (str "branch-" (h/content-hash [base-chain-head :parallel branch-index]))))

(defn with-parallel-branches
  "Execute functions in parallel branches with deterministic addressing.

  Each function receives a context with a unique branch chain-head.
  The branch-heads are computed from the current chain-head + index.

  After all branches complete, the original context's chain-head is
  updated to include all branch results (via hash).

  Args:
    ctx: Execution context
    branch-fns: Vector of (fn [branched-ctx] ...) functions

  Returns: Vector of results from each branch

  NOTE: The branched contexts share the same underlying state,
  but each has its own chain-head for address generation.
  For true isolation, fork the context first."
  [ctx branch-fns]
  (let [base-head (get-chain-head ctx)
        n (count branch-fns)

        ;; Compute all branch heads upfront (deterministic)
        branch-heads (mapv #(branch-head base-head %) (range n))

        ;; Execute each branch with its own chain-head
        ;; NOTE: This is sequential - for actual parallelism,
        ;; the caller should fork contexts and run on thread pool
        results (mapv
                 (fn [idx branch-fn]
                   (set-chain-head! ctx (nth branch-heads idx))
                   (branch-fn ctx))
                 (range n)
                 branch-fns)

        ;; Update chain-head to reflect all branches completed
        ;; This hash depends on base + all branch heads
        merged-head (keyword (str "merged-" (h/content-hash [base-head :merged branch-heads])))]

    (set-chain-head! ctx merged-head)
    results))

;; =============================================================================
;; Convenience Macros (CLJ only)
;; =============================================================================

#?(:clj
   (defmacro with-source-loc
     "Capture source location at macro expansion time."
     [& body]
     (let [source-loc {:file *file*
                       :line (:line (meta &form))
                       :column (:column (meta &form))}]
       `(let [~'*source-loc* ~source-loc]
          ~@body))))

;; =============================================================================
;; Debug Helpers
;; =============================================================================

(defn address-debug-info
  "Extract debug info from an address keyword.

  Returns the UUID part which can be looked up if needed."
  [addr]
  (when (keyword? addr)
    (let [s (name addr)]
      (when-let [idx (str/index-of s "-")]
        {:prefix (subs s 0 idx)
         :hash (subs s (inc idx))}))))
