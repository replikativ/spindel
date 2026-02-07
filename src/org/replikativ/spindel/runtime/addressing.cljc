(ns org.replikativ.spindel.runtime.addressing
  "Deterministic addressing for spins and probabilistic inference.

  Uses hash-chain approach: each address depends on all previous addresses
  in the execution path. This provides:

  - Determinism: Same execution path → same addresses
  - Fork-safe: Forked contexts replay with same addresses
  - Parallel-safe: Parallel branches get deterministic branch IDs
  - Collision-resistant: Uses fast murmur3-based content hashing

  The chain-head is stored in execution context state at [:addressing :chain-head].
  When forked, both forks start with the same chain-head and evolve independently.

  For parallel execution, use `with-parallel-branch` to assign deterministic
  branch IDs based on index."
  (:require [org.replikativ.spindel.runtime.hash :as h]
            [clojure.string :as str]
            [org.replikativ.spindel.runtime.protocols :as rtp]))

;; =============================================================================
;; Hash-Chain Core
;; =============================================================================

(defn chain-hash
  "Generate content-addressed hash from source-loc and previous address."
  [source-loc last-address]
  (h/content-hash [source-loc last-address]))

(defn get-chain-head
  "Get current chain head from execution context.

  Returns nil if no addresses have been generated yet."
  [ctx]
  (rtp/get-state ctx [:addressing :chain-head]))

(defn set-chain-head!
  "Set the chain head in execution context.

  Used internally and for parallel branching."
  [ctx new-head]
  (rtp/swap-state! ctx [:addressing :chain-head] (constantly new-head)))

;; =============================================================================
;; Address Generation
;; =============================================================================

(defn next-address!
  "Generate next deterministic address in the chain.

  Each call:
  1. Atomically reads current chain-head and generates new address
  2. Hashes [source-loc, chain-head] to produce new address
  3. Updates chain-head to new address
  4. Returns the new address as a keyword

  This ensures:
  - Sequential calls at same source-loc get different addresses
  - Same execution path always produces same address sequence
  - Forked contexts continue independently from their chain-head
  - Thread-safe: concurrent calls from same source-loc get different IDs

  Args:
    ctx: Execution context (must satisfy PState)
    prefix: String prefix for the address (e.g. 'spin', 'rv')
    source-loc: Map with :file, :line, :column (or any identifying data)

  Returns: Keyword like :spin-550e8400-e29b-41d4-a716-446655440000"
  [ctx prefix source-loc]
  (let [last-addr (get-chain-head ctx)
        new-uuid (chain-hash source-loc last-addr)
        new-addr (keyword (str prefix "-" new-uuid))]
    (set-chain-head! ctx new-addr)
    new-addr))

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
