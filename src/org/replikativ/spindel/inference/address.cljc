(ns org.replikativ.spindel.inference.address
  "Address generation and trace manipulation.

  Addresses are keywords that uniquely identify probabilistic choices.
  Traces are simple maps: {address -> value}.

  UNIFIED ADDRESSING: Uses hash-chain addressing from engine/addressing.
  The same mechanism is used by spins and choose sites for deterministic
  addresses that survive fork/restore.

  Hash-chain approach:
  - Each address = hash(source-loc, previous-address)
  - Sequential calls at same location get different addresses
  - Forked contexts with same chain-head get same address sequence
  - Collision-resistant: SHA-512 -> UUID-5 (128-bit) via hasch

  No more choice stack management - the hash-chain encodes the execution path."
  (:require [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.addressing :as addressing]))

;; =============================================================================
;; Address Generation (Unified with engine/addressing)
;; =============================================================================

(defn make-address
  "Generate unique address for random variable using hash-chain addressing.

  Uses the UNIFIED addressing system from engine/addressing:
  1. Source location (captured at macro expansion time)
  2. Previous addresses in the chain (hash-chain)
  3. Optional explicit name (for named variables)

  Each call advances the chain, so:
  - Sequential calls at same source-loc get different addresses
  - Forked contexts with same chain-head get same address sequence
  - No collisions (SHA-512 -> UUID-5, 128-bit)

  Args:
  - ctx: Execution context (must satisfy PState)
  - source-loc: Map with :file, :line, :column (from &env)
  - opts: Optional map with :name for named variables

  Returns: Keyword address like :rv-550e8400-e29b-41d4-a716-446655440000"
  ([ctx source-loc]
   (make-address ctx source-loc nil))
  ([ctx source-loc opts]
   (if-let [explicit-name (:name opts)]
     ;; Named variables get explicit address (doesn't advance chain)
     (keyword (str "rv-" (name explicit-name)))
     ;; Generate via hash-chain (advances chain)
     (addressing/next-address! ctx "rv" source-loc))))

;; =============================================================================
;; Trace Manipulation
;; =============================================================================

(defn extract-trace
  "Extract trace from execution context.

  Returns map: {address -> value}
  Trace is stored directly in [:inference :trace]."
  [context]
  (or (rtp/get-state context [:inference :trace]) {}))

(defn apply-trace
  "Apply trace values to execution context for MCMC replay.

  trace: Map of address -> value
  Used by MCMC kernels to replay with modified values."
  [context trace]
  (rtp/swap-state! context [:inference :trace] (constantly trace)))

(defn compatible-traces?
  "Check if two traces have compatible addresses.

  Traces are compatible if they have the same set of addresses.
  Required for merging particles or comparing MCMC proposals."
  [trace1 trace2]
  (= (set (keys trace1))
     (set (keys trace2))))

(defn merge-traces
  "Merge two compatible traces.

  Prefers values from trace2 (newer trace).
  Throws if traces are incompatible."
  [trace1 trace2]
  (when-not (compatible-traces? trace1 trace2)
    (throw (ex-info "Cannot merge incompatible traces"
                    {:addresses1 (keys trace1)
                     :addresses2 (keys trace2)})))
  (merge trace1 trace2))

;; =============================================================================
;; Address Registry
;; =============================================================================

(defn get-address-registry
  "Get registry of addresses encountered during execution.

  Returns map: address -> {:dist ... :metadata ...}"
  [context]
  (get-in context [:inference :address-registry] {}))

(defn register-address!
  "Register address with distribution and metadata.

  Used for tracking all random variables in a trace.
  Enables introspection and debugging."
  [context address dist metadata]
  (assoc-in context [:inference :address-registry address]
            {:dist dist
             :metadata metadata
             :first-seen #?(:clj (java.util.Date.)
                            :cljs (js/Date.))}))

(defn lookup-address
  "Look up distribution and metadata for address."
  [context address]
  (get-in context [:inference :address-registry address]))
