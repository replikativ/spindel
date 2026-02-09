(ns org.replikativ.spindel.runtime.cache
  "Global content-addressed cache for spin results.

  Enables sharing computation across execution contexts (forks) when
  dependency values are identical.

  Cache key: [spin-id deps-hash effect-ctx-hash]
  - spin-id: Which spin (code)
  - deps-hash: Content hash of dependency VALUES (not IDs)
  - effect-ctx-hash: Hash of effect handler configuration (nil for now)

  When multiple forks have identical dependency values, they share the same
  deps-hash and get cache hits, avoiding redundant computation.

  Performance: Uses fast murmur3-based content hashing."
  (:require [org.replikativ.spindel.runtime.hash :as h]
            [org.replikativ.spindel.log :as log]))

;; =============================================================================
;; Global Cache
;; =============================================================================

(defonce global-cache
  ^{:doc "Global content-addressed cache shared across all execution contexts.

  Structure: {[spin-id deps-hash effect-ctx-hash] Result}

  Example:
    {[spin-123 #uuid \"abc...\" nil] {:status :ok :value 42}
     [spin-123 #uuid \"xyz...\" nil] {:status :ok :value 99}
     [spin-456 #uuid \"abc...\" nil] {:status :ok :value 100}}

  Note: Same spin-id with different deps-hash = different cache entries.
        Different spin-ids with same deps-hash = independent entries."}
  (atom {}))

;; =============================================================================
;; Content Hashing
;; =============================================================================

(defn compute-deps-identity
  "Compute identity hash from dependency generations (O(1) per dependency).

  Instead of hashing entire VALUES (which can be 10k+ items), this function
  hashes {signal-id -> generation} pairs. Since generation is a monotonically
  increasing integer that changes whenever the signal value changes, this
  provides the same cache invalidation semantics as content hashing but in O(1).

  Args:
    signal-generations - Map of {signal-id generation}, e.g. {sig-1 5, sig-2 12}
    spin-hashes        - Map of {spin-id deps-hash}, e.g. {spin-a #uuid \"...\"}
    effect-ctx-hash    - Hash of effect handler config (nil for MVP)

  Returns: UUID-5 derived from generations via hasch.core

  Example:
    (compute-deps-identity {:sig-1 5 :sig-2 12} {:spin-a #uuid \"...\"} nil)
    ;=> #uuid \"def-456...\"

  Property: Same generations → same hash
  Property: Different generations → different hash (cache miss, recompute)"
  [signal-generations spin-hashes effect-ctx-hash]
  (h/content-hash
    {:signals signal-generations
     :spins spin-hashes
     :effect-ctx effect-ctx-hash}))

;; =============================================================================
;; Cache Operations
;; =============================================================================

(defn lookup
  "Lookup cached result by content address.

  Args:
    spin-id - Spin identifier
    deps-hash - Content hash of dependency values
    effect-ctx-hash - Effect handler configuration hash (nil for now)

  Returns: Result record or nil if not in cache

  Example:
    (lookup spin-123 #uuid \"abc...\" nil)
    ;=> {:status :ok :value 42 :completed? true}
    ;; or nil if not cached"
  [spin-id deps-hash effect-ctx-hash]
  (let [cache-key [spin-id deps-hash effect-ctx-hash]
        result (get @global-cache cache-key)]
    (when result
      (log/trace! {:event :cache/lookup-hit
                   :data {:spin-id spin-id :deps-hash deps-hash}}))
    result))

(defn store!
  "Store result in global cache at content address.

  Args:
    spin-id - Spin identifier
    deps-hash - Content hash of dependency values
    effect-ctx-hash - Effect handler configuration hash (nil for now)
    result - Result record to cache

  Returns: result (for chaining)

  Example:
    (store! spin-123 #uuid \"abc...\" nil
            {:status :ok :value 42 :completed? true})
    ;=> {:status :ok :value 42 :completed? true}

  Side effects: Adds entry to global-cache atom"
  [spin-id deps-hash effect-ctx-hash result]
  (let [cache-key [spin-id deps-hash effect-ctx-hash]]
    (swap! global-cache assoc cache-key result)
    (log/trace! {:event :cache/store
                 :data {:spin-id spin-id :deps-hash deps-hash}})
    result))

;; =============================================================================
;; Cache Management
;; =============================================================================

(defn stats
  "Get cache statistics.

  Returns: Map with :total-entries and :memory-estimate

  Example:
    (stats)
    ;=> {:total-entries 1234
    ;    :memory-estimate 123400}"
  []
  (let [entry-count (count @global-cache)]
    {:total-entries entry-count
     ;; Rough estimate: 100 bytes per entry (very approximate!)
     :memory-estimate (* entry-count 100)}))

(defn clear!
  "Clear entire global cache.

  Useful for testing or manual cache invalidation.

  Returns: nil

  Side effects: Resets global-cache to empty map"
  []
  (reset! global-cache {})
  (log/debug! {:event :cache/cleared})
  nil)

(defn evict!
  "Evict specific cache entry.

  Args:
    spin-id - Spin identifier
    deps-hash - Content hash
    effect-ctx-hash - Effect context hash

  Returns: true if entry existed, false otherwise

  Side effects: Removes entry from global-cache if present"
  [spin-id deps-hash effect-ctx-hash]
  (let [cache-key [spin-id deps-hash effect-ctx-hash]
        existed? (contains? @global-cache cache-key)]
    (swap! global-cache dissoc cache-key)
    (when existed?
      (log/debug! {:event :cache/evicted
                   :data {:spin-id spin-id :deps-hash deps-hash}}))
    existed?))

;; =============================================================================
;; Debugging Helpers
;; =============================================================================

(defn cache-keys
  "Get all cache keys for inspection.

  Returns: Seq of [spin-id deps-hash effect-ctx-hash] tuples

  Useful for debugging cache behavior."
  []
  (keys @global-cache))

(defn cache-entries
  "Get all cache entries for inspection.

  Returns: Map of cache-key → result

  WARNING: This can be large! Use for debugging only."
  []
  @global-cache)

(defn cache-for-spin
  "Get all cached entries for a specific spin-id.

  Args:
    spin-id - Spin identifier

  Returns: Map of deps-hash → result

  Example:
    (cache-for-spin spin-123)
    ;=> {#uuid \"abc...\" {:status :ok :value 42}
    ;    #uuid \"xyz...\" {:status :ok :value 99}}"
  [spin-id]
  (into {}
    (keep (fn [[[tid deps-hash _eff-ctx] result]]
            (when (= tid spin-id)
              [deps-hash result]))
          @global-cache)))
