(ns org.replikativ.spindel.incremental.deltaable.protocols
  "Protocols for deltaable collections.

   Defines the core protocols that deltaable types implement:
   - PDeltaable: delta tracking (get-deltas, deltaable?)
   - PWrapDeltaable: wrapping plain collections as deltaable
   - PUnwrapDeltaable: unwrapping deltaable to plain collections")

;; Protocol: Collection-Level Structural Deltas

(defprotocol PDeltaable
  "Protocol for collections that track structural changes as deltas.

   Collections implementing this protocol record operations (conj, assoc, dissoc)
   and make them available as a sequence of deltas.

   Delta format:
   {:delta :add/:remove/:update
    :path [:users 0 :name]
    :value new-value
    :old-value old-value}  ; For :update only"
  (get-deltas [this]
    "Returns sequence of deltas since last reset, or nil if no structural deltas.

     For simple values (numbers, strings, keywords): returns nil
     For collections (vectors, maps, sets): returns [{:delta ...} ...]")
  (deltaable? [this]
    "Returns true if this is a deltaable collection (DeltaableVector/Map/Set).
     Returns false for plain values and non-deltaable collections."))

;; Protocol: Wrapping Custom Types as Deltaable (for extensibility)

(defprotocol PWrapDeltaable
  "Protocol for wrapping custom types as deltaable collections.

   Extend this protocol to add deltaable tracking to your custom types.
   This enables signals to contain custom types with delta tracking.

   Note: With shallow wrapping, this only wraps the TOP-LEVEL.
   Nested values remain plain collections."
  (wrap-deltaable [x]
    "Wrap x as a top-level deltaable collection.

     - For already-deltaable collections: returns unchanged
     - For plain vectors/maps/sets: wraps as DeltaableVector/Map/Set
     - For custom types: define your own implementation
     - For other values: returns unchanged (treated as leaf values)"))

;; Protocol: Unwrapping Deltaables to Plain Collections

(defprotocol PUnwrapDeltaable
  "Protocol for unwrapping deltaable collections to plain collections.

   Symmetric counterpart to IWrapDeltaable. Extend this protocol to provide
   custom unwrapping behavior for your types."
  (unwrap-deltaable [x]
    "Recursively unwrap deltaable collections to plain collections.

     - For deltaable collections: recursively unwraps to plain vectors/maps/sets
     - For plain values: returns unchanged
     - For nil: returns nil

     This is the explicit way to compare deltaable collections with plain ones,
     since deltaables only equal other deltaables with matching value + deltas."))
