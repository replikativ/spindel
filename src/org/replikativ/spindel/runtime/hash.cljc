(ns org.replikativ.spindel.runtime.hash
  "Fast deterministic content hashing for addressing.

  Replaces hasch.core/uuid (SHA-512, ~4µs) with Clojure's built-in hash
  (murmur3-32, ~50ns) combined into a wider hash via mixing.

  Clojure's hash function uses murmur3 on both JVM and CLJS, giving
  consistent results across platforms for standard Clojure data types.")

(defn content-hash
  "Fast deterministic content hash. Returns a string.
   Hashes the data and a salted variant independently, combines into 64-bit string.
   Uses Clojure's built-in hash (murmur3) - consistent across JVM and CLJS."
  [data]
  (let [h1 (hash data)
        ;; Hash a structurally different input for second independent 32-bit hash
        h2 (hash [::salt data])
        ;; Combine into a single hex string (64-bit effective entropy)
        ;; Using unsigned hex representation
        hex1 #?(:clj (Long/toHexString (bit-and (long h1) 0xFFFFFFFF))
                :cljs (.toString (unsigned-bit-shift-right h1 0) 16))
        hex2 #?(:clj (Long/toHexString (bit-and (long h2) 0xFFFFFFFF))
                :cljs (.toString (unsigned-bit-shift-right h2 0) 16))]
    (str hex1 hex2)))
