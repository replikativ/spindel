(ns org.replikativ.spindel.engine.hash
  "Fast deterministic content hashing for addressing.

  Uses hasch.fast/sha256-uuid for 128-bit cryptographic hashes (SHA-256)
  with cross-platform consistency (JVM + CLJS)."
  (:require [hasch.fast :as hf]))

(defn content-hash
  "Fast deterministic content hash. Returns a UUID.
   Uses hasch.fast SHA-256 — cryptographically secure, cross-platform consistent."
  [data]
  (hf/sha256-uuid data))
