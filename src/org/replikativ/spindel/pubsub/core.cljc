(ns org.replikativ.spindel.pubsub.core
  "Zeitlauf Pub/Sub: Fan-out and topic-based routing for PAsyncSeq.

   This namespace provides pub/sub patterns for spindel, replacing core.async's
   pub/sub/mult patterns with spindel-native abstractions.

   Key Concepts:
   - Mult: Fan-out from single source to multiple consumers
   - Pub: Topic-based routing to per-topic mults
   - Buffer: Backpressure management (fixed, dropping, sliding)

   Semantics (matching core.async):
   - Backpressure by default: producer waits for consumers
   - Rendezvous default: nil buffer = synchronous handoff
   - Per-subscription buffers: each tap can have different buffering
   - Lazy pumps: start on first tap/subscription

   Example - Mult (fan-out):
     (require '[org.replikativ.spindel.pubsub.core :as pubsub])
     (require '[is.simm.partial-cps.sequence :refer [anext]])

     (def m (pubsub/mult source-aseq))
     (def tap1 (pubsub/tap m (pubsub/fixed-buffer 10)))
     (def tap2 (pubsub/tap m))  ; rendezvous

     ;; Both tap1 and tap2 receive all items from source

   Example - Pub (topic routing):
     (def p (pubsub/pub source-aseq :type))
     (def events-sub (pubsub/sub p :user-event))
     (def logs-sub (pubsub/sub p :log-entry))

     ;; events-sub receives items where (= :user-event (:type item))
     ;; logs-sub receives items where (= :log-entry (:type item))"
  (:require [org.replikativ.spindel.pubsub.buffer :as buffer]
            [org.replikativ.spindel.pubsub.mult :as mult]
            [org.replikativ.spindel.pubsub.pub :as pub]))

;; =============================================================================
;; Buffer API
;; =============================================================================

(def fixed-buffer
  "Create a fixed-size buffer. When full, producer blocks.
   (fixed-buffer 10)"
  buffer/fixed-buffer)

(def dropping-buffer
  "Create a dropping buffer. Never blocks - drops new items when full.
   (dropping-buffer 100)"
  buffer/dropping-buffer)

(def sliding-buffer
  "Create a sliding buffer. Never blocks - drops oldest items when full.
   (sliding-buffer 100)"
  buffer/sliding-buffer)

(def unblocking?
  "Returns true if buffer never blocks producer."
  buffer/unblocking?)

;; =============================================================================
;; Mult API
;; =============================================================================

(def mult
  "Create a mult over a source PAsyncSeq for fan-out.
   (mult source-aseq)"
  mult/mult)

(def tap
  "Create a tap on a mult. Returns PAsyncSeq receiving all items.
   (tap m)                      ; rendezvous
   (tap m (fixed-buffer 10))    ; buffered"
  mult/tap)

(def untap
  "Remove a tap from mult."
  mult/untap)

(def mult-pump
  "Get the pump spin for a mult (nil if not started)."
  mult/mult-pump)

(def mult-closed?
  "Returns true if mult's source is exhausted."
  mult/mult-closed?)

;; =============================================================================
;; Pub API
;; =============================================================================

(def pub
  "Create a pub over source with topic-based routing.
   (pub source-aseq :type)
   (pub source-aseq :type buf-fn)"
  pub/pub)

(def sub
  "Subscribe to a topic on a pub. Returns PAsyncSeq.
   (sub p :events)
   (sub p :events (fixed-buffer 10))"
  pub/sub)

(def unsub
  "Unsubscribe from a topic."
  pub/unsub)

(def unsub-all
  "Unsubscribe all from a pub."
  pub/unsub-all)

(def pub-closed?
  "Returns true if pub's source is exhausted."
  pub/pub-closed?)
