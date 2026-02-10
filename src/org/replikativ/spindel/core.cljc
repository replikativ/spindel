(ns org.replikativ.spindel.core
  "Spindel - Incremental Reactive Computation with Deterministic Execution

   Main entry point namespace. Re-exports core user-facing APIs so you can
   require a single namespace for most use cases:

     (require '[org.replikativ.spindel.core :as s :refer [spin signal await track]])

   For advanced usage, require individual namespaces directly."
  (:refer-clojure :exclude [for])
  (:require
   [org.replikativ.spindel.engine.context :as ctx]
   [org.replikativ.spindel.effects.await :as fx-await]
   [org.replikativ.spindel.effects.track :as fx-track]
   [org.replikativ.spindel.effects.yield :as fx-yield]
   [org.replikativ.spindel.spin.combinators :as combinators]
   [org.replikativ.spindel.spin.sync :as sync]
   [org.replikativ.spindel.incremental.deltaable :as deltaable]
   [org.replikativ.spindel.pubsub.buffer :as pubsub-buf]
   [org.replikativ.spindel.pubsub.mult :as pubsub-mult]
   [org.replikativ.spindel.pubsub.pub :as pubsub-pub]
   [org.replikativ.spindel.dom.router :as dom-router]
   [org.replikativ.spindel.dom.ssr :as ssr]
   #?(:clj [org.replikativ.spindel.spin.cps :as spin-cps])
   #?(:clj [org.replikativ.spindel.signal :as sig])
   #?(:clj [org.replikativ.spindel.seq.core :as seq-core]))
  #?(:cljs (:require-macros [org.replikativ.spindel.core :refer [spin signal batch gen-aseq for router link]])))

;; =============================================================================
;; Dynamic Bindings
;; =============================================================================

;; NOTE: *execution-context* cannot be re-exported as a proper binding target.
;; Use `ec/*execution-context*` directly with `binding`:
;;   (require '[org.replikativ.spindel.engine.core :as ec])
;;   (binding [ec/*execution-context* ctx] ...)

;; =============================================================================
;; Macros (CLJ-only definitions, CLJS gets them via :require-macros)
;; =============================================================================

#?(:clj
   (defmacro spin
     "Create a cached, reactive spin with automatic dependency tracking.
      See org.replikativ.spindel.spin.cps/spin for full docs."
     [& body]
     `(spin-cps/spin ~@body)))

#?(:clj
   (defmacro signal
     "Create a reactive signal with deterministic ID.
      See org.replikativ.spindel.signal/signal for full docs."
     [& args]
     `(sig/signal ~@args)))

#?(:clj
   (defmacro batch
     "Execute body with signal updates batched into a single reactive propagation.
      See org.replikativ.spindel.signal/batch for full docs."
     [& body]
     `(sig/batch ~@body)))

#?(:clj
   (defmacro gen-aseq
     "Generate a lazy async sequence using yield.
      See org.replikativ.spindel.seq.core/gen-aseq for full docs."
     [& body]
     `(seq-core/gen-aseq ~@body)))

#?(:clj
   (defmacro for
     "Async sequence comprehension with spindel effects support.
      See org.replikativ.spindel.seq.core/for for full docs."
     [seq-exprs body-expr]
     `(seq-core/for ~seq-exprs ~body-expr)))

;; =============================================================================
;; Effects (functions, work as CPS breakpoints when called inside spin)
;; =============================================================================

(def await
  "Suspend until spin/deferred value is available, track dependency.
   Use inside spin bodies, never use @ (deref) inside spins."
  fx-await/await)

(def track
  "Read signal with dual perspective {:keys [new old deltas]}.
   Use inside spin bodies for reactive signal observation."
  fx-track/track)

(def yield
  "Emit a value in an async sequence generator (gen-aseq)."
  fx-yield/yield)

;; =============================================================================
;; Runtime / Execution Context
;; =============================================================================

(def create-execution-context
  "Create a new root execution context."
  ctx/create-execution-context)

(def fork-context
  "Create a lightweight O(1) fork with copy-on-write overlay."
  ctx/fork-context)

(def snapshot-context
  "Create an immutable snapshot of context state."
  ctx/snapshot-context)

(def restore-snapshot
  "Restore a snapshot to create a live context."
  ctx/restore-snapshot)

(def stop-context!
  "Stop a context's background drain thread."
  ctx/stop-context!)

(def serialize-context
  "Serialize context to EDN for checkpointing/distribution."
  ctx/serialize-context)

(def deserialize-context
  "Deserialize EDN back to a live context."
  ctx/deserialize-context)

;; =============================================================================
;; Combinators
;; =============================================================================

(def parallel
  "Execute spins concurrently, return vector of results."
  combinators/parallel)

(def race
  "Return result of first spin to complete."
  combinators/race)

(def sleep
  "Create a spin that completes after given duration (ms)."
  combinators/sleep)

(def debounce
  "Delay delivery until quiet period elapses."
  combinators/debounce)

(def throttle
  "Limit delivery to max frequency."
  combinators/throttle)

(def timeout
  "Race a spin against a deadline with fallback value."
  combinators/timeout)

(def sample
  "Take value at fixed intervals."
  combinators/sample)

(def relieve
  "Drop intermediate values, keep latest."
  combinators/relieve)

(def accumulate
  "Accumulate intervals for delta preservation."
  combinators/accumulate)

;; =============================================================================
;; Synchronization Primitives
;; =============================================================================

(def deferred
  "Create a one-shot deferred value (uses *execution-context*)."
  sync/deferred)

(def deliver!
  "Deliver a value to a deferred from an external context."
  sync/deliver!)

(def mailbox
  "Create a mailbox for message passing (uses *execution-context*)."
  sync/mailbox)

(def post!
  "Post a message to a mailbox from an external context."
  sync/post!)

(def never
  "Create a spin that never completes."
  sync/never)

;; =============================================================================
;; Deltaable Collections
;; =============================================================================

(def deltaable-vector
  "Create a delta-tracking vector."
  deltaable/deltaable-vector)

(def deltaable-map
  "Create a delta-tracking map."
  deltaable/deltaable-map)

(def deltaable-set
  "Create a delta-tracking set."
  deltaable/deltaable-set)

;; =============================================================================
;; Pub/Sub
;; =============================================================================

(def mult
  "Create a mult over a source PAsyncSeq for fan-out."
  pubsub-mult/mult)

(def tap
  "Create a tap on a mult. Returns PAsyncSeq receiving all items."
  pubsub-mult/tap)

(def untap
  "Remove a tap from mult."
  pubsub-mult/untap)

(def pub
  "Create a pub over source with topic-based routing."
  pubsub-pub/pub)

(def sub
  "Subscribe to a topic on a pub. Returns PAsyncSeq."
  pubsub-pub/sub)

(def unsub
  "Unsubscribe from a topic."
  pubsub-pub/unsub)

;; =============================================================================
;; Buffer factories (for pub/sub)
;; =============================================================================

(def fixed-buffer
  "Create a fixed-size buffer. When full, producer blocks."
  pubsub-buf/fixed-buffer)

(def dropping-buffer
  "Create a dropping buffer. Never blocks - drops new items when full."
  pubsub-buf/dropping-buffer)

(def sliding-buffer
  "Create a sliding buffer. Never blocks - drops oldest items when full."
  pubsub-buf/sliding-buffer)

;; =============================================================================
;; Router
;; =============================================================================

#?(:clj
   (defmacro router
     "Create a signal-based router from route definitions.
      See org.replikativ.spindel.dom.router/router for full docs."
     [& args]
     `(dom-router/router ~@args)))

#?(:clj
   (defmacro link
     "Render an <a> element with click interception for client-side navigation.
      See org.replikativ.spindel.dom.router/link for full docs."
     [& args]
     `(dom-router/link ~@args)))

(def navigate!
  "Navigate to a new route (pushState)."
  dom-router/navigate!)

(def replace-route!
  "Navigate to a new route (replaceState, no new history entry)."
  dom-router/replace!)

(def route-href
  "Generate a path string from route name and params. Pure, no side effects."
  dom-router/href)

;; =============================================================================
;; Server-Side Rendering
;; =============================================================================

(def render-to-string
  "Render a vdom tree to an HTML string for SSR."
  ssr/render-to-string)
