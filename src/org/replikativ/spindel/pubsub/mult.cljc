(ns org.replikativ.spindel.pubsub.mult
  "Mult: Fan-out from PAsyncSeq to multiple taps.

   A mult takes a source PAsyncSeq and allows multiple consumers (taps) to
   independently receive all items. Each tap has its own buffer for backpressure.

   Key semantics (matching core.async):
   - Backpressure by default: producer waits until ALL taps accept
   - Per-tap buffers: each tap can have different buffer configuration
   - Rendezvous default: nil buffer means synchronous handoff
   - Lazy pump: pump spin starts on first tap

   Unlike core.async channels, PAsyncSeq is copy-on-read, so mult provides
   the coordination layer for synchronized fan-out."
  (:refer-clojure :exclude [await])
  (:require [is.simm.partial-cps.sequence :refer [PAsyncSeq anext]]
            [org.replikativ.spindel.pubsub.buffer :as buf]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.fault :as fault]
            #?(:clj [org.replikativ.spindel.spin.cps :refer [spin]])
            [org.replikativ.spindel.effects.await :refer [await]])
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]])))

;; =============================================================================
;; Fault reporting — delegates to the engine-wide hook (engine/fault.cljc)
;; =============================================================================

(defn set-fault-reporter!
  "Override how engine faults are reported — `::pump-rejected` here plus
   ALL engine fault events (`engine.fault/continuation-fault`,
   `engine.fault/executor-task-fault`, …). `f` is
   (fn [event-keyword data-map]). Default writes to stderr /
   console.error. simmis routes these into Telemere.

   Since the reporter was hoisted to `engine/fault.cljc`, this is a
   delegating alias kept for API compatibility — it sets the ENGINE-WIDE
   hook, not a mult-local one."
  [f] (fault/set-fault-reporter! f))

(defn- report-fault! [event data]
  (fault/report-fault! event data))

;; =============================================================================
;; Simple Promise for Coordination (no runtime required)
;; =============================================================================

(defn- make-promise
  "Create a simple promise that can be delivered once and read multiple times.
   Uses a standard Clojure atom - no runtime dependency.
   Uses compare-and-set! instead of swap! to avoid side effects inside retry-able swap fns.

   ## Cross-ctx delivery fix
   The watcher is the awaiter's `resolve` CPS continuation. When the
   producer's thread invokes it via `deliver!`, the Clojure dynamic var
   `*execution-context*` is whatever the producer has bound — often a
   different execution context from the one that registered the
   watcher. Without restoring the awaiter's ctx, the completion event
   gets enqueued on the producer's ctx, where no await-cont is
   registered for the awaiter's parent, and the parent deadlocks.

   We capture `*execution-context*` at `await-spin` construction
   (before the watcher is added) and re-establish it around the
   watcher invocation so the spin completes against its own ctx."
  []
  (let [state (atom {:delivered? false :value nil :watchers []})]
    {:state state
     :deliver! (fn [value]
                 (loop []
                   (let [s @state]
                     (if (:delivered? s)
                       value  ;; Already delivered - no-op
                       (if (compare-and-set! state s {:delivered? true :value value :watchers []})
                         ;; CAS succeeded - notify watchers from the state we replaced.
                         ;; Each watcher resumes a consumer spin; a watcher runs ON
                         ;; THE PRODUCER'S STACK (the source pump), so an unguarded
                         ;; throw there unwinds INTO the pump, cancels its await cont,
                         ;; and wedges the whole bus (dossier: bug-bus-source-pump-
                         ;; lost-waiter). Isolate each consumer fault: report it, keep
                         ;; delivering to the other watchers, never propagate to the
                         ;; producer.
                         (do (doseq [w (:watchers s)]
                               (try (w value)
                                    (catch #?(:clj Throwable :cljs :default) e
                                      (report-fault! ::watcher-fault {:error e}))))
                             value)
                         ;; CAS failed (concurrent modification) - retry
                         (recur))))))
     :await-spin (fn []
                   (let [captured-ctx (try (ec/current-execution-context)
                                           (catch #?(:clj Throwable :cljs :default) _ nil))]
                     (spin-core/make-spin
                      (fn [resolve _reject]
                        ;; Wrap resolve so the completion fires against the
                        ;; ctx that registered the await, not the producer's.
                        (let [wrapped (if captured-ctx
                                        (fn [v]
                                          (binding [ec/*execution-context* captured-ctx]
                                            (resolve v)))
                                        resolve)]
                          (loop []
                            (let [s @state]
                              (if (:delivered? s)
                                (wrapped (:value s))
                                ;; Try to add watcher via CAS
                                (when-not (compare-and-set! state s (update s :watchers conj wrapped))
                                  ;; CAS failed - retry (will re-check delivered? on next iteration)
                                  (recur))))))
                        spin-core/incomplete))))}))

(defn- deliver-promise! [p value]
  ((:deliver! p) value))

(defn- promise-spin [p]
  ((:await-spin p)))

;; =============================================================================
;; TapSeq - Per-tap async sequence
;; =============================================================================

(defrecord TapState
           [;; Buffer (nil = rendezvous)
            buffer
     ;; Promise: signaled when item available in buffer
     ;; Consumer awaits this when buffer is empty
            item-available-atom
     ;; Promise: signaled when space available in buffer
     ;; Producer awaits this when buffer is full
            space-available-atom
     ;; Whether this tap is closed
            closed?
     ;; Close when source closes?
            close-with-source?
     ;; Error if any
            error])

(defn- create-tap-state
  "Create initial tap state."
  [buffer close-with-source?]
  (->TapState buffer
              (atom (make-promise))    ; item-available-atom
              (atom (make-promise))    ; space-available-atom
              (atom false)             ; closed?
              close-with-source?
              (atom nil)))             ; error

(defn- signal-item-available!
  "Signal that an item is available. Creates fresh promise for next signal."
  [tap-state-atom]
  (let [old-promise @(:item-available-atom @tap-state-atom)]
    ;; Swap in fresh promise and signal old one
    (reset! (:item-available-atom @tap-state-atom) (make-promise))
    (deliver-promise! old-promise :item-available)))

(defn- signal-space-available!
  "Signal that space is available. Creates fresh promise for next signal."
  [tap-state-atom]
  (let [old-promise @(:space-available-atom @tap-state-atom)]
    ;; Swap in fresh promise and signal old one
    (reset! (:space-available-atom @tap-state-atom) (make-promise))
    (deliver-promise! old-promise :space-available)))

(deftype TapSeq [mult-ref tap-id tap-state-atom]
  PAsyncSeq
  (anext [this]
    (spin
      ;; Use loop instead of recursive (await (anext this)) to avoid
      ;; stack overflow in CLJS where promise delivery is synchronous
     (loop []
       (let [{:keys [buffer closed? error item-available-atom]} @tap-state-atom]
         (cond
            ;; Check for error first
           (and error @error)
           (throw @error)

            ;; Check if closed
           (and closed? @closed?)
           (if (and buffer (pos? (count buffer)))
              ;; Drain remaining buffer
             (let [item (buf/remove! buffer)]
               (signal-space-available! tap-state-atom)
               [item this])
              ;; Nothing left
             nil)

            ;; Check for rendezvous item (nil buffer case)
           (and (nil? buffer) (contains? @tap-state-atom :rendezvous-item))
           (let [item (:rendezvous-item @tap-state-atom)]
              ;; Remove item and signal space available
             (swap! tap-state-atom dissoc :rendezvous-item)
             (signal-space-available! tap-state-atom)
             [item this])

            ;; Try to get from buffer
           (and buffer (pos? (count buffer)))
           (let [item (buf/remove! buffer)]
             (signal-space-available! tap-state-atom)
             [item this])

            ;; Buffer empty (or rendezvous with no item) - wait for item.
            ;;
            ;; Check-act-recheck: capture the waiter promise BEFORE
            ;; re-reading state. A producer racing between our cond
            ;; check above and our waiter read would deliver the OLD
            ;; promise (currently in item-available-atom) and install
            ;; a NEW one. Without the recheck we'd capture the NEW
            ;; (undelivered) promise and hang forever. By capturing
            ;; first then re-checking, we either notice progress and
            ;; recur, or await the same promise the producer would
            ;; deliver to.
           :else
           (let [waiter @item-available-atom
                 state' @tap-state-atom]
             (cond
               (and (:error state') @(:error state'))
               (throw @(:error state'))
               (and (:closed? state') @(:closed? state'))
               (recur)
               (and (nil? (:buffer state'))
                    (contains? state' :rendezvous-item))
               (recur)
               (and (:buffer state') (pos? (count (:buffer state'))))
               (recur)
               :else
               (do (await (promise-spin waiter))
                   (recur))))))))))

(defn- close-tap!
  "Close a tap, optionally with error.

   Wakes both consumer-side and producer-side waiters. The
   producer-side wake is critical: when the pump is blocked on a
   full buffer's `space-available-atom` and the user untaps that
   tap, without this signal the pump would await on a promise that
   no other code path will ever deliver, jamming all remaining
   taps. The matching `:closed?` re-check in `deliver-to-all-taps!`
   ensures the pump cleanly skips delivery after waking instead of
   adding to the dead tap's buffer."
  [tap-state-atom & [error]]
  (when error
    (reset! (:error @tap-state-atom) error))
  (reset! (:closed? @tap-state-atom) true)
  ;; Wake any waiting consumer (anext awaiting an item).
  (signal-item-available! tap-state-atom)
  ;; Wake any waiting producer (pump blocked on full buffer or rendezvous).
  (signal-space-available! tap-state-atom))

;; =============================================================================
;; Mult
;; =============================================================================

(defprotocol PMult
  "Protocol for mult operations."

  (tap* [mult tap-id buffer close?]
    "Add a tap. Returns TapSeq for consuming.

     tap-id: Unique identifier for this tap
     buffer: Buffer instance or nil for rendezvous
     close?: Close tap when source closes")

  (untap* [mult tap-id]
    "Remove a tap by ID.")

  (untap-all* [mult]
    "Remove all taps."))

(defrecord Mult
           [;; Source PAsyncSeq
            source-aseq
     ;; {tap-id -> tap-state-atom}
            taps-atom
     ;; Is source closed?
            closed-atom
     ;; The pump spin (runs in background)
            pump-spin-atom
     ;; Has pump started?
            pump-started-atom])

(defn- deliver-to-all-taps!
  "Deliver item to all taps, respecting backpressure.

   Returns spin that completes when all taps have accepted (or are unblocking).

   Each producer-side await (`space-available-atom`) is followed by a
   `:closed?` re-check: an `untap` during the wait wakes us via
   `close-tap!`'s signal — without bailing out here we would either
   leak the rendezvous slot or add to a dead buffer."
  [taps-atom item]
  (spin
   (let [taps @taps-atom]
     (loop [tap-entries (seq taps)]
       (when tap-entries
         (let [[_tap-id tap-state-atom] (first tap-entries)
               {:keys [buffer closed? space-available-atom]} @tap-state-atom]
           (when-not @closed?
             (if (nil? buffer)
                ;; Rendezvous: signal item, wait for consumer to take.
                ;; Capture the space-available waiter BEFORE signaling
                ;; item-available, otherwise a fast consumer can take the
                ;; rendezvous-item and signal space-available before we
                ;; read the waiter, leaving us awaiting the (undelivered)
                ;; new waiter forever.
               (do
                 (swap! tap-state-atom assoc :rendezvous-item item)
                 (let [waiter @space-available-atom]
                   (signal-item-available! tap-state-atom)
                    ;; Recheck: if consumer already took the item before
                    ;; we awaited, we'd see no :rendezvous-item and need
                    ;; not wait. Otherwise wait on the captured waiter.
                   (when (contains? @tap-state-atom :rendezvous-item)
                     (await (promise-spin waiter))))
                  ;; Post-await: if the tap was closed during the wait,
                  ;; the consumer never took the rendezvous-item. Clean
                  ;; up the orphaned slot.
                 (when @closed?
                   (swap! tap-state-atom dissoc :rendezvous-item)))

                ;; Buffered: add to buffer, signal if was empty
               (do
                  ;; Wait for space if buffer is full (blocking buffers only).
                  ;; Same check-act-recheck pattern as on the consumer side.
                 (when (and (not (buf/unblocking? buffer))
                            (buf/full? buffer))
                   (let [waiter @space-available-atom]
                     (when (buf/full? buffer)
                       (await (promise-spin waiter)))))
                  ;; Post-await: if the tap was closed during the wait,
                  ;; adding to the buffer would leak the item into a dead
                  ;; tap. Skip the add and move on to the next tap.
                 (when-not @closed?
                   (buf/add! buffer item)
                   (signal-item-available! tap-state-atom)))))

           (recur (next tap-entries))))))))

(defn- start-pump!
  "Start the pump spin that pulls from source and delivers to taps.

   The pump runs as a detached spin - we enqueue its execution via the event system
   to ensure proper execution context binding."
  [mult]
  (let [{:keys [source-aseq taps-atom closed-atom pump-spin-atom]} mult
        ;; Capture context - needed for event-based execution
        context (ec/current-execution-context)
        pump (spin
              (loop [source source-aseq]
                (if-let [result (await (anext source))]
                  (let [[item rest-seq] result]
                     ;; Deliver to all taps
                    (await (deliver-to-all-taps! taps-atom item))
                    (recur rest-seq))
                   ;; Source exhausted
                  (do
                    (reset! closed-atom true)
                     ;; Close taps that requested close-with-source
                    (doseq [[_tap-id tap-state-atom] @taps-atom]
                      (when (:close-with-source? @tap-state-atom)
                        (close-tap! tap-state-atom)))))))]
    (reset! pump-spin-atom pump)
    ;; Kick off pump execution via event system (not future!)
    ;; This ensures execution context is properly bound when pump executes
    (ec/enqueue-event! {:type :spin-execution
                        :id (spin-core/spin-id pump)
                        :spin pump
                        :execution-context context
                        :resolve-fn (fn [_] nil)
                        ;; A pump rejection means the fan-out loop died — the mult
                        ;; is now deaf. This was swallowed with zero logging; make
                        ;; it loud. With consumer faults isolated (see deliver!) the
                        ;; pump should never reject on a consumer's behalf, so any
                        ;; rejection here is a genuine engine/source fault worth
                        ;; surfacing (the embedder's watchdog can then rebuild the
                        ;; bus). We do NOT auto-restart: the source position is lost
                        ;; on reject, so a naive restart would replay from the head.
                        :reject-fn (fn [reason]
                                     (report-fault! ::pump-rejected
                                                    {:reason reason
                                                     :spin-id (spin-core/spin-id pump)}))})
    pump))

(extend-type Mult
  PMult
  (tap* [mult tap-id buffer close?]
    (let [{:keys [taps-atom pump-started-atom]} mult
          tap-state-atom (atom (create-tap-state buffer close?))
          tap-seq (->TapSeq mult tap-id tap-state-atom)]
      ;; Register tap
      (swap! taps-atom assoc tap-id tap-state-atom)
      ;; Start pump on first tap (lazy)
      (when (compare-and-set! pump-started-atom false true)
        (start-pump! mult))
      tap-seq))

  (untap* [mult tap-id]
    (let [{:keys [taps-atom]} mult]
      (when-let [tap-state-atom (get @taps-atom tap-id)]
        (close-tap! tap-state-atom)
        (swap! taps-atom dissoc tap-id))))

  (untap-all* [mult]
    (let [{:keys [taps-atom]} mult]
      (doseq [[_tap-id tap-state-atom] @taps-atom]
        (close-tap! tap-state-atom))
      (reset! taps-atom {}))))

(defn mult
  "Create a mult over a source PAsyncSeq.

   Returns a Mult that can be tapped multiple times. Each tap receives
   all items from the source. The pump starts lazily on first tap.

   Example:
     (def m (mult source-aseq))
     (def tap1 (tap m (fixed-buffer 10)))
     (def tap2 (tap m))  ; rendezvous

     ;; Both tap1 and tap2 receive all items from source"
  [source-aseq]
  (->Mult source-aseq
          (atom {})     ; taps
          (atom false)  ; closed
          (atom nil)    ; pump-spin
          (atom false)  ; pump-started
          ))

;; =============================================================================
;; Public API
;; =============================================================================

(defn tap
  "Create a tap on a mult.

   Returns a PAsyncSeq that receives all items from the mult's source.

   Options:
     buffer - Buffer instance or nil for rendezvous (default: nil)
     close? - Close tap when source closes (default: true)

   Example:
     (tap m)                           ; rendezvous
     (tap m (fixed-buffer 10))         ; buffered
     (tap m (sliding-buffer 100))      ; sliding window
     (tap m nil false)                 ; rendezvous, don't auto-close"
  ([mult]
   (tap mult nil true))
  ([mult buffer]
   (tap mult buffer true))
  ([mult buffer close?]
   (let [tap-id (keyword (gensym "tap-"))]
     (tap* mult tap-id buffer close?))))

(defn untap
  "Remove a tap from mult by its TapSeq.

   Note: Currently requires tap-id. Consider storing tap-id in TapSeq
   for easier untap-by-reference."
  [mult tap-seq]
  (when (instance? TapSeq tap-seq)
    (untap* mult (.-tap-id tap-seq))))

(defn mult-pump
  "Get the pump spin for a mult.

   Returns nil if pump hasn't started (no taps yet).
   Can be used to await mult completion or check status."
  [mult]
  @(:pump-spin-atom mult))

(defn mult-closed?
  "Returns true if mult's source has been exhausted."
  [mult]
  @(:closed-atom mult))

(defn tap-closed?
  "Returns true if a tap has been closed (via untap or source close)."
  [tap-seq]
  (when (instance? TapSeq tap-seq)
    @(:closed? @(.-tap-state-atom tap-seq))))
