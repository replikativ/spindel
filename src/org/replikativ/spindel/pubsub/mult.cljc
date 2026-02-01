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
  (:require [is.simm.partial-cps.sequence :refer [PAsyncSeq anext]]
            [org.replikativ.spindel.pubsub.buffer :as buf]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.runtime.core :as rtc]
            #?(:clj [org.replikativ.spindel.spin.cps :refer [spin]])
            [org.replikativ.spindel.effects.await :refer [await]])
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]])))

;; =============================================================================
;; Simple Promise for Coordination (no runtime required)
;; =============================================================================

(defn- make-promise
  "Create a simple promise that can be delivered once and read multiple times.
   Uses a standard Clojure atom - no runtime dependency."
  []
  (let [state (atom {:delivered? false :value nil :watchers []})]
    {:state state
     :deliver! (fn [value]
                 (let [watchers-to-notify (atom nil)]
                   (swap! state (fn [s]
                                  (if (:delivered? s)
                                    s
                                    (do
                                      (reset! watchers-to-notify (:watchers s))
                                      {:delivered? true :value value :watchers []}))))
                   ;; Notify watchers
                   (doseq [w @watchers-to-notify]
                     (w value)))
                 value)
     :await-spin (fn []
                   (spin-core/make-spin
                    (fn [resolve _reject]
                      (let [s @state]
                        (if (:delivered? s)
                          (resolve (:value s))
                          ;; Add watcher - but check again in case delivered concurrently
                          (let [already-delivered? (atom false)]
                            (swap! state (fn [s]
                                           (if (:delivered? s)
                                             (do (reset! already-delivered? true) s)
                                             (update s :watchers conj resolve))))
                            (when @already-delivered?
                              (resolve (:value @state)))))
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

          ;; Buffer empty (or rendezvous with no item) - wait for item
          :else
          (do
            ;; Wait for item-available signal
            (await (promise-spin @item-available-atom))
            ;; Retry (state may have changed)
            (await (anext this))))))))

(defn- close-tap!
  "Close a tap, optionally with error."
  [tap-state-atom & [error]]
  (when error
    (reset! (:error @tap-state-atom) error))
  (reset! (:closed? @tap-state-atom) true)
  ;; Signal to wake up any waiting consumers
  (signal-item-available! tap-state-atom))

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

   Returns spin that completes when all taps have accepted (or are unblocking)."
  [taps-atom item]
  (spin
    (let [taps @taps-atom]
      (loop [tap-entries (seq taps)]
        (when tap-entries
          (let [[_tap-id tap-state-atom] (first tap-entries)
                {:keys [buffer closed? space-available-atom]} @tap-state-atom]
            (when-not @closed?
              (if (nil? buffer)
                ;; Rendezvous: signal item, wait for consumer to take
                ;; For rendezvous, we put the item in a temporary holder
                ;; and wait for consumer to acknowledge
                (do
                  ;; Store item for rendezvous pickup
                  (swap! tap-state-atom assoc :rendezvous-item item)
                  (signal-item-available! tap-state-atom)
                  ;; Wait for space (consumer took item)
                  (await (promise-spin @space-available-atom)))

                ;; Buffered: add to buffer, signal if was empty
                (do
                  ;; Wait for space if buffer is full (blocking buffers only)
                  (when (and (not (buf/unblocking? buffer))
                             (buf/full? buffer))
                    (await (promise-spin @space-available-atom)))
                  ;; Add to buffer
                  (buf/add! buffer item)
                  ;; Signal item available
                  (signal-item-available! tap-state-atom))))

            (recur (next tap-entries))))))))

(defn- start-pump!
  "Start the pump spin that pulls from source and delivers to taps.

   The pump runs as a detached spin - we deref it in a future to kick it off
   without blocking the caller."
  [mult]
  (let [{:keys [source-aseq taps-atom closed-atom pump-spin-atom]} mult
        ;; Capture context for CLJS callback
        context (rtc/current-execution-context)
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
    ;; Kick off pump execution in background
    ;; We need to invoke the spin to trigger execution
    #?(:clj (future @pump)
       :cljs (js/setTimeout #(binding [rtc/*execution-context* context]
                               (pump (fn [_] nil) (fn [_] nil))) 0))
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
