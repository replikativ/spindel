(ns org.replikativ.spindel.pubsub.pub
  "Pub: Topic-based routing over PAsyncSeq.

   A pub takes a source PAsyncSeq and routes items to topic-specific mults
   based on a topic function. Subscribers subscribe to specific topics.

   Key semantics (matching core.async):
   - Topic function extracts topic from each item
   - Per-topic mults: each topic has its own mult for fan-out
   - Buffer function: customize buffer per topic
   - Lazy topic creation: mults created on first subscription to topic

   Example:
     (def p (pub source-aseq :type))
     (def events-sub (sub p :user-event))
     (def logs-sub (sub p :log-entry))"
  (:require [is.simm.partial-cps.sequence :refer [PAsyncSeq anext]]
            [org.replikativ.spindel.pubsub.mult :as mult]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.engine.core :as ec]
            #?(:clj [org.replikativ.spindel.spin.cps :refer [spin]])
            [org.replikativ.spindel.effects.await :refer [await]])
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]])))

;; =============================================================================
;; Internal Topic Mult Management
;; =============================================================================

;; Simple promise (same as in mult.cljc).
;; The await-spin captures *execution-context* at construction time and
;; re-binds it around the watcher's resolve invocation, so a producer
;; that delivers from a different ctx (e.g. a fork-ctx pump signaling
;; awaiters registered on a parent ctx) still enqueues the awaiter's
;; :spin-completion event on the awaiter's own ctx. See the same
;; comment in mult.cljc/make-promise for details.
(defn- make-promise
  "Create a simple promise that can be delivered once and read multiple times.
   Uses compare-and-set! instead of swap! to avoid side effects inside retry-able swap fns."
  []
  (let [state (atom {:delivered? false :value nil :watchers []})]
    {:state state
     :deliver! (fn [value]
                 (loop []
                   (let [s @state]
                     (if (:delivered? s)
                       value  ;; Already delivered - no-op
                       (if (compare-and-set! state s {:delivered? true :value value :watchers []})
                         ;; CAS succeeded - notify watchers from the state we replaced
                         (do (doseq [w (:watchers s)]
                               (w value))
                             value)
                         ;; CAS failed (concurrent modification) - retry
                         (recur))))))
     :await-spin (fn []
                   (let [captured-ctx (try (ec/current-execution-context)
                                           (catch #?(:clj Throwable :cljs :default) _ nil))]
                     (spin-core/make-spin
                      (fn [resolve _reject]
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

(defn- ensure-topic-mult!
  "Ensure a mult exists for the given topic. Creates one if needed.

   Returns the mult for the topic."
  [mults-atom topic]
  (or (:mult (get @mults-atom topic))
      (let [;; Create a promise-based async sequence for this topic
            ;; Items will be pushed when they arrive.
            ;; PersistentQueue is required for FIFO: vector + (rest) +
            ;; (conj item) corrupts order because rest returns a seq,
            ;; and conj on a seq prepends instead of appending.
            topic-items-atom (atom #?(:clj  clojure.lang.PersistentQueue/EMPTY
                                      :cljs cljs.core/PersistentQueue.EMPTY))
            topic-waiter-atom (atom (make-promise))  ; Single waiter promise
            topic-closed-atom (atom false)

            ;; Create async seq that pulls from topic-items
            topic-aseq (reify PAsyncSeq
                         (anext [this]
                           (spin
                            (cond
                               ;; Check for items
                              (seq @topic-items-atom)
                              (let [item (peek @topic-items-atom)]
                                (swap! topic-items-atom pop)
                                [item this])

                               ;; Closed with no items
                              @topic-closed-atom
                              nil

                               ;; No items - wait for notification.
                               ;; Check-act-recheck: capture waiter BEFORE
                               ;; re-checking items/closed, so a producer
                               ;; that delivers the OLD promise and installs
                               ;; a NEW one between our checks doesn't strand
                               ;; us awaiting the (undelivered) NEW promise.
                              :else
                              (let [waiter @topic-waiter-atom]
                                (if (or (seq @topic-items-atom)
                                        @topic-closed-atom)
                                  (await (anext this))
                                  (do (await (promise-spin waiter))
                                      (await (anext this)))))))))

            ;; Create mult over the topic seq
            topic-mult (mult/mult topic-aseq)

            ;; Store the push function for delivering items
            push-fn (fn [item]
                      (swap! topic-items-atom conj item)
                      ;; Signal that items are available
                      (let [old-promise @topic-waiter-atom]
                        (reset! topic-waiter-atom (make-promise))
                        (deliver-promise! old-promise :item-available)))

            close-fn (fn []
                       (reset! topic-closed-atom true)
                       ;; Signal close
                       (let [old-promise @topic-waiter-atom]
                         (reset! topic-waiter-atom (make-promise))
                         (deliver-promise! old-promise :closed)))]

        ;; Atomically add if not present
        (:mult (get (swap! mults-atom
                           (fn [mults]
                             (if (contains? mults topic)
                               mults
                               (assoc mults topic {:mult topic-mult
                                                   :push-fn push-fn
                                                   :close-fn close-fn}))))
                    topic)))))

;; =============================================================================
;; Pub Protocol
;; =============================================================================

(defprotocol PPub
  "Protocol for pub operations."

  (sub* [pub topic buffer close?]
    "Subscribe to a topic. Returns TapSeq for consuming.

     topic: Topic key (result of topic-fn)
     buffer: Buffer instance or nil for rendezvous
     close?: Close subscription when topic closes")

  (unsub* [pub topic tap-seq]
    "Unsubscribe from a topic.")

  (unsub-all* [pub]
    "Unsubscribe all from all topics.")

  (unsub-all-topic* [pub topic]
    "Unsubscribe all from a specific topic."))

;; =============================================================================
;; Pub Record
;; =============================================================================

(defrecord Pub
           [;; Source PAsyncSeq
            source-aseq
     ;; Function to extract topic from item
            topic-fn
     ;; Function (topic) -> buffer for new subscriptions
            buf-fn
     ;; {topic -> {:mult Mult :push-fn fn :close-fn fn}}
            mults-atom
     ;; Is source closed?
            closed-atom
     ;; The pump spin
            pump-spin-atom
     ;; Has pump started?
            pump-started-atom])

(defn- start-pub-pump!
  "Start the pump spin that pulls from source and routes to topic mults.

   The pump runs as a detached spin - we enqueue its execution via the event system
   to ensure proper execution context binding."
  [pub]
  (let [{:keys [source-aseq topic-fn mults-atom closed-atom pump-spin-atom]} pub
        ;; Capture runtime - needed for event-based execution
        runtime (ec/current-execution-context)
        pump (spin
              (loop [source source-aseq]
                (if-let [result (await (anext source))]
                  (let [[item rest-seq] result
                        topic (topic-fn item)]
                     ;; Ensure topic mult exists (auto-create if needed to prevent
                     ;; race between pump and late subscribers)
                    (ensure-topic-mult! mults-atom topic)
                    ((:push-fn (get @mults-atom topic)) item)
                    (recur rest-seq))
                   ;; Source exhausted
                  (do
                    (reset! closed-atom true)
                     ;; Close all topic mults
                    (doseq [[_topic {:keys [close-fn]}] @mults-atom]
                      (close-fn))))))]
    (reset! pump-spin-atom pump)
    ;; Kick off pump execution via event system (not future!)
    ;; This ensures execution context is properly bound when pump executes
    (ec/enqueue-event! {:type :spin-execution
                        :id (spin-core/spin-id pump)
                        :spin pump
                        :execution-context runtime
                        :resolve-fn (fn [_] nil)
                        :reject-fn (fn [_] nil)})
    pump))

(extend-type Pub
  PPub
  (sub* [pub topic buffer close?]
    (let [{:keys [mults-atom pump-started-atom]} pub
          topic-mult (ensure-topic-mult! mults-atom topic)]
      ;; Start pump on first subscription (lazy)
      (when (compare-and-set! pump-started-atom false true)
        (start-pub-pump! pub))
      ;; Create tap on topic mult
      (mult/tap topic-mult buffer close?)))

  (unsub* [pub topic tap-seq]
    (let [{:keys [mults-atom]} pub]
      (when-let [{:keys [mult]} (get @mults-atom topic)]
        (mult/untap mult tap-seq))))

  (unsub-all* [pub]
    (let [{:keys [mults-atom]} pub]
      (doseq [[_topic {:keys [mult]}] @mults-atom]
        (mult/untap-all* mult))
      (reset! mults-atom {})))

  (unsub-all-topic* [pub topic]
    (let [{:keys [mults-atom]} pub]
      (when-let [{:keys [mult close-fn]} (get @mults-atom topic)]
        (mult/untap-all* mult)
        (close-fn)
        (swap! mults-atom dissoc topic)))))

;; =============================================================================
;; Public API
;; =============================================================================

(defn pub
  "Create a pub over a source PAsyncSeq with topic-based routing.

   topic-fn: Function to extract topic from each item
   buf-fn:   Optional function (topic) -> buffer for new subscriptions (default: nil = rendezvous)

   Returns a Pub that can be subscribed to by topic.

   Example:
     ;; Route by :type field
     (def p (pub source-aseq :type))

     ;; Subscribe to specific topics
     (def user-events (sub p :user-event))
     (def system-logs (sub p :system-log))

     ;; Custom buffers per topic
     (def p2 (pub source-aseq :type
                  (fn [topic]
                    (case topic
                      :high-volume (sliding-buffer 1000)
                      :critical (fixed-buffer 100)
                      nil))))  ; rendezvous for others"
  ([source-aseq topic-fn]
   (pub source-aseq topic-fn (constantly nil)))
  ([source-aseq topic-fn buf-fn]
   (->Pub source-aseq
          topic-fn
          buf-fn
          (atom {})     ; mults
          (atom false)  ; closed
          (atom nil)    ; pump-spin
          (atom false)  ; pump-started
          )))

(defn sub
  "Subscribe to a topic on a pub.

   Returns a PAsyncSeq that receives items matching the topic.

   Options:
     buffer - Buffer instance or nil (default: uses pub's buf-fn)
     close? - Close subscription when topic closes (default: true)

   Example:
     (sub p :events)                        ; use pub's default buffer
     (sub p :events (fixed-buffer 10))      ; custom buffer
     (sub p :events nil false)              ; rendezvous, don't auto-close"
  ([pub topic]
   (sub pub topic ((:buf-fn pub) topic) true))
  ([pub topic buffer]
   (sub pub topic buffer true))
  ([pub topic buffer close?]
   (sub* pub topic buffer close?)))

(defn unsub
  "Unsubscribe from a topic."
  [pub topic tap-seq]
  (unsub* pub topic tap-seq))

(defn unsub-all
  "Unsubscribe all from a pub (all topics)."
  [pub]
  (unsub-all* pub))

(defn pub-closed?
  "Returns true if pub's source has been exhausted."
  [pub]
  @(:closed-atom pub))
