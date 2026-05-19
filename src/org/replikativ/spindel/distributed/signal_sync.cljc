(ns org.replikativ.spindel.distributed.signal-sync
  "Kabel pub/sub sync strategy for Spindel signals.

  Bridges Spindel's reactive signal system with Kabel's topic-based
  pub/sub, enabling signals to be observed across network peers.

  Server-side:
    (export-signal! peer :my-topic my-signal)
    ;; Signal changes are automatically published to subscribers

  Client-side:
    (def proxy (subscribe-signal! peer :my-topic))
    ;; proxy is a Spindel signal — track it in spins normally
    (spin (let [v (:new (track proxy))] (render v)))"
  (:require [kabel.pubsub :as pubsub]
            [kabel.pubsub.protocol :as proto]
            #?(:clj [clojure.core.async :as a :refer [chan put! close! go <! >!]]
               :cljs [cljs.core.async :as a :refer [chan put! close!]]))
  #?(:cljs (:require-macros [cljs.core.async.macros :refer [go]])))

;; =============================================================================
;; Signal Sync Strategy
;; =============================================================================

(defrecord SignalSyncStrategy [signal-atom on-update-fn]
  proto/PSyncStrategy

  (-init-client-state [_]
    ;; Client sends its current value hash, or closes channel if no state
    (let [ch (chan 1)
          current @signal-atom]
      (if (some? current)
        (do (put! ch {:hash (hash current)})
            (close! ch))
        (close! ch))
      ch))

  (-handshake-items [_ client-state]
    ;; Server sends current value if client doesn't have it
    (let [ch (chan 1)
          current @signal-atom
          client-hash (:hash client-state)]
      (when (and (some? current)
                 (or (nil? client-hash)
                     (not= (hash current) client-hash)))
        (put! ch {:type :snapshot :value current}))
      (close! ch)
      ch))

  (-apply-handshake-item [_ {:keys [value]}]
    ;; Client sets signal to server's value
    (let [ch (chan 1)]
      (try
        (reset! signal-atom value)
        (when on-update-fn (on-update-fn value))
        (put! ch {:ok true})
        (catch #?(:clj Exception :cljs js/Error) e
          (put! ch {:error e})))
      (close! ch)
      ch))

  (-apply-publish [_ {:keys [value]}]
    ;; Client applies update from server
    (let [ch (chan 1)]
      (try
        (reset! signal-atom value)
        (when on-update-fn (on-update-fn value))
        (put! ch {:ok true})
        (catch #?(:clj Exception :cljs js/Error) e
          (put! ch {:error e})))
      (close! ch)
      ch)))

;; =============================================================================
;; Server-Side API
;; =============================================================================

(defn export-signal!
  "Export a Spindel signal as a Kabel pub/sub topic.

  When the signal's value changes, publishes to all subscribers.
  Subscribers receive the current value via handshake on connect.

  Args:
    peer     - Kabel peer atom
    topic    - Topic keyword (e.g., :agent/glm-status)
    signal   - Spindel signal (or any atom-like watchable)
    opts     - Optional map:
               :batch-size       - handshake batch size (default 20)
               :watch-key        - key for add-watch (default topic)

  Returns: topic"
  [peer topic signal & {:keys [batch-size watch-key]
                        :or {batch-size 20}}]
  (let [wk (or watch-key (keyword "signal-sync" (name topic)))]
    ;; Register pub/sub topic with signal strategy
    (pubsub/register-topic! peer topic
                            {:strategy (->SignalSyncStrategy signal nil)
                             :batch-size batch-size})

    ;; Watch signal for changes, publish deltas
    (add-watch signal wk
               (fn [_ _ old-val new-val]
                 (when (not= old-val new-val)
                   (pubsub/publish! peer topic {:value new-val}))))

    topic))

(defn unexport-signal!
  "Stop exporting a signal. Removes watch and unregisters topic.

  Args:
    peer   - Kabel peer atom
    topic  - Topic keyword
    signal - The signal that was exported"
  [peer topic signal & {:keys [watch-key]}]
  (let [wk (or watch-key (keyword "signal-sync" (name topic)))]
    (remove-watch signal wk)
    (pubsub/unregister-topic! peer topic)))

;; =============================================================================
;; Client-Side API
;; =============================================================================

(defn subscribe-signal!
  "Subscribe to a remote signal via Kabel pub/sub.

  Returns an atom that is kept in sync with the server's signal.
  The atom can be used as a Spindel signal via (track proxy).

  For Spindel signal integration, pass :runtime and the returned
  value will be a proper Spindel signal.

  Args:
    peer    - Kabel client peer atom
    topic   - Topic keyword to subscribe to
    opts    - Optional map:
              :initial-value  - Initial value before handshake (default nil)
              :on-update      - (fn [new-val]) callback on each update
              :atom           - Use this atom instead of creating a new one

  Returns: atom holding the remote signal's value"
  [peer topic & {:keys [initial-value on-update atom]}]
  (let [;; Create local state holder
        local (or atom (clojure.core/atom initial-value))

        ;; Strategy that updates local atom/signal
        strategy (->SignalSyncStrategy local on-update)]

    ;; Subscribe via Kabel pub/sub
    (pubsub/subscribe! peer #{topic}
                       {:strategies {topic strategy}})

    local))

(defn unsubscribe-signal!
  "Unsubscribe from a remote signal.

  Args:
    peer  - Kabel client peer atom
    topic - Topic keyword"
  [peer topic]
  (pubsub/unsubscribe! peer #{topic}))
