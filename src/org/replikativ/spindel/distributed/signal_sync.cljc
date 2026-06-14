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

;; A convergent ygg-signal JOINS an incoming remote value with the local one (so
;; concurrent local + remote updates converge) instead of clobbering it under
;; blind LWW. Two join hooks, mirroring the sync/async split of the value itself:
;;
;;   `merge-fn`       (optional) `(fn [current incoming] -> merged)` — a SYNC
;;                    join. In-memory convergent values + a JVM (`:sync? true`)
;;                    durable CRDT register with `merge-fn = c/-join`.
;;   `merge-await-fn` (optional) `(fn [current incoming] -> awaitable)` — an
;;                    ASYNC join returning a partial-cps CPS (what `c/-join`
;;                    returns for a durable CRDT opened `:sync? false`, i.e. a
;;                    cljs/konserve-backed value whose join suspends on IO). The
;;                    incoming value is committed only once the CPS resolves.
;;
;; At most one is set. nil/nil ⇒ LWW reset (the default; correct for ordinary
;; last-writer-wins signals). `merge-await-fn` takes precedence when both happen
;; to be present.
(defn- apply-incoming!
  "Apply an incoming remote `value` to the strategy's signal: JOIN (sync via
   `merge-fn`, or async via `merge-await-fn`) when convergent, else LWW reset.
   Returns a channel that yields `{:ok true}` (or `{:error e}`) once the value is
   committed — async so a konserve-backed join can suspend before the commit."
  [{:keys [signal-atom on-update-fn merge-fn merge-await-fn]} value]
  (let [ch (chan 1)
        commit! (fn [v]
                  (cond
                    ;; IDEMPOTENT no-op: a convergent join that added nothing
                    ;; returns the SAME value (the CRDT's -join returns the
                    ;; receiver identically). Skip the reset! entirely — no
                    ;; spurious reactive tick, and (crucially) no re-publish, so a
                    ;; mutually-synced peer network does not run away re-joining
                    ;; equal states.
                    (identical? v @signal-atom)
                    (do (put! ch {:ok true :changed? false}) (close! ch))
                    :else
                    (do (try
                          (reset! signal-atom v)
                          (when on-update-fn (on-update-fn @signal-atom))
                          (put! ch {:ok true :changed? true})
                          (catch #?(:clj Exception :cljs js/Error) e
                            (put! ch {:error e})))
                        (close! ch))))]
    (if merge-await-fn
      ;; Async join: the CPS runs the (possibly IO-suspending) join, then we
      ;; commit the merged value on resolve. `(merge-await-fn cur incoming)` is a
      ;; partial-cps `(fn [resolve reject])`.
      (let [cps (merge-await-fn @signal-atom value)]
        (cps commit!
             (fn [err] (put! ch {:error err}) (close! ch))))
      ;; Sync path: an in-memory join, or LWW reset.
      (commit! (if merge-fn (merge-fn @signal-atom value) value)))
    ch))

(defrecord SignalSyncStrategy [signal-atom on-update-fn merge-fn merge-await-fn]
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

  (-apply-handshake-item [this {:keys [value]}]
    ;; Client adopts server's value — JOIN when convergent, else LWW reset.
    (apply-incoming! this value))

  (-apply-publish [this {:keys [value]}]
    ;; Client applies update from server — JOIN when convergent, else LWW reset.
    (apply-incoming! this value)))

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
  [peer topic signal & {:keys [batch-size watch-key merge-fn merge-await-fn]
                        :or {batch-size 20}}]
  (let [wk (or watch-key (keyword "signal-sync" (name topic)))]
    ;; Register pub/sub topic with signal strategy
    (pubsub/register-topic! peer topic
                            {:strategy (->SignalSyncStrategy signal nil merge-fn merge-await-fn)
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
  [peer topic & {:keys [initial-value on-update atom merge-fn merge-await-fn]}]
  (let [;; Create local state holder
        local (or atom (clojure.core/atom initial-value))

        ;; Strategy that updates local atom/signal
        strategy (->SignalSyncStrategy local on-update merge-fn merge-await-fn)]

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
