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

;; A convergent ygg-signal JOINS/APPLIES an incoming remote update into the local
;; value (so concurrent local + remote updates converge) instead of clobbering it
;; under blind LWW. ONE hook per perspective, plus a single sync/async mode flag —
;; the yggdrasil op is `async+sync` (it returns a VALUE on JVM / a partial-cps CPS
;; on cljs by the value's own mode), so there is no separate sync vs async hook;
;; `async?` just tells us whether to AWAIT the result or commit it directly:
;;
;;   `merge-fn`       (optional) `(fn [current incoming] -> merged|CPS)` — the
;;                    STATE-path JOIN (`c/-join`). Full value over the wire.
;;   `apply-delta-fn` (optional) `(fn [current delta] -> new|CPS)` — the OP-path
;;                    apply (`c/-apply-delta`): a live update ships just the op
;;                    (`{:delta δ}`), the receiver applies it — O(δ), no full state.
;;                    Sender side = `export-signal!`'s `:delta-fn`.
;;   `async?`         when true the two hooks return a partial-cps CPS (durable
;;                    `:sync? false` / cljs) that we await before committing; when
;;                    false they return a value committed directly.
;;
;; An incoming message is `{:delta δ}` (op-path) OR `{:value v}` (state-path); the
;; receiver dispatches on which key is present. With no `merge-fn`, a `{:value}` is
;; an LWW reset (the default; correct for ordinary last-writer-wins signals).
(defn- apply-incoming!
  "Apply an incoming sync `msg` to the strategy's signal. `{:delta δ}` → OP-path
   (`apply-delta-fn`); `{:value v}` → STATE-path (`merge-fn` JOIN, else LWW reset).
   Returns a channel yielding `{:ok true}` (or `{:error e}`) once committed — async
   so a konserve-backed join/apply can suspend before the commit."
  [{:keys [signal-atom on-update-fn merge-fn apply-delta-fn async?]} msg]
  (let [ch (chan 1)
        commit! (fn [v]
                  (cond
                    ;; IDEMPOTENT no-op: a convergent join/apply that added
                    ;; nothing returns the SAME value (the CRDT op returns the
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
                        (close! ch))))
        ;; ONE adapter for the async+sync result: a value (sync) is committed
        ;; directly; a CPS (async) is awaited, then committed on resolve.
        run! (fn [result]
               (if async?
                 (result commit! (fn [err] (put! ch {:error err}) (close! ch)))
                 (commit! result)))]
    (if (and apply-delta-fn (contains? msg :delta))
      (run! (apply-delta-fn @signal-atom (:delta msg)))         ; OP-path
      (let [v (:value msg)]
        (run! (if merge-fn (merge-fn @signal-atom v) v))))      ; STATE-path (join / LWW)
    ch))

(defrecord SignalSyncStrategy [signal-atom on-update-fn merge-fn apply-delta-fn async?]
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
    ;; Handshake always carries a full snapshot (STATE-path) — catch-up on connect.
    (apply-incoming! this {:value value}))

  (-apply-publish [this msg]
    ;; A live update: {:delta δ} (OP-path) or {:value v} (STATE-path).
    (apply-incoming! this msg)))

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
  [peer topic signal & {:keys [batch-size watch-key merge-fn delta-fn async?]
                        :or {batch-size 20}}]
  (let [wk (or watch-key (keyword "signal-sync" (name topic)))]
    ;; Register pub/sub topic with signal strategy
    (pubsub/register-topic! peer topic
                            {:strategy (->SignalSyncStrategy signal nil merge-fn nil async?)
                             :batch-size batch-size})

    ;; Watch signal for changes, publish either the OP (a δ — `delta-fn` yields the
    ;; local op) or the full STATE. With `delta-fn`, a value carrying NO δ is a
    ;; remote-integrated change → nothing to propagate (no echo); a value with a δ
    ;; ships just that op. Without `delta-fn`, ship the value (LWW, as before).
    (add-watch signal wk
               (fn [_ _ old-val new-val]
                 (when (not= old-val new-val)
                   (if delta-fn
                     (when-let [d (delta-fn new-val)]
                       (when (if (coll? d) (seq d) true)
                         (pubsub/publish! peer topic {:delta d})))
                     (pubsub/publish! peer topic {:value new-val})))))

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
  [peer topic & {:keys [initial-value on-update atom merge-fn apply-delta-fn async?]}]
  (let [;; Create local state holder
        local (or atom (clojure.core/atom initial-value))

        ;; Strategy: STATE-path (merge-fn) for full values + handshake, OP-path
        ;; (apply-delta-fn) for live deltas; `async?` awaits a CPS result (durable
        ;; cljs) vs commits a value directly (JVM / in-mem).
        strategy (->SignalSyncStrategy local on-update merge-fn apply-delta-fn async?)]

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
