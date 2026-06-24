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
            #?(:clj  [clojure.core.async :as a :refer [chan put! close!]]
               :cljs [cljs.core.async :as a :refer [chan put! close!]])))

;; =============================================================================
;; Signal Sync Strategy
;; =============================================================================

;; A convergent ygg-signal JOINS/APPLIES an incoming remote update into the local
;; value (so concurrent local + remote updates converge) instead of clobbering it
;; under blind LWW. ONE hook per perspective, plus the standard `:sync?` mode flag
;; (as in konserve / persistent-sorted-set / the yggdrasil durable layer: last
;; opt, DEFAULTS TO ASYNC when absent). The yggdrasil op is `async+sync` — it
;; returns a VALUE for `:sync? true` (JVM / in-mem) or a partial-cps CPS otherwise
;; (durable `:sync? false` / cljs) — so there is no separate sync vs async hook;
;; `sync?` just tells us whether to commit the result directly or await the CPS:
;;
;;   `merge-fn`       (optional) `(fn [current incoming] -> merged|CPS)` — the
;;                    STATE-path JOIN (`c/-join`). Full value over the wire.
;;   `apply-delta-fn` (optional) `(fn [current delta] -> new|CPS)` — the OP-path
;;                    apply (`c/-apply-delta`): a live update ships just the op
;;                    (`{:delta δ}`), the receiver applies it — O(δ), no full state.
;;                    Sender side = `export-signal!`'s `:delta-fn`.
;;   `sync?`          true ⇒ the hooks return a value (commit directly); absent/
;;                    false ⇒ a CPS we await before committing. Set it from the
;;                    caller's platform (JVM sync / cljs async) — the same `:sync?`
;;                    the convergent ops default to (a system carries no mode).
;;
;; An incoming message is `{:delta δ}` (op-path) OR `{:value v}` (state-path); the
;; receiver dispatches on which key is present. With no `merge-fn`, a `{:value}` is
;; an LWW reset (the default; correct for ordinary last-writer-wins signals) and
;; is committed directly regardless of `sync?` (a plain value, never a CPS).
(defn- apply-incoming!
  "Apply an incoming sync `msg` to the strategy's signal. `{:delta δ}` → OP-path
   (`apply-delta-fn`); `{:value v}` → STATE-path (`merge-fn` JOIN, else LWW reset).
   Returns a channel yielding `{:ok true}` (or `{:error e}`) once committed — async
   so a konserve-backed join/apply can suspend before the commit.

   The convergent paths integrate via an ATOMIC `swap-vals!` (sync) so a concurrent
   LOCAL `swap!` on the same signal is not lost to a blind reset! of a value computed
   from a stale read — which would silently drop a peer's own write (the hub never
   echoes a peer its own δ, so the loss would be permanent). `apply-delta-fn`/
   `merge-fn` are pure CRDT ops, safe under CAS retry. The async (durable/cljs) path
   is single-threaded, so compute-then-reset there is race-free."
  [{:keys [signal-atom on-update-fn merge-fn apply-delta-fn sync?]} msg]
  (let [ch (chan 1)
        ;; IDEMPOTENT no-op: a convergent op that added nothing returns the receiver
        ;; identically ⇒ no reactive tick and (crucially) no re-publish, so a
        ;; mutually-synced network does not run away re-joining equal states.
        finish! (fn [old new]
                  (if (identical? old new)
                    (do (put! ch {:ok true :changed? false}) (close! ch))
                    (do (when on-update-fn (on-update-fn new))
                        (put! ch {:ok true :changed? true})
                        (close! ch))))
        commit! (fn [integrate]
                  (try
                    (if sync?
                      ;; atomic recompute against the live value
                      (let [[old new] (swap-vals! signal-atom integrate)]
                        (finish! old new))
                      ;; async CPS: compute then await then reset (single-threaded)
                      (let [old @signal-atom]
                        ((integrate old)
                         (fn [v] (reset! signal-atom v) (finish! old v))
                         (fn [err] (put! ch {:error err}) (close! ch)))))
                    (catch #?(:clj Exception :cljs js/Error) e
                      (put! ch {:error e}) (close! ch))))]
    (cond
      ;; OP-path: apply just the delta (cheap, no full state).
      (contains? msg :delta)
      (if apply-delta-fn
        (commit! (fn [cur] (apply-delta-fn cur (:delta msg))))
        ;; A δ we can't apply (no apply-delta-fn on this perspective) — IGNORE it.
        ;; Do NOT fall through to the LWW branch (which would reset the signal to
        ;; nil and clobber state).
        (do (put! ch {:ok true :changed? false}) (close! ch)))
      ;; STATE-path JOIN (convergent): a value we know how to merge.
      merge-fn
      (commit! (fn [cur] (merge-fn cur (:value msg))))
      ;; CONVERGENT but OP-only (apply-delta-fn set, no merge-fn): a raw {:value}
      ;; (e.g. a connect-handshake snapshot) would LWW-CLOBBER concurrent local
      ;; state. The presence of a convergent hook marks this signal convergent, so
      ;; we must NEVER blind-reset it — IGNORE the value; convergence rides the
      ;; δ/state-fn path. (Wire `state-fn` so the handshake ships a joinable δ, not
      ;; a raw value — see SignalSyncStrategy's state-fn note + `sync-signal!`.)
      apply-delta-fn
      (do (put! ch {:ok true :changed? false}) (close! ch))
      ;; STATE-path LWW (ordinary, non-convergent signal): a plain value, set directly.
      :else
      (let [old @signal-atom]
        (reset! signal-atom (:value msg))
        (finish! old (:value msg))))
    ch))

;; `state-fn` (optional): project the local value to a SERIALIZABLE full-state
;; snapshot for the connect handshake (catch-up). A convergent CRDT *value* is not
;; wire-serializable (it carries stores + a comparator/join fn), so a late/
;; reconnecting joiner cannot receive the raw record — but it CAN receive the
;; value's plain-data projection (`g/elements` for a G-Set, the OR-map's map, …)
;; and apply it as a δ into its own empty replica. With `state-fn`, the handshake
;; ships `{:type :snapshot :delta (state-fn current)}` (plain data) and the joiner
;; integrates it via `apply-delta-fn` — exactly the replikativ metadata-catch-up.
;; Without it, the handshake ships the raw value (`{:value}`) — fine for ordinary
;; serializable LWW signals.
(defrecord SignalSyncStrategy [signal-atom on-update-fn merge-fn apply-delta-fn sync? state-fn]
  proto/PSyncStrategy

  (-init-client-state [_]
    ;; Client sends the hash of its current (plain-projected) value, or closes if none.
    (let [ch (chan 1)
          current @signal-atom]
      (if (some? current)
        (do (put! ch {:hash (hash (if state-fn (state-fn current) current))})
            (close! ch))
        (close! ch))
      ch))

  (-handshake-items [_ client-state]
    ;; Server sends its current value if the client doesn't already have it. With
    ;; `state-fn` the snapshot is the plain-data projection shipped as a δ (so a
    ;; non-serializable CRDT value still crosses); otherwise the raw value.
    (let [ch (chan 1)
          current @signal-atom
          client-hash (:hash client-state)
          snap (if state-fn (state-fn current) current)]
      (when (and (some? current)
                 (or (nil? client-hash)
                     (not= (hash snap) client-hash)))
        (put! ch (if state-fn
                   {:type :snapshot :delta snap}
                   {:type :snapshot :value current})))
      (close! ch)
      ch))

  (-apply-handshake-item [this item]
    ;; Catch-up on connect: a plain-data `:delta` snapshot (OP-path, convergent) or
    ;; a full `:value` snapshot (STATE-path).
    (apply-incoming! this (if (contains? item :delta)
                            {:delta (:delta item)}
                            {:value (:value item)})))

  (-apply-publish [this msg]
    ;; A live update: {:delta δ} (OP-path) or {:value v} (STATE-path).
    (apply-incoming! this msg)))

;; =============================================================================
;; Server-Side API
;; =============================================================================

;; A watch that ships the local δ (or full value) on every change — the publishing
;; half shared by export-signal! and sync-signal!.
(defn- attach-publish-watch! [peer topic signal wk delta-fn clear-delta-fn]
  (add-watch signal wk
             (fn [_ _ old-val new-val]
               (when (not= old-val new-val)
                 (if delta-fn
                   (when-let [d (delta-fn new-val)]
                     (when (if (coll? d) (seq d) true)
                       (pubsub/publish! peer topic {:delta d})
                       ;; Clear the δ we just shipped so it doesn't re-accrue + re-ship.
                       ;; `=`-preserving (δ lives in metadata) ⇒ this re-seat's watch
                       ;; fire short-circuits on the `(not= old new)` guard above.
                       (when clear-delta-fn (swap! signal clear-delta-fn))))
                   (pubsub/publish! peer topic {:value new-val}))))))

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
               :delta-fn         - extract the local δ to ship just the OP (else ship state)
               :clear-delta-fn   - drop the just-shipped δ from the signal (OP-path only): keeps
                                   the local δ bounded — without it deltas ACCRUE in the value's
                                   metadata, so every op re-ships the whole accumulated δ and memory
                                   grows unboundedly. Clearing is a pure metadata op (`=`-preserving),
                                   so the re-seat does NOT re-fire the watch.
               :merge-fn         - JOIN an incoming remote {:value} into the local one (convergent
                                   STATE-path). Pass it for CRDT signals so an incoming value is
                                   merged, never LWW-reset. (`sync-signal!` wires this for you.)
               :state-fn         - project the local value to a serializable snapshot for the
                                   connect handshake (a non-serializable CRDT value ships its
                                   plain-data projection as a δ instead of a raw value).
               :sync?            - run the strategy's apply path synchronously (JVM) vs async.

  Returns: topic"
  [peer topic signal & {:keys [batch-size watch-key merge-fn delta-fn clear-delta-fn sync? state-fn]
                        :or {batch-size 20}}]
  (let [wk (or watch-key (keyword "signal-sync" (name topic)))]
    ;; Register pub/sub topic with signal strategy
    (pubsub/register-topic! peer topic
                            {:strategy (->SignalSyncStrategy signal nil merge-fn nil sync? state-fn)
                             :batch-size batch-size})

    ;; Watch signal for changes, publish either the OP (a δ — `delta-fn` yields the
    ;; local op) or the full STATE. With `delta-fn`, a value carrying NO δ is a
    ;; remote-integrated change → nothing to propagate (no echo); a value with a δ
    ;; ships just that op. Without `delta-fn`, ship the value (LWW, as before).
    (attach-publish-watch! peer topic signal wk delta-fn clear-delta-fn)

    topic))

(defn sync-signal!
  "BIDIRECTIONAL convergent sync of a signal over a kabel pub/sub topic — the
   symmetric union of `export-signal!` (publish the local δ) and `subscribe-signal!`
   (apply a remote δ) on ONE shared `signal`. EVERY peer calls this; the kabel hub
   relays each peer's δ to all the others (`pubsub.cljc` applies an incoming publish
   to the local strategy AND, on the topic owner, re-fans it to the other
   subscribers), and each peer integrates it via `apply-delta-fn` (OP-path) or
   `merge-fn` (STATE-path / handshake).

   No runaway: the CRDT join is idempotent (an apply that adds nothing returns the
   receiver `identical?` → `apply-incoming!` skips the reset! and re-publish), an
   integrated remote value carries no δ (`delta-fn` → nil → the watch publishes
   nothing), and `clear-delta-fn` bounds the shipped δ.

   TOPOLOGY: kabel.pubsub forwards only from the topic OWNER, so pass `:owner? true`
   on exactly ONE peer (the hub/server — it `register-topic!`s); every other peer
   omits it and `subscribe!`s. The owner still publishes + applies like everyone
   else; it is just additionally the relay.

   opts:
     :owner?          this peer owns the topic (register-topic!) vs subscribe!
     :merge-fn        STATE-path JOIN `(fn [cur incoming])` — used for the connect
                      handshake (catch-up); for a non-serializable CRDT value start
                      the signal at the empty replica and rely on the δ path instead.
     :apply-delta-fn  OP-path apply `(fn [cur δ])` (`c/-apply-delta`).
     :delta-fn        extract the local δ to ship just the op (else ship full value).
     :clear-delta-fn  drop the just-shipped δ (keeps it bounded).
     :sync?           true ⇒ hooks return a value (JVM/in-mem); absent ⇒ await a CPS.
     :batch-size :watch-key  as in export-signal!."
  [peer topic signal & {:keys [owner? batch-size watch-key merge-fn apply-delta-fn delta-fn clear-delta-fn sync? state-fn]
                        :or {batch-size 20}}]
  (let [wk       (or watch-key (keyword "signal-sync" (name topic)))
        strategy (->SignalSyncStrategy signal nil merge-fn apply-delta-fn sync? state-fn)]
    (if owner?
      (pubsub/register-topic! peer topic {:strategy strategy :batch-size batch-size})
      (pubsub/subscribe! peer #{topic} {:strategies {topic strategy}}))
    (attach-publish-watch! peer topic signal wk delta-fn clear-delta-fn)
    topic))

(defn unsync-signal!
  "Stop a bidirectional sync: remove the publish watch and detach the topic
   (unregister if owner, else unsubscribe)."
  [peer topic signal & {:keys [owner? watch-key]}]
  (let [wk (or watch-key (keyword "signal-sync" (name topic)))]
    (remove-watch signal wk)
    (if owner?
      (pubsub/unregister-topic! peer topic)
      (pubsub/unsubscribe! peer #{topic}))))

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
  [peer topic & {:keys [initial-value on-update atom merge-fn apply-delta-fn sync? state-fn]}]
  (let [;; Create local state holder
        local (or atom (clojure.core/atom initial-value))

        ;; Strategy: STATE-path (merge-fn) for full values + handshake, OP-path
        ;; (apply-delta-fn) for live deltas; `:sync? true` commits a value directly
        ;; (JVM / in-mem), absent/false awaits a CPS result (durable cljs).
        strategy (->SignalSyncStrategy local on-update merge-fn apply-delta-fn sync? state-fn)]

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
