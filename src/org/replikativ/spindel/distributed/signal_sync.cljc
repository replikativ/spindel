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
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.engine.core :as ec]
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

   Both commit paths are race-free so a concurrent LOCAL `swap!` (or another apply) on
   the same signal is never lost — which would silently drop a peer's own write (the
   hub never echoes a peer its own δ, so the loss would be permanent). BOTH paths commit
   through the same `cas-read`+`cas!` loop (`compare-and-set`), re-integrating on a
   losing race — NOT `swap-vals!` (which throws on a SignalRef: it is IAtom, not IAtom2).
   This matters most on the async (durable/cljs) path: `await` is a cooperative yield
   point, so 'single-threaded' does NOT mean non-interleaved — a write landing during
   the suspension is detected by the CAS and the op re-run. `apply-delta-fn`/`merge-fn`
   are idempotent/commutative CRDT ops, safe under retry."
  [{:keys [signal-atom on-update-fn merge-fn apply-delta-fn sync?]} msg]
  (let [ch (chan 1)
        ;; The strategy's KIND, named once: a signal is CONVERGENT iff it carries any
        ;; conflict-resolving hook (STATE-path `merge-fn` and/or OP-path
        ;; `apply-delta-fn`); otherwise it is an ordinary LWW signal. A convergent
        ;; signal is NEVER blind-reset — the `:else` LWW branch is reachable only when
        ;; `(not convergent?)`, so a wire message we can't integrate is dropped, never
        ;; clobbered. (This is the transport-level kind; the yggdrasil protocol →
        ;; hook mapping lives in the `ygg-signal` seam, see `ygg-signal/sync-opts`.)
        convergent? (boolean (or merge-fn apply-delta-fn))
        ;; IDEMPOTENT no-op: a convergent op that added nothing returns the receiver
        ;; identically ⇒ no reactive tick and (crucially) no re-publish, so a
        ;; mutually-synced network does not run away re-joining equal states.
        finish! (fn [old new]
                  (if (identical? old new)
                    (do (put! ch {:ok true :changed? false}) (close! ch))
                    (do (when on-update-fn (on-update-fn new))
                        (put! ch {:ok true :changed? true})
                        (close! ch))))
        fail!   (fn [e] (put! ch {:error e}) (close! ch))
        ;; Commit `(integrate old)` against the signal via an atomic compare-and-set,
        ;; re-integrating on a losing race (a concurrent local swap! or another apply
        ;; landing in between) — nothing is lost, the CRDT op is idempotent/commutative.
        ;; `cas!`/`cas-read` work on a SignalRef AND a plain atom, whereas `swap-vals!`
        ;; throws on a SignalRef (IAtom, not IAtom2); `cas-read` returns the RAW value
        ;; `cas!` compares against (not `@`, which is unwrapped for a SignalRef and would
        ;; never match). `integrate` returns a VALUE (sync?, JVM/in-mem) or a partial-cps
        ;; CPS (async, durable/cljs — the konserve-backed join suspends before commit);
        ;; `run` normalizes both to "call k with the integrated value". Only the async
        ;; SignalRef path needs the execution context rebound across the post-IO resume
        ;; (it may land off the engine thread); the sync path stays on the calling thread.
        commit! (fn [integrate]
                  (let [ctx    (when (and (not sync?) (sig/signal-ref? signal-atom))
                                 (ec/current-execution-context))
                        rebind (fn [thunk] (if ctx (ec/with-context ctx (thunk)) (thunk)))
                        run    (fn [integrated k] (if sync? (k integrated) (integrated k fail!)))]
                    (letfn [(attempt []
                              (try
                                (let [old (rebind (fn [] (sig/cas-read signal-atom)))]
                                  (run (integrate old)
                                       (fn [new]
                                         (try
                                           (if (rebind (fn [] (sig/cas! signal-atom old new)))
                                             (finish! old new)
                                             (attempt))   ; value moved mid-commit — re-integrate
                                           (catch #?(:clj Exception :cljs js/Error) e (fail! e))))))
                                (catch #?(:clj Exception :cljs js/Error) e (fail! e))))]
                      (attempt))))]
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
      ;; CONVERGENT but no merge-fn for this {:value} (e.g. an OP-only signal taking a
      ;; connect-handshake snapshot): blind-resetting would LWW-CLOBBER concurrent
      ;; local state, so we IGNORE it — convergence rides the δ/state-fn path. (Wire
      ;; `state-fn` so the handshake ships a joinable δ, not a raw value — see
      ;; SignalSyncStrategy's state-fn note + `sync-signal!`.) Gated on the named
      ;; `convergent?` kind so the LWW `:else` is unreachable for convergent signals.
      convergent?
      (do (put! ch {:ok true :changed? false}) (close! ch))
      ;; STATE-path LWW (ordinary, non-convergent signal): a plain value, set directly.
      ;; This read-then-`reset!` is deliberately NON-atomic — unlike the convergent
      ;; `commit!` paths above, LWW semantics ARE last-writer-wins, so a concurrent
      ;; local `swap!` racing this reset is acceptable by definition (one of the two
      ;; writes wins; neither is a CRDT op that must be preserved). Only convergent
      ;; signals need the CAS loop (losing a peer's un-echoed δ would be permanent).
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
    ;; The connecting peer ships its PROJECTION (a joinable δ for a convergent value,
    ;; else the raw value), not just a hash — so the owner can INTEGRATE it during the
    ;; handshake. That makes the connect catch-up BIDIRECTIONAL (replikativ-style): two
    ;; peers each holding prior writes converge to the union, not only owner→joiner. The
    ;; `:hash` still lets the owner skip a no-op reply. (Convergent join is idempotent/
    ;; commutative, so the owner integrating + the joiner re-receiving is safe.)
    (let [ch (chan 1)
          current @signal-atom
          snap (when (some? current) (if state-fn (state-fn current) current))]
      (when (some? snap)
        (put! ch (cond-> {:hash (hash snap)}
                   state-fn       (assoc :delta snap)      ; convergent → joinable δ
                   (not state-fn) (assoc :value current)))) ; serializable / LWW value
      (close! ch)
      ch))

  (-handshake-items [this client-state]
    ;; SYMMETRIC catch-up: integrate the connecting peer's projection into OUR signal
    ;; (the direction that was missing — `apply-incoming!`, the same idempotent path
    ;; live publishes use) AND reply with OUR snapshot, so after one round-trip both
    ;; sides hold the union. Crucially we reply our PRE-integration snapshot (captured
    ;; here, before `apply-incoming!`), NOT the post-join value: the joiner integrates
    ;; our OWN state, whose nodes it has already synced (konserve-sync), rather than our
    ;; post-join union whose freshly-created nodes may not be shipped yet. Convergence
    ;; is symmetric — each side joins the other's own state. Integrating a remote value
    ;; carries no local δ ⇒ no echo on our watch.
    (let [out     (chan 1)
          current @signal-atom
          snap    (if state-fn (state-fn current) current)
          reply!  (fn []
                    (when (and (some? snap) (not= (hash snap) (:hash client-state)))
                      (put! out (if state-fn
                                  {:type :snapshot :delta snap}
                                  {:type :snapshot :value current})))
                    (close! out))]
      (if (or (contains? client-state :delta) (contains? client-state :value))
        ;; integrate the joiner's state, THEN reply our pre-captured snapshot
        (a/take! (apply-incoming! this client-state) (fn [_] (reply!)))
        (reply!))
      out))

  (-apply-handshake-item [this item]
    ;; Catch-up on connect: a snapshot is already {:delta …} (OP-path, convergent)
    ;; or {:value …} (STATE-path) — plus a :type tag apply-incoming! ignores — so
    ;; dispatch on it directly (apply-incoming! keys on :delta / :value).
    (apply-incoming! this item))

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

(declare sync-signal!)

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
  ;; export-signal! is publish-only `sync-signal!`: the owner of the topic, with no
  ;; apply-delta-fn (it ships δ/state out but does not OP-apply incoming δ — a
  ;; passed merge-fn still JOINs incoming {:value} on the STATE-path). Forwarding
  ;; keeps a SINGLE register-topic! + attach-publish-watch! path (see sync-signal!).
  [peer topic signal & opts]
  (apply sync-signal! peer topic signal :owner? true opts))

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

  Returns a plain atom kept in sync with the server's signal — a value holder.
  Read it with `@proxy`; for change notifications use `:on-update`. NOTE: a plain
  atom is NOT reactively trackable in a spin (`track` requires a SignalRef). To
  consume the remote value reactively, pass your own SignalRef as `:atom` (a pure
  subscriber never adds a watch, so a SignalRef is safe here) and `track` that.

  Args:
    peer    - Kabel client peer atom
    topic   - Topic keyword to subscribe to
    opts    - Optional map:
              :initial-value  - Initial value before handshake (default nil)
              :on-update      - (fn [new-val]) callback on each update
              :atom           - Hold state in this atom/SignalRef instead of a fresh atom
              :merge-fn       - STATE-path JOIN for convergent values (else LWW)
              :apply-delta-fn - OP-path apply for live deltas (`{:delta δ}`)
              :sync?          - true ⇒ hooks return a value; absent ⇒ await a CPS
              :state-fn       - project to a serializable handshake snapshot

  Returns: the atom (or SignalRef) holding the remote signal's value"
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
