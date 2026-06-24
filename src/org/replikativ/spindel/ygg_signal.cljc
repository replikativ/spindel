(ns org.replikativ.spindel.ygg-signal
  "A **ygg-signal**: a spindel signal whose value is a yggdrasil SYSTEM (a CRDT, a
   composite, datahike, git, …) — the bridge that lets a yggdrasil interval-value
   live inside a signal ('make yggdrasil values fit into signals as interval-style
   operations').

   The signal *core* stays yggdrasil-free; this ns is the yggdrasil-aware seam.
   A ygg-signal value IS the system, so you MUTATE it with the ordinary signal
   primitives — `swap!` for a sync (JVM) value, `swap-await!` (from a spin) for an
   async (cljs / konserve-IO) one: `(swap! sig #(g/conj % :x))`. (`async-system?`
   tells you which, if a cross-platform caller needs to choose.) Mutate with a plain
   `swap!` — for distributed OP-path sync the export clears the shipped δ for you
   (`:clear-delta-fn ygg-clear-delta-fn`), so each op's δ is exactly that op and the
   in-memory δ stays bounded; you needn't clear inline.

   The distributed-sync hooks are `ygg-delta-fn` / `ygg-apply-delta-fn` / `ygg-clear-delta-fn`
   (the OP path) and `ygg-merge-fn` (the STATE-path JOIN — a remote update converges with
   the local value rather than clobbering it under LWW); pass them to
   `signal-sync/export-signal!` / `subscribe-signal!`.

   fork/overlay of a ygg-signal value (request `:following`, fall back to
   `:frozen`) uses yggdrasil's Overlayable directly."
  (:require [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.nodes :as nodes]
            [yggdrasil.protocols :as ygg]
            [yggdrasil.convergent :as yc]
            [yggdrasil.convergent.overlay :as ovl]))

(defn ygg-signal
  "Create a signal holding the yggdrasil system `sys`, and index it as a FORKABLE
   signal so a context fork isolates it (overlay/snapshot) rather than sharing the
   live store. Read the effective system with [[system-of]] (or `@yref` /
   `ygg/system` at the context layer); mutate with `swap!` / `swap-await!`.

   The value is stored as the RAW system, NON-deltaable: a yggdrasil system is a
   record (map-like), so the signal's default deltaable wrapping would turn it into
   a DeltaableMap and break protocol dispatch (`system-type`, `-join`, …). We seat
   the node directly with `deltaable? false` so deref returns the system itself."
  [sys]
  (let [s (sig/signal sys)]
    (ec/swap-state! [:nodes (:id s)]
                    (fn [_] (nodes/->signal-node sys nil nil false #{} 0)))
    (ec/swap-state! [:forkable-signals] #(conj (or % #{}) (:id s)))
    s))

(defn effective-system
  "Unwrap a ygg-signal's stored VALUE to its effective WRITABLE system: in a fork
   the value is an Overlay (overlay-system = the isolated/branched writable
   system); at the root it's the system itself. The deref seam — `@yref` and
   `ygg/system` resolve through this so callers always see a plain system whether
   or not the context is forked."
  [v]
  (if (ovl/overlay? v) (ovl/overlay-system v) v))

(defn system-of
  "The effective writable system held by ygg-signal `sig` in the current context
   (unwrapping a fork's Overlay). Requires `*execution-context*` bound."
  [sig]
  (effective-system (sig/deref-signal sig)))

(defn following-of
  "The ygg-signal's effective READ value with live-parent following: for a
   `:following` convergent overlay this is `join(parent-live, own-delta)` — it
   reflects the parent's concurrent evolution AND the fork's own writes; for a
   `:frozen`/root value it's the writable system. The reactive read a spin
   `track`s when it wants to see the parent advance."
  [sig]
  (let [v (sig/deref-signal sig)]
    (if (ovl/overlay? v) (ovl/overlay-value v) v)))

(defn async-system?
  "Whether `sys` is async-backed — a durable CRDT/composite opened `:sync? false`
   (cljs / konserve over async storage), whose ops return a partial-cps CPS. Such
   a value must be mutated via `swap-await!`; a sync system (JVM datahike/git/CRDT
   — no `:opts` or `:sync? true`) takes a plain `swap!`. Delegates to yggdrasil's
   supported predicate (`ygg/system-async?`) — do not peek `(:opts sys)` here."
  [sys]
  (ygg/system-async? sys))

(defn sync-system?
  "Whether `sys`'s ops run synchronously (return a value, not a CPS) — JVM /
   in-mem / `:sync? true` durable. The `:sync?` flag to pass `export-signal!` /
   `subscribe-signal!` for this value. The complement of [[async-system?]];
   delegates to `ygg/system-sync?`."
  [sys]
  (ygg/system-sync? sys))


(defn ops
  "The pending local δ (ops applied to ygg-signal `sig` since the last propagation)
   — the OP perspective. A small value joinable into a peer (`set` for a G-Set,
   `{:adds.. :removals..}` for a 2P/OR-Set, …), or nil if none. State is `@sig`;
   ops is this. (The dual perspective lives in the value: state + δ-in-meta.)"
  [sig]
  (yc/delta-of (sig/deref-signal sig)))

(def ygg-delta-fn
  "Sender hook for `export-signal!`'s `:delta-fn` — extract a convergent
   ygg-signal's local δ so a live update ships just the OP (`{:delta δ}`), not full
   state. A remote-integrated value carries no δ ⇒ nothing to propagate (no echo)."
  yc/delta-of)

(def ygg-clear-delta-fn
  "Sender hook for `export-signal!`'s `:clear-delta-fn` — drop a convergent
   ygg-signal's local δ once it has been shipped, so it doesn't re-accrue (in the
   value's metadata) and re-ship on the next op. A pure `=`-preserving metadata op,
   so the export's re-seat won't re-fire the watch."
  yc/clear-delta)

(defn ygg-apply-delta-fn
  "Receiver hook for `subscribe-signal!`'s `:apply-delta-fn` — integrate a peer's δ
   into the local convergent value (the OP-path, O(δ)). Returns the new value
   without a local δ (remote ops don't re-propagate)."
  [current delta]
  (yc/-apply-delta current delta))

(defn ygg-merge-fn
  "Signal-sync STATE-path merge for a CONVERGENT ygg-signal value: JOIN the
   incoming remote value with the local one (so concurrent local + remote updates
   converge) rather than LWW-overwrite. Use as `:merge-fn` on `export-signal!` /
   `subscribe-signal!`. `c/-join` is `async+sync`: it returns the merged value
   directly for a JVM/in-mem value, or a partial-cps CPS for a durable
   `:sync? false` (cljs/konserve) value — pass `:sync?` (= [[sync-system?]]) so
   signal-sync commits the value vs awaits the CPS. ONE hook, both modes."
  [current incoming]
  (yc/-join current incoming))
