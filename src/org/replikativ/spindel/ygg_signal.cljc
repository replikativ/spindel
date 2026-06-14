(ns org.replikativ.spindel.ygg-signal
  "A **ygg-signal**: a spindel signal whose value is a yggdrasil SYSTEM (a CRDT, a
   composite, datahike, git, …) — the bridge that lets a yggdrasil interval-value
   live inside a signal ('make yggdrasil values fit into signals as interval-style
   operations').

   The signal *core* stays yggdrasil-free; this ns is the yggdrasil-aware seam:
   - `ygg-swap!` — ONE mutate that works for sync (JVM) and async (cljs /
     konserve-IO) systems, dispatching on the value's sync-mode: a `swap!` for a
     sync system, `swap-await!` (await from a spin) for an async one. So the same
     call works whether the room's KB is a JVM datahike or a browser durable CRDT.
   - `ygg-merge-fn` — the convergent JOIN for distributed sync (a remote update
     converges with the local value rather than clobbering it under LWW); pass it
     as `:merge-fn` to `signal-sync/export-signal!` / `subscribe-signal!`.

   fork/overlay of a ygg-signal value (request `:following`, fall back to
   `:frozen`) is the next step — it uses yggdrasil's Overlayable directly."
  (:require [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.nodes :as nodes]
            [yggdrasil.convergent :as yc]
            [yggdrasil.convergent.overlay :as ovl]))

(defn ygg-signal
  "Create a signal holding the yggdrasil system `sys`, and index it as a FORKABLE
   signal so a context fork isolates it (overlay/snapshot) rather than sharing the
   live store. Read the effective system with [[system-of]] (or `@yref` /
   `ygg/system` at the context layer); mutate with `ygg-swap!`.

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
   — no `:opts` or `:sync? true`) takes a plain `swap!`."
  [sys]
  (false? (:sync? (:opts sys))))

(defn ygg-swap!
  "Mutate a ygg-signal. `f` is a yggdrasil op `(fn [sys & args] -> sys')` —
   e.g. `#(g/add % :x)`, `#(p/merge! % branch)`, `#(p/commit! % msg)`. Dispatches
   on the value's sync-mode: a plain `swap!` (returns the new system) for a sync
   system, `swap-await!` (returns a partial-cps async — `await` it from a spin)
   for an async one. So one call covers JVM and cljs ygg-signals alike."
  [ygg-sig f & args]
  (if (async-system? (sig/deref-signal ygg-sig))
    (apply sig/swap-await! ygg-sig f args)
    (apply swap! ygg-sig f args)))

(defn ygg-merge-fn
  "Signal-sync merge for a CONVERGENT ygg-signal value: JOIN the incoming remote
   value with the local one (so concurrent local + remote updates converge)
   rather than LWW-overwrite. Use as `:merge-fn` on `export-signal!` /
   `subscribe-signal!` for a SYNC value — an in-memory convergent value or a JVM
   (`:sync? true`) durable CRDT, whose `-join` returns the merged value directly."
  [current incoming]
  (yc/-join current incoming))

(defn ygg-merge-await-fn
  "Signal-sync merge for an ASYNC convergent ygg-signal value — a durable CRDT
   opened `:sync? false` (cljs / konserve over async storage), whose `-join`
   suspends on IO and returns a partial-cps CPS rather than a value. Use as
   `:merge-await-fn` on `export-signal!` / `subscribe-signal!`: the incoming
   remote value is JOINED with the local one and committed only once the join
   resolves. (Same `c/-join` as the sync hook — the value's own sync-mode decides
   whether it returns a value or a CPS; pick the hook to match, exactly as
   `ygg-swap!` dispatches `swap!` vs `swap-await!` by [[async-system?]].)"
  [current incoming]
  (yc/-join current incoming))
