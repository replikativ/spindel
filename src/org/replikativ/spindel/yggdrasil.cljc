(ns org.replikativ.spindel.yggdrasil
  "Yggdrasil integration for spindel execution contexts — the **ygg-signal** model.

   Each registered yggdrasil system lives as its own **ygg-signal**: a spindel
   signal whose value is the system (a git repo, a datahike conn, a konserve CRDT,
   or a composite of several). There is NO privileged workspace and no
   `[:external-refs]` side-channel — systems ARE signal values, so a spin can
   `track` one and re-run when it changes, and forking is uniform with the rest of
   the reactive graph.

   Key concepts:
   - register!: create a ygg-signal for a system (indexed under its system-id) and
     mark it forkable; returns a YggRef keyed by the system-id.
   - YggRef / system / get-system: resolve a system id to the EFFECTIVE writable
     system in the current context (unwrapping a fork's Overlay) — the same YggRef
     works in parent and forked contexts.
   - fork-context forks each ygg-signal's value via yggdrasil's `Overlayable`
     (`PForkable/fork-value`): the default OVERLAY fork from the current head
     (`:following`, degrading to `:frozen` for versioned git/datahike), or a
     SNAPSHOT fork that pins a fixed snapshot-id (`fork-context … :snapshots`).
   - context-diff / context-conflicts: per-system delta of a fork vs its
     parent, using each system's own merge-base.
   - merge-to-parent! / discard-from-parent!: parent-controlled merge-down /
     discard of the fork's per-system overlays.

   ASYNC+SYNC (portability, Design B): the engine stays synchronous and every
   fn that drives a DURABLE yggdrasil op (`fork!`, merge/discard/diff/conflicts)
   is written `async+sync` — SYNC on the JVM (returns a value, byte-identical to
   before) and a partial-cps CONTINUATION on cljs (each durable call `await`ed).
   So a DURABLE convergent-CRDT BRANCH fork works on cljs too; call these fns
   inside a partial-cps `async` and `await` (`<?`) their result on cljs. Plain
   engine reads (`system`, `@yref`, `registered-systems`, `set-node-value!`) stay
   synchronous. Snapshot forks remain JVM-first (see `fork-value`).

   Naming convention: Prefix YggRef vars with 'y' (e.g., ygit, ydb) to signal
   deref needed.

   Example:
     (def ygit (ygg/register! (git/create \".\")))   ; one ygg-signal: {git}
     (def ydb  (ygg/register! (dh/connect cfg)))      ; another: {db}

     @ygit                      ; => the git system in the current context
     (ygg/system \"dvergr-db\")   ; => the db system (canonical accessor)

     ;; Fork overlays every ygg-signal (git/datahike → branched fork worktree/conn)
     (let [child-ctx (ctx/fork-context parent-ctx)]
       (ec/with-context child-ctx
         @ygit  ; => git system on the forked overlay branch (automatic!)
         (d/transact! @@ydb [{:foo/bar 1}]))
       (ygg/merge-to-parent! child-ctx))            ; merge each overlay down"
  (:require [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.nodes :as nodes]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.ygg-signal :as ys]
            ;; protocols/types/overlay are cljc → required on BOTH platforms so the
            ;; bridge resolves/forks/diffs yggdrasil systems in cljs too. Only
            ;; yggdrasil.gc is JVM-only (it backs gc!/gc-system!, which stay :clj).
            [yggdrasil.protocols :as ygg]
            [yggdrasil.types :as ygt]
            [yggdrasil.convergent :as yc]
            [yggdrasil.convergent.overlay :as ovl]
            [clojure.string :as str]
            [is.simm.partial-cps.async :as pcps]
            #?(:clj  [is.simm.partial-cps.async :refer [async await]]
               :cljs [is.simm.partial-cps.async :refer [await]])
            #?(:clj [yggdrasil.macros :refer [async+sync]])
            #?@(:clj [[yggdrasil.gc :as ygg-gc]]))
  #?(:cljs (:require-macros [yggdrasil.macros :refer [async+sync]]
                            [is.simm.partial-cps.async :refer [async]])))

;; =============================================================================
;; Index keys
;; =============================================================================

;; [:ygg-signals]      {system-id -> SignalRef}  — an ADDRESSING INDEX (yggdrasil
;;                                                  system-id → which signal holds
;;                                                  it), NOT a parallel signal store:
;;                                                  the systems are ordinary forkable
;;                                                  signal nodes in [:nodes]. It only
;;                                                  exists to resolve/enumerate a
;;                                                  system by its DOMAIN id (`system`,
;;                                                  `registered-systems`, the by-id
;;                                                  YggRef); `@yref` alone wouldn't
;;                                                  need it.
;; [:forkable-signals] #{signal-id …}            — the engine's fork hook (set by
;;                                                  ygg-signal); fork-context forks
;;                                                  each of these signal values.
(def registry-key :ygg-signals)

;; =============================================================================
;; fork-value — how a context fork isolates a yggdrasil system value
;; =============================================================================

(defn- overlay-fork
  "OVERLAY fork: an isolated workspace over the system at its CURRENT head.
   Request the directive's mode (default :following); each system grants it or
   degrades (versioned git/datahike → :frozen branch fork). Returns an Overlay."
  [sys directive]
  (ygg/overlay sys {:mode (or (:mode directive) :following)}))

(defn- snapshot-fork
  "SNAPSHOT fork: pin a FIXED `snap-id` (a content-addressed snapshot-id — git
   sha / datahike commit) and branch an isolated writable head off it. The
   'fix a value, run it again in isolation' primitive. Versioned systems do this
   natively; a convergent system without a branch map falls back to the system
   unchanged (snapshot fork targets versioned systems for now).

   Returns a plain branched SYSTEM (not an Overlay) — pinned at a PAST value, it
   is for reproduce/replay/experiment, where you read or run in isolation and
   drop the `snap-<fork>` branch rather than merge it back. So a snapshot fork
   is NOT auto-managed by merge-to-parent! / discard-from-parent! (which act on
   overlays); lifecycle cleanup of snapshot forks is a follow-up."
  [sys fork-id snap-id]
  (if (satisfies? ygg/Branchable sys)
    (let [new-branch (keyword (str "snap-" (name fork-id)))]
      (-> sys (ygg/branch! new-branch snap-id) (ygg/checkout new-branch)))
    sys))

(defn- caps [sys]
  (when (satisfies? ygg/SystemIdentity sys) (ygg/capabilities sys)))

(defn- convergent-branchable?
  "A convergent system that is GENUINELY branchable — the CAPABILITY, not mere
   protocol satisfaction (cdvcs satisfies Branchable as no-ops but is `:branchable
   false`). These fork as a real yggdrasil BRANCH."
  [sys]
  (and (satisfies? yc/PConvergent sys)
       (boolean (:branchable (caps sys)))))

(defn- fork-branch-name?
  "True if `b` is a fork branch (engine fork-ids are `:fork-<uuid>` keywords)."
  [b]
  (and b (str/starts-with? (name b) "fork-")))

(defn- branch-fork
  "BRANCH fork (the DEFAULT for convergent systems): a REAL branched system as the
   fork value — inherits the parent tip, so `@kref`/`g/elements`/`g/conj` operate on
   it directly (no overlay footguns). `fork-id` is the engine-assigned `:fork-<uuid>`
   keyword, used as the branch name.

   JVM-ONLY: the engine's `fork-value` hook is synchronous, but durable `branch!`/
   `checkout` are SYNC on the JVM (values) and ASYNC on cljs (CPS). So on the JVM
   `fork-value` branch-forks here directly; on cljs `fork-value` DEFERS (returns the
   parent system unchanged) and `fork!` finishes the branch in an AWAITED post-pass."
  [sys fork-id]
  (-> sys (ygg/branch! fork-id) (ygg/checkout fork-id)))

;; `Object`/`default`: extend the engine's PForkable to ALL values so a forkable
;; ygg-signal's value is branch/overlay/snapshot-forked; non-yggdrasil values fall to
;; identity. cljs has no `Object` root — use the `default` dispatch.
(extend-protocol rtp/PForkable
  #?(:clj Object :cljs default)
  (fork-value [this fork-id directive]
    (cond
      ;; nested fork (fork of a fork) → fork the overlay's effective system
      (ovl/overlay? this)
      (rtp/fork-value (ovl/overlay-system this) fork-id directive)

      ;; SNAPSHOT fork (pin a fixed value) — any Snapshotable, versioned or convergent.
      ;; JVM-FIRST: `snapshot-fork` calls durable `branch!`/`checkout` synchronously, which
      ;; only yields a value on the JVM (cljs returns a CPS). Snapshot forks stay JVM-first;
      ;; the async lift (Design B) covers the DEFAULT branch-fork path, not snapshot forks.
      (and (= :snapshot (:fork directive)) (satisfies? ygg/Snapshotable this))
      (snapshot-fork this fork-id (:snapshot directive))

      ;; CONVERGENT + genuinely branchable → BRANCH fork by DEFAULT.
      ;; `:convergent-fork :overlay` forces the (optional) live-:following overlay.
      ;; `fork-value` is a SYNC engine hook, but durable branch-fork is async on cljs, so
      ;; on cljs we DEFER (return `this` unchanged) and let `fork!`'s awaited post-pass
      ;; branch it; the JVM branch-forks here directly (a value).
      (convergent-branchable? this)
      (if (= :overlay (:convergent-fork directive))
        (overlay-fork this directive)
        #?(:clj (branch-fork this fork-id) :cljs this))

      ;; CONVERGENT but not branchable (cdvcs) → overlay if it has one, else FAIL LOUD
      ;; (rather than NPE deep in a GSet op on a non-branchable value).
      (satisfies? yc/PConvergent this)
      (if (satisfies? ygg/Overlayable this)
        (overlay-fork this directive)
        (throw (ex-info "Cannot fork this convergent system: neither :branchable (no branch-fork) nor Overlayable (no overlay-fork)."
                        {:system-type (ygg/system-type this)
                         :system-id   (ygg/system-id this)
                         :hint "Implement Branchable or Overlayable for it, or fork a branchable convergent CRDT."})))

      ;; VERSIONED, non-convergent (datahike/git) → existing overlay path (UNCHANGED)
      (satisfies? ygg/Snapshotable this)
      (overlay-fork this directive)

      ;; not a yggdrasil value → identity (the engine default)
      :else this)))

;; =============================================================================
;; Resolution
;; =============================================================================

(defn- registry
  "The {system-id -> SignalRef} map in `ctx` (or the current context). Inherited
   by a fork via overlay fall-through; empty when nothing is registered."
  ([] (or (ec/get-state [registry-key]) {}))
  ([ctx] (or (rtp/get-state ctx [registry-key]) {})))

(defn- node-value
  "The current VALUE (system or Overlay) of ygg-signal `sig-ref` in `ctx`."
  [ctx sig-ref]
  (some-> (rtp/get-state ctx [:nodes (:id sig-ref)]) nodes/get-value))

(defn- resolve-system
  "Resolve `sys-id` to its EFFECTIVE writable system in the current context
   (unwrapping a fork's Overlay), or nil if absent."
  [sys-id]
  (when-let [sig-ref (get (registry) sys-id)]
    (ys/system-of sig-ref)))

;; =============================================================================
;; YggRef — fork-safe reference to a registered system
;; =============================================================================

;; Stores only the system-id; resolves through the registry + the ygg-signal in
;; the dynamic *execution-context*. The same YggRef works in parent and forks.

#?(:clj
   (deftype YggRef [id]
     clojure.lang.IDeref
     (deref [_this]
       (if-let [sys (resolve-system id)]
         sys
         (throw (ex-info "Yggdrasil system not found in current context"
                         {:id id
                          :hint "Ensure you're inside a bound execution context with registered systems"}))))

     clojure.lang.IMeta
     (meta [_this]
       (when-let [sys (resolve-system id)]
         {:system-id id
          :system-type (ygg/system-type sys)
          :current-branch (ygg/current-branch sys)})))

   :cljs
   (deftype YggRef [id]
     IDeref
     (-deref [_this]
       (if-let [sys (resolve-system id)]
         sys
         (throw (ex-info "Yggdrasil system not found in current context"
                         {:id id
                          :hint "Ensure you're inside a bound execution context with registered systems"}))))
     IMeta
     (-meta [_this]
       (when-let [sys (resolve-system id)]
         {:system-id id
          :system-type (ygg/system-type sys)
          :current-branch (ygg/current-branch sys)}))))

(defn ygg-ref?
  "Returns true if x is a YggRef."
  [x]
  (instance? YggRef x))

(defn ygg-ref-id
  "Get the system ID from a YggRef."
  [yref]
  (.-id yref))

;; =============================================================================
;; Registration — a ygg-signal per system
;; =============================================================================

(defn register!
  "Register a yggdrasil system into the current context as a ygg-signal.

   Creates a forkable ygg-signal holding `sys`, indexes it under its system-id,
   and returns a YggRef that resolves the system from context. The same YggRef
   works in the parent and in forked contexts (where it resolves to the fork's
   isolated overlay/branch).

   Args:
     sys - Yggdrasil system (must implement SystemIdentity; Snapshotable for forks)

   Returns: YggRef

   Example:
     (def ygit (register! (git/create \".\")))
     @ygit  ; => the git system"
  [sys]
  (let [sys-id (ygg/system-id sys)
        sig    (ys/ygg-signal sys)]
    (ec/swap-state! [registry-key] #(assoc (or % {}) sys-id sig))
    (->YggRef sys-id)))

(defn unregister!
  "Remove the system identified by `sys-id` — the mirror of `register!`. Drops it
   from the registry and the forkable-signal set. Returns true if removed."
  [sys-id]
  (when-let [sig-ref (get (registry) sys-id)]
    (ec/swap-state! [registry-key] #(dissoc % sys-id))
    (ec/swap-state! [:forkable-signals] #(disj (or % #{}) (:id sig-ref)))
    true))

(defn system
  "Get a registered system by id from the current context — the EFFECTIVE writable
   system (branch-correct inside a fork). Returns nil if absent.

   The canonical accessor — prefer this (or @ygg-ref) over reaching into context
   state by hand."
  [sys-id]
  (resolve-system sys-id))

(defn get-system
  "Alias for `system` (backwards-compatible name)."
  [sys-id]
  (system sys-id))

(defn system-signal
  "The ygg-signal (SignalRef) holding system `sys-id` in the current context, or
   nil. Use it to `track` the system reactively in a spin, or to `reset!`/`swap!`
   its value directly (e.g. seat a converged peer value). Prefer `system` /
   `@yref` for plain reads."
  [sys-id]
  (get (registry) sys-id))

(defn registered-systems
  "All registered systems in the current context as {system-id -> system} (the
   EFFECTIVE systems). Empty map when nothing is registered."
  []
  (into {} (keep (fn [[sid sig-ref]]
                   (when-let [s (ys/system-of sig-ref)] [sid s])))
        (registry)))

(defn following
  "The live-following READ value of registered system `sys-id` (for a `:following`
   convergent fork this reflects the parent's concurrent evolution joined with the
   fork's own writes; otherwise the writable system). Use in a spin via `track`."
  [sys-id]
  (when-let [sig-ref (get (registry) sys-id)]
    (ys/following-of sig-ref)))

;; =============================================================================
;; Per-system fork pairs (child overlay vs parent system)
;; =============================================================================

(defn- shared-pairs
  "Seq of [sys-id sig-ref child-val parent-sys] for systems present in BOTH the
   child and parent registries — child-val is the fork's value (an Overlay when
   forked), parent-sys the parent context's effective system."
  [child-ctx parent-ctx]
  (let [preg (registry parent-ctx)]
    (for [[sid sig-ref] (registry child-ctx)
          :let  [psys (when-let [pr (get preg sid)] (ys/effective-system (node-value parent-ctx pr)))]
          :when psys]
      [sid sig-ref (node-value child-ctx sig-ref) psys])))

(defn- child-only
  "{system-id -> SignalRef} for systems registered ONLY in the fork (no parent
   counterpart)."
  [child-ctx parent-ctx]
  (let [preg (registry parent-ctx)]
    (into {} (remove (fn [[sid _]] (contains? preg sid))) (registry child-ctx))))

(defn- set-node-value!
  "Swap ygg-signal `sig-ref`'s node value in `ctx` to `v` (system or overlay),
   preserving observers and bumping generation."
  [ctx sig-ref v]
  (rtp/swap-state! ctx [:nodes (:id sig-ref)]
                   (fn [node]
                     (nodes/->signal-node v nil nil false
                                          (if node (nodes/get-observers node) #{})
                                          (inc (or (:generation node) 0))))))

;; =============================================================================
;; Async context conveyance
;; =============================================================================

(defn- convey-context
  "Wrap a durable-op partial-cps thunk so its resolve/reject re-bind the
   *execution-context* captured NOW. spindel deliberately EXCLUDES
   *execution-context* from partial-cps binding capture (engine/bindings.cljc):
   it is re-bound only by the engine on a spin resume. So when a spin `await`s a
   durable bridge op, the op's INTERNAL konserve await resolves on a foreign
   thread (JVM) / a later microtask (cljs) and the spin's continuation would
   otherwise resume with NO context bound — `@yref`, `system-signal`,
   `resolve-system` (and the spin's own result-caching) all read the context and
   would throw. Re-binding around resolve/reject carries the captured context
   into that continuation, so the NATURAL fork API works fully async through a
   spin (mirrors distributed/core's `chan->spin` rebind).

   Returns a THUNK (partial-cps-compatible), so a raw `async`/`<?` caller keeps
   working too (and also gains the re-bind, dropping the manual post-await
   `binding` those call sites used). On the JVM SYNC path the arg is a plain
   VALUE (not a fn) and is returned unchanged — byte-identical sync behavior."
  [x]
  (if (fn? x)
    (let [ctx ec/*execution-context*]
      (fn [resolve reject]
        ;; `*in-trampoline* false` forces a FRESH synchronous trampoline for the
        ;; resume so the continuation runs to its next suspend WITHIN this binding
        ;; (on cljs a live outer trampoline would otherwise bounce it to a later
        ;; microtask, escaping the binding) — mirrors distributed/core `chan->spin`.
        (x (fn [v] (binding [ec/*execution-context* ctx pcps/*in-trampoline* false] (resolve v)))
           (fn [e] (binding [ec/*execution-context* ctx pcps/*in-trampoline* false] (reject e))))))
    x))

;; =============================================================================
;; Fork Handle (explicit control)
;; =============================================================================

(defrecord ForkHandle [child-ctx parent-ctx fork-id])

(defn fork-handle?
  "Returns true if x is a ForkHandle."
  [x]
  (instance? ForkHandle x))

(defn fork!
  "Create a forked execution context with every ygg-signal overlaid (or snapshot-
   forked, per `opts`). Returns a ForkHandle for explicit merge/discard control.

   opts (optional): forwarded to `ctx/fork-context` —
     :mode      :following (default) | :frozen — overlay fork relation to parent
     :snapshots {system-id -> snapshot-id} — pin those systems at fixed values
     :convergent-fork :branch (default) | :overlay — a CONVERGENT CRDT forks as a
       real yggdrasil BRANCH by default (the natural CRDT API works in the fork: read
       `@ref`, write `g/conj`, `merge-fork!` folds back). `:overlay` forces the live-
       `:following` overlay workspace instead. datahike/git always overlay-fork.

   Permission model:
   - An agent CAN fork from its current context (creating children).
   - An agent CAN merge its own children back into its branch.
   - An agent CANNOT merge its own context into its parent.

   Example:
     (let [fork (fork!)]
       (with-fork fork
         (spit (str (git/worktree-path @ygit) \"/new.clj\") \"...\"))
       (merge-fork! fork))"
  ([] (fork! {}))
  ([opts]
   (convey-context
    (async+sync
     (:sync? (merge yc/default-opts opts))
     (async
      (let [parent-ctx (ec/current-execution-context)
           ;; translate :snapshots from SYSTEM-id keys (what callers know) to the
           ;; SIGNAL-id keys fork-context forks by.
            snaps  (when-let [s (:snapshots opts)]
                     (into {} (keep (fn [[sid snap]]
                                      (when-let [sr (get (registry parent-ctx) sid)]
                                        [(:id sr) snap])))
                           s))
            fopts  (cond-> opts snaps (assoc :snapshots snaps))
            child-ctx  (apply ctx/fork-context parent-ctx (mapcat identity fopts))
            fork-id    (:fork-id child-ctx)
            popts  (merge yc/default-opts opts)]
       ;; POST-PASS (Design B async lift): the engine's `fork-context`/`fork-value`
       ;; hook is SYNCHRONOUS, so a convergent BRANCH fork — durable `branch!`/`checkout`
       ;; that only yield a value synchronously on the JVM — is done here, AWAITED, over
       ;; the parent's branchable-convergent signals. On the JVM `fork-value` already
       ;; branched each (its `current-branch` is a `fork-<uuid>`), so the guard makes this
       ;; a NO-OP; on cljs `fork-value` deferred (left the parent value), so this branches
       ;; each and seats the branched system as the fork's value. ONE code path, both
       ;; platforms (async+sync collapses to `do` on the JVM).
        (loop [ps (seq (shared-pairs child-ctx parent-ctx))]
          (when ps
            (let [[_sid sig-ref cval _psys] (first ps)]
              (when (and (convergent-branchable? cval)
                         (not (fork-branch-name? (ygg/current-branch cval))))
                (let [_        (await (ygg/branch! cval fork-id (ygg/current-branch cval) popts))
                      branched (await (ygg/checkout cval fork-id popts))]
                  (set-node-value! child-ctx sig-ref branched))))
            (recur (next ps))))
        (->ForkHandle child-ctx parent-ctx fork-id)))))))

;; `with-fork` is a JVM-only convenience macro. On cljs use the engine form it
;; expands to directly: `(ec/with-context (:child-ctx fork) …)`.
#?(:clj
   (defmacro with-fork
     "Execute body in fork's context. YggRef derefs (@ygit, @ydb) resolve to
      forked instances within body."
     [fork-handle & body]
     `(ec/with-context (:child-ctx ~fork-handle)
        ~@body)))

;; =============================================================================
;; Diff / Conflicts (per-system merge-base)
;; =============================================================================

(defn- system-merge-base-diff
  "The fork's OWN changes in one system. Diff the MERGE-BASE (common ancestor of
   parent + fork) → fork, so a live parent's concurrent advance is excluded.
   Resolves everything to SNAPSHOT-IDS (git sha / datahike db hash). `fsys` is
   the fork's writable system (the overlay's overlay-system)."
  [fsys psys]
  (async+sync
   (:sync? yc/default-opts)
   (async
    (let [psnap (let [v (ygg/snapshot-id psys)] (if (fn? v) (await v) v))
          fsnap (let [v (ygg/snapshot-id fsys)] (if (fn? v) (await v) v))]
      ;; `snapshot-id`/`common-ancestor`/`diff` are `async+sync` on the system's DEFAULT
      ;; opts (no opts arity) — a partial-cps CONTINUATION on cljs / under async, but a
      ;; plain VALUE on the JVM (default `:sync? true`). So `await` ONLY when the result is
      ;; a continuation (a fn); awaiting a plain value crashes the JVM async path (partial-
      ;; cps would invoke the value as `(v resolve reject)`).
      (or (try
            (let [v (ygg/common-ancestor fsys psnap fsnap)
                  base (if (fn? v) (await v) v)]
              (when base
                (let [d (ygg/diff fsys base fsnap)]
                  (if (fn? d) (await d) d))))
            (catch #?(:clj Throwable :cljs :default) _ nil))
          (try
            (let [d (ygg/diff fsys psnap fsnap)]
              (if (fn? d) (await d) d))
            (catch #?(:clj Throwable :cljs :default) t
              (ygt/diff-error psnap fsnap (ex-message t)))))))))

(defn context-diff
  "Per-system delta of a forked context vs its parent — the unified diff a
   reviewer reads: {system-id -> typed yggdrasil delta (GitDiff / DatahikeDiff /
   DiffError)}. nil when the context has no parent. Non-Mergeable systems are
   omitted."
  [child-ctx]
  (convey-context
   (async+sync
    (:sync? yc/default-opts)
    (async
     (when-let [parent-ctx (:parent-ctx child-ctx)]
      ;; accumulating loop (not `into`/`keep`) — `system-merge-base-diff` is awaited.
       (loop [ps (seq (shared-pairs child-ctx parent-ctx)) acc {}]
         (if ps
           (let [[sid _ cval psys] (first ps)
                 fsys (ys/effective-system cval)
                 acc* (if (and (satisfies? ygg/Mergeable fsys)
                               (satisfies? ygg/Graphable fsys))
                        (assoc acc sid (await (system-merge-base-diff fsys psys)))
                        acc)]
             (recur (next ps) acc*))
           acc)))))))

(defn context-conflicts
  "Per-system conflicts of a forked context vs its parent, each tagged
   `:system`. nil when the context has no parent."
  [child-ctx]
  (convey-context
   (async+sync
    (:sync? yc/default-opts)
    (async
     (when-let [parent-ctx (:parent-ctx child-ctx)]
      ;; accumulating loop (not `into`/`mapcat`) — `snapshot-id`/`conflicts` are `await`ed
      ;; ONLY when a continuation (a fn): default-opts `snapshot-id` is a plain value on the
      ;; JVM but a CPS on cljs; `conflicts` is `[]` for conflict-free CRDTs, CPS for versioned.
       (loop [ps (seq (shared-pairs child-ctx parent-ctx)) acc []]
         (if ps
           (let [[sid _ cval psys] (first ps)
                 fsys (ys/effective-system cval)
                 more (if (satisfies? ygg/Mergeable fsys)
                        (try
                          (let [ps1  (let [v (ygg/snapshot-id psys)] (if (fn? v) (await v) v))
                                fs1  (let [v (ygg/snapshot-id fsys)] (if (fn? v) (await v) v))
                                pres (ygg/conflicts psys ps1 fs1)
                                cs   (if (fn? pres) (await pres) pres)]
                            (mapv #(assoc % :system sid) cs))
                          (catch #?(:clj Throwable :cljs :default) _ nil))
                        nil)]
             (recur (next ps) (into acc (or more []))))
           acc)))))))

;; =============================================================================
;; Merge / Discard (Parent-Controlled)
;; =============================================================================

(defn merge-to-parent!
  "Merge a forked context's per-system overlays into its parent.

   Algorithm:
     1. Pre-check conflicts (unless :strategy or :force given); abort untouched
        if any system conflicts.
     2. For each shared system: `merge-down!` the fork's overlay into the parent
        system, point the parent's ygg-signal at the merged system, and discard
        the overlay (delete the fork branch / worktree).
     3. Carry CHILD-ONLY systems (registered only in the fork) into the parent.
   A system merge that throws leaves the parent ygg-signal for that system
   unchanged and re-throws with diagnostics (git/datahike have no cross-store
   2PC; the conflict pre-check makes mid-merge failure unlikely).

   Args:
     child-ctx - Child ExecutionContext to merge from
     opts      - {:strategy … :force true :message … :on-merge (fn [m])}

   Returns: {:merged [sys-id …] :child-only [sys-id …]} or nil if no parent."
  ([child-ctx] (merge-to-parent! child-ctx {}))
  ([child-ctx opts]
   (convey-context
    (async+sync
     (:sync? (merge yc/default-opts opts))
     (async
      (when-let [parent-ctx (:parent-ctx child-ctx)]
        (let [pairs (shared-pairs child-ctx parent-ctx)]
         ;; 1. conflict pre-check (FAIL-SAFE: a throwing detector counts as an
         ;; indeterminate conflict so the gate aborts rather than blind-merges).
         ;; `snapshot-id`/`conflicts` are `await`ed ONLY when a continuation (a fn):
         ;; default-opts `snapshot-id` is a plain value on the JVM but a CPS on cljs;
         ;; `conflicts` is `[]` for conflict-free convergent CRDTs, CPS for versioned.
          (when-not (or (:strategy opts) (:force opts))
            (let [confs (loop [ps (seq pairs) acc []]
                          (if ps
                            (let [[sid _ cval psys] (first ps)
                                  fsys (ys/effective-system cval)
                                  more (if (satisfies? ygg/Mergeable fsys)
                                         (try
                                           (let [ps1  (let [v (ygg/snapshot-id psys)] (if (fn? v) (await v) v))
                                                 fs1  (let [v (ygg/snapshot-id fsys)] (if (fn? v) (await v) v))
                                                 pres (ygg/conflicts psys ps1 fs1)
                                                 cs   (if (fn? pres) (await pres) pres)]
                                             (mapv #(assoc % :system sid) cs))
                                           (catch #?(:clj Throwable :cljs :default) e
                                             [{:system sid :indeterminate? true
                                               :error (ex-message e)}]))
                                         [])]
                              (recur (next ps) (into acc more)))
                            acc))]
              (when (seq confs)
                (throw (ex-info "context merge has conflicts; aborting (pass :strategy or :force)"
                                {:conflicts (vec confs)})))))
         ;; 2. merge each overlay down, repoint the parent ygg-signal, discard.
         ;; ROLLBACK SEMANTICS PRESERVED: each merged value is COMPUTED first, and the
         ;; parent ygg-signal is repointed only AFTER; a throwing/rejecting durable op
         ;; leaves that system's parent untouched and propagates (git/datahike have no
         ;; cross-store 2PC — the pre-check makes mid-merge failure unlikely).
          (let [merged (loop [ps (seq pairs) acc []]
                         (if ps
                           (let [[sid sig-ref cval psys] (first ps)
                                 acc* (cond
                                       ;; OVERLAY fork (convergent :overlay opt + datahike/git): join back.
                                        (ovl/overlay? cval)
                                        (let [m (await (ygg/merge-down! cval opts))]
                                          (set-node-value! parent-ctx sig-ref m)
                                          (ygg/discard! cval)
                                          (conj acc sid))

                                       ;; BRANCH-forked convergent: `cval` is a real system on `:fork-<uuid>`.
                                       ;; Check out the parent branch (loads its LIVE head for durable stores),
                                       ;; `merge!` the fork branch in, drop the fork branch. Await each (can't
                                       ;; thread-first through CPS on cljs); `mopts` threads `:sync?`.
                                        (and (satisfies? yc/PConvergent cval)
                                             (fork-branch-name? (ygg/current-branch cval)))
                                        (let [mopts   (merge yc/default-opts opts)
                                              fbranch (ygg/current-branch cval)
                                              pbranch (ygg/current-branch psys)
                                              co      (await (ygg/checkout cval pbranch mopts))
                                              mg      (await (ygg/merge! co fbranch mopts))
                                              m       (await (ygg/delete-branch! mg fbranch mopts))]
                                          (set-node-value! parent-ctx sig-ref m)
                                          (conj acc sid))

                                        :else acc)]
                             (recur (next ps) acc*))
                           acc))
               ;; 3. carry child-only systems into the parent registry + nodes.
                co (child-only child-ctx parent-ctx)]
            (doseq [[sid sig-ref] co]
              (rtp/swap-state! parent-ctx [registry-key] #(assoc (or % {}) sid sig-ref))
              (rtp/swap-state! parent-ctx [:forkable-signals] #(conj (or % #{}) (:id sig-ref)))
              (set-node-value! parent-ctx sig-ref (node-value child-ctx sig-ref)))
            (when-let [cb (:on-merge opts)]
              (cb {:merged merged :child-only (vec (keys co))
                   :parent-ctx parent-ctx :child-ctx child-ctx}))
            {:merged merged :child-only (vec (keys co))}))))))))

(defn discard-from-parent!
  "Discard a forked context's per-system overlays without merging — `discard!`
   each shared overlay (deleting git worktrees / fork branches). Fork-ONLY
   systems have no shared overlay; the `:on-discard` callback receives them so
   an external owner can clean up (delete the store, drop a deferred grant).

   Args:
     child-ctx - Child ExecutionContext to discard
     opts      - {:on-discard (fn [{:keys [child-only child-ctx]}])}

   Returns: nil"
  ([child-ctx] (discard-from-parent! child-ctx {}))
  ([child-ctx opts]
   (convey-context
    (async+sync
     (:sync? (merge yc/default-opts opts))
     (async
      (when-let [parent-ctx (:parent-ctx child-ctx)]
       ;; `discard!` on an overlay is a synchronous no-op (returns nil); `delete-branch!`
       ;; is async — await it. Loop (not doseq) so the await threads on cljs.
        (loop [ps (seq (shared-pairs child-ctx parent-ctx))]
          (when ps
            (let [[_ _ cval _] (first ps)]
              (cond
                (ovl/overlay? cval) (ygg/discard! cval)
               ;; branch-forked convergent: drop the fork branch (its nodes GC later).
                (and (satisfies? yc/PConvergent cval)
                     (fork-branch-name? (ygg/current-branch cval)))
                (await (ygg/delete-branch! cval (ygg/current-branch cval) (merge yc/default-opts opts)))))
            (recur (next ps))))
        (when-let [cb (:on-discard opts)]
          (let [co (child-only child-ctx parent-ctx)]
            (cb {:child-only (vec (keys co))
                 :child-only-systems (into {} (keep (fn [[sid sr]]
                                                      (when-let [s (ys/effective-system (node-value child-ctx sr))]
                                                        [sid s])))
                                           co)
                 :child-ctx child-ctx}))))
      nil)))))

;; ForkHandle variants (delegate to the ctx-based ops)

(defn merge-fork!
  "Merge fork's overlays to parent (ForkHandle variant of merge-to-parent!)."
  ([fork-handle] (merge-fork! fork-handle {}))
  ([fork-handle opts] (merge-to-parent! (:child-ctx fork-handle) opts)))

(defn discard-fork!
  "Discard fork's overlays (ForkHandle variant of discard-from-parent!)."
  ([fork-handle] (discard-fork! fork-handle {}))
  ([fork-handle opts] (discard-from-parent! (:child-ctx fork-handle) opts)))

;; =============================================================================
;; Merge From Parent (Parent → Child sync)
;; =============================================================================

(defn merge-from-parent!
  "Merge the parent's current state INTO a child context (inverse of
   merge-to-parent!) — for long-lived agent forks that need to stay in sync.
   Per shared system, merge the parent's branch into the fork's writable system
   and repoint the fork's ygg-signal. Called from within / on the child context.

   Args:
     child-ctx - The child ExecutionContext to update
     opts      - Optional merge opts {:strategy … :message …}

   Returns: nil"
  ([child-ctx] (merge-from-parent! child-ctx {}))
  ([child-ctx opts]
   (convey-context
    (async+sync
     (:sync? (merge yc/default-opts opts))
     (async
      (when-let [parent-ctx (:parent-ctx child-ctx)]
       ;; Loop (not doseq) so `checkout`/`merge!` await-thread on cljs.
        (loop [ps (seq (shared-pairs child-ctx parent-ctx))]
          (when ps
            (let [[_ sig-ref cval psys] (first ps)
                  fsys (ys/effective-system cval)]
              (when (and (satisfies? ygg/Branchable fsys)
                         (satisfies? ygg/Mergeable fsys))
                (let [cbranch (ygg/current-branch fsys)
                      pbranch (ygg/current-branch psys)
                     ;; thread :sync? — `opts` is a merge-opts map without it; else the
                     ;; JVM async branch seats a CPS continuation (the finding-#3 twin).
                      mopts   (merge yc/default-opts {:message (str "Merge from " (name pbranch))} opts)
                      co      (await (ygg/checkout fsys cbranch mopts))
                      m       (await (ygg/merge! co pbranch mopts))]
                 ;; repoint: if cval is an overlay, update its writable system in
                 ;; place; else repoint the node. (both sync)
                  (if (ovl/overlay? cval)
                    (ovl/reseat-overlay! cval m)
                    (set-node-value! child-ctx sig-ref m)))))
            (recur (next ps)))))
      nil)))))

(defn merge-fork-from-parent!
  "Merge parent's current state into a fork (ForkHandle variant)."
  ([fork-handle] (merge-fork-from-parent! fork-handle {}))
  ([fork-handle opts]
   (merge-from-parent! (:child-ctx fork-handle) opts)))

;; =============================================================================
;; Accessors
;; =============================================================================

(defn parent-system
  "Get the parent context's version of a system (read-only). Works with a YggRef
   or a raw system. Must be called from a child context. Returns nil at root."
  [sys-or-ref]
  (let [sys-id (if (ygg-ref? sys-or-ref)
                 (ygg-ref-id sys-or-ref)
                 (ygg/system-id sys-or-ref))
        ctx        (ec/current-execution-context)
        parent-ctx (:parent-ctx ctx)]
    (when parent-ctx
      (when-let [sig-ref (get (registry parent-ctx) sys-id)]
        (ys/effective-system (node-value parent-ctx sig-ref))))))

;; =============================================================================
;; Optional Helpers (datahike double-deref ergonomics + GC)
;; =============================================================================

(defn db
  "Get current db value from a datahike YggRef. Equivalent to @@ydb."
  [ydb-ref]
  @@ydb-ref)

#?(:clj
   (defn q
     "Query helper that handles datahike double-deref automatically.

      Example: (q ydb '[:find ?n :where [?e :user/name ?n]])"
     [ydb-ref query & args]
     (apply (requiring-resolve 'datahike.api/q) query @@ydb-ref args)))

#?(:clj
   (defn gc-system!
     "Reclaim unreachable storage for a single yggdrasil system. Thin re-export of
      `yggdrasil.gc/gc-system!`. `opts` are adapter-specific — datahike honours
      `:remove-before <Date>` (default epoch = keep ALL history), git honours
      `:grace-period-ms`; `:dry-run?` reports without deleting."
     ([sys] (ygg-gc/gc-system! sys {}))
     ([sys opts] (ygg-gc/gc-system! sys opts))))

#?(:clj
   (defn gc!
     "Reclaim unreachable storage across EVERY registered system in the current
      context — each datahike kb/msgs + git repo GC'd in one pass. `opts` flow to
      each adapter (`:remove-before`, `:grace-period-ms`, `:dry-run?`). Returns
      {system-id -> report}, or nil if nothing is registered."
     ([] (gc! {}))
     ([opts]
      (let [reports (into {}
                          (keep (fn [[sid sys]]
                                  (when (satisfies? ygg/GarbageCollectable sys)
                                    [sid (ygg-gc/gc-system! sys opts)])))
                          (registered-systems))]
        (when (seq reports) reports)))))
