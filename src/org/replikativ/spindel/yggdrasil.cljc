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
   - workspace-diff / workspace-conflicts: per-system delta of a fork vs its
     parent, using each system's own merge-base.
   - merge-to-parent! / discard-from-parent!: parent-controlled merge-down /
     discard of the fork's per-system overlays.

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
            #?@(:clj [[yggdrasil.protocols :as ygg]
                      [yggdrasil.types :as ygt]
                      [yggdrasil.gc :as ygg-gc]
                      [yggdrasil.convergent.overlay :as ovl]])))

;; =============================================================================
;; Index keys
;; =============================================================================

;; [:ygg-signals]      {system-id -> SignalRef}  — the resolution registry.
;; [:forkable-signals] #{signal-id …}            — the engine's fork hook (set by
;;                                                  ygg-signal); fork-context forks
;;                                                  each of these signal values.
(def registry-key :ygg-signals)

;; =============================================================================
;; fork-value — how a context fork isolates a yggdrasil system value
;; =============================================================================

#?(:clj
   (defn- overlay-fork
     "OVERLAY fork: an isolated workspace over the system at its CURRENT head.
      Request the directive's mode (default :following); each system grants it or
      degrades (versioned git/datahike → :frozen branch fork). Returns an Overlay."
     [sys directive]
     (ygg/overlay sys {:mode (or (:mode directive) :following)})))

#?(:clj
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
       sys)))

#?(:clj
   (extend-protocol rtp/PForkable
     Object
     (fork-value [this fork-id directive]
       (cond
         ;; nested fork (fork of a fork) → fork the overlay's effective system
         (ovl/overlay? this) (rtp/fork-value (ovl/overlay-system this) fork-id directive)
         ;; a yggdrasil system → overlay (default) or snapshot fork
         (satisfies? ygg/Snapshotable this)
         (if (= :snapshot (:fork directive))
           (snapshot-fork this fork-id (:snapshot directive))
           (overlay-fork this directive))
         ;; not a yggdrasil value → identity (the engine default)
         :else this))))

;; =============================================================================
;; Resolution
;; =============================================================================

#?(:clj
   (defn- registry
     "The {system-id -> SignalRef} map in `ctx` (or the current context). Inherited
      by a fork via overlay fall-through; empty when nothing is registered."
     ([] (or (ec/get-state [registry-key]) {}))
     ([ctx] (or (rtp/get-state ctx [registry-key]) {}))))

#?(:clj
   (defn- node-value
     "The current VALUE (system or Overlay) of ygg-signal `sig-ref` in `ctx`."
     [ctx sig-ref]
     (some-> (rtp/get-state ctx [:nodes (:id sig-ref)]) nodes/get-value)))

#?(:clj
   (defn- resolve-system
     "Resolve `sys-id` to its EFFECTIVE writable system in the current context
      (unwrapping a fork's Overlay), or nil if absent."
     [sys-id]
     (when-let [sig-ref (get (registry) sys-id)]
       (ys/system-of sig-ref))))

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
       (throw (ex-info "Yggdrasil not yet supported in ClojureScript" {:id id})))
     IMeta
     (-meta [_this] {:system-id id})))

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
  #?(:clj
     (let [sys-id (ygg/system-id sys)
           sig    (ys/ygg-signal sys)]
       (ec/swap-state! [registry-key] #(assoc (or % {}) sys-id sig))
       (->YggRef sys-id))
     :cljs
     (throw (ex-info "Yggdrasil not yet supported in ClojureScript" {}))))

(defn unregister!
  "Remove the system identified by `sys-id` — the mirror of `register!`. Drops it
   from the registry and the forkable-signal set. Returns true if removed."
  [sys-id]
  #?(:clj
     (when-let [sig-ref (get (registry) sys-id)]
       (ec/swap-state! [registry-key] #(dissoc % sys-id))
       (ec/swap-state! [:forkable-signals] #(disj (or % #{}) (:id sig-ref)))
       true)
     :cljs
     (throw (ex-info "Yggdrasil not yet supported in ClojureScript" {}))))

(defn system
  "Get a registered system by id from the current context — the EFFECTIVE writable
   system (branch-correct inside a fork). Returns nil if absent.

   The canonical accessor — prefer this (or @ygg-ref) over reaching into context
   state by hand."
  [sys-id]
  #?(:clj (resolve-system sys-id)
     :cljs nil))

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
  #?(:clj (get (registry) sys-id)
     :cljs nil))

(defn registered-systems
  "All registered systems in the current context as {system-id -> system} (the
   EFFECTIVE systems). Empty map when nothing is registered."
  []
  #?(:clj (into {} (keep (fn [[sid sig-ref]]
                           (when-let [s (ys/system-of sig-ref)] [sid s])))
                (registry))
     :cljs {}))

(defn following
  "The live-following READ value of registered system `sys-id` (for a `:following`
   convergent fork this reflects the parent's concurrent evolution joined with the
   fork's own writes; otherwise the writable system). Use in a spin via `track`."
  [sys-id]
  #?(:clj (when-let [sig-ref (get (registry) sys-id)]
            (ys/following-of sig-ref))
     :cljs nil))

;; =============================================================================
;; Per-system fork pairs (child overlay vs parent system)
;; =============================================================================

#?(:clj
   (defn- shared-pairs
     "Seq of [sys-id sig-ref child-val parent-sys] for systems present in BOTH the
      child and parent registries — child-val is the fork's value (an Overlay when
      forked), parent-sys the parent context's effective system."
     [child-ctx parent-ctx]
     (let [preg (registry parent-ctx)]
       (for [[sid sig-ref] (registry child-ctx)
             :let  [psys (when-let [pr (get preg sid)] (ys/effective-system (node-value parent-ctx pr)))]
             :when psys]
         [sid sig-ref (node-value child-ctx sig-ref) psys]))))

#?(:clj
   (defn- child-only
     "{system-id -> SignalRef} for systems registered ONLY in the fork (no parent
      counterpart)."
     [child-ctx parent-ctx]
     (let [preg (registry parent-ctx)]
       (into {} (remove (fn [[sid _]] (contains? preg sid))) (registry child-ctx)))))

#?(:clj
   (defn- set-node-value!
     "Swap ygg-signal `sig-ref`'s node value in `ctx` to `v` (system or overlay),
      preserving observers and bumping generation."
     [ctx sig-ref v]
     (rtp/swap-state! ctx [:nodes (:id sig-ref)]
                      (fn [node]
                        (nodes/->signal-node v nil nil false
                                             (if node (nodes/get-observers node) #{})
                                             (inc (or (:generation node) 0)))))))

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
   #?(:clj
      (let [parent-ctx (ec/current-execution-context)
            ;; translate :snapshots from SYSTEM-id keys (what callers know) to the
            ;; SIGNAL-id keys fork-context forks by.
            snaps  (when-let [s (:snapshots opts)]
                     (into {} (keep (fn [[sid snap]]
                                      (when-let [sr (get (registry parent-ctx) sid)]
                                        [(:id sr) snap])))
                           s))
            opts   (cond-> opts snaps (assoc :snapshots snaps))
            child-ctx  (apply ctx/fork-context parent-ctx (mapcat identity opts))
            fork-id    (:fork-id child-ctx)]
        (->ForkHandle child-ctx parent-ctx fork-id))
      :cljs
      (throw (ex-info "Yggdrasil fork not yet supported in ClojureScript" {})))))

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

#?(:clj
   (defn- system-merge-base-diff
     "The fork's OWN changes in one system. Diff the MERGE-BASE (common ancestor of
      parent + fork) → fork, so a live parent's concurrent advance is excluded.
      Resolves everything to SNAPSHOT-IDS (git sha / datahike db hash). `fsys` is
      the fork's writable system (the overlay's overlay-system)."
     [fsys psys]
     (let [psnap (ygg/snapshot-id psys)
           fsnap (ygg/snapshot-id fsys)]
       (or (try
             (let [base (ygg/common-ancestor fsys psnap fsnap)]
               (when base (ygg/diff fsys base fsnap)))
             (catch Throwable _ nil))
           (try (ygg/diff fsys psnap fsnap)
                (catch Throwable t (ygt/diff-error psnap fsnap (.getMessage t))))))))

#?(:clj
   (defn workspace-diff
     "Per-system delta of a forked context vs its parent — the unified diff a
      reviewer reads: {system-id -> typed yggdrasil delta (GitDiff / DatahikeDiff /
      DiffError)}. nil when the context has no parent. Non-Mergeable systems are
      omitted."
     [child-ctx]
     (when-let [parent-ctx (:parent-ctx child-ctx)]
       (into {}
             (keep (fn [[sid _ cval psys]]
                     (let [fsys (ys/effective-system cval)]
                       (when (and (satisfies? ygg/Mergeable fsys)
                                  (satisfies? ygg/Graphable fsys))
                         [sid (system-merge-base-diff fsys psys)]))))
             (shared-pairs child-ctx parent-ctx)))))

#?(:clj
   (defn workspace-conflicts
     "Per-system conflicts of a forked context vs its parent, each tagged
      `:system`. nil when the context has no parent."
     [child-ctx]
     (when-let [parent-ctx (:parent-ctx child-ctx)]
       (into []
             (mapcat (fn [[sid _ cval psys]]
                       (let [fsys (ys/effective-system cval)]
                         (when (satisfies? ygg/Mergeable fsys)
                           (try (map #(assoc % :system sid)
                                     (ygg/conflicts psys
                                                    (ygg/snapshot-id psys)
                                                    (ygg/snapshot-id fsys)))
                                (catch Throwable _ nil))))))
             (shared-pairs child-ctx parent-ctx)))))

;; context-diff: backwards-compatible alias.
#?(:clj (def context-diff workspace-diff))

;; =============================================================================
;; Merge / Discard (Parent-Controlled)
;; =============================================================================

#?(:clj
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
      (when-let [parent-ctx (:parent-ctx child-ctx)]
        (let [pairs (shared-pairs child-ctx parent-ctx)]
          ;; 1. conflict pre-check (FAIL-SAFE: a throwing detector counts as an
          ;; indeterminate conflict so the gate aborts rather than blind-merges).
          (when-not (or (:strategy opts) (:force opts))
            (let [confs (mapcat (fn [[sid _ cval psys]]
                                  (let [fsys (ys/effective-system cval)]
                                    (when (satisfies? ygg/Mergeable fsys)
                                      (try (map #(assoc % :system sid)
                                                (ygg/conflicts psys
                                                               (ygg/snapshot-id psys)
                                                               (ygg/snapshot-id fsys)))
                                           (catch Throwable e
                                             [{:system sid :indeterminate? true
                                               :error (.getMessage e)}])))))
                                pairs)]
              (when (seq confs)
                (throw (ex-info "workspace merge has conflicts; aborting (pass :strategy or :force)"
                                {:conflicts (vec confs)})))))
          ;; 2. merge each overlay down, repoint the parent ygg-signal, discard.
          (let [merged (reduce
                        (fn [acc [sid sig-ref cval _psys]]
                          (if (ovl/overlay? cval)
                            (let [m (ygg/merge-down! cval opts)]
                              (set-node-value! parent-ctx sig-ref m)
                              (ygg/discard! cval)
                              (conj acc sid))
                            acc))
                        []
                        pairs)
                ;; 3. carry child-only systems into the parent registry + nodes.
                co (child-only child-ctx parent-ctx)]
            (doseq [[sid sig-ref] co]
              (rtp/swap-state! parent-ctx [registry-key] #(assoc (or % {}) sid sig-ref))
              (rtp/swap-state! parent-ctx [:forkable-signals] #(conj (or % #{}) (:id sig-ref)))
              (set-node-value! parent-ctx sig-ref (node-value child-ctx sig-ref)))
            (when-let [cb (:on-merge opts)]
              (cb {:merged merged :child-only (vec (keys co))
                   :parent-ctx parent-ctx :child-ctx child-ctx}))
            {:merged merged :child-only (vec (keys co))}))))))

#?(:clj
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
      (when-let [parent-ctx (:parent-ctx child-ctx)]
        (doseq [[_ _ cval _] (shared-pairs child-ctx parent-ctx)]
          (when (ovl/overlay? cval) (ygg/discard! cval)))
        (when-let [cb (:on-discard opts)]
          (let [co (child-only child-ctx parent-ctx)]
            (cb {:child-only (vec (keys co))
                 :child-only-systems (into {} (keep (fn [[sid sr]]
                                                      (when-let [s (ys/effective-system (node-value child-ctx sr))]
                                                        [sid s])))
                                           co)
                 :child-ctx child-ctx}))))
      nil)))

;; ForkHandle variants (delegate to the ctx-based ops)

#?(:clj
   (defn merge-fork!
     "Merge fork's overlays to parent (ForkHandle variant of merge-to-parent!)."
     ([fork-handle] (merge-fork! fork-handle {}))
     ([fork-handle opts] (merge-to-parent! (:child-ctx fork-handle) opts))))

#?(:clj
   (defn discard-fork!
     "Discard fork's overlays (ForkHandle variant of discard-from-parent!)."
     ([fork-handle] (discard-fork! fork-handle {}))
     ([fork-handle opts] (discard-from-parent! (:child-ctx fork-handle) opts))))

;; =============================================================================
;; Merge From Parent (Parent → Child sync)
;; =============================================================================

#?(:clj
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
      (when-let [parent-ctx (:parent-ctx child-ctx)]
        (doseq [[_ sig-ref cval psys] (shared-pairs child-ctx parent-ctx)]
          (let [fsys (ys/effective-system cval)]
            (when (and (satisfies? ygg/Branchable fsys)
                       (satisfies? ygg/Mergeable fsys))
              (let [cbranch (ygg/current-branch fsys)
                    pbranch (ygg/current-branch psys)
                    m (-> fsys
                          (ygg/checkout cbranch)
                          (ygg/merge! pbranch
                                      (merge {:message (str "Merge from " (name pbranch))} opts)))]
                ;; repoint: if cval is an overlay, update its writable system in
                ;; place; else repoint the node.
                (if (ovl/overlay? cval)
                  (ovl/reseat-overlay! cval m)
                  (set-node-value! child-ctx sig-ref m)))))))
      nil)))

#?(:clj
   (defn merge-fork-from-parent!
     "Merge parent's current state into a fork (ForkHandle variant)."
     ([fork-handle] (merge-fork-from-parent! fork-handle {}))
     ([fork-handle opts]
      (merge-from-parent! (:child-ctx fork-handle) opts))))

;; =============================================================================
;; Accessors
;; =============================================================================

#?(:clj
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
           (ys/effective-system (node-value parent-ctx sig-ref)))))))

;; =============================================================================
;; Optional Helpers (datahike double-deref ergonomics + GC)
;; =============================================================================

#?(:clj
   (defn db
     "Get current db value from a datahike YggRef. Equivalent to @@ydb."
     [ydb-ref]
     @@ydb-ref))

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
