(ns org.replikativ.spindel.yggdrasil
  "Yggdrasil integration for spindel execution contexts.

   A context holds ONE pforkable external-ref: a yggdrasil `CompositeSystem`
   *workspace* of all registered systems (git + chat-db + KB + code-index + …).
   `register!` composes each system into that one workspace; forking forks the
   workspace as a unit (shared branch namespace across all sub-systems); diff /
   merge / discard are single workspace operations.

   Key concepts:
   - register!: compose a yggdrasil system into the context's workspace
     (stored once at [:external-refs ::workspace]); returns a YggRef keyed by
     the system's id.
   - YggRef / system / get-system: resolve a sub-system id THROUGH the
     workspace composite — transparently branch-correct in forked contexts.
   - fork-context forks the single workspace via the PForkable protocol
     (CompositeSystem is Branchable → its branch! fans out to every sub-system
     with the SAME fork branch name).
   - workspace-diff / workspace-conflicts: per-sub-system delta vs parent, using
     the per-system MERGE-BASE (mixed native bases — datahike :db, git main).
   - merge-to-parent! / discard-from-parent!: parent-controlled, transactional
     merge / discard of the fork's branches.

   Naming convention: Prefix YggRef vars with 'y' (e.g., ygit, ydb) to signal
   deref needed.

   Example:
     (def ygit (ygg/register! (git/create \".\")))   ; workspace = {git}
     (def ydb  (ygg/register! (dh/connect cfg)))      ; workspace = {git, db}

     @ygit                      ; => the git sub-system in the current context
     (ygg/system \"dvergr-db\")   ; => the db sub-system (canonical accessor)

     ;; Fork branches the whole workspace atomically (shared branch name)
     (let [child-ctx (ctx/fork-context parent-ctx)]
       (ec/with-context child-ctx
         @ygit  ; => git sub-system on the forked branch (automatic!)
         (d/transact! @@ydb [{:foo/bar 1}]))
       (ygg/merge-to-parent! child-ctx))            ; transactional"
  (:require [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.context :as ctx]
            #?@(:clj [[yggdrasil.protocols :as ygg]
                      [yggdrasil.types :as ygt]
                      [yggdrasil.composite :as ygc]])))

;; =============================================================================
;; The workspace external-ref key
;; =============================================================================

;; The single pforkable external-ref: a CompositeSystem of all registered
;; yggdrasil systems. Keeping it under one key means fork-context forks the
;; workspace as a unit (no per-system fan-out at the spindel layer — the
;; composite's own branch! fans out one level down).
(def workspace-key ::workspace)

;; =============================================================================
;; PForkable Extension for Yggdrasil Systems
;; =============================================================================

;; Extend yggdrasil system types to implement PForkable so fork-context can
;; fork them. The catch-all matches any Branchable yggdrasil system — including
;; the CompositeSystem workspace, whose branch! fans out to every sub-system.

#?(:clj
   (defn- fork-ygg-system
     "Fork a yggdrasil system to a new branch via the Branchable protocol.
      Works for any system type, including a CompositeSystem (whose branch!
      fans the new branch name out to every sub-system)."
     [sys fork-id]
     (let [current-branch (ygg/current-branch sys)
           new-branch (keyword (str (name current-branch) "-" (name fork-id)))]
       (-> sys
           (ygg/branch! new-branch)
           (ygg/checkout new-branch)))))

#?(:clj
   (extend-protocol rtp/PForkable
     Object
     (pfork [this fork-id]
       (if (satisfies? ygg/Branchable this)
         (fork-ygg-system this fork-id)
         (throw (ex-info "Object does not implement yggdrasil Branchable protocol"
                         {:type (type this)
                          :hint "Only yggdrasil systems can be registered as external-refs"}))))))

;; =============================================================================
;; Workspace + resolution
;; =============================================================================

#?(:clj
   (defn workspace
     "The context's CompositeSystem workspace (all registered systems as one),
      or nil if nothing registered yet. Reads the current execution context, or
      an explicit `ctx`."
     ([] (ec/get-state [:external-refs workspace-key]))
     ([ctx] (rtp/get-state ctx [:external-refs workspace-key]))))

#?(:clj
   (defn- resolve-system
     "Resolve a sub-system by id THROUGH the workspace composite in the current
      context. Falls back to a direct [:external-refs id] read for contexts that
      predate the workspace (or where nothing is registered) so resolution stays
      robust. Returns the system or nil."
     [id]
     (if-let [ws (ec/get-state [:external-refs workspace-key])]
       (or (get (:systems ws) id)
           (when (= id (ygg/system-id ws)) ws))
       (ec/get-state [:external-refs id]))))

;; =============================================================================
;; YggRef - Fork-safe reference to a yggdrasil sub-system
;; =============================================================================

;; Stores only the sub-system id; resolves via the workspace in the dynamic
;; *execution-context*. The same YggRef works in parent and forked contexts.

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
       (if-let [sys (ec/get-state [:external-refs id])]
         sys
         (throw (ex-info "Yggdrasil system not found in current context"
                         {:id id}))))

     IMeta
     (-meta [_this]
       {:system-id id})))

(defn ygg-ref?
  "Returns true if x is a YggRef."
  [x]
  (instance? YggRef x))

(defn ygg-ref-id
  "Get the system ID from a YggRef."
  [yref]
  (.-id yref))

;; =============================================================================
;; Registration — compose into the workspace
;; =============================================================================

(defn register!
  "Compose a yggdrasil system into the current context's workspace.

   The first call creates the workspace CompositeSystem; subsequent calls
   rebuild it with the new system added. The workspace is stored ONCE at
   [:external-refs ::workspace] and is automatically forked as a unit when
   fork-context is called (via the PForkable protocol).

   Returns a YggRef that resolves the system from context (through the
   workspace). The same YggRef works in parent and forked contexts.

   Args:
     sys - Yggdrasil system (must implement SystemIdentity and Branchable)

   Returns: YggRef

   Example:
     (def ygit (register! (git/create \".\")))
     @ygit  ; => the git system"
  [sys]
  #?(:clj
     (let [sys-id  (ygg/system-id sys)
           ws      (ec/get-state [:external-refs workspace-key])
           sys-map (assoc (if ws (:systems ws) {}) sys-id sys)
           new-ws  (ygc/composite (vals sys-map)
                                  :branch :main
                                  :name "spindel-workspace")]
       (ec/swap-state! [:external-refs workspace-key] (constantly new-ws))
       (->YggRef sys-id))
     :cljs
     (throw (ex-info "Yggdrasil not yet supported in ClojureScript" {}))))

(defn unregister!
  "Remove the system identified by `sys-id` from the current context's workspace
   composite — the mirror of `register!`. No-op if absent. When the last system
   is removed the workspace is cleared (so `system` returns nil). Returns true if
   a system was removed."
  [sys-id]
  #?(:clj
     (when-let [ws (ec/get-state [:external-refs workspace-key])]
       (let [systems (:systems ws)]
         (when (contains? systems sys-id)
           (let [sys-map (dissoc systems sys-id)]
             (ec/swap-state! [:external-refs workspace-key]
                             (constantly (when (seq sys-map)
                                           (ygc/composite (vals sys-map)
                                                          :branch :main
                                                          :name "spindel-workspace"))))
             true))))
     :cljs
     (throw (ex-info "Yggdrasil not yet supported in ClojureScript" {}))))

(defn system
  "Get a registered sub-system by id from the current context, resolved through
   the workspace. Branch-correct inside a forked context. Returns nil if absent.

   The canonical accessor — prefer this (or @ygg-ref) over reaching into
   [:external-refs …] by hand."
  [sys-id]
  #?(:clj (resolve-system sys-id)
     :cljs (ec/get-state [:external-refs sys-id])))

(defn get-system
  "Alias for `system` (backwards-compatible name)."
  [sys-id]
  (system sys-id))

(defn registered-systems
  "All registered sub-systems in the current context as {sys-id → system}
   (the workspace's :systems map). Empty map when nothing is registered."
  []
  #?(:clj (if-let [ws (ec/get-state [:external-refs workspace-key])]
            (:systems ws)
            {})
     :cljs {}))

;; =============================================================================
;; Per-system pair helpers (child fork vs parent)
;; =============================================================================

#?(:clj
   (defn- sub-systems
     "The {sys-id → system} map of a context's workspace, or nil."
     [c]
     (when-let [ws (rtp/get-state c [:external-refs workspace-key])]
       (:systems ws))))

#?(:clj
   (defn- mergeable-pairs
     "Seq of [sys-id child-sys parent-sys] for sub-systems present in BOTH the
      child and parent workspaces and Branchable in the child."
     [child-ctx parent-ctx]
     (let [child-sys  (sub-systems child-ctx)
           parent-sys (sub-systems parent-ctx)]
       (for [[sid csys] child-sys
             :when (satisfies? ygg/Branchable csys)
             :let  [psys (get parent-sys sid)]
             :when psys]
         [sid csys psys]))))

;; =============================================================================
;; Fork Handle (explicit control / backwards compatibility)
;; =============================================================================

(defrecord ForkHandle [child-ctx parent-ctx fork-id])

(defn fork-handle?
  "Returns true if x is a ForkHandle."
  [x]
  (instance? ForkHandle x))

(defn fork!
  "Create a forked execution context with the workspace branched.

   Convenience wrapper around ctx/fork-context that returns a ForkHandle for
   explicit merge/discard control. The actual forking of the workspace happens
   in fork-context via the PForkable protocol.

   Permission model:
   - An agent CAN fork from its current context (creating children).
   - An agent CAN merge its own children back into its branch.
   - An agent CANNOT merge its own context into its parent.

   Example:
     (let [fork (fork!)]
       (with-fork fork
         (spit (str (git/worktree-path @ygit) \"/new.clj\") \"...\"))
       (merge-fork! fork))"
  []
  #?(:clj
     (let [parent-ctx (ec/current-execution-context)
           child-ctx  (ctx/fork-context parent-ctx)
           fork-id    (:fork-id child-ctx)]
       (->ForkHandle child-ctx parent-ctx fork-id))
     :cljs
     (throw (ex-info "Yggdrasil fork not yet supported in ClojureScript" {}))))

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
     "The fork's OWN changes in one sub-system. Preferred: diff the MERGE-BASE
      (common ancestor of parent + fork) → fork, so a live parent's concurrent
      advance is excluded (git merge-base is exact). Falls back to parent→fork
      when the merge-base can't be resolved.

      Resolves everything to SNAPSHOT-IDS (git sha / datahike db hash) rather than
      branch keywords — the sub-systems have mixed native branch names, so a
      branch keyword (`:main` / `:main-fork-x`) is not a valid ref to pass
      uniformly, whereas each system's own snapshot-id always is."
     [csys psys]
     (let [psnap (ygg/snapshot-id psys)
           fsnap (ygg/snapshot-id csys)]
       (or (try
             (let [base (ygg/common-ancestor csys psnap fsnap)]
               (when base (ygg/diff csys base fsnap)))
             (catch Throwable _ nil))
           (try (ygg/diff csys psnap fsnap)
                (catch Throwable t (ygt/->DiffError psnap fsnap (.getMessage t))))))))

#?(:clj
   (defn workspace-diff
     "Per-sub-system delta of a forked context vs its parent — the unified diff a
      reviewer reads: {sys-id → typed yggdrasil delta (GitDiff / DatahikeDiff /
      DiffError)}. nil when the context has no parent.

      Each sub-system is diffed on its OWN branch pair using the merge-base
      (mixed native bases — datahike :db, git main — so a shared base branch name
      would be wrong). Non-Mergeable sub-systems are omitted."
     [child-ctx]
     (when-let [parent-ctx (:parent-ctx child-ctx)]
       (into {}
             (keep (fn [[sid csys psys]]
                     (when (and (satisfies? ygg/Mergeable csys)
                                (satisfies? ygg/Graphable csys))
                       [sid (system-merge-base-diff csys psys)])))
             (mergeable-pairs child-ctx parent-ctx)))))

#?(:clj
   (defn workspace-conflicts
     "Per-sub-system conflicts of a forked context vs its parent, each tagged
      `:system`. nil when the context has no parent. Often empty (datahike
      conflict detection is conservative today)."
     [child-ctx]
     (when-let [parent-ctx (:parent-ctx child-ctx)]
       (into []
             (mapcat (fn [[sid csys psys]]
                       (when (satisfies? ygg/Mergeable csys)
                         (try (map #(assoc % :system sid)
                                   (ygg/conflicts csys
                                                  (ygg/snapshot-id psys)
                                                  (ygg/snapshot-id csys)))
                              (catch Throwable _ nil)))))
             (mergeable-pairs child-ctx parent-ctx)))))

;; context-diff: backwards-compatible alias (richer per-system map dropped in
;; favour of the typed deltas from workspace-diff).
#?(:clj (def context-diff workspace-diff))

;; =============================================================================
;; Merge / Discard (Parent-Controlled, transactional)
;; =============================================================================

#?(:clj
   (defn merge-to-parent!
     "Merge a forked context's workspace into its parent — TRANSACTIONAL across
      sub-systems.

      Algorithm:
        1. Pre-check conflicts (unless :strategy or :force given); abort
           untouched if any sub-system conflicts.
        2. Stage every sub-system merge as a value.
        3. Only when ALL succeed, atomically swap the parent's workspace and
           delete the fork's branches.
      If any sub-system merge throws, the parent workspace pointer is left
      unchanged (no half-merge of the logical state) and the error is re-thrown
      with diagnostics. (Underlying store writes for already-merged sub-systems
      may have landed — git/datahike have no cross-store 2PC; the conflict
      pre-check makes mid-merge failure unlikely.)

      Args:
        child-ctx - Child ExecutionContext to merge from
        opts      - Optional {:strategy … :force true :message …} passed to
                    yggdrasil merge!

      Returns: {:merged [sys-id …]} or nil if child has no parent."
     ([child-ctx] (merge-to-parent! child-ctx {}))
     ([child-ctx opts]
      (when-let [parent-ctx (:parent-ctx child-ctx)]
        (let [pairs     (mergeable-pairs child-ctx parent-ctx)
              parent-ws (rtp/get-state parent-ctx [:external-refs workspace-key])]
          ;; 1. conflict pre-check
          (when-not (or (:strategy opts) (:force opts))
            (let [confs (mapcat (fn [[sid csys psys]]
                                  (when (satisfies? ygg/Mergeable csys)
                                    (try (map #(assoc % :system sid)
                                              (ygg/conflicts csys
                                                             (ygg/snapshot-id psys)
                                                             (ygg/snapshot-id csys)))
                                         (catch Throwable _ nil))))
                                pairs)]
              (when (seq confs)
                (throw (ex-info "workspace merge has conflicts; aborting (pass :strategy or :force)"
                                {:conflicts (vec confs)})))))
          ;; 2. stage all merges (capture rollback snapshots for diagnostics)
          (let [rollback (into {} (map (fn [[sid _ psys]] [sid (ygg/snapshot-id psys)])) pairs)
                merged   (try
                           (reduce (fn [acc [sid _csys psys :as pair]]
                                     (let [csys    (nth pair 1)
                                           pbranch (ygg/current-branch psys)
                                           cbranch (ygg/current-branch csys)
                                           m (-> psys
                                                 (ygg/checkout pbranch)
                                                 (ygg/merge! cbranch opts))]
                                       (assoc acc sid m)))
                                   {} pairs)
                           (catch Throwable e
                             (throw (ex-info "workspace merge failed mid-way; parent workspace left unchanged"
                                             {:rollback rollback} e))))]
            ;; 3. commit atomically. CARRY child-only systems too — a system
            ;; registered in the fork has no parent counterpart in `pairs`, so
            ;; without this merge would silently DROP it (it's on its own default
            ;; branch, not a to-be-deleted fork branch). Then delete child branches,
            ;; then fire :on-merge so an external registry can reconcile in-band.
            (let [child-only (apply dissoc (sub-systems child-ctx)
                                    (keys (sub-systems parent-ctx)))]
              (rtp/swap-state! parent-ctx [:external-refs workspace-key]
                               (constantly (assoc parent-ws
                                                  :systems (merge (sub-systems parent-ctx)
                                                                  merged child-only))))
              (doseq [[_ csys psys] pairs]
                (ygg/delete-branch! psys (ygg/current-branch csys)))
              (when-let [cb (:on-merge opts)]
                (cb {:merged (vec (keys merged)) :child-only (vec (keys child-only))
                     :parent-ctx parent-ctx :child-ctx child-ctx}))
              {:merged (vec (keys merged)) :child-only (vec (keys child-only))})))))))

#?(:clj
   (defn discard-from-parent!
     "Discard a forked context's workspace branches without merging. Deletes each
      shared sub-system's fork branch (removing git worktrees etc.). Called from
      parent. Fork-ONLY systems (registered in the fork, e.g. an agent-created DB)
      have no shared branch to delete and their stores are NOT removed here — the
      `:on-discard` callback receives them so an external owner can clean up (delete
      the store, drop a deferred registry grant) and avoid an orphaned/resurrected DB.

      Args:
        child-ctx - Child ExecutionContext to discard
        opts      - {:on-discard (fn [{:keys [child-only child-ctx]}])}

      Returns: nil"
     ([child-ctx] (discard-from-parent! child-ctx {}))
     ([child-ctx opts]
      (when-let [parent-ctx (:parent-ctx child-ctx)]
        (doseq [[_ csys psys] (mergeable-pairs child-ctx parent-ctx)]
          (ygg/delete-branch! psys (ygg/current-branch csys)))
        (when-let [cb (:on-discard opts)]
          (let [child-only (apply dissoc (sub-systems child-ctx)
                                  (keys (sub-systems parent-ctx)))]
            (cb {:child-only (vec (keys child-only)) :child-only-systems child-only
                 :child-ctx child-ctx}))))
      nil)))

;; ForkHandle variants (delegate to the ctx-based ops)

#?(:clj
   (defn merge-fork!
     "Merge fork's workspace to parent (ForkHandle variant of merge-to-parent!)."
     ([fork-handle] (merge-fork! fork-handle {}))
     ([fork-handle opts] (merge-to-parent! (:child-ctx fork-handle) opts))))

#?(:clj
   (defn discard-fork!
     "Discard fork's workspace branches (ForkHandle variant of
      discard-from-parent!)."
     ([fork-handle] (discard-fork! fork-handle {}))
     ([fork-handle opts] (discard-from-parent! (:child-ctx fork-handle) opts))))

;; =============================================================================
;; Merge From Parent (Parent → Child sync)
;; =============================================================================

#?(:clj
   (defn merge-from-parent!
     "Merge parent's current state INTO a child context (inverse of
      merge-to-parent!). Useful for long-lived agent branches that need to stay
      in sync with the parent. Operates per sub-system, then swaps the child's
      workspace. Called from within the child context.

      Args:
        child-ctx - The child ExecutionContext to update
        opts      - Optional merge opts {:strategy … :message …}

      Returns: nil"
     ([child-ctx] (merge-from-parent! child-ctx {}))
     ([child-ctx opts]
      (when-let [parent-ctx (:parent-ctx child-ctx)]
        (let [parent-sys (sub-systems parent-ctx)
              child-ws   (rtp/get-state child-ctx [:external-refs workspace-key])
              child-sys  (sub-systems child-ctx)
              merged     (reduce
                          (fn [acc [sid csys]]
                            (let [psys (get parent-sys sid)]
                              (if (and psys
                                       (satisfies? ygg/Branchable csys)
                                       (satisfies? ygg/Mergeable csys))
                                (let [cbranch (ygg/current-branch csys)
                                      pbranch (ygg/current-branch psys)
                                      m (-> csys
                                            (ygg/checkout cbranch)
                                            (ygg/merge! pbranch
                                                        (merge {:message (str "Merge from " (name pbranch))}
                                                               opts)))]
                                  (assoc acc sid m))
                                acc)))
                          {} child-sys)]
          (rtp/swap-state! child-ctx [:external-refs workspace-key]
                           (constantly (assoc child-ws
                                              :systems (merge child-sys merged))))))
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
     "Get parent context's version of this sub-system (read-only). Works with a
      YggRef or a raw system. Must be called from a child context. Returns nil
      at root."
     [sys-or-ref]
     (let [sys-id (if (ygg-ref? sys-or-ref)
                    (ygg-ref-id sys-or-ref)
                    (ygg/system-id sys-or-ref))
           ctx        (ec/current-execution-context)
           parent-ctx (:parent-ctx ctx)]
       (when parent-ctx
         (get (sub-systems parent-ctx) sys-id)))))

;; =============================================================================
;; Optional Helpers (for datahike double-deref ergonomics)
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
