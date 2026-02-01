(ns org.replikativ.spindel.yggdrasil
  "Yggdrasil integration for spindel execution contexts.

   Provides fork-safe references to yggdrasil systems (git, datahike, btrfs, etc.)
   that automatically resolve from the current execution context.

   Key concepts:
   - YggRef: Reference type wrapping system ID, resolves via *execution-context*
   - register!: Register a yggdrasil system as external-ref, returns YggRef
   - fork-context automatically forks all external-refs via PForkable protocol
   - merge-fork!/discard-fork!: Parent-controlled merge/discard of forked branches

   Naming convention: Prefix YggRef vars with 'y' (e.g., ygit, ydb) to signal deref needed.

   Example:
     (def ygit (ygg/register! (git/create \".\")))
     (def ydb (ygg/register! (dh/connect cfg)))

     @ygit  ; => GitSystem in current context

     ;; Fork automatically branches all registered yggdrasil systems
     (let [child-ctx (ctx/fork-context parent-ctx)]
       (rtc/with-context child-ctx
         @ygit  ; => GitSystem on forked branch (automatic!)
         (d/transact! @ydb [{:foo/bar 1}]))
       (ygg/merge-to-parent! child-ctx))

   For explicit fork handle pattern (backwards compatible):
     (let [fork (ygg/fork!)]
       (ygg/with-fork fork
         @ygit)  ; => forked
       (ygg/merge-fork! fork))"
  (:require [org.replikativ.spindel.runtime.core :as rtc]
            [org.replikativ.spindel.runtime.protocols :as rtp]
            [org.replikativ.spindel.runtime.context :as ctx]
            #?(:clj [yggdrasil.protocols :as ygg])))

;; =============================================================================
;; PForkable Extension for Yggdrasil Systems
;; =============================================================================

;; Extend yggdrasil system types to implement PForkable.
;; This allows fork-context to automatically fork them.

#?(:clj
   (defn- fork-ygg-system
     "Fork a yggdrasil system to a new branch.

      Uses yggdrasil's Branchable protocol - works for any system type.

      Args:
        sys - Yggdrasil system (must implement Branchable)
        fork-id - Keyword ID for the fork

      Returns: New system instance on the new branch"
     [sys fork-id]
     (let [current-branch (ygg/current-branch sys)
           new-branch (keyword (str (name current-branch) "-" (name fork-id)))]
       (-> sys
           (ygg/branch! new-branch)
           (ygg/checkout new-branch)))))

;; Extend PForkable to all yggdrasil system types
;; We use extend-protocol with Object as a catch-all for any yggdrasil system
;; that implements the Branchable protocol

#?(:clj
   (extend-protocol rtp/PForkable
     ;; Default implementation for any object that implements yggdrasil Branchable
     ;; This works because yggdrasil systems are records that satisfy the protocol
     Object
     (pfork [this fork-id]
       (if (satisfies? ygg/Branchable this)
         (fork-ygg-system this fork-id)
         (throw (ex-info "Object does not implement yggdrasil Branchable protocol"
                         {:type (type this)
                          :hint "Only yggdrasil systems can be registered as external-refs"}))))))

;; =============================================================================
;; YggRef - Fork-safe reference to yggdrasil system
;; =============================================================================

;; Following RuntimeAtom pattern: stores only ID, uses dynamic *execution-context*

#?(:clj
   (deftype YggRef [id]
     clojure.lang.IDeref
     (deref [_this]
       ;; Look up from [:external-refs id] in current context
       (if-let [sys (rtc/get-state [:external-refs id])]
         sys
         (throw (ex-info "Yggdrasil system not found in current context"
                         {:id id
                          :hint "Ensure you're inside a bound execution context with registered systems"}))))

     clojure.lang.IMeta
     (meta [_this]
       (when-let [sys (rtc/get-state [:external-refs id])]
         {:system-id id
          :system-type (ygg/system-type sys)
          :current-branch (ygg/current-branch sys)})))

   :cljs
   (deftype YggRef [id]
     IDeref
     (-deref [_this]
       (if-let [sys (rtc/get-state [:external-refs id])]
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
;; Registration
;; =============================================================================

(defn register!
  "Register a yggdrasil system with current execution context.

   The system is stored in [:external-refs] and will be automatically
   forked when fork-context is called (via PForkable protocol).

   Returns a YggRef that resolves to the current system from context.
   The same YggRef works in parent and forked contexts.

   Args:
     sys - Yggdrasil system (must implement SystemIdentity and Branchable)

   Returns: YggRef

   Example:
     (def ygit (register! (git/create \".\")))
     @ygit  ; => the git system"
  [sys]
  #?(:clj
     (let [sys-id (ygg/system-id sys)]
       (rtc/swap-state! [:external-refs sys-id] (constantly sys))
       (->YggRef sys-id))
     :cljs
     (throw (ex-info "Yggdrasil not yet supported in ClojureScript" {}))))

(defn get-system
  "Get registered system by ID from current context.

   Prefer using @ygg-ref instead.

   Args:
     sys-id - System ID (string)

   Returns: Yggdrasil system or nil"
  [sys-id]
  (rtc/get-state [:external-refs sys-id]))

(defn registered-systems
  "Get all registered yggdrasil systems from current context.

   Returns: Map of {sys-id -> system}"
  []
  (rtc/get-state [:external-refs]))

;; =============================================================================
;; Fork Handle (for backwards compatibility and explicit control)
;; =============================================================================

(defrecord ForkHandle [child-ctx parent-ctx fork-id])

(defn fork-handle?
  "Returns true if x is a ForkHandle."
  [x]
  (instance? ForkHandle x))

;; =============================================================================
;; Fork Creation
;; =============================================================================

(defn fork!
  "Create a forked execution context with branched yggdrasil systems.

   This is a convenience wrapper around ctx/fork-context that returns
   a ForkHandle for explicit merge/discard control.

   The actual forking of yggdrasil systems happens automatically in
   fork-context via the PForkable protocol.

   Returns ForkHandle for later merge/discard. Must be called from parent context.

   Permission model:
   - An agent CAN fork from its current context (creating children)
   - An agent CAN merge its own children back into its branch
   - An agent CANNOT merge its own context into its parent

   Example:
     (let [fork (fork!)]
       (with-fork fork
         ;; Work in forked context - @ygit is on forked branch
         (spit (str (git/worktree-path @ygit) \"/new.clj\") \"...\"))
       (merge-fork! fork))"
  []
  #?(:clj
     (let [parent-ctx (rtc/current-execution-context)
           ;; fork-context automatically forks all [:external-refs] via PForkable
           child-ctx (ctx/fork-context parent-ctx)
           fork-id (:fork-id child-ctx)]
       (->ForkHandle child-ctx parent-ctx fork-id))

     :cljs
     (throw (ex-info "Yggdrasil fork not yet supported in ClojureScript" {}))))

#?(:clj
   (defmacro with-fork
     "Execute body in fork's context.

      YggRef derefs (@ygit, @ydb) resolve to forked instances within body.

      Args:
        fork-handle - ForkHandle from fork!
        body - Forms to execute in forked context

      Example:
        (let [fork (fork!)]
          (with-fork fork
            (spit (str (git/worktree-path @ygit) \"/new.clj\") \"...\"))
          (merge-fork! fork))"
     [fork-handle & body]
     `(rtc/with-context (:child-ctx ~fork-handle)
        ~@body)))

;; =============================================================================
;; Merge/Discard (Parent-Controlled)
;; =============================================================================

#?(:clj
   (defn merge-fork!
     "Merge fork's yggdrasil changes to parent. Called from parent context.

      Permission model: You can only merge forks that YOU created.
      The child context has no privileges to merge into its parent.

      Args:
        fork-handle - ForkHandle from fork!

      Returns: nil

      Example:
        (let [fork (fork!)]
          (with-fork fork
            ;; Make changes...
            )
          (merge-fork! fork))"
     [fork-handle]
     (let [{:keys [child-ctx parent-ctx]} fork-handle
           child-systems (rtp/get-state child-ctx [:external-refs])
           parent-systems (rtp/get-state parent-ctx [:external-refs])]

       (doseq [[sys-id child-sys] child-systems
               :when (satisfies? ygg/Branchable child-sys)
               :let [parent-sys (get parent-systems sys-id)
                     child-branch (ygg/current-branch child-sys)
                     parent-branch (ygg/current-branch parent-sys)]]
         ;; Merge child branch into parent branch
         (let [merged-sys (-> parent-sys
                              (ygg/checkout parent-branch)
                              (ygg/merge! child-branch))]
           ;; Update parent context with merged system
           (rtp/swap-state! parent-ctx [:external-refs sys-id] (constantly merged-sys)))

         ;; Cleanup: delete child branch
         (ygg/delete-branch! parent-sys child-branch))

       nil)))

#?(:clj
   (defn discard-fork!
     "Discard fork's yggdrasil branches without merging. Called from parent context.

      Cleans up the forked branches. The fork handle should not be used after this.

      Args:
        fork-handle - ForkHandle from fork!

      Returns: nil"
     [fork-handle]
     (let [{:keys [child-ctx parent-ctx]} fork-handle
           child-systems (rtp/get-state child-ctx [:external-refs])
           parent-systems (rtp/get-state parent-ctx [:external-refs])]

       (doseq [[sys-id child-sys] child-systems
               :when (satisfies? ygg/Branchable child-sys)
               :let [parent-sys (get parent-systems sys-id)
                     child-branch (ygg/current-branch child-sys)]]
         ;; Delete child branch (also removes worktree for git)
         (ygg/delete-branch! parent-sys child-branch))

       nil)))

;; =============================================================================
;; Direct Context Merge/Discard (without ForkHandle)
;; =============================================================================

#?(:clj
   (defn merge-to-parent!
     "Merge child context's yggdrasil changes to its parent.

      Alternative to merge-fork! when working directly with contexts
      instead of ForkHandle.

      Args:
        child-ctx - Child ExecutionContext to merge from

      Returns: nil"
     [child-ctx]
     (when-let [parent-ctx (:parent-ctx child-ctx)]
       (let [child-systems (rtp/get-state child-ctx [:external-refs])
             parent-systems (rtp/get-state parent-ctx [:external-refs])]

         (doseq [[sys-id child-sys] child-systems
                 :when (satisfies? ygg/Branchable child-sys)
                 :let [parent-sys (get parent-systems sys-id)
                       child-branch (ygg/current-branch child-sys)
                       parent-branch (ygg/current-branch parent-sys)]]
           (let [merged-sys (-> parent-sys
                                (ygg/checkout parent-branch)
                                (ygg/merge! child-branch))]
             (rtp/swap-state! parent-ctx [:external-refs sys-id] (constantly merged-sys)))
           (ygg/delete-branch! parent-sys child-branch))))
     nil))

#?(:clj
   (defn discard-from-parent!
     "Discard child context's yggdrasil branches without merging.

      Alternative to discard-fork! when working directly with contexts.

      Args:
        child-ctx - Child ExecutionContext to discard

      Returns: nil"
     [child-ctx]
     (when-let [parent-ctx (:parent-ctx child-ctx)]
       (let [child-systems (rtp/get-state child-ctx [:external-refs])
             parent-systems (rtp/get-state parent-ctx [:external-refs])]

         (doseq [[sys-id child-sys] child-systems
                 :when (satisfies? ygg/Branchable child-sys)
                 :let [parent-sys (get parent-systems sys-id)
                       child-branch (ygg/current-branch child-sys)]]
           (ygg/delete-branch! parent-sys child-branch))))
     nil))

;; =============================================================================
;; Accessors
;; =============================================================================

#?(:clj
   (defn parent-system
     "Get parent context's version of this system (read-only access).

      Works with YggRef or raw system. Must be called from child context.

      Args:
        sys-or-ref - YggRef or raw yggdrasil system

      Returns: Parent's system instance, or nil if at root"
     [sys-or-ref]
     (let [sys-id (if (ygg-ref? sys-or-ref)
                    (ygg-ref-id sys-or-ref)
                    (ygg/system-id sys-or-ref))
           ctx (rtc/current-execution-context)
           parent-ctx (:parent-ctx ctx)]
       (when parent-ctx
         (rtp/get-state parent-ctx [:external-refs sys-id])))))

;; =============================================================================
;; Optional Helpers (for datahike double-deref ergonomics)
;; =============================================================================

#?(:clj
   (defn db
     "Get current db value from a datahike YggRef.

      Equivalent to @@ydb - handles the double-deref.

      Args:
        ydb-ref - YggRef wrapping a datahike connection

      Returns: Current datahike db value"
     [ydb-ref]
     @@ydb-ref))

#?(:clj
   (defn q
     "Query helper that handles datahike double-deref automatically.

      Args:
        ydb-ref - YggRef wrapping a datahike connection
        query - Datalog query
        args - Additional query arguments

      Returns: Query result

      Example:
        (q ydb '[:find ?n :where [?e :user/name ?n]])"
     [ydb-ref query & args]
     (apply (requiring-resolve 'datahike.api/q) query @@ydb-ref args)))
