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
   - merge-fork! / discard-fork!: affine parent-controlled settlement of the
     fork's per-system overlays. The ForkHandle is the only settlement authority.

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
     (let [fork (ygg/fork!)]
       (ec/with-context (:child-ctx fork)
         @ygit  ; => git system on the forked overlay branch (automatic!)
         (d/transact! @@ydb [{:foo/bar 1}]))
       (ygg/merge-fork! fork))                       ; merge each overlay down"
  (:require [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.state-backend :as backend]
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
(def ^:private fork-authority-key ::fork-authority)

;; Registry shape is part of a fork's settlement authority. On the JVM this
;; lock closes the validation/CAS race between partition-fork! and a concurrent
;; register!/unregister!. ClojureScript executes these synchronous transitions
;; on one event loop, so no monitor is needed there.
#?(:clj (defonce ^:private registry-authority-lock (Object.)))

(defn- with-registry-authority-lock [f]
  #?(:clj (locking registry-authority-lock (f))
     :cljs (f)))

(defn- ensure-world-shape-mutable!
  ([] (ensure-world-shape-mutable! (ec/current-execution-context)))
  ([ctx]
   (when-let [authority (rtp/get-state ctx [fork-authority-key])]
     (let [{:keys [status operation]} @authority]
       (when-not (= :open status)
         (throw (ex-info "Fork world system registry is frozen"
                         {:type ::fork-world-shape-frozen
                          :status status
                          :operation operation})))))
   true))

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

   Returns a plain branched SYSTEM (not an Overlay) — pinned at a PAST value.
   Its `snap-<fork>` branch is managed by the same ForkHandle lifecycle as a
   regular branch fork: merge explicitly to adopt it, or discard to clean it up."
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
  (with-registry-authority-lock
    (fn []
      (ensure-world-shape-mutable!)
      (let [sys-id (ygg/system-id sys)
            sig    (ys/ygg-signal sys)]
        (ec/swap-state! [registry-key] #(assoc (or % {}) sys-id sig))
        (->YggRef sys-id)))))

(defn unregister!
  "Remove the system identified by `sys-id` — the mirror of `register!`. Drops it
   from the registry and the forkable-signal set. Returns true if removed."
  [sys-id]
  (with-registry-authority-lock
    (fn []
      (ensure-world-shape-mutable!)
      (when-let [sig-ref (get (registry) sys-id)]
        (ec/swap-state! [registry-key] #(dissoc % sys-id))
        (ec/swap-state! [:forkable-signals] #(disj (or % #{}) (:id sig-ref)))
        true))))

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

(defn- scoped-shared-pairs
  "Shared pairs for `scope`, failing closed when a descriptor-owned system no
   longer exists in the parent. A missing parent is a changed settlement shape,
   never a child-only system that can be silently carried or skipped."
  [child-ctx parent-ctx scope]
  (let [pairs (vec (shared-pairs child-ctx parent-ctx))]
    (if-not scope
      pairs
      (let [parent-reg (registry parent-ctx)
            selected (filterv (fn [[sid child-ref _ _]]
                                (and (contains? scope sid)
                                     (= (:id child-ref)
                                        (:id (get parent-reg sid)))))
                              pairs)
            present (set (map first selected))
            missing (set (remove present scope))]
        (when (seq missing)
          (throw (ex-info "Fork settlement system shape changed"
                          {:type ::fork-system-shape-changed
                           :missing-from-parent missing
                           :scope scope})))
        selected))))

(defn- set-node-value!
  "Swap ygg-signal `sig-ref`'s node value in `ctx` to `v` (system or overlay),
   preserving observers and bumping generation."
  [ctx sig-ref v]
  (rtp/swap-state! ctx [:nodes (:id sig-ref)]
                   (fn [node]
                     (nodes/->signal-node v nil nil false
                                          (if node (nodes/get-observers node) #{})
                                          (inc (or (:generation node) 0))))))

(defn- ensure-parent-signal-and-seat!
  "After durable merge work, atomically verify that `expected-ref` still names
   `sid` in the parent registry and seat the merged value. This closes the async
   unregister/re-register race that would otherwise update an obsolete node."
  [parent-ctx sid expected-ref value]
  (with-registry-authority-lock
    (fn []
      (let [current-ref (get (registry parent-ctx) sid)]
        (when-not (= (:id expected-ref) (:id current-ref))
          (throw (ex-info "Fork settlement system shape changed during merge"
                          {:type ::fork-system-shape-changed
                           :system sid
                           :expected-signal (:id expected-ref)
                           :current-signal (:id current-ref)})))
        (set-node-value! parent-ctx expected-ref value)))))

(defn- ensure-registry-mutable! [ctx]
  (with-registry-authority-lock #(ensure-world-shape-mutable! ctx)))

(defn- carry-child-only!
  "Atomically carry child-only systems into a mutable parent registry. Internal
   settlement must obey the same world-shape frontier as public registration."
  [parent-ctx child-ctx systems]
  (with-registry-authority-lock
    (fn []
      (ensure-world-shape-mutable! parent-ctx)
      (doseq [[sid sig-ref] systems]
        (rtp/swap-state! parent-ctx [registry-key] #(assoc (or % {}) sid sig-ref))
        (rtp/swap-state! parent-ctx [:forkable-signals] #(conj (or % #{}) (:id sig-ref)))
        (set-node-value! parent-ctx sig-ref (node-value child-ctx sig-ref))))))

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
;; Fork Handle (explicit affine control)
;; =============================================================================

(defrecord ForkHandle [child-ctx parent-ctx fork-id descriptor authority token])

(defn fork-handle?
  "Returns true if x is a ForkHandle."
  [x]
  (instance? ForkHandle x))

(defn fork-descriptor
  "Portable creation-time description of `fork-handle` plus its current owner and
   settlement status. The descriptor contains only data; live contexts, callbacks,
   errors, and the affine authority token never cross this boundary.

   For Snapshotable systems, per-system `:head` is the head observed immediately
   after fork creation. A durable branch remains the live locator after it
   advances; a later settlement journal/export API will checkpoint terminal
   heads for restart recovery. Non-forkable compatibility systems are reported
   honestly as `:kind :shared` rather than pretending they were isolated."
  [fork-handle]
  (let [{:keys [status owner operation partitions]} @(:authority fork-handle)]
    (cond-> (assoc (:descriptor fork-handle)
                   :fork/owner owner
                   :fork/status status)
      operation (assoc :fork/operation operation)
      partitions (assoc :fork/partitions partitions))))

(defn fork-disposition
  "Process-local lifecycle view of a ForkHandle, without its authority token."
  [fork-handle]
  (dissoc @(:authority fork-handle) :token :error :last-error))

(defn open-fork?
  "True when this exact handle still owns the open settlement capability. A
   transferred handle is stale even though the adopted handle remains open."
  [fork-handle]
  (let [{:keys [status token]} @(:authority fork-handle)]
    (and (= :open status) (= token (:token fork-handle)))))

(defn- authority-error [fork-handle state]
  (if (not= (:token fork-handle) (:token state))
    (ex-info "ForkHandle settlement authority was transferred"
             {:type ::stale-fork-handle
              :fork-id (:fork-id fork-handle)
              :owner (:owner state)
              :status (:status state)})
    (ex-info "ForkHandle is not open"
             {:type ::fork-not-open
              :fork-id (:fork-id fork-handle)
              :owner (:owner state)
              :status (:status state)
              :operation (:operation state)})))

(defn- ensure-open-authority! [fork-handle]
  (let [state @(:authority fork-handle)]
    (when-not (and (= :open (:status state))
                   (= (:token fork-handle) (:token state)))
      (throw (authority-error fork-handle state))))
  fork-handle)

(defn transfer-fork!
  "Transfer an OPEN fork's affine settlement authority to `new-owner`.

   Returns a new ForkHandle over the same child/parent world. The old handle is
   immediately stale and can no longer merge, discard, transfer, or advance from
   its parent. No substrate state is copied and no branch is created. This is the
   primitive a durable proposal/room adoption layer uses after it has persisted
   ownership and arranged GC retention."
  [fork-handle new-owner]
  (when (nil? new-owner)
    (throw (ex-info "Fork owner cannot be nil"
                    {:type ::invalid-fork-owner
                     :fork-id (:fork-id fork-handle)})))
  (loop []
    (let [authority (:authority fork-handle)
          state @authority]
      (when-not (and (= :open (:status state))
                     (= (:token fork-handle) (:token state)))
        (throw (authority-error fork-handle state)))
      (let [new-token (random-uuid)
            next-state (assoc state :owner new-owner :token new-token)]
        (if (compare-and-set! authority state next-state)
          (assoc fork-handle
                 :token new-token
                 :descriptor (assoc (:descriptor fork-handle) :fork/owner new-owner))
          (recur))))))

(defn- partition-fork-under-lock!
  [fork-handle partitions]
  ;; Fail on affine authority before inspecting caller-supplied partition data;
  ;; an in-flight advance/settlement is the governing state of the capability.
  (ensure-open-authority! fork-handle)
  (let [parts (vec partitions)
        descriptor (:descriptor fork-handle)
        described (set (keys (:fork/systems descriptor)))
        registered (set (keys (registry (:child-ctx fork-handle))))
        world-systems (or (:fork/world-systems descriptor) described)
        system-sets (mapv (comp set :systems) parts)
        frequencies (frequencies (mapcat seq system-sets))
        overlap (into #{} (keep (fn [[sid n]] (when (> n 1) sid))) frequencies)
        covered (set (keys frequencies))
        unknown (set (remove described covered))
        omitted (set (remove covered described))]
    (when (< (count parts) 2)
      (throw (ex-info "Fork partition requires at least two parts"
                      {:type ::invalid-fork-partition
                       :partition-count (count parts)})))
    (when-let [idx (first (keep-indexed (fn [idx part]
                                          (when (or (not (set? (:systems part)))
                                                    (empty? (:systems part)))
                                            idx))
                                        parts))]
      (throw (ex-info "Each fork partition must name a non-empty system set"
                      {:type ::invalid-fork-partition
                       :partition-index idx
                       :partition (nth parts idx)})))
    (when-let [idx (first (keep-indexed (fn [idx part]
                                          (when (nil? (:owner part)) idx))
                                        parts))]
      (throw (ex-info "Each fork partition requires an owner"
                      {:type ::invalid-fork-owner
                       :partition-index idx})))
    (when (seq overlap)
      (throw (ex-info "Fork partitions overlap"
                      {:type ::overlapping-fork-partition
                       :systems overlap})))
    (when (or (seq unknown) (seq omitted))
      (throw (ex-info "Fork partitions must exactly cover the described world"
                      {:type ::incomplete-fork-partition
                       :unknown unknown
                       :omitted omitted
                       :described described})))
    ;; New child-only systems and removed descriptor systems do not yet have a
    ;; portable creation/basis entry. Refuse to mint misleading partial handles;
    ;; a later descriptor checkpoint/journal can make this case partitionable.
    (when (not= world-systems registered)
      (throw (ex-info "Fork system shape changed after creation"
                      {:type ::fork-system-shape-changed
                       :described world-systems
                       :registered registered
                       :added (set (remove world-systems registered))
                       :removed (set (remove registered world-systems))})))
    (let [partition-of (or (:fork/settlement-id descriptor)
                           (:fork/id descriptor))
          prepared
          (mapv (fn [{:keys [systems owner purpose]}]
                  (let [settlement-id (random-uuid)
                        token (random-uuid)
                        part-descriptor
                        (cond-> (assoc descriptor
                                       :fork/settlement-id settlement-id
                                       :fork/partition-of partition-of
                                       :fork/world-systems world-systems
                                       :fork/systems (select-keys (:fork/systems descriptor)
                                                                  systems)
                                       :fork/owner owner)
                          purpose (assoc :fork/purpose purpose))]
                    {:descriptor part-descriptor
                     :authority (atom {:status :open :owner owner :token token})
                     :token token}))
                parts)
          authority (:authority fork-handle)]
      (loop []
        (let [state @authority]
          (when-not (and (= :open (:status state))
                         (= (:token fork-handle) (:token state)))
            (throw (authority-error fork-handle state)))
          (let [next-state (assoc state
                                  :status :partitioned
                                  :operation :partition
                                  :partitions (mapv #(get-in % [:descriptor
                                                                :fork/settlement-id])
                                                    prepared))]
            (if (compare-and-set! authority state next-state)
              (mapv (fn [{:keys [descriptor authority token]}]
                      (->ForkHandle (:child-ctx fork-handle)
                                    (:parent-ctx fork-handle)
                                    (:fork-id fork-handle)
                                    descriptor authority token))
                    prepared)
              (recur))))))))

(defn partition-fork!
  "Consume one OPEN fork settlement capability and return disjoint capabilities
   over the same execution world.

   `partitions` is a vector of at least two maps:

     [{:systems #{system-id ...} :owner owner-id :purpose optional-tag} ...]

   Every descriptor-named system must occur exactly once: overlaps, omissions,
   unknown systems, nil owners, and worlds whose registered system shape changed
   after fork creation are rejected without consuming the original handle. Each
   returned handle may then be transferred, merged, or discarded independently.

   This partitions substrate *settlement authority*, not runtime access. The
   handles intentionally retain the same child execution context and must remain
   trusted host capabilities rather than values exposed to sandboxed code. Once
   partitioned, that world's system registry is frozen so its exhaustive scopes
   cannot be invalidated by later registration changes."
  [fork-handle partitions]
  (with-registry-authority-lock
    #(partition-fork-under-lock! fork-handle partitions)))

(defn- terminal-status [operation]
  (case operation
    :merge :merged
    :discard :discarded
    (throw (ex-info "Unknown fork settlement operation"
                    {:type ::invalid-settlement-operation
                     :operation operation}))))

(defn- claim-settlement! [fork-handle operation]
  (loop []
    (let [authority (:authority fork-handle)
          state @authority]
      (cond
        (not= (:token fork-handle) (:token state))
        (throw (authority-error fork-handle state))

        (= :open (:status state))
        (let [next-state (-> state
                             (assoc :status :settling
                                    :operation operation
                                    :phase :preflight)
                             (dissoc :last-operation :last-error))]
          (if (compare-and-set! authority state next-state)
            {:execute? true}
            (recur)))

        (and (= (terminal-status operation) (:status state))
             (= operation (:operation state)))
        {:execute? false :result (:result state)}

        :else
        (throw (authority-error fork-handle state))))))

(defn- complete-settlement! [fork-handle operation result]
  (swap! (:authority fork-handle)
         (fn [state]
           (if (and (= (:token fork-handle) (:token state))
                    (= :settling (:status state))
                    (= operation (:operation state)))
             (-> state
                 (assoc :status (terminal-status operation) :result result)
                 (dissoc :phase :last-operation :last-error))
             state)))
  result)

(defn- mark-settlement-mutating! [fork-handle operation]
  (swap! (:authority fork-handle)
         (fn [state]
           (if (and (= (:token fork-handle) (:token state))
                    (= :settling (:status state))
                    (= operation (:operation state)))
             (assoc state :phase :mutating)
             state))))

(defn- fail-settlement! [fork-handle operation error]
  (swap! (:authority fork-handle)
         (fn [state]
           (if (and (= (:token fork-handle) (:token state))
                    (= :settling (:status state))
                    (= operation (:operation state)))
             ;; Read-only preflight failures leave the capability retryable. Once
             ;; any substrate may have changed, reopening would falsely advertise
             ;; a pristine world and permit destructive double settlement.
             (if (= :preflight (:phase state))
               (-> state
                   (assoc :status :open
                          :last-operation operation
                          :last-error error)
                   (update :settlement-attempts (fnil inc 0))
                   (dissoc :operation :phase))
               (-> state
                   (assoc :status :incomplete
                          :last-operation operation
                          :last-error error)
                   (update :settlement-attempts (fnil inc 0))))
             state)))
  error)

(defn- claim-advance! [fork-handle]
  (loop []
    (let [authority (:authority fork-handle)
          state @authority]
      (when-not (and (= :open (:status state))
                     (= (:token fork-handle) (:token state)))
        (throw (authority-error fork-handle state)))
      (let [next-state (-> state
                           (assoc :status :advancing
                                  :operation :advance-from-parent
                                  :phase :preflight)
                           (dissoc :last-operation :last-error))]
        (if (compare-and-set! authority state next-state)
          true
          (recur))))))

(defn- mark-advance-mutating! [fork-handle]
  (swap! (:authority fork-handle)
         (fn [state]
           (if (and (= (:token fork-handle) (:token state))
                    (= :advancing (:status state))
                    (= :advance-from-parent (:operation state)))
             (assoc state :phase :mutating)
             state))))

(defn- complete-advance! [fork-handle]
  (swap! (:authority fork-handle)
         (fn [state]
           (if (and (= (:token fork-handle) (:token state))
                    (= :advancing (:status state))
                    (= :advance-from-parent (:operation state)))
             (-> state
                 (assoc :status :open)
                 (dissoc :operation :phase :last-operation :last-error))
             state)))
  nil)

(defn- fail-advance! [fork-handle error]
  (swap! (:authority fork-handle)
         (fn [state]
           (if (and (= (:token fork-handle) (:token state))
                    (= :advancing (:status state))
                    (= :advance-from-parent (:operation state)))
             (if (= :preflight (:phase state))
               (-> state
                   (assoc :status :open
                          :last-operation :advance-from-parent
                          :last-error error)
                   (update :advance-attempts (fnil inc 0))
                   (dissoc :operation :phase))
               (-> state
                   (assoc :status :incomplete
                          :last-operation :advance-from-parent
                          :last-error error)
                   (update :advance-attempts (fnil inc 0))))
             state)))
  error)

(defn- complete-callback! [fork-handle]
  (swap! (:authority fork-handle)
         #(-> % (assoc :callback-status :completed) (dissoc :callback-error))))

(defn- fail-callback! [fork-handle error]
  ;; Settlement is already terminal: callback failure must never resurrect the
  ;; consumed world. Keep a portable diagnostic so an owner can repair the
  ;; post-commit integration without retrying substrate settlement.
  (swap! (:authority fork-handle)
         #(assoc % :callback-status :failed :callback-error (ex-message error)))
  error)

(defn- run-post-commit! [fork-handle callback payload]
  (when callback
    (try
      (callback payload)
      (complete-callback! fork-handle)
      (catch #?(:clj Throwable :cljs :default) error
        (fail-callback! fork-handle error)
        (throw error)))))

(defn- memoized-cps
  "Return a single-execution partial-CPS expression. Every invocation observes
   the same resolution; callers that invoke it while running are joined rather
   than executing its body again."
  [start]
  (let [state (atom {:status :idle :waiters []})]
    (fn [resolve reject]
      (let [launch? (volatile! false)
            snapshot
            (swap! state
                   (fn [s]
                     (case (:status s)
                       :idle (do (vreset! launch? true)
                                 {:status :running :waiters [[resolve reject]]})
                       :running (update s :waiters conj [resolve reject])
                       s)))]
        (cond
          @launch?
          (letfn [(settle! [status value]
                    (let [waiters (volatile! nil)]
                      (swap! state
                             (fn [s]
                               (vreset! waiters (:waiters s))
                               (assoc s
                                      :status status
                                      (if (= :resolved status) :value :error) value
                                      :waiters [])))
                      (doseq [[res rej] @waiters]
                        ((if (= :resolved status) res rej) value))))]
            (try
              (start #(settle! :resolved %)
                     #(settle! :rejected %))
              (catch #?(:clj Throwable :cljs :default) error
                (settle! :rejected error))))

          (= :resolved (:status snapshot)) (resolve (:value snapshot))
          (= :rejected (:status snapshot)) (reject (:error snapshot))
          :else nil)))))

(defn- settle-sync!
  [fork-handle operation operation-f result-f callback]
  (let [{:keys [execute? result]} (claim-settlement! fork-handle operation)]
    (if-not execute?
      result
      (let [payload (try
                      (operation-f)
                      (catch #?(:clj Throwable :cljs :default) error
                        (fail-settlement! fork-handle operation error)
                        (throw error)))
            result (result-f payload)]
        (complete-settlement! fork-handle operation result)
        (run-post-commit! fork-handle callback payload)
        result))))

(defn- settle-async!
  [fork-handle operation operation-f result-f callback]
  ;; Claim authority only when the CPS expression is actually executed. Merely
  ;; constructing an awaitable must not strand the fork in :settling.
  (memoized-cps
   (fn [resolve reject]
     (try
       (let [{:keys [execute? result]} (claim-settlement! fork-handle operation)]
         (if-not execute?
           (resolve result)
           (letfn [(succeed! [payload]
                     (let [result (result-f payload)]
                       (complete-settlement! fork-handle operation result)
                       (try
                         (run-post-commit! fork-handle callback payload)
                         (resolve result)
                         (catch #?(:clj Throwable :cljs :default) error
                           (reject error)))))
                   (fail! [error]
                     (fail-settlement! fork-handle operation error)
                     (reject error))]
             (try
               (let [x (operation-f)]
                 (if (fn? x)
                   (x succeed! fail!)
                   (succeed! x)))
               (catch #?(:clj Throwable :cljs :default) error
                 (fail! error))))))
       (catch #?(:clj Throwable :cljs :default) error
         (reject error))))))

(defn- settle-fork!
  [fork-handle operation opts operation-f result-f callback]
  (if (:sync? (merge yc/default-opts opts))
    (settle-sync! fork-handle operation operation-f result-f callback)
    (settle-async! fork-handle operation operation-f result-f callback)))

(defn fork!
  "Create a forked execution context with every ygg-signal overlaid (or snapshot-
   forked, per `opts`). Returns a ForkHandle for explicit merge/discard control.

   opts (optional): forwarded to `ctx/fork-context` —
     :mode      :following (default) | :frozen — overlay fork relation to parent
     :executor  optional child executor (default: share the parent's executor)
     :snapshots {system-id -> snapshot-id} — pin those systems at fixed values
     :systems   :all (default) | :none | #{system-id ...} — systems visible and
       forked in the child. Excluded systems are hidden, never shared writable.
     :rights    {system-id :write} — optional explicit grants. Other rights are
       rejected until the substrate can enforce them rather than merely label them.
     :purpose   portable descriptor tag such as :run/:particle/:proposal
     :owner     initial affine settlement owner (default parent context fork-id)
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
            parent-reg (registry parent-ctx)
            systems-opt (get opts :systems :all)
            selected-ids (cond
                           (= :all systems-opt) (set (keys parent-reg))
                           (= :none systems-opt) #{}
                           (set? systems-opt) systems-opt
                           :else (throw (ex-info "Invalid :systems fork policy"
                                                 {:type ::invalid-systems-policy
                                                  :systems systems-opt})))
            unknown (seq (remove #(contains? parent-reg %) selected-ids))
            _known-systems (when unknown
                             (throw (ex-info "Fork policy names unregistered systems"
                                             {:type ::unknown-fork-systems
                                              :systems (vec unknown)
                                              :registered (vec (keys parent-reg))})))
            rights (or (:rights opts) {})
            unknown-rights (seq (remove selected-ids (keys rights)))
            _known-rights (when unknown-rights
                            (throw (ex-info "Fork rights name systems outside the selected world"
                                            {:type ::unknown-fork-rights
                                             :systems (vec unknown-rights)
                                             :selected (vec selected-ids)})))
            unsupported-rights (seq (remove (fn [[_ right]] (= :write right)) rights))
            _enforced-rights (when unsupported-rights
                               (throw (ex-info "Only :write fork rights are currently enforceable"
                                               {:type ::unsupported-fork-rights
                                                :rights (into {} unsupported-rights)
                                                :supported #{:write}})))
            snapshot-ids (set (keys (:snapshots opts)))
            _included-snapshots (when-let [excluded (seq (remove selected-ids snapshot-ids))]
                                  (throw (ex-info "Snapshot policy names systems excluded from the fork"
                                                  {:type ::excluded-snapshot-systems
                                                   :systems (vec excluded)})))
            selected-reg (select-keys parent-reg selected-ids)
            selected-signal-ids (into #{} (map (comp :id val)) selected-reg)
            excluded-signal-ids (into #{}
                                      (keep (fn [[sid sig-ref]]
                                              (when-not (contains? selected-ids sid)
                                                (:id sig-ref))))
                                      parent-reg)
            ;; A registry-only filter is insufficient: a retained raw SignalRef
            ;; otherwise falls through the context overlay to the parent's mutable
            ;; system. Seat nil-valued child-local nodes for every excluded signal,
            ;; preserving the parent while making the retained capability inert.
            attenuated-nodes
            (into {}
                  (keep (fn [sig-id]
                          (when-let [pnode (rtp/get-state parent-ctx [:nodes sig-id])]
                            [sig-id (nodes/->signal-node nil nil nil false #{}
                                                         (inc (or (:generation pnode) 0)))])))
                  excluded-signal-ids)
           ;; translate :snapshots from SYSTEM-id keys (what callers know) to the
           ;; SIGNAL-id keys fork-context forks by.
            snaps  (when-let [s (:snapshots opts)]
                     (into {} (keep (fn [[sid snap]]
                                      (when-let [sr (get selected-reg sid)]
                                        [(:id sr) snap])))
                           s))
            state-updates (-> (or (:state-updates opts) {})
                              (assoc registry-key
                                     (backend/full-replacement selected-reg)
                                     :forkable-signals selected-signal-ids)
                              (update :nodes #(merge (or % {}) attenuated-nodes)))
            fopts  (cond-> (-> opts
                               (dissoc :systems :purpose :owner :rights)
                               (assoc :state-updates state-updates
                                      :forkable-signals selected-signal-ids))
                     snaps (assoc :snapshots snaps))
            child-ctx  (apply ctx/fork-context parent-ctx (mapcat identity fopts))
            fork-id    (:fork-id child-ctx)
            popts  (merge yc/default-opts opts)
            owner  (or (:owner opts) (:fork-id parent-ctx))]
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
                         (not= fork-id (ygg/current-branch cval)))
                (let [_        (await (ygg/branch! cval fork-id (ygg/current-branch cval) popts))
                      branched (await (ygg/checkout cval fork-id popts))]
                  (set-node-value! child-ctx sig-ref branched))))
            (recur (next ps))))
        ;; Capture the actual granted per-system fork shape, not merely the
        ;; requested policy. Versioned systems may degrade :following to :frozen.
        (let [systems
              (loop [ps (seq (shared-pairs child-ctx parent-ctx)) acc {}]
                (if ps
                  (let [[sid _ cval psys] (first ps)
                        csys (ys/effective-system cval)
                        pv (when (satisfies? ygg/Snapshotable psys)
                             (ygg/snapshot-id psys))
                        cv (when (satisfies? ygg/Snapshotable csys)
                             (ygg/snapshot-id csys))
                        parent-head (if (fn? pv) (await pv) pv)
                        child-head (if (fn? cv) (await cv) cv)
                        snapshot? (contains? snapshot-ids sid)
                        branch (when (satisfies? ygg/Branchable csys)
                                 (ygg/current-branch csys))
                        kind (cond snapshot? :snapshot
                                   (ovl/overlay? cval) :overlay
                                   (= fork-id branch) :branch
                                   (= cval psys) :shared
                                   :else :forked)
                        entry {:base-snapshot (cond snapshot? (get-in opts [:snapshots sid])
                                                    (ovl/overlay? cval) (ygg/base-ref cval)
                                                    :else parent-head)
                               :head child-head
                               :branch branch
                               :mode (cond (ovl/overlay? cval) (:mode cval)
                                           (= :shared kind) :shared
                                           :else :frozen)
                               :kind kind
                               :rights (if (= :shared kind)
                                         :shared
                                         (get-in opts [:rights sid] :write))}]
                    (recur (next ps) (assoc acc sid entry)))
                  acc))
              descriptor {:fork/id fork-id
                          :fork/parent (:fork-id parent-ctx)
                          :fork/purpose (or (:purpose opts) :unspecified)
                          :fork/owner owner
                          :fork/systems systems}
              token (random-uuid)
              authority (atom {:status :open :owner owner :token token})]
          ;; The child world observes this shared authority atom. It remains
          ;; mutable while OPEN, but partition-fork!'s atomic transition freezes
          ;; registry shape for every recursively subdivided capability.
          (rtp/swap-state! child-ctx [fork-authority-key] (constantly authority))
          (->ForkHandle child-ctx parent-ctx fork-id descriptor authority token))))))))

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

(defn- context-diff-scoped
  [child-ctx scope]
  (convey-context
   (async+sync
    (:sync? yc/default-opts)
    (async
     (when-let [parent-ctx (:parent-ctx child-ctx)]
      ;; accumulating loop (not `into`/`keep`) — `system-merge-base-diff` is awaited.
       (loop [ps (seq (scoped-shared-pairs child-ctx parent-ctx scope))
              acc {}]
         (if ps
           (let [[sid _ cval psys] (first ps)
                 fsys (ys/effective-system cval)
                 acc* (if (and (satisfies? ygg/Mergeable fsys)
                               (satisfies? ygg/Graphable fsys))
                        (assoc acc sid (await (system-merge-base-diff fsys psys)))
                        acc)]
             (recur (next ps) acc*))
           acc)))))))

(defn context-diff
  "Per-system delta of a forked context vs its parent — the unified diff a
   reviewer reads: {system-id -> typed yggdrasil delta (GitDiff / DatahikeDiff /
   DiffError)}. nil when the context has no parent. Non-Mergeable systems are
  omitted."
  [child-ctx]
  (context-diff-scoped child-ctx nil))

(defn- context-conflicts-scoped
  [child-ctx scope]
  (convey-context
   (async+sync
    (:sync? yc/default-opts)
    (async
     (when-let [parent-ctx (:parent-ctx child-ctx)]
      ;; accumulating loop (not `into`/`mapcat`) — durable calls are awaited.
       (loop [ps (seq (scoped-shared-pairs child-ctx parent-ctx scope))
              acc []]
         (if ps
           (let [[sid _ cval psys] (first ps)
                 fsys (ys/effective-system cval)
                 more (if (satisfies? ygg/Mergeable fsys)
                        (try
                          (let [ps1 (let [v (ygg/snapshot-id psys)]
                                      (if (fn? v) (await v) v))
                                fs1 (let [v (ygg/snapshot-id fsys)]
                                      (if (fn? v) (await v) v))
                                pres (ygg/conflicts psys ps1 fs1)
                                cs (if (fn? pres) (await pres) pres)]
                            (mapv #(assoc % :system sid) cs))
                          (catch #?(:clj Throwable :cljs :default) _ nil))
                        nil)]
             (recur (next ps) (into acc (or more []))))
           acc)))))))

(defn context-conflicts
  "Per-system conflicts of a forked context vs its parent, each tagged
   `:system`. nil when the context has no parent."
  [child-ctx]
  (context-conflicts-scoped child-ctx nil))

(declare handle-system-scope)

(defn fork-diff
  "Per-system delta restricted to the settlement authority of `fork-handle`.
   Original handles see the whole child world; partition handles see only their
   disjoint descriptor-named scope."
  [fork-handle]
  (convey-context
   (async+sync
    (:sync? yc/default-opts)
    (async
     (let [x (context-diff-scoped (:child-ctx fork-handle)
                                  (handle-system-scope fork-handle))]
       (if (fn? x) (await x) x))))))

(defn fork-conflicts
  "Conflict projection restricted to `fork-handle`'s settlement scope."
  [fork-handle]
  (convey-context
   (async+sync
    (:sync? yc/default-opts)
    (async
     (let [x (context-conflicts-scoped (:child-ctx fork-handle)
                                       (handle-system-scope fork-handle))]
       (if (fn? x) (await x) x))))))

;; =============================================================================
;; Merge / Discard (Parent-Controlled)
;; =============================================================================

(defn- managed-branch?
  "True only when this handle's creation descriptor names the branch currently
   held by `cval`. Prefixes are not authority: user-created fork-/snap- branches
   must never be settled accidentally."
  [fork-handle sid cval]
  (let [{:keys [kind branch]} (get-in (:descriptor fork-handle) [:fork/systems sid])]
    (and (contains? #{:branch :snapshot} kind)
         (= branch (ygg/current-branch cval)))))

(defn- handle-system-scope
  "nil means the original handle owns the whole evolving child world. A
   partitioned handle owns exactly the systems named in its descriptor."
  [fork-handle]
  (when (contains? (:descriptor fork-handle) :fork/partition-of)
    (set (keys (get-in fork-handle [:descriptor :fork/systems])))))

(defn- handle-shared-pairs [fork-handle]
  (scoped-shared-pairs (:child-ctx fork-handle)
                       (:parent-ctx fork-handle)
                       (handle-system-scope fork-handle)))

(defn- handle-child-only [fork-handle]
  ;; A partition's descriptor systems were all shared when the exhaustive split
  ;; was minted. If one later disappears from the parent, handle-shared-pairs
  ;; fails closed; it must never be reclassified as child-only.
  (if (handle-system-scope fork-handle)
    {}
    (child-only (:child-ctx fork-handle) (:parent-ctx fork-handle))))

(defn- merge-fork-context!
  "Merge a ForkHandle's per-system overlays into its parent.

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

   Internal substrate operation. Public callers must settle through
   `merge-fork!`, which owns the affine lifecycle and post-commit callback."
  [fork-handle opts]
  (let [child-ctx (:child-ctx fork-handle)]
    (convey-context
     (async+sync
      (:sync? (merge yc/default-opts opts))
      (async
       (when-let [parent-ctx (:parent-ctx child-ctx)]
         (let [pairs (handle-shared-pairs fork-handle)
               co (handle-child-only fork-handle)]
           ;; Carrying a newly registered child system changes the parent's
           ;; world shape. Reject before any substrate mutation when that parent
           ;; has already been partitioned/frozen.
           (when (seq co)
             (ensure-registry-mutable! parent-ctx))
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
           (when (or (seq pairs) (seq co))
             (mark-settlement-mutating! fork-handle :merge))
           (let [merged (loop [ps (seq pairs) acc []]
                          (if ps
                            (let [[sid sig-ref cval psys] (first ps)
                                  acc* (cond
                                       ;; OVERLAY fork (convergent :overlay opt + datahike/git): join back.
                                         (ovl/overlay? cval)
                                         (let [m (await (ygg/merge-down! cval opts))]
                                           (ensure-parent-signal-and-seat!
                                            parent-ctx sid sig-ref m)
                                           (ygg/discard! cval)
                                           (conj acc sid))

                                       ;; Managed BRANCH fork: `cval` is a real system on a private
                                       ;; `:fork-<uuid>` or `:snap-<uuid>` branch.
                                       ;; Check out the parent branch (loads its LIVE head for durable stores),
                                       ;; `merge!` the fork branch in, drop the fork branch. Await each (can't
                                       ;; thread-first through CPS on cljs); `mopts` threads `:sync?`.
                                         (and (satisfies? ygg/Branchable cval)
                                              (satisfies? ygg/Mergeable cval)
                                              (managed-branch? fork-handle sid cval))
                                         (let [mopts   (merge yc/default-opts opts)
                                               fbranch (ygg/current-branch cval)
                                               pbranch (ygg/current-branch psys)
                                               co      (await (ygg/checkout cval pbranch mopts))
                                               mg      (await (ygg/merge! co fbranch mopts))]
                                           (ensure-parent-signal-and-seat!
                                            parent-ctx sid sig-ref mg)
                                           (let [m (await (ygg/delete-branch! mg fbranch mopts))]
                                             (ensure-parent-signal-and-seat!
                                              parent-ctx sid sig-ref m))
                                           (conj acc sid))

                                         :else acc)]
                              (recur (next ps) acc*))
                            acc))]
            ;; 3. carry child-only systems into the parent registry + nodes.
             (when (seq co)
               (carry-child-only! parent-ctx child-ctx co))
             {:merged merged :child-only (vec (keys co))
              :parent-ctx parent-ctx :child-ctx child-ctx}))))))))

(defn- discard-fork-context!
  "Discard a ForkHandle's per-system overlays without merging — `discard!`
   each shared overlay (deleting git worktrees / fork branches). Fork-ONLY
   systems have no shared overlay; the `:on-discard` callback receives them so
   an external owner can clean up (delete the store, drop a deferred grant).

   Internal substrate operation. Public callers must settle through
   `discard-fork!`."
  [fork-handle opts]
  (let [child-ctx (:child-ctx fork-handle)]
    (convey-context
     (async+sync
      (:sync? (merge yc/default-opts opts))
      (async
       (when-let [parent-ctx (:parent-ctx child-ctx)]
         (let [pairs (handle-shared-pairs fork-handle)
               co (handle-child-only fork-handle)]
           (when (seq pairs)
             (mark-settlement-mutating! fork-handle :discard))
       ;; `discard!` on an overlay is a synchronous no-op (returns nil); `delete-branch!`
       ;; is async — await it. Loop (not doseq) so the await threads on cljs.
           (loop [ps (seq pairs)]
             (when ps
               (let [[sid _ cval _] (first ps)]
                 (cond
                   (ovl/overlay? cval) (ygg/discard! cval)
               ;; Managed branch fork: drop the private branch (its nodes GC later).
                   (and (satisfies? ygg/Branchable cval)
                        (managed-branch? fork-handle sid cval))
                   (await (ygg/delete-branch! cval (ygg/current-branch cval) (merge yc/default-opts opts)))))
               (recur (next ps))))
           {:child-only (vec (keys co))
            :child-only-systems (into {} (keep (fn [[sid sr]]
                                                 (when-let [s (ys/effective-system (node-value child-ctx sr))]
                                                   [sid s])))
                                      co)
            :child-ctx child-ctx})))))))

(defn merge-fork!
  "Merge an OPEN fork's overlays to its parent exactly once. Repeating the same
   successful operation returns its cached result; discard/transfer afterwards
   fails without touching the substrate. `:on-merge`, when supplied, runs once
   after terminal settlement; its failure is reported as `:callback-status
   :failed` and never reopens the already-mutated world."
  ([fork-handle] (merge-fork! fork-handle {}))
  ([fork-handle opts]
   (settle-fork! fork-handle :merge opts
                 #(merge-fork-context! fork-handle (dissoc opts :on-merge))
                 #(select-keys % [:merged :child-only])
                 (:on-merge opts))))

(defn discard-fork!
  "Discard an OPEN fork exactly once. Repeating the same successful operation is
   idempotent and returns the cached result. `:on-discard` has the same
   post-commit, single-execution semantics as `:on-merge`."
  ([fork-handle] (discard-fork! fork-handle {}))
  ([fork-handle opts]
   (settle-fork! fork-handle :discard opts
                 #(discard-fork-context! fork-handle (dissoc opts :on-discard))
                 (constantly nil)
                 (:on-discard opts))))

;; =============================================================================
;; Merge From Parent (Parent → Child sync)
;; =============================================================================

(defn- merge-fork-context-from-parent!
  "Merge the parent's current state INTO a child context (inverse of
   merge-fork!) — for long-lived agent forks that need to stay in sync.
   Per shared system, merge the parent's branch into the fork's writable system
   and repoint the fork's ygg-signal. Called from within / on the child context.

   Args:
     fork-handle - The open fork to update
     opts        - Optional merge opts {:strategy … :message …}

   Returns: nil"
  ([fork-handle] (merge-fork-context-from-parent! fork-handle {}))
  ([fork-handle opts]
   (let [child-ctx (:child-ctx fork-handle)]
     (convey-context
      (async+sync
       (:sync? (merge yc/default-opts opts))
       (async
        ;; Claim when the CPS expression executes, not when it is constructed.
        ;; The :advancing lease excludes transfer, partition, and settlement for
        ;; the full async checkout/merge interval.
        (claim-advance! fork-handle)
        (try
          (when-let [parent-ctx (:parent-ctx child-ctx)]
            (let [pairs (vec (filter (fn [[sid _ _ _]]
                                       (not= :shared (get-in (:descriptor fork-handle)
                                                             [:fork/systems sid :kind])))
                                     (handle-shared-pairs fork-handle)))]
              (when (seq pairs)
                ;; From this point a durable adapter may have changed even if a
                ;; later operation rejects; do not reopen authority on failure.
                (mark-advance-mutating! fork-handle))
              ;; Loop (not doseq) so checkout/merge await-thread on cljs.
              (loop [ps (seq pairs)]
                (when ps
                  (let [[_ sig-ref cval psys] (first ps)
                        fsys (ys/effective-system cval)]
                    (when (and (satisfies? ygg/Branchable fsys)
                               (satisfies? ygg/Mergeable fsys))
                      (let [cbranch (ygg/current-branch fsys)
                            pbranch (ygg/current-branch psys)
                            ;; Thread :sync?; otherwise the JVM async branch can
                            ;; accidentally seat a CPS continuation as a system.
                            mopts (merge yc/default-opts
                                         {:message (str "Merge from " (name pbranch))}
                                         opts)
                            co (await (ygg/checkout fsys cbranch mopts))
                            m (await (ygg/merge! co pbranch mopts))]
                        (if (ovl/overlay? cval)
                          (ovl/reseat-overlay! cval m)
                          (set-node-value! child-ctx sig-ref m)))))
                  (recur (next ps))))))
          (complete-advance! fork-handle)
          (catch #?(:clj Throwable :cljs :default) error
            (fail-advance! fork-handle error)
            (throw error)))))))))

(defn merge-fork-from-parent!
  "Merge the parent's current state into an OPEN fork. The ForkHandle is the
   authority for both settlement directions; raw child contexts cannot bypass it."
  ([fork-handle] (merge-fork-from-parent! fork-handle {}))
  ([fork-handle opts]
   (merge-fork-context-from-parent! fork-handle opts)))

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
