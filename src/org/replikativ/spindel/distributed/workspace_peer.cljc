(ns org.replikativ.spindel.distributed.workspace-peer
  "Reflect a yggdrasil composite *workspace* between peers: when the server
   forks/advances a room, a subscribing peer re-seats its `[:external-refs
   ::workspace]` to the same branch + head, snapshot-isolated.

   Layering (see doc/distributed-context-reflection.md):

     transport          (app owns)  konserve-sync per-system stores + registry,
                                     kabel.pubsub, signal_sync for the descriptor
       │ callbacks
       ▼
     workspace-peer     (this ns)   pure GATE + a small state machine that, when
                                     every target system's local head has reached
                                     its pinned head, re-seats the workspace.
       │ ec/swap-state!
       ▼
     ygg/system         (location-transparent — apps write the same code on both
                         sides; the sub-system they deref is the locally-synced,
                         branch-correct one)

   Two inputs drive the peer:

   1. **Checkout descriptor** (what the server wants the client at) — rides the
      `signal_sync` bridge:
        {:branch  <kw>
         :systems {system-id {:store-id .. :branch <kw> :head <token> :hlc ..}}}
      The descriptor is irreducible: the snapshot indices carry content +
      history + per-[system,branch] heads, but NOT which branch a room is
      *checked out* to, and a client needs a branch name to re-seat a writable
      conn. (composite.clj's `commit!` entry has no branch; `branch!` writes no
      entry; the branch lives in in-memory `current-branch-name`.)

   2. **Head updates** (what's actually synced locally) — each system store's
      konserve-sync `:on-key-update` for the branch-pointer key. Because the
      datahike/registry `:key-sort-fn` publishes content blocks before the
      mutable pointer, an `:on-key-update` for the branch key means \"that
      commit's blocks are fully local\" — the per-store fetch-gate. The app
      forwards it via `apply-head-update!`.

   The peer is **dependency-injected** so this namespace needs no konserve-sync,
   datahike, or yggdrasil require (the app already holds the peers + cfgs):
     :resolve-system-fn (fn [system-id branch] -> ygg-system)   ; branch-scoped
     :compose-fn        (fn [{system-id -> ygg-system}] -> workspace-value)
   On the JVM the app passes `#(ygc/composite (vals %) :branch B …)`; the seated
   value is whatever `ygg/system` resolves through (a CompositeSystem)."
  (:require [org.replikativ.spindel.engine.core :as ec]))

;; =============================================================================
;; Pure composite gate (the one genuinely-new coordination function)
;; =============================================================================

(defn merge-head-update
  "Fold a single store's freshly-synced branch head into head-state.
   head-state shape: {system-id {branch head-token}}."
  [head-state system-id branch head-token]
  (assoc-in head-state [system-id branch] head-token))

(defn gate
  "Pure composite fetch-gate. Given the checkout `descriptor` and the locally
   synced `head-state`, decide whether the workspace may be exposed at the
   target snapshot yet.

   Returns:
     {:ready?    bool                ; every target system reached its pinned head
      :pending   #{system-id …}      ; systems whose local head has NOT yet caught up
      :statuses  {system-id {:target t :local l :reached? bool}}}

   `:reached?` is head-token equality. Under single-writer with a per-commit
   descriptor that is the correct gate: the descriptor advances monotonically as
   commits land, and `:key-sort-fn` guarantees a branch-pointer head update only
   fires once that commit's blocks are present. A transient where the descriptor
   still names head C while the store already advanced to C' simply isn't
   `ready?` until the descriptor catches up to C' (which it does, per commit)."
  [descriptor head-state]
  (let [systems (:systems descriptor)
        statuses (reduce-kv
                  (fn [acc sid {:keys [branch head]}]
                    (let [local (get-in head-state [sid branch])]
                      (assoc acc sid {:target head
                                      :local local
                                      :reached? (and (some? local) (= local head))})))
                  {}
                  systems)
        pending (into #{}
                      (comp (remove (comp :reached? val)) (map key))
                      statuses)]
    {:ready? (and (seq systems) (empty? pending))
     :pending pending
     :statuses statuses}))

;; =============================================================================
;; Single-writer lease (the branch-owner field)
;; =============================================================================

(defn writable?
  "Single-writer lease check: true iff `self-id` holds the branch-owner lease
   named by the checkout `descriptor`'s `:owner`. A descriptor with no `:owner`
   is **read-only** for everyone (the safe default — fork to write, then claim).

   This is the single-head regime made explicit: at most one peer owns a branch,
   so its `transact!`s are unambiguous and merge is needed only at fold-to-parent.
   The owner is part of the same `signal_sync`'d control plane as the checkout, so
   ownership transfers (hand-off, takeover) ride the existing descriptor channel."
  [descriptor self-id]
  (and (some? self-id) (= self-id (:owner descriptor))))

(defn claim
  "Server/owner side: stamp `owner-id` as the branch-owner on a descriptor before
   publishing it. Returns the descriptor with `:owner` set."
  [descriptor owner-id]
  (assoc descriptor :owner owner-id))

;; =============================================================================
;; Peer state machine
;; =============================================================================

(def workspace-key ::workspace)

(defn make-workspace-peer
  "Create a workspace-peer bound to execution context `ctx`.

   opts:
     :ctx               the execution context to re-seat the workspace into (req)
     :resolve-system-fn (fn [system-id branch] -> ygg-system) (req) — build/look
                        up the locally-synced, branch-scoped sub-system.
     :compose-fn        (fn [{system-id -> ygg-system}] -> workspace-value)
                        — combine resolved systems into the value stored at
                        [:external-refs ::workspace]. Defaults to the systems map
                        (useful for tests); JVM apps pass a CompositeSystem builder.
     :on-reseat         (fn [workspace-value descriptor]) optional — fired after a
                        successful re-seat (e.g. to notify UI / log).

   Returns an atom holding the peer state; drive it with `set-descriptor!` and
   `apply-head-update!`."
  [{:keys [ctx resolve-system-fn compose-fn on-reseat]}]
  (assert ctx ":ctx is required")
  (assert resolve-system-fn ":resolve-system-fn is required")
  (atom {:ctx ctx
         :resolve-system-fn resolve-system-fn
         :compose-fn (or compose-fn identity)
         :on-reseat on-reseat
         :descriptor nil
         :head-state {}
         :seated nil}))      ; the descriptor currently reflected in the workspace

(defn- reseat!
  "Build the workspace value for `descriptor` and swap it into the context.
   Returns the seated workspace value."
  [{:keys [ctx resolve-system-fn compose-fn on-reseat]} descriptor]
  (let [systems (reduce-kv
                 (fn [acc sid {:keys [branch]}]
                   (assoc acc sid (resolve-system-fn sid branch)))
                 {}
                 (:systems descriptor))
        ws (compose-fn systems)]
    (binding [ec/*execution-context* ctx]
      (ec/swap-state! [:external-refs workspace-key] (constantly ws)))
    (when on-reseat (on-reseat ws descriptor))
    ws))

(defn- maybe-reseat!
  "Recompute the gate from current peer state; if ready and the target differs
   from what's already seated, re-seat the workspace. Returns the gate result
   (with :reseated? added)."
  [peer]
  (let [{:keys [descriptor head-state seated]} @peer
        g (gate descriptor head-state)]
    (if (and (:ready? g) (not= descriptor seated))
      (do (reseat! @peer descriptor)
          (swap! peer assoc :seated descriptor)
          (assoc g :reseated? true))
      (assoc g :reseated? false))))

(defn set-descriptor!
  "Set the target checkout descriptor (from the signal_sync'd control plane).
   Triggers a gate re-evaluation + re-seat if ready."
  [peer descriptor]
  (swap! peer assoc :descriptor descriptor)
  (maybe-reseat! peer))

(defn apply-head-update!
  "Record that `system-id`'s `branch` is now locally synced to `head-token`
   (from a konserve-sync :on-key-update on the branch-pointer key). Triggers a
   gate re-evaluation + re-seat if ready."
  [peer system-id branch head-token]
  (swap! peer update :head-state merge-head-update system-id branch head-token)
  (maybe-reseat! peer))

(defn current-workspace
  "Read the workspace value currently seated in the peer's context (or nil)."
  [peer]
  (binding [ec/*execution-context* (:ctx @peer)]
    (ec/get-state [:external-refs workspace-key])))

(defn gate-status
  "Current gate result without mutating (for diagnostics / UI)."
  [peer]
  (let [{:keys [descriptor head-state]} @peer]
    (gate descriptor head-state)))

(defn peer-writable?
  "Does `self-id` hold the single-writer lease for the peer's current checkout?"
  [peer self-id]
  (writable? (:descriptor @peer) self-id))
