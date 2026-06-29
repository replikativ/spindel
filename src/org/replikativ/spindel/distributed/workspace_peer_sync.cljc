(ns org.replikativ.spindel.distributed.workspace-peer-sync
  "Live wiring for the workspace-peer: connect a `konserve-sync` per-system
   store + a `signal_sync`'d checkout descriptor to a `workspace-peer` so an
   app gets location-transparent forks for free.

   Provided-dep namespace: it `require`s konserve-sync, which is only a spindel
   :test dep — exactly the pattern konserve-sync itself uses for its datahike
   walker (a src/ ns requiring datahike that is only a :test dep). Spindel's
   runtime :deps stay lean; downstream apps (dvergr, simmis) that use this ns
   already carry konserve-sync. The pure gate (`workspace-peer`) has no such
   dependency.

   Layering recap:
     konserve-sync store  --:on-key-update-->  apply-head-update!  ┐
     signal_sync desc     --on-update------->  set-descriptor!     ┴-> gate -> re-seat

   The re-seat is pure yggdrasil — `checkout-resolver` materializes a
   branch-scoped sub-system via `ygg/checkout` (which uses `d/connect :branch`,
   the client-safe path proven by the datahike wire test), and
   `composite-composer` folds them into a CompositeSystem. So apps pass only
   their {system-id -> locally-synced ygg-system} + the peer/topics; no datahike
   glue.

   CROSS-PLATFORM: this ns is `.cljc` and compiles on BOTH JVM and cljs — the
   web client uses the same code (no divergence). yggdrasil is fully cljc, so the
   gate/resolve/compose + fork/merge orchestration are platform-neutral. The ONLY
   reader-conditional is at the konserve-sync transport leaves: on the JVM they
   resolve lazily via `requiring-resolve` (keeps konserve-sync a provided/:test
   dep, runtime :deps stay lean); on cljs there is no `requiring-resolve`, so a
   web client INJECTS its transport (`:subscribe-fn` / `:register-fn`) — it already
   carries konserve-sync. The pure gate (`workspace-peer`) has no such dependency."
  (:require [org.replikativ.spindel.distributed.workspace-peer :as wp]
            [org.replikativ.spindel.distributed.signal-sync :as ssync]
            [org.replikativ.spindel.ygg-signal :as ys]
            [yggdrasil.protocols :as ygg]
            [yggdrasil.composite :as ygc]))

;; konserve-sync transport batteries. The default subscribe/register/sync-opts are a
;; JVM convenience resolved LAZILY via `requiring-resolve` (konserve-sync stays a
;; provided/:test dep; runtime :deps stay lean). cljs has no `requiring-resolve`, so the
;; web client INJECTS the transport (`:subscribe-fn` etc.) — these stubs only throw if a
;; cljs caller relied on the JVM default. ONE code path; the platform split is just here.
(defn- ks-subscribe-store! [& args]
  #?(:clj  (apply (requiring-resolve 'konserve-sync.transport.kabel-pubsub/subscribe-store!) args)
     :cljs (throw (ex-info "On cljs, inject :subscribe-fn (konserve-sync transport is not auto-resolved)" {:args args}))))
(defn- ks-register-store! [& args]
  #?(:clj  (apply (requiring-resolve 'konserve-sync.transport.kabel-pubsub/register-store!) args)
     :cljs (throw (ex-info "On cljs, inject :register-fn (konserve-sync transport is not auto-resolved)" {:args args}))))
(defn- kcrdt-sync-opts []
  #?(:clj  ((requiring-resolve 'konserve-sync.walkers.crdt/crdt-sync-opts))
     :cljs (throw (ex-info "On cljs, pass crdt sync-opts explicitly (konserve-sync is not auto-resolved)" {}))))

;; =============================================================================
;; yggdrasil-based resolve / compose defaults
;; =============================================================================

(defn- as-branch
  "Coerce a branch designator to the KEYWORD yggdrasil's Branchable/checkout
   protocol expects. The datahike adapter does `(assoc cfg :branch B)` with no
   coercion, and datahike's config spec REJECTS a string `:branch` — so passing
   `(name branch)` (a string) breaks a real checkout. Idempotent on keywords."
  [b]
  (if (keyword? b) b (keyword b)))

(defn checkout-resolver
  "Build a :resolve-system-fn for `make-workspace-peer` from a `lookup-fn`
   (system-id -> the locally-synced base ygg-system). Returns the
   branch-scoped sub-system via `ygg/checkout` — which connects with
   `(assoc cfg :branch B)` (client-safe; NOT branch-as-db). `branch` is coerced
   to a keyword (datahike's config spec requires it)."
  [lookup-fn]
  (fn [system-id branch]
    (ygg/checkout (lookup-fn system-id) (as-branch branch))))

(defn composite-composer
  "Build a :compose-fn that folds the resolved sub-systems into a
   CompositeSystem on `branch` — the value `ygg/system` resolves through."
  [branch]
  (fn [systems-map]
    (ygc/composite (vals systems-map) {:branch branch :name "spindel-workspace"})))

;; =============================================================================
;; konserve-sync :on-key-update -> head update
;; =============================================================================

(defn head-update-handler
  "Build an `:on-key-update (fn [key value op])` that forwards branch-pointer
   updates to `peer` for `system-id`.

   - `branch-key?`   : which keys are branch HEAD pointers. Default `keyword?`
                       (datahike branch heads are keyword keys: :db, :fork, …),
                       excluding the `:branches` set key itself.
   - `head-token-fn` : extract a comparable head token from the synced value.
                       Default `identity`. For datahike pass an extractor of the
                       commit-id so the token matches the server's descriptor
                       head (whole-stored-db equality is brittle across the
                       fressian round-trip; a commit-id is stable)."
  [peer system-id & {:keys [branch-key? head-token-fn]
                     :or {branch-key? keyword? head-token-fn identity}}]
  (fn [k v _op]
    (when (and (branch-key? k) (not= k :branches))
      (wp/apply-head-update! peer system-id k (head-token-fn v)))))

;; =============================================================================
;; Attach transport to the peer
;; =============================================================================

(defn attach-store!
  "Subscribe a system's konserve store on `client-peer` and forward its
   branch-head updates into `peer`. `:sync-opts` is the konserve-sync walker
   bundle (`:walk-fn` + `:key-sort-fn`) — REQUIRED for any multi-node store (a
   datahike store or a PSS-backed durable CRDT): without it the default walker
   ships only the root and the replica never reconstructs. `:on-complete`,
   `:head-token-fn`, `:branch-key?` are honored; `:subscribe-fn` overrides
   konserve-sync's `subscribe-store!` (for tests). Returns the subscribe channel."
  [peer client-peer system-id topic local-store
   & {:keys [subscribe-fn head-token-fn branch-key? on-complete sync-opts]}]
  (let [subscribe (or subscribe-fn ks-subscribe-store!)
        on-key-update (head-update-handler
                       peer system-id
                       :head-token-fn (or head-token-fn identity)
                       :branch-key? (or branch-key? keyword?))]
    (subscribe client-peer topic local-store
               (cond-> (merge sync-opts {:on-key-update on-key-update})
                 on-complete (assoc :on-complete on-complete)))))

(defn attach-descriptor!
  "Subscribe the `signal_sync`'d checkout descriptor on `client-peer` and
   forward each new descriptor into `peer` via `set-descriptor!`. Returns the
   local descriptor atom/signal (also kept in sync)."
  [peer client-peer topic & {:keys [initial-value]}]
  (ssync/subscribe-signal! client-peer topic
                           :initial-value initial-value
                           :on-update (fn [desc] (wp/set-descriptor! peer desc))))

(defn sync-system!
  "Wire a CONVERGENT system BIDIRECTIONALLY over `topic` (the ygg-signal δ path):
   derive its sync hooks from its convergent protocols (`ys/sync-opts` — PConvergent
   → `merge-fn`, PDeltaApply → `apply-delta-fn`/`delta-fn`/`clear-delta-fn`) and
   `sync-signal!` the system's signal. Both peers' replicas then converge live (CRDT
   join) — the complement to `attach-store!`'s one-way isolated store follow. `owner?`
   makes this peer the topic relay hub (exactly one per topic). `state-fn` projects
   the value to a serializable connect-handshake snapshot (a non-serializable CRDT
   value ships its plain-data projection, e.g. `g/elements`). For NON-convergent
   (durable datahike) systems there is no δ to sync — use the store path instead."
  [client-peer topic ygg-signal & {:keys [owner? sync? state-fn]}]
  ;; deref to the system VALUE to derive its convergent hooks: an ygg-signal is
  ;; `deltaable? false` so `@` returns the raw system, and a plain atom holding a
  ;; convergent value derefs to it too — so `sync-system!` works for both.
  (let [system @ygg-signal
        opts   (cond-> (ys/sync-opts system :sync? sync?)
                 state-fn (assoc :state-fn state-fn))]
    (apply ssync/sync-signal! client-peer topic ygg-signal
           :owner? owner? (mapcat identity opts))))

(defn wire-topology!
  "Subscriber-side replay of a checkout/topology `descriptor`: wire `peer` into the
   same sync mesh the descriptor describes. Each system's `:role` (default
   `:subscriber`) selects the wiring:

     :subscriber    — one-way konserve-sync store FOLLOW (`attach-store!`): fetch the
                      system's content + branch-head updates (feeds the fetch-gate).
                      The right mode for DURABLE (datahike) systems and isolated forks.
     :bidirectional — convergent live SYNC (`sync-system!` over the ygg-signal δ
                      path): both replicas converge via CRDT join. For CONVERGENT
                      systems (G-Set, OR-Map, CDVCS) that should stay co-synced.

   When the descriptor carries a `:descriptor-topic`, also subscribe the signal_sync'd
   descriptor so the peer follows a remote checkout. The descriptor IS the topology,
   so wiring is one call.

   Runtime objects are INJECTED (not part of the shippable data):
     client-peer   - the kabel peer to subscribe/sync on
     store-lookup  - (fn [system-id] -> local konserve store)   [:subscriber systems]
     :signal-lookup - (fn [system-id] -> ygg-signal SignalRef)  [:bidirectional systems]
   Extra opts: `:head-token-fn`/`:branch-key?`/`:subscribe-fn` → `attach-store!`;
   `:sync-opts-lookup` (fn [sid] -> konserve-sync walker bundle) supplies each
   `:subscriber` store's `:walk-fn`/`:key-sort-fn` (required for multi-node
   datahike/PSS stores); `:sync?` → `sync-system!`; `:sync-fn` overrides the
   bidirectional wiring (tests).
   Returns {:stores {sid ch} :synced {sid ch} :descriptor desc-atom|nil}."
  [peer client-peer descriptor store-lookup
   & {:keys [head-token-fn branch-key? subscribe-fn signal-lookup sync? sync-fn
             sync-opts-lookup]}]
  (let [sync-system (or sync-fn
                        (fn [sid topic owner?]
                          (sync-system! client-peer topic (signal-lookup sid)
                                        :owner? owner? :sync? sync?)))
        {:keys [stores synced]}
        (reduce-kv
         (fn [acc sid {:keys [topic role owner?]}]
           (case (or role :subscriber)
             :bidirectional
             (update acc :synced assoc sid (sync-system sid topic owner?))
             ;; :subscriber (default): one-way konserve-sync store follow
             (if topic
               (update acc :stores assoc sid
                       (attach-store! peer client-peer sid topic (store-lookup sid)
                                      :head-token-fn head-token-fn
                                      :branch-key? branch-key?
                                      :subscribe-fn subscribe-fn
                                      :sync-opts (when sync-opts-lookup (sync-opts-lookup sid))))
               acc)))
         {:stores {} :synced {}}
         (:systems descriptor))
        desc (when-let [dt (:descriptor-topic descriptor)]
               (attach-descriptor! peer client-peer dt :initial-value descriptor))]
    {:stores stores :synced synced :descriptor desc}))

;; =============================================================================
;; Cross-system fork: branch a followed remote checkout locally
;; =============================================================================

(defn fork-remote!
  "Fork the currently-followed remote checkout LOCALLY into an isolated,
   single-writer branch. PRECONDITION: `peer` already follows the parent (its
   content is synced locally — see `wire-topology!` / `attach-store!`), so the
   fork reuses that content by structural sharing — `branch!` writes only a new
   branch pointer at the parent head, NO block transfer (the O(1) distributed
   fork).

   Steps: derive the fork descriptor (`wp/fork-descriptor` — re-points each
   system to `fork-branch`, claims `owner-id`, anchors `:fork-of` to the parent
   heads); create `fork-branch` on each local system; mark its head locally
   present (a local branch needs no konserve-sync round-trip); seat the
   descriptor so the peer re-seats onto the writable fork. Merge back to the
   parent later via `merge-fork-remote!` (the `:fork-of` LCA).

   Isolated single-writer BY DESIGN — no continuous sync to origin (that
   contradicts single-writer-per-branch); a bidirectionally-converging fork is a
   future `:role` opt. This does NOT call `wire-topology!`: the fork is local and
   isolated; `wire-topology!` is for FOLLOWING a remote checkout, the complement
   to forking one.

   DI: `system-lookup` (system-id -> local ygg-system) for `branch!`; `branch-fn`
   overrides `ygg/branch!` (tests / functional adapters). Returns the fork
   descriptor.

   NB: assumes STATEFUL adapters (datahike) where `branch!` side-effects the
   shared backend so a later `checkout fork-branch` finds it. For a functional
   adapter pass a `branch-fn` that persists the new branch where `system-lookup`
   will surface it."
  [peer descriptor fork-branch owner-id system-lookup & {:keys [branch-fn]}]
  (let [fork-desc (wp/fork-descriptor descriptor fork-branch owner-id)
        branch!   (or branch-fn (fn [sys b] (ygg/branch! sys b)))]
    (wp/set-descriptor! peer fork-desc)
    (doseq [[sid s] (:systems descriptor)]
      (branch! (system-lookup sid) fork-branch)
      ;; a locally-created branch's head is present immediately — feed the gate
      ;; the parent head it now points at (fork-descriptor kept :head at parent)
      (wp/apply-head-update! peer sid fork-branch (:head s)))
    fork-desc))

(defn merge-fork-remote!
  "Fold a fork created by `fork-remote!` back into its parent branch — the
   lifecycle counterpart. For each system in `fork-desc`, check out the PARENT
   branch and `ygg/merge!` the FORK BRANCH into it. Note yggdrasil's merge
   contract: `merge!`'s source is a branch KEYWORD (or snapshot id), NOT a system
   value — so the fork branch is merged by NAME (the datahike adapter does
   `(-> parent (checkout parent-branch) (merge! fork-branch))`). It is identity-keyed
   3-way against the common ancestor (the `:fork-of` head is that LCA).

   By default it is FAIL-SAFE: unless `:force`/`:strategy` is given, it first
   collects per-system `ygg/conflicts` between the parent + fork snapshot-ids; if
   any system conflicts (or a detector throws — counted as indeterminate) it aborts
   WITHOUT merging and returns `{:merged {} :conflicts {sid [...]}}`. Mirrors
   `yggdrasil.cljc/merge-to-parent!` for the branch (rather than overlay) case.

   DI: `system-lookup` (system-id -> local base ygg-system); `checkout-fn`
   (sys branch -> branch-scoped system, default `ygg/checkout`); `snapshot-id-fn`
   (sys -> snapshot id, default `ygg/snapshot-id`); `merge-fn`
   (parent-sys fork-branch opts -> merged-sys, default `ygg/merge!`); `conflicts-fn`
   (parent-sys parent-snap fork-snap -> seq, default `ygg/conflicts`). `opts`:
   `:strategy`/`:force`/`:message` pass through to the merge.

   Returns {:merged {sid merged-system} :conflicts {sid [conflict…]}}. On success
   the parent branch carries the merged head — advance/publish it via the existing
   descriptor channel (the owner re-exports the parent checkout); extract a head
   token with `ygg/snapshot-id`."
  [fork-desc system-lookup & {:keys [checkout-fn snapshot-id-fn merge-fn conflicts-fn opts]}]
  (let [parent-branch (get-in fork-desc [:fork-of :branch])
        fork-branch   (:branch fork-desc)
        checkout      (or checkout-fn (fn [sys b] (ygg/checkout sys (as-branch b))))
        snap-id       (or snapshot-id-fn (fn [sys] (ygg/snapshot-id sys)))
        merge!        (or merge-fn (fn [psys src o] (ygg/merge! psys src o)))
        conflicts     (or conflicts-fn (fn [psys a b] (ygg/conflicts psys a b)))
        sides         (reduce-kv
                       (fn [acc sid _]
                         (let [base (system-lookup sid)]
                           (assoc acc sid {:parent (checkout base parent-branch)
                                           :fork   (checkout base fork-branch)})))
                       {}
                       (:systems fork-desc))
        ;; FAIL-SAFE conflict pre-check (skipped under :strategy/:force)
        confs (when-not (or (:strategy opts) (:force opts))
                (reduce-kv
                 (fn [acc sid {:keys [parent fork]}]
                   (let [cs (try (seq (conflicts parent (snap-id parent) (snap-id fork)))
                                 (catch #?(:clj Throwable :cljs :default) e
                                   [{:system sid :indeterminate? true :error (ex-message e)}]))]
                     (cond-> acc cs (assoc sid (vec cs)))))
                 {}
                 sides))]
    (if (seq confs)
      {:merged {} :conflicts confs}
      (reduce-kv
       ;; merge the fork BRANCH (by name) into the checked-out parent system
       (fn [acc sid {:keys [parent]}]
         (assoc-in acc [:merged sid] (merge! parent fork-branch (or opts {}))))
       {:merged {} :conflicts {}}
       sides))))

;; =============================================================================
;; Server-side: publish the checkout descriptor
;; =============================================================================

(defn export-descriptor!
  "Server side: export a checkout-descriptor `signal` (a spindel signal/atom
   holding {:branch, :systems {id {:branch :head ..}} [:owner peer-id]}) on
   `server-peer` under `topic`, so subscribers re-seat when the room
   forks/advances. Thin wrapper over signal_sync `export-signal!`."
  [server-peer topic signal]
  (ssync/export-signal! server-peer topic signal))

;; =============================================================================
;; Registry-as-synced-store (durable control plane: history / as-of)
;; =============================================================================

(defn register-registry!
  "Server side: register a yggdrasil registry's konserve store (`registry-kv-store`,
   i.e. `(:kv-store registry)`) for remote access under `topic`. The registry is a
   durable conflict-free system (a content-addressed 2P-Set), so it syncs through
   the generic crdt walker + the keyword-last fetch-gate. Subscribers replicate
   the whole snapshot index for history/as-of and project live = adds − removals
   with `regw/read-registry-entries`."
  [server-peer topic registry-kv-store]
  (ks-register-store! server-peer topic registry-kv-store (kcrdt-sync-opts)))

(defn subscribe-registry!
  "Client side: replicate a registry store into `local-store`. `on-roots` fires
   with `local-store` whenever `:crdt/roots` updates — i.e. a fully-synced
   registry view is local (the keyword-last gate guarantees the trees precede the
   pointer). Read it with `konserve-sync.walkers.yggdrasil-registry/read-registry-entries`
   / `latest-by-system-branch`. `:subscribe-fn` overrides konserve-sync (tests)."
  [client-peer topic local-store & {:keys [on-roots on-complete subscribe-fn]}]
  (let [subscribe (or subscribe-fn ks-subscribe-store!)]
    (subscribe client-peer topic local-store
               {:on-key-update (fn [k _v _op]
                                 (when (and on-roots (= k :crdt/roots))
                                   (on-roots local-store)))
                :on-complete on-complete})))
