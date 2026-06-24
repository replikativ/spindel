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

   Layering recap (doc/distributed-context-reflection.md):
     konserve-sync store  --:on-key-update-->  apply-head-update!  ┐
     signal_sync desc     --on-update------->  set-descriptor!     ┴-> gate -> re-seat

   The re-seat is pure yggdrasil — `checkout-resolver` materializes a
   branch-scoped sub-system via `ygg/checkout` (which uses `d/connect :branch`,
   the client-safe path proven by the datahike wire test), and
   `composite-composer` folds them into a CompositeSystem. So apps pass only
   their {system-id -> locally-synced ygg-system} + the peer/topics; no datahike
   glue."
  (:require [org.replikativ.spindel.distributed.workspace-peer :as wp]
            [org.replikativ.spindel.distributed.signal-sync :as ssync]
            #?@(:clj [[yggdrasil.protocols :as ygg]
                      [yggdrasil.composite :as ygc]])))

;; konserve-sync is a PROVIDED/optional dep: only on the classpath of apps that use this
;; wiring (dvergr, simmis), NOT in spindel's runtime :deps. Resolve its fns LAZILY via
;; `requiring-resolve` so this ns loads/AOT-compiles against runtime :deps alone. (JVM
;; server-transport wiring; a proper cljc/cljs split of this ns is a separate follow-up.)
#?(:clj
   (do
     (defn- ks-subscribe-store! [& args]
       (apply (requiring-resolve 'konserve-sync.transport.kabel-pubsub/subscribe-store!) args))
     (defn- ks-register-store! [& args]
       (apply (requiring-resolve 'konserve-sync.transport.kabel-pubsub/register-store!) args))
     (defn- kcrdt-sync-opts []
       ((requiring-resolve 'konserve-sync.walkers.crdt/crdt-sync-opts)))))

;; =============================================================================
;; yggdrasil-based resolve / compose defaults
;; =============================================================================

#?(:clj
   (defn checkout-resolver
     "Build a :resolve-system-fn for `make-workspace-peer` from a `lookup-fn`
      (system-id -> the locally-synced base ygg-system). Returns the
      branch-scoped sub-system via `ygg/checkout` — which connects with
      `(assoc cfg :branch B)` (client-safe; NOT branch-as-db)."
     [lookup-fn]
     (fn [system-id branch]
       (ygg/checkout (lookup-fn system-id) (name branch)))))

#?(:clj
   (defn composite-composer
     "Build a :compose-fn that folds the resolved sub-systems into a
      CompositeSystem on `branch` — the value `ygg/system` resolves through."
     [branch]
     (fn [systems-map]
       (ygc/composite (vals systems-map) {:branch branch :name "spindel-workspace"}))))

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
   branch-head updates into `peer`. Extra opts (e.g. :on-complete,
   :head-token-fn) are honored; `:subscribe-fn` overrides konserve-sync's
   `subscribe-store!` (for tests). Returns the subscribe channel."
  [peer client-peer system-id topic local-store
   & {:keys [subscribe-fn head-token-fn branch-key? on-complete]}]
  (let [subscribe (or subscribe-fn ks-subscribe-store!)
        on-key-update (head-update-handler
                       peer system-id
                       :head-token-fn (or head-token-fn identity)
                       :branch-key? (or branch-key? keyword?))]
    (subscribe client-peer topic local-store
               (cond-> {:on-key-update on-key-update}
                 on-complete (assoc :on-complete on-complete)))))

(defn attach-descriptor!
  "Subscribe the `signal_sync`'d checkout descriptor on `client-peer` and
   forward each new descriptor into `peer` via `set-descriptor!`. Returns the
   local descriptor atom/signal (also kept in sync)."
  [peer client-peer topic & {:keys [initial-value]}]
  (ssync/subscribe-signal! client-peer topic
                           :initial-value initial-value
                           :on-update (fn [desc] (wp/set-descriptor! peer desc))))

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
