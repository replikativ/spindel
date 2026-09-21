(ns org.replikativ.spindel.engine.component
  "Non-reactive, context-selected components of an execution world.

  Signals represent values whose changes participate in the FRP graph. A world
  component instead represents ambient runtime state—an interpreter heap, a
  capability table, or another process-local resource. `ComponentRef` is stable
  across forks; resolving it through a bound ExecutionContext selects that
  world's realization.

  Registration is fail-closed: a value must explicitly implement
  `PWorldComponent`, or be wrapped with `forkable`, `shared` or `pinned`. Component forking
  must be rollback-free and process-local. Effectful resources such as database
  branches and worktrees use Yggdrasil ForkHandles, where acquisition can be
  settled."
  (:refer-clojure :exclude [resolve])
  (:require [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp]))

(defrecord ComponentRef [id])

(defprotocol PWorldComponent
  (realization [component]
    "Return the value selected for programs running in this world."))

(defrecord ForkableComponent [value fork-fn]
  PWorldComponent
  (realization [_] value)

  rtp/PForkable
  (fork-value [_ fork-id directive]
    (->ForkableComponent (fork-fn value fork-id directive) fork-fn)))

(defrecord SharedComponent [value]
  PWorldComponent
  (realization [_] value)

  rtp/PForkable
  (fork-value [this _fork-id _directive] this))

(defrecord PinnedComponent [store version read]
  PWorldComponent
  (realization [_] (read store version))

  rtp/PForkable
  (fork-value [this _fork-id _directive] this))

(defn forkable
  "Declare how a rollback-free process-local value is realized in a fork.

  `fork-fn` must not acquire durable resources requiring explicit cleanup."
  [value fork-fn]
  (->ForkableComponent value fork-fn))

(defn shared
  "Explicitly declare that `value` may be shared by reference across worlds."
  [value]
  (->SharedComponent value))

(defn pinned
  "Declare a VERSIONED value that worlds share by reference but read at the
  version they pinned: `(read store version)` is its realization. A fork reads
  what its source read, whatever the store has become since; a world moves on
  with `repin!`. For values that are too large to fork and must be common to
  every world of a search, such as the parameters a population of rollouts
  samples from while a trainer produces the next version. `version` is
  portable data, so it can be recorded with whatever was computed under it
  (`pinned-version`)."
  [store version read]
  (->PinnedComponent store version read))

(defn component-ref?
  [x]
  (instance? ComponentRef x))

(defn register!
  "Register `value` in the bound ExecutionContext and return its stable ref.

  `id` is optional and useful when an embedding needs deterministic addressing.
  Registration updates the component map and fork index atomically."
  ([value]
   (register! (random-uuid) value))
  ([id value]
   (when-not (satisfies? PWorldComponent value)
     (throw (ex-info
             "World component requires an explicit fork or sharing policy"
             {:type ::missing-fork-policy
              :component/id id
              :hint "Implement PWorldComponent and PForkable, or use component/forkable, component/shared or component/pinned."})))
   (let [ref (->ComponentRef id)]
     (ec/swap-state!
      []
      (fn [state]
        (when (contains? (or (:world/components state) {}) id)
          (throw (ex-info "World component id is already registered"
                          {:type ::duplicate-component
                           :component/id id})))
        (-> state
            (assoc-in [:world/components id] value)
            (update :world/forkable-components (fnil conj #{}) id))))
     ref)))

(defn unregister!
  "Remove a component reference from the bound world.

   Idempotent and world-local: unregistering a component in a child hides that
   realization without removing its parent's. Existing descendants that
   already materialized the component retain their own realization."
  [ref]
  (let [id (:id ref)]
    (ec/swap-state!
     []
     (fn [state]
       (-> state
           (update :world/components #(dissoc (or % {}) id))
           (update :world/forkable-components #(disj (or % #{}) id))))))
  nil)

(defn resolve-in
  "Resolve `ref` in `ctx`, returning its fork-local realization."
  [ctx ref]
  (let [id (:id ref)
        components (ec/get-state-in ctx [:world/components])]
    (if (contains? components id)
      (realization (get components id))
      (throw (ex-info "World component is not available in this context"
                      {:type ::missing-component
                       :component/id id
                       :fork-id (:fork-id ctx)})))))

(defn resolve
  "Resolve `ref` through the currently bound ExecutionContext."
  [ref]
  (resolve-in (ec/current-execution-context) ref))

(defn registered
  "Return the bound world's `{component-id value}` map. Intended for inspection."
  []
  (update-vals (or (ec/get-state [:world/components]) {}) realization))

(defn pinned?
  "Whether `component` (a registered value, not a ref) is a pinned one."
  [component]
  (instance? PinnedComponent component))

(defn pinned-version
  "The version `ref` is pinned at in `ctx` (default: the bound world), or nil
  when it is not a pinned component."
  ([ref] (pinned-version (ec/current-execution-context) ref))
  ([ctx ref]
   (let [component (get (ec/get-state-in ctx [:world/components]) (:id ref))]
     (when (instance? PinnedComponent component)
       (:version component)))))

(defn repin!
  "Move the bound world's pin of `ref` to `version`. World-local: forks taken
  before keep the version they had."
  [ref version]
  (let [id (:id ref)]
    (ec/swap-state!
     [:world/components id]
     (fn [component]
       (when-not (instance? PinnedComponent component)
         (throw (ex-info "Not a pinned world component"
                         {:type ::not-pinned :component/id id})))
       (assoc component :version version))))
  nil)
