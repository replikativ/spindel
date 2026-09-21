(ns org.replikativ.spindel.savepoint.portable
  "Tier 2: a savepoint as data.

  A continuation cannot leave the process. A savepoint that names a function
  to continue with can:

    (savepoint :conversation/turn m {:resume `after-turn :args [k]
                                     :state [[:conversation]]})

  `persist` turns such a savepoint into plain data: the named function and its
  arguments, the declared paths of world state, the world's seed, the snapshot
  id of every registered Yggdrasil system and the version of every pinned
  component. `hydrate!` forks a host world pinned at those snapshots, writes
  the state, and runs `(apply f (conj args value))` there, where `value` is
  what the savepoint is resumed with. Running a persisted savepoint and
  invoking a remote function are the same operation.

  Only declared state travels. The engine's own state (nodes, continuations,
  subscriptions) is not the computation's state: the named function starts a
  new computation, and what it needs from the old one it declares.

  Law: for a portable `sp`, `(hydrate! session (persist sp) v)` is
  observationally `(resume (fork sp) v)`, up to effects outside the world. It
  is a requirement on the program: the named function must do what the
  continuation does."
  (:require [org.replikativ.spindel.effects.savepoint :as sp]
            [org.replikativ.spindel.engine.component :as component]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.hash :as h]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.world.scope :as world-scope]
            [org.replikativ.spindel.yggdrasil :as ygg]
            [yggdrasil.protocols :as yp]))

(defn- invoke!
  "Call `make-operation` and deliver its value-or-CPS result. It is a thunk so
  that an authority which throws rejects, like one which rejects."
  [make-operation resolve reject]
  (try
    (let [operation (make-operation)]
      (if (fn? operation)
        (operation resolve reject)
        (resolve operation)))
    (catch #?(:clj Throwable :cljs :default) error
      (reject error))))

(defn- snapshot-ids
  "{system-id snapshot-id} of the systems registered in `world`."
  [world]
  (binding [ec/*execution-context* world]
    (into {}
          (map (fn [[system-id system]]
                 (let [id (yp/snapshot-id system)]
                   (when (fn? id)
                     (throw (ex-info "persist needs synchronous snapshot ids"
                                     {:type ::async-snapshot-id :system system-id})))
                   [system-id id])))
          (ygg/registered-systems))))

(defn- pinned-versions [world]
  (into {}
        (keep (fn [[id c]]
                (when (component/pinned? c) [id (:version c)])))
        (rtp/get-state world [:world/components])))

(defn persist
  "The portable form of `sp`: plain data, with `:savepoint/id` its content
  hash (a prefix identity that is the same across runs and machines). Throws
  when `sp` is not pending or names no `:resume`.

  With a resource authority on the session, what is left in the world's
  wallet moves into an escrow named by that id, so the authority cannot be
  spent both here and wherever the data is hydrated. Returns a CPS operation
  resolving the data."
  [sp]
  (fn [resolve reject]
    (let [[resolve reject] (sp/in-callers-world resolve reject)]
      (try
        (let [world (:savepoint/world sp)
              portable (:savepoint/portable sp)]
          (when-not (sp/pending? sp)
            (throw (ex-info "Cannot persist a savepoint that is not pending"
                            {:type ::sp/not-pending :operation :persist})))
          (when-not portable
            (throw (ex-info "Savepoint names no :resume function"
                            {:type ::not-portable
                             :savepoint/site (:savepoint/site sp)})))
          (let [body {:savepoint/site (:savepoint/site sp)
                      :savepoint/address (:savepoint/address sp)
                      :savepoint/seq (:savepoint/seq sp)
                      :savepoint/payload (:savepoint/payload sp)
                      :savepoint/resume (select-keys portable [:fn :args])
                      :world/seed (sp/seed world)
                      :world/state (into {} (map (fn [path] [path (rtp/get-state world path)]))
                                         (:state portable))
                      :world/systems (snapshot-ids world)
                      :world/pinned (pinned-versions world)}
                data (assoc body :savepoint/id (h/content-hash body))
                authority (:authority @(:scope (sp/session world)))]
            (if authority
              (invoke! #(world-scope/escrow! authority world (:savepoint/id data))
                       (fn [_] (resolve (assoc data :world/escrow? true)))
                       reject)
              (resolve data))))
        (catch #?(:clj Throwable :cljs :default) error
          (reject error))))))

(defn- resolve-fn [sym]
  #?(:clj (or (some-> (requiring-resolve sym) deref)
              (throw (ex-info "Resume function not found" {:type ::unknown-resume :fn sym})))
     :cljs (throw (ex-info "Pass :resolve to hydrate! on this platform"
                           {:type ::unknown-resume :fn sym}))))

(defn hydrate!
  "Continue the persisted savepoint `data` with `value`, in a new world of
  `session`.

  The session's root is the HOST world: the systems and pinned components the
  data names must be registered there. The new world is a fork of it, pinned
  at the recorded snapshots and versions, with the recorded state and seed.

  Options:
    :resolve  (fn [sym]) -> the resume function (default: `requiring-resolve`
              on the JVM; required in ClojureScript)
    :handlers as for `savepoint/fork`

  Returns a CPS operation resolving the new world. The computation's
  savepoints and its end reach that world's handlers."
  ([session data value] (hydrate! session data value nil))
  ([session data value {resolve-sym :resolve child-handlers :handlers}]
   (fn [resolve reject]
     (let [[resolve reject] (sp/in-callers-world resolve reject)
           scope (:scope session)
           host (:root session)
           authority (:authority @scope)]
       (world-scope/fork!
        scope host
        {:fork-opts (when (seq (:world/systems data))
                      {:snapshots (:world/systems data)})}
        (fn [{world :child-ctx}]
          (letfn [(run! []
                    (try
                      (doseq [[path v] (:world/state data)]
                        (rtp/swap-state! world path (constantly v)))
                      (rtp/swap-state! world [:savepoint/seed] (constantly (:world/seed data)))
                      (rtp/swap-state! world [:savepoint/seq]
                                       (constantly (inc (:savepoint/seq data))))
                      (binding [ec/*execution-context* world]
                        (doseq [[id version] (:world/pinned data)]
                          (component/repin! (component/->ComponentRef id) version)))
                      (when child-handlers
                        (sp/install-handlers! world child-handlers))
                      (let [{f :fn args :args} (:savepoint/resume data)
                            task (binding [ec/*execution-context* world]
                                   (apply ((or resolve-sym resolve-fn) f) (conj (vec args) value)))]
                        (sp/start-in! session world task)
                        (resolve world))
                      (catch #?(:clj Throwable :cljs :default) error
                        (sp/release-world! session world)
                        (reject error))))]
            (if (and authority (:world/escrow? data))
              (invoke! #(world-scope/claim! authority (:savepoint/id data) world)
                       (fn [_] (run!))
                       (fn [error]
                         (sp/release-world! session world)
                         (reject error)))
              (run!))))
        reject)))))
