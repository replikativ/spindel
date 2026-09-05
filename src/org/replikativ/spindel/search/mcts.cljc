(ns org.replikativ.spindel.search.mcts
  "Finite Monte Carlo tree search over canonical Spindel worlds.

   Search state lives in the caller's execution context. Each expanded node is
   a frozen Yggdrasil fork, rollout effects run in a scratch descendant, and
   every speculative ForkHandle is discarded before a portable result is
   delivered. Applying the selected action is intentionally a separate effect."
  (:require [org.replikativ.spindel.atom :as ratom]
            [is.simm.partial-cps.async :as pcps-async]
            [org.replikativ.spindel.effects.await :refer [await await-finalization]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.hash :as h]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.world.scope :as world-scope]))

(defn- finite-number? [value]
  (and (number? value)
       #?(:clj (Double/isFinite (double value))
          :cljs (js/Number.isFinite value))))

(def ^:private max-safe-integer 9007199254740991)

(defn- portable-number? [value]
  (and (finite-number? value)
       #?(:clj (or (instance? Double value)
                   (instance? Float value)
                   (and (or (instance? Byte value)
                            (instance? Short value)
                            (instance? Integer value)
                            (instance? Long value))
                        (<= (- max-safe-integer) value max-safe-integer)))
          :cljs (or (not (integer? value))
                    (<= (- max-safe-integer) value max-safe-integer)))))

(defn- portable-value?
  "True for the immutable, cross-runtime data subset accepted as a search key."
  [value]
  (cond
    (or (nil? value) (boolean? value) (string? value)
        (keyword? value) (symbol? value) (uuid? value)) true
    (number? value) (portable-number? value)
    (vector? value) (every? portable-value? value)
    (list? value) (every? portable-value? value)
    (set? value) (every? portable-value? value)
    (and (map? value) (not (record? value)))
    (every? (fn [[key item]]
              (and (portable-value? key) (portable-value? item)))
            value)
    :else false))

(defn- require-portable! [kind value]
  (when-not (portable-value? value)
    (throw (ex-info (str "MCTS " (name kind)
                         " must be immutable cross-runtime data")
                    {:type ::non-portable-value
                     :kind kind
                     :value-type (str (type value))})))
  value)

(defn- validate-options! [{:keys [max-simulations max-depth max-nodes
                                  exploration]}]
  (when-not (pos-int? max-simulations)
    (throw (ex-info ":max-simulations must be a positive integer"
                    {:type ::invalid-options})))
  (when-not (pos-int? max-depth)
    (throw (ex-info ":max-depth must be a positive integer"
                    {:type ::invalid-options})))
  (when-not (pos-int? max-nodes)
    (throw (ex-info ":max-nodes must be a positive integer"
                    {:type ::invalid-options})))
  (when-not (and (finite-number? exploration) (not (neg? exploration)))
    (throw (ex-info ":exploration must be a finite non-negative number"
                    {:type ::invalid-options}))))

(defn- deterministic-index [seed coordinates n]
  (when (pos? n)
    (let [hex (subs (str (h/content-hash [seed coordinates])) 0 8)
          value #?(:clj (Long/parseLong hex 16)
                   :cljs (js/parseInt hex 16))]
      (mod value n))))

(defn- action-vector [value]
  (let [actions (mapv #(require-portable! :action %) value)]
    (when-not (= (count actions) (count (set actions)))
      (throw (ex-info "MCTS actions must be unique at each state"
                      {:type ::duplicate-actions :actions actions})))
    actions))

(defn- context-call
  "Return an external await operation that runs thunk's value-or-Spin as an
   explicitly owned task in context. The activity value lets cancellation find
   the task in the same fork where its continuations live."
  [scope context operation thunk]
  (fn [resolve reject]
    (let [caller-context (ec/current-execution-context)
          settled? (atom false)]
      (binding [ec/*execution-context* context]
        ;; Construct as well as execute the task in its target world. Creating
        ;; it in the caller would register its deterministic ID in the wrong
        ;; context, allowing different world evaluations to alias cached nodes.
        (let [task (spin
                    (let [value (thunk)]
                      (if (satisfies? spin-core/PSpin value)
                        (await value)
                        value)))
              activity (world-scope/begin-activity!
                        scope :mcts/evaluation
                        {:task task :context context :operation operation})
              finish! (fn [callback value]
                        (when (compare-and-set! settled? false true)
                          (world-scope/end-activity! scope activity)
                          (binding [ec/*execution-context* caller-context
                                    pcps-async/*in-trampoline* false]
                            (spin-core/resume callback value))))]
          (try
            (sync/spawn! task {:on-success #(finish! resolve %)
                               :on-error #(finish! reject %)})
            (catch #?(:clj Throwable :cljs :default) error
              ;; A synchronous terminal callback may throw after claiming the
              ;; operation. Preserve that callback failure; otherwise release
              ;; the evaluation lease and reject the still-pending await.
              (if @settled?
                (throw error)
                (finish! reject error)))))))))

(defn- cancel-evaluations! [scope]
  (doseq [{:keys [task context]}
          (world-scope/activity-values scope :mcts/evaluation)]
    (try
      (binding [ec/*execution-context* context]
        (spin-core/cancel-spin! task))
      (catch #?(:clj Throwable :cljs :default) _
        nil))))

(defn- node-id [seed path]
  (h/content-hash [:mcts seed path]))

(defn- mean-value [{:keys [visits value-total]}]
  (if (pos? visits) (/ value-total visits) 0.0))

(defn uct-score
  "Pure UCT score. Unvisited children have positive infinite priority."
  [parent-visits child exploration]
  (if (zero? (:visits child))
    ##Inf
    (+ (mean-value child)
       (* exploration
          (Math/sqrt (/ (Math/log (double (max 1 parent-visits)))
                        (:visits child)))))))

(defn- choose-best-child [tree node seed simulation exploration]
  (let [children (mapv tree (:children node))
        scored (mapv #(assoc % ::score
                             (uct-score (:visits node) % exploration))
                     children)
        best-score (apply max (map ::score scored))
        tied (filterv #(= best-score (::score %)) scored)]
    (:id (nth tied (deterministic-index
                    seed [:select simulation (:id node)] (count tied))))))

(defn- select-path
  [tree root-id seed simulation exploration max-depth max-nodes]
  (loop [node-id root-id
         path [root-id]]
    (let [node (get tree node-id)]
      (if (or (:terminal? node)
              (>= (:depth node) max-depth)
              (and (seq (:untried node)) (< (count tree) max-nodes))
              (empty? (:children node)))
        path
        (let [child-id (choose-best-child tree node seed simulation exploration)]
          (recur child-id (conj path child-id)))))))

(defn- remove-at [values idx]
  (into (subvec values 0 idx) (subvec values (inc idx))))

(defn- backpropagate [tree path reward]
  (reduce (fn [next-tree id]
            (-> next-tree
                (update-in [id :visits] inc)
                (update-in [id :value-total] + (double reward))))
          tree
          path))

(defn- require-isolated-world! [world phase]
  (let [systems (get-in world [:descriptor :fork/systems])
        shared (->> systems
                    (keep (fn [[system-id descriptor]]
                            (when (= :shared (:kind descriptor)) system-id)))
                    vec)]
    (when (seq shared)
      (throw (ex-info
              "MCTS speculative world contains shared registered systems"
              {:type ::shared-world-systems
               :phase phase
               :systems shared
               :fork/id (get-in world [:descriptor :fork/id])})))
    world))

(defn- rollout
  [environment scope context state path simulation seed start-depth max-depth]
  (spin
   (let [scratch (require-isolated-world!
                  (await (fn [resolve reject]
                           (world-scope/fork! scope context resolve reject)))
                  :rollout)
         scratch-context (:child-ctx scratch)]
     (loop [current state
            depth start-depth
            coordinates path]
       (let [terminal? (boolean
                        (await (context-call scope scratch-context :mcts/terminal
                                             #((:terminal? environment) current))))]
         (if (or terminal? (>= depth max-depth))
           (double
            (await (context-call scope scratch-context :mcts/reward
                                 #((:reward environment) current))))
           (let [actions (action-vector
                          (await (context-call scope scratch-context :mcts/actions
                                               #((:actions environment) current))))]
             (if (empty? actions)
               (double
                (await (context-call scope scratch-context :mcts/reward
                                     #((:reward environment) current))))
               (let [idx (if-let [policy (:rollout-action environment)]
                           (policy actions {:seed seed
                                            :simulation simulation
                                            :depth depth
                                            :path coordinates})
                           (deterministic-index seed
                                                [:rollout simulation depth coordinates]
                                                (count actions)))
                     _ (when-not (and (int? idx) (<= 0 idx) (< idx (count actions)))
                         (throw (ex-info "Rollout policy returned an invalid index"
                                         {:type ::invalid-rollout-index
                                          :index idx
                                          :action-count (count actions)})))
                     action (nth actions idx)
                     next-state
                     (await (context-call scope scratch-context :mcts/transition
                                          #((:transition environment)
                                            current action)))]
                 (recur next-state (inc depth) (conj coordinates action)))))))))))

(defn- expand-node
  [environment scope tree parent-id simulation seed max-depth]
  (spin
   (let [parent (get tree parent-id)
         actions (:untried parent)
         idx (deterministic-index seed [:expand simulation parent-id]
                                  (count actions))
         action (nth actions idx)
         world (require-isolated-world!
                (await (fn [resolve reject]
                         (world-scope/fork! scope (:context parent)
                                            resolve reject)))
                :expansion)
         child-context (:child-ctx world)
         next-state
         (await (context-call scope child-context :mcts/transition
                              #((:transition environment) (:state parent) action)))
         terminal? (boolean
                    (await (context-call scope child-context :mcts/terminal
                                         #((:terminal? environment) next-state))))
         child-actions (if (or terminal? (>= (inc (:depth parent)) max-depth))
                         []
                         (action-vector
                          (await (context-call scope child-context :mcts/actions
                                               #((:actions environment) next-state)))))
         path (conj (:path parent) action)
         child-id (node-id seed path)
         child {:id child-id
                :parent parent-id
                :action action
                :path path
                :depth (inc (:depth parent))
                :state next-state
                :context child-context
                :world world
                :terminal? terminal?
                :untried child-actions
                :children []
                :visits 0
                :value-total 0.0}]
     {:tree (-> tree
                (assoc child-id child)
                (assoc-in [parent-id :untried] (remove-at actions idx))
                (update-in [parent-id :children] conj child-id))
      :child-id child-id})))

(defn- project-node [node descriptors-by-id]
  (let [creation (some-> node :world :descriptor)
        descriptor (get descriptors-by-id (:fork/id creation) creation)]
    (cond-> {:node/id (:id node)
             :node/parent (:parent node)
             :node/action (:action node)
             :node/path (:path node)
             :node/depth (:depth node)
             :node/terminal? (:terminal? node)
             :node/visits (:visits node)
             :node/mean-value (mean-value node)}
      descriptor (assoc :world/descriptor descriptor))))

(defn- choose-root-action [tree root seed]
  (when (seq (:children root))
    (let [children (mapv tree (:children root))
          max-visits (apply max (map :visits children))
          visited (filterv #(= max-visits (:visits %)) children)
          max-mean (apply max (map mean-value visited))
          tied (filterv #(= max-mean (mean-value %)) visited)]
      (:action (nth tied (deterministic-index seed :final (count tied)))))))

(defn search
  "Return a finite Spin<SearchResult> for a single-agent maximizing problem.

   environment requires:
   - :actions     state -> vector or Spin<vector> (observational)
   - :transition state action -> next-state or Spin<next-state> (may mutate world)
   - :terminal?   state -> boolean or Spin<boolean> (observational)
   - :reward      state -> finite number or Spin<number> (observational)

   Options include :max-simulations, :max-depth, :max-nodes, :exploration,
   :seed, :world-opts, and a pure :continue? predicate receiving progress.
   Seed and actions must be immutable cross-runtime data. Speculative forks
   containing identity-forked :shared systems are rejected before evaluation.
   All speculative worlds are discarded. The selected action is never applied
   to the ambient world."
  ([environment initial-state] (search environment initial-state {}))
  ([environment initial-state opts]
   (let [{:keys [max-simulations max-depth max-nodes exploration seed
                 world-opts continue?]
          :or {max-simulations 100
               max-depth 32
               max-nodes 1000
               exploration (Math/sqrt 2.0)
               seed 0
               world-opts {}
               continue? (constantly true)}} opts]
     (validate-options! {:max-simulations max-simulations
                         :max-depth max-depth
                         :max-nodes max-nodes
                         :exploration exploration})
     (require-portable! :seed seed)
     (doseq [key [:actions :transition :terminal? :reward]]
       (when-not (fn? (get environment key))
         (throw (ex-info (str "MCTS environment requires " key)
                         {:type ::invalid-environment :key key}))))
     (when-not (fn? continue?)
       (throw (ex-info ":continue? must be a function"
                       {:type ::invalid-options :option :continue?})))
     (when (and (contains? environment :rollout-action)
                (not (fn? (:rollout-action environment))))
       (throw (ex-info ":rollout-action must be a function"
                       {:type ::invalid-environment
                        :key :rollout-action})))
     (spin
      (let [parent-context (ec/current-execution-context)
            scope (world-scope/create {:purpose :mcts
                                       :fork-opts world-opts})
            search-activity (world-scope/begin-activity! scope :mcts/search)
            simulations (volatile! 0)
            settled? (volatile! false)]
        (try
          (let [root-id (node-id seed [])
                terminal? (boolean
                           (await
                            (context-call scope parent-context :mcts/terminal
                                          #((:terminal? environment)
                                            initial-state))))
                actions (if terminal?
                          []
                          (action-vector
                           (await
                            (context-call scope parent-context :mcts/actions
                                          #((:actions environment)
                                            initial-state)))))
                tree (ratom/atom
                      {root-id {:id root-id
                                :parent nil
                                :action nil
                                :path []
                                :depth 0
                                :state initial-state
                                :context parent-context
                                :world nil
                                :terminal? terminal?
                                :untried actions
                                :children []
                                :visits 0
                                :value-total 0.0}})]
            (loop [simulation 0]
              (when (and (< simulation max-simulations)
                         (continue? {:simulations simulation
                                     :nodes (count @tree)}))
                (let [selected-path
                      (select-path @tree root-id seed simulation
                                   exploration max-depth max-nodes)
                      leaf-id (peek selected-path)
                      leaf (get @tree leaf-id)
                      expandable? (and (seq (:untried leaf))
                                       (< (count @tree) max-nodes)
                                       (< (:depth leaf) max-depth))
                      expansion (when expandable?
                                  (await (expand-node environment scope @tree
                                                      leaf-id simulation seed
                                                      max-depth)))
                      _ (when expansion (reset! tree (:tree expansion)))
                      rollout-id (or (:child-id expansion) leaf-id)
                      rollout-node (get @tree rollout-id)
                      path (cond-> selected-path expansion (conj rollout-id))
                      reward (if (:terminal? rollout-node)
                               (double
                                (await
                                 (context-call scope (:context rollout-node)
                                               :mcts/reward
                                               #((:reward environment)
                                                 (:state rollout-node)))))
                               (await (rollout environment scope
                                               (:context rollout-node)
                                               (:state rollout-node)
                                               (:path rollout-node)
                                               simulation seed
                                               (:depth rollout-node) max-depth)))]
                  (when-not (finite-number? reward)
                    (throw (ex-info "MCTS reward must be finite"
                                    {:type ::invalid-reward :reward reward})))
                  (reset! tree (backpropagate @tree path reward))
                  (vreset! simulations (inc simulation))
                  (recur (inc simulation)))))
            (let [root (get @tree root-id)
                  selected-action (choose-root-action @tree root seed)
                  portable-tree @tree]
              (world-scope/end-activity! scope search-activity)
              (await-finalization
               (world-scope/discard-when-quiescent! scope))
              (let [descriptors (world-scope/descriptors scope)
                    descriptors-by-id (into {} (map (juxt :fork/id identity))
                                            descriptors)]
                (vreset! settled? true)
                {:search/algorithm :uct
                 :search/status :completed
                 :search/seed seed
                 :search/simulations @simulations
                 :search/node-count (count portable-tree)
                 :search/selected-action selected-action
                 :search/root {:visits (:visits root)
                               :mean-value (mean-value root)}
                 :search/nodes (->> (vals portable-tree)
                                    (sort-by (comp str :id))
                                    (mapv #(project-node % descriptors-by-id)))
                 :world/descriptors descriptors})))
          (finally
            (when-not @settled?
              (world-scope/request-cancel! scope)
              (cancel-evaluations! scope)
              (world-scope/end-activity! scope search-activity)
              (await-finalization
               (world-scope/discard-when-quiescent! scope))))))))))
