(ns org.replikativ.spindel.lifetime.lockstep
  "Partial runtime oracle. Run with -X:test :nses for smoke; the standalone
   entry point must override the :test alias main-opts (see REPORT.md).
   Unsupported edges stop a walk: deleting them could change its meaning."
  (:refer-clojure :exclude [await])
  (:require [clojure.java.io :as io]
            [clojure.set :as set]
            [clojure.data :as data]
            [clojure.walk :as walk]
            [is.simm.partial-cps.async :as cps]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.addressing :as addressing]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.effects :as effects]
            [org.replikativ.spindel.engine.executor :as ex]
            [org.replikativ.spindel.engine.nodes :as nodes]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.incremental.deltaable :as delta]
            [org.replikativ.spindel.lifetime.bfs-check :as bfs]
            [org.replikativ.spindel.lifetime.check-io :as check-io]
            [org.replikativ.spindel.lifetime.generative-check :as generative]
            [org.replikativ.spindel.lifetime.invariants :as inv]
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.lockstep-manifests :as manifests]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.core :as sc]
            [org.replikativ.spindel.spin.cps :as spin-cps :refer [spin]]
            [org.replikativ.spindel.yggdrasil :as ygg]
            [clojure.test.check.generators :as gen]
            [yggdrasil.convergent.gset :as g]))

(declare entity-view canonical-view)

;; The descriptor owns both sides of the comparison and the laws it can enable.
;; Unimplemented views have concrete paths, but cannot be enabled vacuously.
(defn world-view [paths]
  (fn [state]
    (into {} (for [[w row] (:worlds state)]
               [w (into {} (for [path paths] [path (get-in row path :absent)]))]))))

(defn path-view [paths]
  (fn [state] (into {} (for [path paths] [path (get-in state path :absent)]))))

(defn token-view [state]
  {:worlds (into {} (for [[w world] (:worlds state)]
                      [w (into {} (for [[e row] (:entities world)] [e (:tokens row)]))]))
   :handles (get-in state [:env :handles] :absent)})

(defn row-fields-view [table fields]
  (fn [state]
    (into {} (for [[w world] (:worlds state)]
               [w (into {} (for [[id row] (get world table)]
                             [id (select-keys row fields)]))]))))

(def components
  (into {}
        (for [[id step paths laws scope]
              [[:entities :A3 [[:entities]] #{:L1 :L3 :L4 :L5 :L6 :L7 :L8 :L9 :L10 :L11 :L13 :L20 :L22 :L23} :world]
               [:entity-locality :C2 [[:entities]] #{:L9 :L20} :world]
               [:dirty :B3 [[:entities]] #{} :world]
               [:pins :C2 [[:pins]] #{:L1 :L3 :L4 :L7 :L13 :L14 :L16 :L18 :L19} :world]
               [:waiters :B2 [[:env :waiters] [:env :native]] #{:L16 :L18 :L19 :L24} :global]
               [:scopes :B1 [[:scopes] [:root]] #{:L1 :L2 :L3 :L6 :L7 :L9 :L14 :L16 :L18 :L19} :world]
               [:owners :B1 [[:entities]] #{:L1 :L3 :L6 :L7 :L23} :world]
               [:run-owners :B1 [[:runs]] #{:L2 :L6} :world]
               [:reasons :B3 [[:entities]] #{:L1 :L3 :L7 :L13} :world]
               [:runs :B3 [[:runs]] #{:L1 :L2 :L3 :L4 :L5 :L6 :L7 :L9 :L10 :L13 :L14 :L15 :L16 :L18 :L19 :L22} :world]
               [:obligations :B2 [[:obligations]] #{:L1 :L3 :L4 :L5 :L6 :L7 :L9 :L10 :L13 :L14 :L16 :L18 :L19 :L20 :L22 :L24} :world]
               [:tokens :B5 [[:entities] [:env :handles]] #{:L3 :L7 :L8} :mixed]
               [:registry :C1 [[:registry] [:known-worlds] [:lineages]] #{:L4 :L9 :L20 :L21} :global]
               [:lineage :C1 [[:lineage]] #{:L9 :L14 :L21 :L23} :world]
               [:fdeps :D1 [[:fdeps]] #{:L1 :L3 :L4 :L5 :L7 :L10 :L11 :L13 :L16 :L18 :L19 :L20 :L22} :world]
               [:releasing :D1 [[:releasing]] #{:L1 :L3 :L4 :L10 :L13 :L16 :L18 :L19 :L20 :L22} :world]
               [:queue :D1 [[:queue]] #{:L4 :L5 :L10 :L13 :L16 :L18 :L19 :L20 :L22} :world]
               [:environment :D1 [[:env :outside] [:env :threads]] #{:L10 :L13 :L15 :L22} :global]
               [:world-status :C1 [[:status] [:id] [:root]] #{:L9 :L14 :L16 :L19 :L20 :L21} :world]
               [:admission :E1 [[:admission] [:seal-seq] [:seq]] #{:L16 :L19 :L22} :world]
               [:cuts :E2 [[:cuts]] #{:L13 :L22} :global]
               [:caps :F1 [[:caps] [:durable :caps]] #{:L1 :L3 :L4 :L13 :L16 :L17 :L18 :L19 :L20 :L22} :global]
               [:records :F2 [[:records] [:durable :records] [:freed-bases] [:restarted?] [:model :durable-systems]] #{:L16 :L17 :L18 :L19} :global]]
              :let [view (case id
                           :run-owners (row-fields-view :runs [:owner])
                           :scopes (fn [state]
                                     {:roots ((world-view [[:root]]) state)
                                      :scopes ((row-fields-view :scopes [:kind :parent :status]) state)})
                           (case scope :world (world-view paths) :mixed token-view (path-view paths)))]]
          [id {:enabled? (= id :entities) :step step
               :model-paths paths :projected-paths paths :scope scope
               :model-view (case id
                             :entities #(entity-view % true)
                             :owners #(entity-view % true (:owners components))
                             view)
               :projected-view (case id :entities #(entity-view % false)
                                     :owners #(entity-view % false (:owners components)) view)
               :available? (if (= id :entities)
                             #(and (map? (:worlds %)) (every? (comp map? :entities val) (:worlds %)))
                             (constantly false))
               :compare = :invariants (conj laws :L12)
               :partial-invariants (if (= id :entities) #{:L12} #{})
               :invariant-view (when (= id :entities) #(canonical-view (entity-view % false)))
               :kinds (if (= id :entities) #{:spin :signal} :all)
               :fields (case id :entities [:kind :completed? :result] :tokens [:tokens :handles]
                             :owners [:owner :creator :order] :run-owners [:owner]
                             :scopes [:root :kind :parent :status] :all)
               :payload-fields (if (= id :entities) #{:result} #{})
               :excluded-model-kinds (if (#{:entities :owners} id) {:fork :C2} {})}])))

(defn pause! [_] (throw (ex-info "Only in a scripted spin" {})))

(effects/register-effect-by-symbol!
 'org.replikativ.spindel.lifetime.lockstep/pause!
 (effects/async-effect
  (fn [context {:keys [awaitable]} resolve reject]
    (let [[driver e] awaitable]
      (swap! driver assoc-in [:paused [(:fork-id context) e]]
             {:resolve resolve :reject reject :sid ec/*spin-id*})
      sc/incomplete)))
 'org.replikativ.spindel.engine.effects/one-arg->awaitable-map)

(declare make-script! apply-action!)

(defmacro scripted-spin
  "Each model entity names its own script source site. A single factory call
   site's trace cursor would alias different entities first minted in forks."
  [entity & body]
  `(sc/make-spin ~(spin-cps/build-cps-fn body (spin-cps/build-breakpoints) &env)
                 (addressing/next-id "lockstep-spin" {:file "lifetime-script" :line 1 :column 1}
                                     nil ~entity)
                 nil :computation))

(defn make-script! [driver e]
  (let [s (scripted-spin e
                         (loop []
                           (let [a (pause! [driver e])]
                             (case (:t a)
                               :t07 (if-let [error (:throw a)]
                                      (throw (ex-info "Scripted error" {:type error}))
                                      (get a :value :result))
                               :t05 (do (case (:kind a)
                                          :track (iv/get-new (track (get-in @driver [:handles (last (:debtor a))])))
                                          :await-once (await (or (get-in @driver [:handles (last (:debtor a))])
                                                                 (make-script! driver (last (:debtor a))))))
                                        (recur))
                               (do (apply-action! driver (dissoc a :r)) (recur))))))]
    (swap! driver assoc-in [:handles e] s)
    (swap! driver assoc-in [:ids (sc/spin-id s)] e)
    s))

(defn new-driver []
  (let [rt (ctx/create-execution-context :executor (ex/synchronous-executor))]
    (atom {:contexts {[:w 0] rt} :handles {} :ids {} :paused {} :delivered [] :host-templates #{} :materialized #{} :parents {}})))

(defn close! [driver]
  (doseq [rt (reverse (vals (:contexts @driver)))] (ctx/close-context! rt)))

(defn error-type [e] (or (:type (ex-data e)) (.getName (class e))))

(defn send-command! [driver w e a]
  (let [rt (get-in @driver [:contexts w])
        key [(:fork-id rt) e]
        {:keys [resolve sid]} (get-in @driver [:paused key])]
    (when-not resolve (throw (ex-info "Script is not at a driver checkpoint" {:type ::not-paused :w w :e e})))
    (swap! driver update :paused dissoc key)
    (binding [ec/*execution-context* rt ec/*spin-id* sid cps/*in-trampoline* false]
      (sc/resume resolve a))))

(defn scope-restriction [a]
  (when (and (:scope a) (not= :root (first (:scope a)))) {:step :B1 :reason :explicit-scope}))

(def action-support
  (merge
   (into {} (for [[step ts] [[:B6 [:t03]] [:B2 [:t06 :t08 :t35 :unsubscribe]]
                             [:B3 [:t09 :t10 :t15 :slice-enter :t38]] [:B1 [:t12]] [:B4 [:t13 :join]]
                             [:C2 [:t14]] [:B5 [:t16 :t17 :t18]] [:E1 [:t26]]
                             [:E2 [:t20 :t20q :t22 :t23 :t24 :t25]] [:E3 [:t21]]
                             [:F1 [:t32 :t33]] [:F2 [:t27 :t28 :t29 :t30 :t31]]
                             [:D1 [:t34 :t36 :t37 :queued :arrival :native-progress :waiter-unregister :thread-entry]]]
                  t ts]
              [t {:status :not-yet :step step :restrictions (constantly nil) :dispatch nil}]))
   (update-vals
    {:t08 {:status :macrostep-only :extent :local-completion :reason :needs-microstep-hook :dispatch nil}
     :t01 {:lexical? true
           :dispatch (fn [driver {:keys [w e]}]
                       (if ec/*spin-id*
                         (swap! driver update :materialized conj [w e])
                         (when-not (get-in @driver [:handles e])
                           (swap! driver update :host-templates conj [w e])))
                       (if-let [old (get-in @driver [:handles e])]
                         (let [fresh (sc/make-spin (sc/spin-body old) (sc/spin-id old) nil :computation)]
                           (swap! driver assoc-in [:handles e] fresh))
                         (make-script! driver e)))}
     :t02 {:lexical? true
           :restrictions (fn [a] (cond (:key a) {:step :B6 :reason :keyed-signal}
                                       (not= :signal (get a :kind :signal)) {:step :B1 :reason :atom-creation}))
           :dispatch (fn [driver {:keys [e value]}]
                       (let [s (sig/->SignalRef
                                (addressing/next-id "lockstep-signal" {:file "lifetime-script" :line 1 :column 1} nil e) value)]
                         (sig/get-signal-value s)
                         (swap! driver assoc-in [:handles e] s)
                         (swap! driver assoc-in [:ids (:id s)] e)))}
     :t04 {:restrictions (fn [a] (when (= :causal-follow (get-in a [:filter :mode]))
                                   {:step :D1 :reason :host-filter}))
           :dispatch (fn [driver {:keys [w e]}]
                       (swap! driver update :materialized conj [w e])
                       (let [s (or (get-in @driver [:handles e]) (make-script! driver e))]
                         (s (fn [x] (swap! driver update :delivered conj {:w w :e e :value x}))
                            (fn [x] (swap! driver update :delivered conj {:w w :e e :error (error-type x)})))))}
     :t05 {:restrictions (fn [a] (when (or (not (#{:track :await-once} (:kind a)))
                                           (not= (or (:w a) [:w 0]) (second (:debtor a))))
                                   {:step :B2 :reason :nonlocal-or-nonscripted-effect}))
           :dispatch (fn [driver {:keys [w r kind debtor] :as a}]
                       (when (= :await-once kind) (swap! driver update :materialized conj [w (last debtor)]))
                       (send-command! driver w (first r) a))}
     :t07 {:dispatch (fn [driver {:keys [w r] :as a}] (send-command! driver w (first r) a))}
     :t11 {:dispatch (fn [driver {:keys [r]}]
                       (when-let [s (get-in @driver [:handles (first r)])] (sc/cancel-spin! s)))}
     :signal-write {:dispatch (fn [driver {:keys [e value]}] (reset! (get-in @driver [:handles e]) value))}
     :t19 {:dispatch (fn [driver {:keys [w v k]}]
                       (let [h (ygg/fork! {:systems :none :sync? true})]
                         (swap! driver assoc-in [:contexts v] (:child-ctx h))
                         (swap! driver assoc-in [:parents v] w)
                         (swap! driver assoc-in [:forks k] h)))}}
    #(merge {:status :implemented :step :A3 :extent :partial :restrictions (constantly nil)} %))))

(defn apply-action! [driver a]
  (let [a (update a :w #(or % [:w 0]))
        {:keys [dispatch lexical?]} (get action-support (:t a))
        w (:w a)]
    (binding [ec/*execution-context* (get-in @driver [:contexts w])]
      (if (and lexical? (:r a))
        (do (swap! driver update :materialized conj [w (:e a)])
            (send-command! driver w (first (:r a)) a))
        (dispatch driver a)))))

(defn unsupported [a]
  (let [{:keys [status restrictions] :as descriptor} (get action-support (:t a))]
    (if (= :implemented status) (or (scope-restriction a) (restrictions a))
        (dissoc (or descriptor {:status :not-yet :step :D1}) :dispatch :restrictions))))

(defn project
  "Read only PState, never backend/atom fields. ids maps native addresses to
   structural script names; unknown runtime nodes stay visible as unknown ids.
   The driver explicitly lists the host templates allowed to be absent. PState exposes the visible view, so comparison uses model read-source;
   local versus inherited storage is explicitly absent until C2."
  ([context] (project context {}))
  ([context ids] (project context ids #{}))
  ([context ids excluded]
   (let [runtime-nodes (rtp/get-state context [:nodes])
         entities
         (into {}
               (for [[id n] runtime-nodes
                     :let [kind (nodes/node-type n)]
                     :when (not (contains? excluded (get ids id id)))]
                 [(get ids id id)
                  (merge {:kind kind :completed? (boolean (:completed? n))
                          :result (if (= kind :signal) (delta/unwrap-deltaable (:snapshot n))
                                      (when-let [result (:result n)]
                                        (if (sc/error? result) {:error (error-type (:payload result))}
                                            (:payload result))))}
                         (zipmap [:owner :creator :kept? :tokens :order :reasons :dirty?] (repeat :absent)))]))]
     (merge {:entities (into entities (for [[id row] (rtp/get-state context [:atoms])]
                                        [(get ids id [:native-atom id])
                                         {:kind :atom :completed? false :result (:value row)}]))}
            (into {} (for [[component {:keys [enabled?]}] components
                           :when (not= :entities component)]
                       [component :absent]))))))

(deftype Payload [value]
  Object
  (equals [_ other] (and (instance? Payload other) (= value (.-value ^Payload other))))
  (hashCode [_] (hash value)))

(defn entity-view
  ([state model?] (entity-view state model? (:entities components)))
  ([state model? descriptor]
   (let [{:keys [fields payload-fields excluded-model-kinds]} descriptor]
     {:worlds
      (into {} (for [[w world] (:worlds state)]
                 [w {:entities
                     (into {} (for [e (if model?
                                        (set (mapcat (comp keys :entities val) (:worlds state)))
                                        (keys (:entities world)))
                                    :let [row (if model? (m/ent state (m/read-source state w e) e)
                                                  (get-in world [:entities e]))]
                                    :when (and row (not (and model? (contains? excluded-model-kinds (:kind row)))))]
                                [e (into {} (for [[k v] (select-keys row fields)]
                                              [k (if (payload-fields k) (Payload. v) v)]))]))}]))})))

(defn canonical-view [view]
  ;; Only semantic positions reach the model alpha-renamer. Opaque payloads are
  ;; restored afterwards, including nested vectors/maps/sets containing id tags.
  (walk/postwalk #(if (instance? Payload %) (.-value ^Payload %) %) (m/canonical view)))

(defn comparable
  ([state] (comparable state true))
  ([state model?]
   (let [views (into {} (for [[id descriptor] components :when (:enabled? descriptor)]
                          [id ((if model? (:model-view descriptor) (:projected-view descriptor)) state)]))]
     ;; All components share one identity namespace. Per-component renaming
     ;; could hide a wrong link to a scope/token represented by another view.
     (select-keys (canonical-view views) (keys views)))))

(defn availability-errors [projection]
  (vec (for [[id descriptor] components
             :when (and (:enabled? descriptor) (not ((:available? descriptor) projection)))]
         {:kind :unavailable-component :component id :step (:step descriptor)})))

(defn invariant-coverage []
  (for [[id _] inv/predicates
        :let [required (set (for [[c descriptor] components :when ((:invariants descriptor) id)] c))
              enabled (set (for [[c descriptor] components :when (:enabled? descriptor)] c))
              full? (and (seq required) (set/subset? required enabled))
              partial (first (for [[c descriptor] components
                                   :when (and (:enabled? descriptor) ((:partial-invariants descriptor) id))] c))]
        :when (or full? partial)]
    (cond-> {:id id :scope (if full? :full :projected-data-only) :required required}
      (not full?) (assoc :partial-component partial))))

(defn projection-invariants [projection]
  (vec (keep (fn [{:keys [id partial-component]}]
               (let [predicate (get (into {} inv/predicates) id)
                     view (if partial-component
                            ((get-in components [partial-component :invariant-view]) projection) projection)]
                 (inv/ev id (predicate view))))
             (invariant-coverage))))

(defn model-deliveries
  ([before state] (model-deliveries before state {}))
  ([before state rejections]
   (vec (for [ev (:events state) :when (= :host-delivery (:event ev))
              :let [w (:world ev)
                    ob (get-in before [:worlds w :obligations (:o ev)])
                    e (or (:e ev) (nth (:debtor ob) 2 nil))
                    source (or (m/read-source state w e) (m/read-source before w e))
                    row (or (m/ent state source e) (m/ent before source e))]]
          (merge {:w w :e e}
                 (if-let [error (get rejections [w e])]
                   {:error error}
                   {:value (if (contains? ev :value) (:value ev) (:result row))}))))))

(def drain-policy :local-completion-fifo-to-script-checkpoint)

(defn completion-hook-reason [before a]
  (when (= :t07 (:t a))
    (let [w (or (:w a) [:w 0]) e (first (:r a))]
      (cond
        (some (comp seq :queue val) (:worlds before)) :preexisting-queue
        (seq (get-in before [:worlds w :fdeps])) :foreign-drain
        (some (fn [[_ ob]] (and (= [:entity w e] (:debtor ob))
                                (:standing? ob) (not= :host (first (:creditor ob)))))
              (get-in before [:worlds w :obligations])) :reactive-reentry))))

(defn changed-entities [before after]
  (set (mapcat
        (fn [w]
          (concat
           (for [e (set/union (set (keys (get-in before [:worlds w :entities])))
                              (set (keys (get-in after [:worlds w :entities]))))
                 :when (not= (m/ent before w e) (m/ent after w e))] [w e])
           (for [r (set/union (set (keys (get-in before [:worlds w :runs])))
                              (set (keys (get-in after [:worlds w :runs]))))
                 :when (not= (m/run before w r) (m/run after w r))]
             [w (or (:spin (m/run before w r)) (:spin (m/run after w r)))])))
        (keys (:worlds after)))))

(defn model-macrostep [before action rejections]
  (let [action (update action :w #(or % [:w 0]))
        first-step (m/attempt (assoc before :events []) action)]
    (loop [previous before a action result first-step constituents [] deliveries [] normative []]
      (let [after (:state result)
            violations (inv/check after)
            constituent {:action a :refusal (:refusal result)
                         :induced (vec (filter #(= :resume (:event %)) (:events after)))
                         :model-invariants violations}
            constituents (conj constituents constituent)
            deliveries (into deliveries (model-deliveries previous after rejections))
            normative (into normative violations)
            w (:w action)
            event (first (get-in after [:worlds w :queue]))]
        (if (and (= :t07 (:t action)) (not (:refusal result)) (:completion event)
                 (= w (:debtor-world event)))
          (let [delivery (merge {:t :t08 :w w :e (:completion event)} (dissoc event :completion :seq))]
            (recur after delivery (m/attempt after delivery) constituents deliveries normative))
          {:state after :refusal (:refusal first-step) :constituents constituents
           :deliveries deliveries :model-normative normative :policy drain-policy
           :affected-entities (cond-> (changed-entities (:state first-step) after)
                                (= :t07 (:t action)) (conj [w (first (:r action))]))})))))

(defn host-template? [driver w e]
  (let [{:keys [materialized host-templates parents]} @driver]
    (loop [w w]
      (cond (contains? materialized [w e]) false
            (contains? host-templates [w e]) true
            (parents w) (recur (parents w))
            :else false))))

(defn projection [driver]
  {:worlds (into {} (for [[w rt] (:contexts @driver)]
                      [w (project rt (:ids @driver)
                                  (set (filter #(host-template? driver w %) (vals (:ids @driver)))))]))})

(defn state-differences [expected projected]
  (let [actual (comparable projected false) expected (comparable expected)]
    (vec (for [[id descriptor] components :when (:enabled? descriptor)
               :when (not ((:compare descriptor) (get expected id) (get actual id)))]
           {:kind :state :component id :expected (get expected id) :actual (get actual id)}))))

(defn constituent-match? [witness constituent]
  (let [a (:action constituent)]
    (or (= witness a)
        (and (= :queued (:t witness)) (= (:w witness) (:w a)) (= :t08 (:t a)))
        (and (= :t08 (:t witness)) (= (:w witness) (:w a)) (= (:e witness) (:e a))
             (every? (fn [[k v]] (= v (get a k))) (dissoc witness :t))))))

(defn touches-drain? [affected action]
  (let [w (or (:w action) [:w 0])]
    (or (contains? affected [w (:e action)])
        (contains? affected [w (first (:r action))])
        (and (= :entity (first (:debtor action)))
             (contains? affected [(second (:debtor action)) (last (:debtor action))])))))

(defn replay
  "Compare at observable boundaries; retain constituent model microsteps.
   Required internal interleavings need a native hook, never a translated walk."
  ([actions] (replay (m/init-state) actions))
  ([initial actions] (replay initial actions {}))
  ([initial actions {:keys [observable-boundaries?]}]
   (let [driver (new-driver)]
     (try
       (let [initial-projection (projection driver)
             unavailable (availability-errors initial-projection)
             errors (if (seq unavailable) unavailable (state-differences initial initial-projection))
             initial-invariants (when-not (seq unavailable) (projection-invariants initial-projection))]
         (if (or (seq errors) (seq initial-invariants))
           {:status :discrepancy :checked 0 :trace [] :differences (vec errors) :invariants initial-invariants}
           (loop [state initial remaining (seq actions) trace [] boundaries [] rejections {} normative []]
             (if-let [a (first remaining)]
               (if-let [why (or (unsupported a)
                                (when-let [reason (completion-hook-reason state a)]
                                  {:reason :needs-microstep-hook :detail reason}))]
                 {:status :skipped :reason why :action a :trace trace :boundaries boundaries
                  :checked (count trace) :model-normative normative}
                 (let [w (or (:w a) [:w 0])
                       rejections (if (and (= :t07 (:t a)) (:throw a))
                                    (assoc rejections [w (first (:r a))] (:throw a)) rejections)
                       {after :state refusal :refusal expected-delivered :deliveries
                        :keys [constituents policy model-normative affected-entities]} (model-macrostep state a rejections)
                       drained (rest constituents)
                       matching (take-while true? (map constituent-match? (next remaining) drained))
                       consumed (count matching)
                       pending-drain (drop consumed drained)
                       internal-interleaving? (and (not observable-boundaries?) (seq pending-drain)
                                                   (some (fn [later]
                                                           (or (some #(constituent-match? later %) pending-drain)
                                                               (touches-drain? affected-entities later)))
                                                         (drop (inc consumed) remaining)))]
                   (if internal-interleaving?
                     {:status :skipped :reason {:reason :needs-microstep-hook :detail :witness-interleaving}
                      :action a :checked (count trace) :trace trace :boundaries boundaries :model-normative normative}
                     (let [start (count (:delivered @driver))
                           actual-refusal (try (binding [cps/*in-trampoline* false] (apply-action! driver a)) nil
                                               (catch Throwable e (error-type e)))
                           projected (projection driver)
                           unavailable (availability-errors projected)
                           delivered (subvec (:delivered @driver) start)
                           bad (cond-> (if (seq unavailable) unavailable (state-differences after projected))
                                 (not= (:error refusal) actual-refusal)
                                 (conj {:kind :refusal :expected (:error refusal) :actual actual-refusal})
                                 (not= expected-delivered delivered)
                                 (conj {:kind :delivery :expected expected-delivered :actual delivered}))
                           invariant-errors (when-not (seq unavailable) (projection-invariants projected))
                           prefix (into trace (take (inc consumed) remaining))
                           boundaries (conj boundaries {:action a :policy policy :constituents constituents})
                           normative (into normative model-normative)]
                       (if (or (seq bad) (seq invariant-errors))
                         {:status :discrepancy :trace prefix :checked (count prefix) :boundaries boundaries
                          :differences bad :invariants invariant-errors :model-normative normative}
                         (recur after (drop (inc consumed) remaining) prefix boundaries rejections normative))))))
               {:status :passed :trace trace :boundaries boundaries :checked (count trace)
                :trace-semantics (if observable-boundaries? :observable-boundaries :model-microsteps)
                :model-normative normative}))))
       (finally (close! driver))))))

(defn witness-actions [witness]
  (or (:actions witness) (get-in witness [:witness :actions])))

(defn witness-records []
  ;; Include all runs, including artifacts added after index.edn was written.
  (let [root (io/file (io/resource check-io/witness-root))]
    (for [file (sort (file-seq root))
          :let [name (str (.relativize (.toPath root) (.toPath file)))]
          :when (and (.isFile file) (not= "index.edn" (.getName file))
                     (re-matches #"run.*\.edn" name))]
      [name (check-io/read-witness name)])))

(defn witnesses []
  (map (fn [[name record]] [name (witness-actions record)]) (witness-records)))

(defn stage-alphabet [state stage transitions]
  ;; Extend model-enabled T4/T2 sites with the explicit owner argument. The
  ;; transition itself still runs in the unchanged model, including refusals.
  (let [enabled (m/enabled state)
        candidates (mapcat
                    (fn [a]
                      (let [w (:w a)
                            unkeyed (when (= :t02 (:t a)) (dissoc a :key))
                            base (cond-> [a] unkeyed (conj unkeyed))]
                        (concat base
                                (for [b base
                                      :when (#{:t02 :t04} (:t b))
                                      scope (concat
                                             (for [[id row] (get-in state [:worlds w :scopes])
                                                   :when (= :open (:status row))] id)
                                             (keys (get-in state [:worlds w :runs])))]
                                  (assoc b :scope scope))))) enabled)]
    (vec (distinct (filter #(and (transitions (:t %))
                                 (manifests/relevant-action? stage %)
                                 (m/within-bounds? (:state (m/attempt state %)))) candidates)))))

(defn exhaustive-walks
  "Every edge of a finite declared alphabet. Stage profiles do not consult
   adapter availability: an unavailable edge remains a failing gate result."
  ([options] (exhaustive-walks options nil nil))
  ([options stage transitions]
   (let [initial (m/init-state options) max-states 2000]
     (loop [frontier [[initial []]] seen #{(m/canonical initial)} walks []]
       (if (or (empty? frontier) (>= (count seen) max-states))
         {:status (if (empty? frontier) :exhausted :state-limit)
          :states (count seen) :edges (count walks) :pending (count frontier)
          :bounds options :alphabet transitions :max-states max-states :walks walks}
         (let [[s path] (first frontier)
               alphabet (if stage (stage-alphabet s stage transitions)
                            (filter #(nil? (unsupported %)) (stage-alphabet s :A3 (set (keys action-support)))))
               edges (for [a alphabet] [(:state (if stage (model-macrostep s a {}) (m/attempt s a)))
                                        (conj path a)])
               [fresh seen] (reduce (fn [[queue visited] [after _ :as edge]]
                                      (let [key (m/canonical after)]
                                        (if (contains? visited key) [queue visited]
                                            [(conj queue edge) (conj visited key)])))
                                    [[] seen] edges)]
           (recur (into (vec (rest frontier)) fresh) seen (into walks (map second edges)))))))))

(defn coverage []
  {:actions (update-vals action-support #(dissoc % :dispatch :restrictions))
   :components (update-vals components #(dissoc % :model-view :projected-view :available? :compare :invariant-view))
   :enabled-invariants (vec (invariant-coverage))
   :limitations [:no-complete-L-predicate-yet :internal-interleavings-need-microstep-hook
                 :frozen-via-cut-not-yet :settlement-api-probes-only]})

(defn settlement-probes []
  (let [driver (new-driver) rt (get-in @driver [:contexts [:w 0]])]
    (try
      (binding [ec/*execution-context* rt cps/*in-trampoline* false]
        (into {} (for [kind [:merge :discard]]
                   (let [h (ygg/fork! {:systems :none :sync? true})
                         settle (if (= :merge kind) ygg/merge-fork! ygg/discard-fork!)
                         result (settle h {:sync? true})]
                     [kind {:result (select-keys result [:status :fork-id :merged :discarded]) :repeat-equal? (= result (settle h {:sync? true}))}]))))
      (finally (close! driver)))))

(defn frozen-probe []
  (let [rt (ctx/create-execution-context :executor (ex/synchronous-executor))]
    (try
      (binding [ec/*execution-context* rt]
        (let [s (sig/signal 1)
              _ (sig/get-signal-value s)
              frozen (ctx/fork-context rt :mode :frozen)
              following (ctx/fork-context rt :mode :following)]
          (reset! s 2)
          {:parent @s :frozen (binding [ec/*execution-context* frozen] @s)
           :following (binding [ec/*execution-context* following] @s)}))
      (finally (ctx/close-context! rt)))))

(defn pending-stamp-index
  "Two explicit in-process layouts: A2 stores retry work in world/ephemeral;
   main before A2 stores it at the top level. An empty A2 index takes priority.
   This probe says nothing about F2 durable/restart recovery."
  [rt]
  (let [a2-path [:world/ephemeral ::ygg/pending-stamps]
        a2 (rtp/get-state rt a2-path)]
    (if (some? a2) {:path a2-path :entries a2}
        {:path [::ygg/pending-stamps] :entries (rtp/get-state rt [::ygg/pending-stamps])})))

(defn stamp-probe []
  (let [rt (ctx/create-execution-context :executor (ex/synchronous-executor))
        calls (atom 0)]
    (try
      (binding [ec/*execution-context* rt cps/*in-trampoline* false]
        (ygg/register! (g/gset "a3-stamp" {:store-config {:backend :memory :id (random-uuid)}} {:sync? true})
                       {:grade :linear
                        :intents (fn [_] [{:intent/id :stamp :footprint #{:stamp}}])
                        :parent-footprint (constantly #{})
                        :stamp (fn [_] (when (= 1 (swap! calls inc))
                                         (throw (ex-info "Scripted stamp failure" {:type ::stamp-error}))))})
        (let [h (ygg/fork! {:sync? true})
              error (try (ygg/merge-fork! h {:sync? true}) nil (catch Throwable e (error-type e)))
              disposition (ygg/fork-disposition h)
              pending (pending-stamp-index rt)
              failed-count (count (:entries pending))]
          (assert (= 1 failed-count) "Failed stamp must retain one in-process retry")
          (let [retried (ygg/retry-stamps! rt)
                recovered-count (count (:entries (pending-stamp-index rt)))]
            (assert (= 0 recovered-count) "Successful retry must remove the pending stamp")
            {:trace [:register-fail-once-stamp :fork :merge :retry-stamps]
             :classification :in-process-probe :durable-recovery :not-validated :step :F2
             :error error :disposition disposition :retry-index-path (:path pending)
             :pending-stamps failed-count :pending-stamps-after-recovery recovered-count
             :retried (count retried) :stamp-calls @calls
             :disposition-after-recovery (ygg/fork-disposition h)})))
      (finally (ctx/close-context! rt)))))

(defn gc-hook-probe []
  (let [rt (ctx/create-execution-context :executor (ex/synchronous-executor))]
    (try
      (binding [ec/*execution-context* rt cps/*in-trampoline* false]
        (let [s (spin 1) id (sc/spin-id s) _ @s
              before (boolean (rtp/get-state rt [:nodes id]))]
          ;; Exactly the notification emitted by main's Cleaner, through engine
          ;; ingress. Intentionally synthetic; it does not establish Java object
          ;; unreachability or emulate the missing incarnation-token protocol.
          (rtp/enqueue! rt {:type :gc-cleanup :id id})
          {:notification :deterministic :before before
           :after (boolean (rtp/get-state rt [:nodes id]))
           :model-transitions :not-yet :step :B5}))
      (finally (ctx/close-context! rt)))))

(def scripted-corpus
  (let [w [:w 0] e [:spin 0] r [e 1] child [:spin 1]]
    {:completion [{:t :t01 :w w :e e :tok [:tok 0]}
                  {:t :t04 :w w :e e :tok [:tok 0]} {:t :t07 :w w :r r :value 42}]
     :errors [{:t :t01 :w w :e e :tok [:tok 0]}
              {:t :t04 :w w :e e :tok [:tok 0]}
              {:t :t07 :w w :r r :value {:error ::scripted-error} :throw ::scripted-error}]
     :cancel [{:t :t04 :w w :e e} {:t :t11 :w w :r r}]
     :track [{:t :t02 :w w :e [:signal 0] :value 1} {:t :t04 :w w :e e}
             {:t :t05 :w w :r r :kind :track :debtor [:entity w [:signal 0]]}]
     :await [{:t :t04 :w w :e e}
             {:t :t05 :w w :r r :kind :await-once :debtor [:entity w child]}]
     :cancel-await [{:t :t04 :w w :e e}
                    {:t :t05 :w w :r r :kind :await-once :debtor [:entity w child]}
                    {:t :t11 :w w :r [child 1]}]
     :collections [{:t :t02 :w w :e [:signal 0] :value [1 2]}]
     :nested [{:t :t04 :w w :e e} {:t :t01 :w w :r r :e child}
              {:t :t04 :w w :e child}]
     :following [{:t :t04 :w w :e e}
                 {:t :t19 :w w :v [:w 1] :k [:cap 0] :scope [:root w]}]}))

(defn supported-generated-walk [choices]
  (loop [state (m/init-state) choices choices actions []]
    (let [alphabet (vec (filter #(nil? (unsupported %)) (m/enabled state)))]
      (if (or (empty? choices) (empty? alphabet)) actions
          (let [a (nth alphabet (mod (first choices) (count alphabet)))]
            (recur (:state (m/attempt state a)) (rest choices) (conj actions a)))))))

(defn discrepancy-key [result]
  {:differences
   (mapv (fn [{:keys [kind expected actual] :as difference}]
           (if (= :state kind)
             {:kind kind :component (:component difference) :delta (vec (take 2 (data/diff expected actual)))}
             (select-keys difference [:kind :component :expected :actual]))) (:differences result))
   :invariants (set (for [{:keys [id evidence]} (:invariants result)]
                      [id (set (map #(hash-map :shape (set (keys %))
                                               :relation (select-keys % [:index :field :kind :relation :non-data-state])) evidence))]))})

(defn minimize-discrepancy [result]
  (let [signature (discrepancy-key result)]
    (loop [actions (:trace result) i 0]
      (if (>= i (count actions)) (assoc result :minimal-trace actions :minimality :single-deletion)
          (let [candidate (vec (concat (subvec actions 0 i) (subvec actions (inc i))))
                replayed (if (= :observable-boundaries (:trace-semantics result))
                           (replay (m/init-state) candidate {:observable-boundaries? true})
                           (replay candidate))]
            (if (and (= :discrepancy (:status replayed)) (= signature (discrepancy-key replayed)))
              (recur candidate 0)
              (recur actions (inc i))))))))

(defn witness-prerequisites [actions]
  (cond-> (set (map manifests/action-stage actions))
    ;; These walks exercise owner-release and inherited closure, beyond B1's
    ;; recording of ownership. Keep the full historical walk pending.
    (and (some #(and (= :t01 (:t %)) (:r %)) actions)
         (some #(= :t11 (:t %)) actions)) (conj :B3)
    (and (some #(= :t19 (:t %)) actions)
         (some #(= :t05 (:t %)) actions)) (conj :C2)))

(defn valid-handle-association? [state a]
  (let [handle (get-in state [:env :handles (:tok a)])]
    (or (nil? (:tok a)) (nil? handle) (= (:e a) (:spin handle)))))

(defn stage-generated-walk [id choices]
  (let [spec (manifests/generated-specs id)
        stage (get spec :stage id)
        transitions (get-in manifests/stages [stage :changes])
        options (merge manifests/profile-defaults (:bounds spec))]
    (loop [state (m/init-state options) choices choices actions []]
      (let [alphabet (cond->> (stage-alphabet state stage transitions)
                       (= :valid-handles (:domain spec)) (filter #(valid-handle-association? state %))
                       (= stage :A3) (remove #(completion-hook-reason state %)))]
        (if (or (empty? choices) (empty? alphabet)) actions
            (let [a (nth alphabet (mod (first choices) (count alphabet)))
                  after (:state (model-macrostep state a {}))]
              (recur after (rest choices) (conj actions a))))))))

(defn case-prerequisites
  "Semantic needs of a COMPLETE walk, beyond its transition alphabet. Refusals
   and reclamation are stage requirements even on otherwise early T ids."
  [actions]
  (loop [state (m/init-state) actions (seq actions)
         needs (witness-prerequisites actions)]
    (if-let [a (first actions)]
      (let [{after :state refusal :refusal} (model-macrostep state a {})
            completion? (= :t07 (:t a))
            row (when completion? (m/ent after (:w a) (first (:r a))))]
        (recur after (next actions)
               (cond-> needs
                 (= :t11 (:t a)) (into #{:B2 :B3})
                 (#{::m/token-spin-mismatch ::m/unknown-handle ::m/idle-cache-released}
                  (:error refusal)) (conj :B5)
                 (and completion? (or (nil? row) (empty? (:tokens row)))) (into #{:B3 :B5})
                 (and (= :t11 (:t a))
                      (some #(= :following (get-in % [:lineage :mode])) (vals (:worlds state))))
                 (into #{:C2 :D1}))))
      needs)))

(defn step-requirements [step]
  (let [stages (manifests/lineage step)
        cumulative (fn [field] (apply set/union #{} (map #(get-in manifests/stages [% field] #{}) stages)))
        declared-transitions (cumulative :changes)
        transitions (cond-> declared-transitions
                      (not (contains? (set stages) :B3)) (disj :t11))
        scripts (merge scripted-corpus manifests/ownership-traces)
        scripted-case (fn [name] {:actions (scripts name)
                                  :prerequisites (set/union (case-prerequisites (scripts name))
                                                            (get manifests/scripted-prerequisites name #{}))})
        cases {:witnesses (into {} (for [[name record] (witness-records)
                                         :let [actions (witness-actions record)]
                                         :when (and (not (:negative-control? record))
                                                    (some #(transitions (:t %)) actions))]
                                     [name {:actions actions
                                            :prerequisites (set/union (case-prerequisites actions)
                                                                      (get manifests/historical-prerequisites name #{}))}]))
               :scripted (into {} (for [name (cumulative :scripted)] [name (scripted-case name)]))
               :regressions (into {} (for [name (cumulative :regressions)] [name (scripted-case name)]))
               :generated (into {} (for [[id spec] manifests/generated-specs
                                         :when (contains? (set stages) (get spec :stage id))
                                         seed (:seeds spec)
                                         :let [choices (gen/generate (gen/vector gen/nat (:length spec)) (:length spec) seed)
                                               actions (stage-generated-walk id choices)]]
                                     [[id seed] {:actions actions :stage id :seed seed
                                                 :prerequisites (set/union (case-prerequisites actions)
                                                                           (:prerequisites spec #{}))}]))
               :profiles (into {} (for [name (cumulative :profiles)
                                        :let [spec (manifests/profile-specs name)]]
                                    [name {:spec spec :prerequisites (conj (:prerequisites spec #{}) (:stage spec))}]))}
        classified (reduce-kv
                    (fn [result kind entries]
                      (assoc result kind (set (for [[id c] entries
                                                    :when (set/subset? (:prerequisites c) (set stages))] id))
                             (keyword (str "pending-" (name kind)))
                             (into {} (for [[id c] entries
                                            :let [missing (set/difference (:prerequisites c) (set stages))]
                                            :when (seq missing)]
                                        [id (assoc c :status :pending :prerequisites missing)]))))
                    {} cases)]
    (merge classified
           {:stage step :stages stages :cases cases
            :stub? (boolean (some #(get-in manifests/stages [% :stub?]) stages))
            :changes (into {} (map #(vector % (get-in manifests/stages [% :changes])) stages))
            :transitions transitions :pending-transitions (set/difference declared-transitions transitions)
            :components (cumulative :components)
            :negative-controls (set (for [[name record] (witness-records) :when (:negative-control? record)] name))})))

(defn check-all
  ([] (check-all :B1))
  ([step]
   (let [requirements (step-requirements step)
         preflight (let [driver (new-driver)]
                     (try (let [p (projection driver)]
                            (into {} (for [[c d] components] [c ((:available? d) p)])))
                          (finally (close! driver))))
         ws (into {} (for [[name actions] (witnesses)] [name (replay actions)]))
         searches (into {} (for [name (:profiles requirements)
                                 :let [{:keys [stage alphabet bounds]} (manifests/profile-specs name)]]
                             [name (exhaustive-walks (merge manifests/profile-defaults bounds) stage alphabet)]))
         replay-boundaries #(assoc (replay (m/init-state) % {:observable-boundaries? true})
                                   :trace-semantics :observable-boundaries :actions (vec %))
         walks (into {} (for [[name search] searches] [name (mapv replay-boundaries (:walks search))]))
         scripted (into {} (for [name (set/union (:scripted requirements) (:regressions requirements))]
                             [name (replay (get-in requirements [:cases :scripted name :actions]))]))
         generated (into {} (for [[stage seed :as id] (:generated requirements)
                                  :let [c (get-in requirements [:cases :generated id])]]
                              [id (assoc (replay-boundaries (:actions c)) :stage stage :seed seed)]))
         unrestricted (mapv (fn [seed]
                              (let [choices (gen/generate (gen/vector gen/nat 20) 20 seed)
                                    walk (generative/random-walk (m/init-state) choices)]
                                {:seed seed :result (replay (mapv :action (:trace walk)))
                                 :supported-result (replay (supported-generated-walk choices))})) (range 10))
         model-results (for [[name record] (witness-records)]
                         {:name name :negative-control? (:negative-control? record)
                          :violations (bfs/violations (bfs/execute (witness-actions record)))})]
     {:pending (select-keys requirements [:pending-scripted :pending-regressions :pending-generated :pending-profiles :pending-witnesses])
      :manifest requirements :coverage (coverage) :component-availability preflight
      :witnesses ws :profiles walks
      :profile-limits (into {} (for [[name search] searches] [name (dissoc search :walks)]))
      :scripted scripted :regressions (select-keys scripted (:regressions requirements))
      :generated generated :unrestricted-generated unrestricted
      :settlement-probes (settlement-probes) :frozen-probe (frozen-probe)
      :stamp-probe (stamp-probe) :gc-hook-probe (gc-hook-probe)
      :model-negative-controls (into {} (for [{:keys [name negative-control? violations]} model-results
                                              :when negative-control?]
                                          [name {:status (if (seq violations) :detected :missed)
                                                 :violations violations}]))
      :model-normative (into {} (for [{:keys [name negative-control? violations]} model-results
                                      :when (and (not negative-control?) (seq violations))]
                                  [name violations]))})))

(defn acceptance
  "Only declared, complete results count. Earlier stage requirements accumulate;
   pending historical walks remain visible without pretending to have passed."
  [report {:keys [witnesses transitions components profiles scripted generated regressions stub?] :as requirements}]
  (let [selected (concat (for [name witnesses] [:witnesses name])
                         (for [name scripted] [:scripted name])
                         (for [name generated] [:generated name])
                         (for [name regressions] [:regressions name]))
        results (concat (map #(get-in report %) selected)
                        (mapcat #(get-in report [:profiles %]) profiles))
        observed (set (for [r results :when (= :passed (:status r))
                            boundary (:boundaries r) constituent (:constituents boundary)
                            :when (nil? (:refusal constituent))] (get-in constituent [:action :t])))
        failures (vec (concat
                       (when stub? [{:kind :manifest-stub}])
                       (for [[kind name :as path] selected
                             :let [r (get-in report path)
                                   actions (get-in requirements (into [:cases] (conj path :actions)))]
                             :when (or (not= :passed (:status r))
                                       (and actions (not= actions (:trace r))))]
                         {:kind :required-result :corpus kind :name name :status (:status r)})
                       (for [t (set/difference transitions observed)] {:kind :required-transition :transition t})
                       (for [c components :when (not (and (true? (get-in report [:coverage :components c :enabled?]))
                                                          (true? (get-in report [:component-availability c]))))]
                         {:kind :required-component :component c})
                       (for [profile profiles
                             :let [walks (get-in report [:profiles profile])]
                             :when (or (not (seq walks))
                                       (not= :exhausted (get-in report [:profile-limits profile :status]))
                                       (not= (count walks) (get-in report [:profile-limits profile :edges]))
                                       (not (every? #(and (= :passed (:status %))
                                                          (vector? (:actions %))
                                                          (= (:actions %) (:trace %))) walks)))]
                         {:kind :required-search :profile profile})))
        normative (into {} (filter (comp seq val) (select-keys (:model-normative report) witnesses)))]
    {:status (cond (seq failures) :failed (seq normative) :model-failed :else :passed)
     :runtime-status (if (seq failures) :failed :passed) :failures failures
     :required-model-failures normative :required requirements
     :model-normative (:model-normative report)}))

(defn -main [& [output mode step]]
  (let [raw (check-all (keyword (or step "B1")))
        results (concat (vals (:witnesses raw)) (vals (:scripted raw)) (mapcat val (:profiles raw))
                        (vals (:generated raw))
                        (mapcat (juxt :result :supported-result) (:unrestricted-generated raw)))
        counts (frequencies (map :status results))
        findings (mapv (comp minimize-discrepancy first val)
                       (group-by discrepancy-key (filter #(= :discrepancy (:status %)) results)))
        report (assoc raw :mode (or mode "diagnostic") :counts counts :discrepancies findings
                      :acceptance (acceptance raw (:manifest raw)))]
    (prn (coverage))
    (prn {:counts counts :witnesses (frequencies (map :status (vals (:witnesses report))))
          :acceptance (:acceptance report) :model-normative (:model-normative report)
          :model-negative-controls (:model-negative-controls report)})
    (when output (spit output (str (pr-str report) "\n")))
    (shutdown-agents)
    (when (if (= mode "accept")
            (not= :passed (get-in report [:acceptance :status]))
            (or (pos? (get counts :discrepancy 0)) (some seq (vals (:model-normative report)))))
      (System/exit 1))))
