(ns org.replikativ.spindel.lifetime.lockstep
  "Partial runtime oracle. Run with -X:test :nses for smoke; the standalone
   entry point must override the :test alias main-opts (see REPORT.md).
   Unsupported edges stop a walk: deleting them could change its meaning."
  (:refer-clojure :exclude [await])
  (:require [clojure.java.io :as io]
            [clojure.set :as set]
            [clojure.data :as data]
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
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.core :as sc]
            [org.replikativ.spindel.spin.cps :as spin-cps :refer [spin]]
            [org.replikativ.spindel.yggdrasil :as ygg]
            [clojure.test.check.generators :as gen]
            [yggdrasil.convergent.gset :as g]))

;; These are deliberately granular. Adding a row implementation must not silently
;; opt its ownership, histories or indexes into the acceptance oracle.
(def components
  {:entities {:enabled? true :view :read-visible :fields [:kind :completed? :result]}
   :entity-locality {:enabled? false :step :C2}
   :dirty {:enabled? false :step :B3}
   :pins {:enabled? false :step :C2}
   :waiters {:enabled? false :step :B2}
   :scopes {:enabled? false :step :B1}
   :owners {:enabled? false :step :B1}
   :reasons {:enabled? false :step :B3}
   :runs {:enabled? false :step :B3}
   :obligations {:enabled? false :step :B2}
   :tokens {:enabled? false :step :B5}
   :registry {:enabled? false :step :C1}
   :lineage {:enabled? false :step :C1}
   :fdeps {:enabled? false :step :D1}
   :releasing {:enabled? false :step :D1}
   :queue {:enabled? false :step :D1}
   :admission {:enabled? false :step :E1}
   :cuts {:enabled? false :step :E2}
   :caps {:enabled? false :step :F1}
   :records {:enabled? false :step :F2}})

(def action-support
  (merge
   (into {} (for [[step ts] [[:B6 [:t03]] [:B2 [:t06 :t08 :t35]]
                             [:B3 [:t09 :t10 :t15]] [:B1 [:t12]] [:B4 [:t13]]
                             [:C2 [:t14]] [:B5 [:t16 :t17 :t18]]
                             [:E1 [:t26]] [:E2 [:t20 :t22 :t23 :t24 :t25]]
                             [:E3 [:t21]] [:F1 [:t32 :t33]]
                             [:F2 [:t27 :t28 :t29 :t30 :t31]] [:D1 [:t34 :t36 :t37 :queued :arrival :native-progress :waiter-unregister :thread-entry]]
                             [:B2 [:unsubscribe]]]
                  t ts] [t {:status :not-yet :step step}]))
   (zipmap [:t01 :t02 :t04 :t05 :t07 :t11 :t19 :signal-write]
           (repeat {:status :implemented :extent :partial}))))

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
    (atom {:contexts {[:w 0] rt} :handles {} :ids {} :paused {} :delivered []})))

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

(defn apply-action! [driver {:keys [t w e r v k] :as a}]
  (let [w (or w [:w 0])
        rt (get-in @driver [:contexts w])]
    (binding [ec/*execution-context* rt]
      (if (and r (#{:t01 :t02} t))
        (send-command! driver w (first r) a)
        (case t
          :t01 (if-let [old (get-in @driver [:handles e])]
                 (let [fresh (sc/make-spin (sc/spin-body old) (sc/spin-id old) nil :computation)]
                   (swap! driver assoc-in [:handles e] fresh))
                 (make-script! driver e))
          :t02 (let [s (sig/->SignalRef
                        (addressing/next-id "lockstep-signal" {:file "lifetime-script" :line 1 :column 1}
                                            nil e) (:value a))]
                 (sig/get-signal-value s)
                 (swap! driver assoc-in [:handles e] s)
                 (swap! driver assoc-in [:ids (:id s)] e))
          :t04 (let [s (or (get-in @driver [:handles e]) (make-script! driver e))]
                 (s (fn [x] (swap! driver update :delivered conj {:w w :e e :value x}))
                    (fn [x] (swap! driver update :delivered conj {:w w :e e :error (error-type x)}))))
          :t05 (send-command! driver w (first r) a)
          :t07 (send-command! driver w (first r) a)
          :t11 (when-let [s (get-in @driver [:handles (first r)])] (sc/cancel-spin! s))
          :signal-write (reset! (get-in @driver [:handles e]) (:value a))
          :t19 (let [h (ygg/fork! {:systems :none :sync? true})]
                 (swap! driver assoc-in [:contexts v] (:child-ctx h))
                 (swap! driver assoc-in [:forks k] h)))))))

(defn unsupported
  "Returns a concrete limitation, including argument-level restrictions."
  [a]
  (let [support (get action-support (:t a))]
    (cond
      (not= :implemented (:status support)) (or support {:status :not-yet :step :D1})
      (and (:scope a) (not= :root (first (:scope a)))) {:step :B1 :reason :explicit-scope}
      (and (= :t02 (:t a)) (or (:key a) (not= :signal (get a :kind :signal)))) {:step :B6 :reason :keyed-or-atom}
      (and (= :t04 (:t a)) (= :causal-follow (get-in a [:filter :mode]))) {:step :D1 :reason :host-filter}
      (and (= :t05 (:t a))
           (or (not (#{:track :await-once} (:kind a)))
               (not= (:w a) (second (:debtor a))))) {:step :B2 :reason :nonlocal-or-nonscripted-effect}
      :else nil)))

(defn project
  "Read only PState, never backend/atom fields. ids maps native addresses to
   structural script names; unknown runtime nodes stay visible as unknown ids.
   Cold host templates have no world entity in T1, until invoked or created in a
   body. PState exposes the visible view, so comparison uses model read-source;
   local versus inherited storage is explicitly absent until C2."
  ([context] (project context {}))
  ([context ids] (project context ids #{}))
  ([context ids other-created]
   (let [runtime-nodes (rtp/get-state context [:nodes])
         created (set/union other-created (set (mapcat :created-spins (vals runtime-nodes))))
         entities
         (into {}
               (for [[id n] runtime-nodes
                     :let [kind (nodes/node-type n)]
                     :when (or (= :signal kind) (:run-gen n) (:created-by n) (contains? created id))]
                 [(get ids id id)
                  (merge {:kind kind :completed? (boolean (:completed? n))
                          :result (if (= kind :signal) (delta/unwrap-deltaable (:snapshot n))
                                      (when-let [result (:result n)]
                                        (if (sc/error? result) {:error (error-type (:payload result))}
                                            (:payload result))))}
                         (zipmap [:owner :creator :kept? :tokens :order :reasons :dirty?] (repeat :absent)))]))]
     (merge {:entities entities}
            (into {} (for [[component {:keys [enabled?]}] components
                           :when (not= :entities component)]
                       [component :absent]))))))

(defn enabled? [component] (true? (get-in components [component :enabled?])))

(defn comparable [state]
  (let [fields (concat (get-in components [:entities :fields])
                       (when (enabled? :owners) [:owner :creator :kept? :order])
                       (when (enabled? :dirty) [:dirty?])
                       (when (enabled? :tokens) [:tokens])
                       (when (enabled? :reasons) [:reasons]))
        world-fields (filter enabled? [:scopes :runs :obligations :fdeps :releasing :queue :lineage :admission :pins])
        global-fields (filter enabled? [:registry :cuts :caps :records])]
    (m/canonical
     (assoc (select-keys state global-fields)
            :worlds (into {} (for [[w world] (:worlds state)]
                               [w (assoc (select-keys world world-fields)
                                         :entities (into {} (for [e (set (mapcat (comp keys :entities val) (:worlds state)))
                                                                  :let [source (m/read-source state w e)
                                                                        row (m/ent state source e)]
                                                                  :when (#{:spin :signal} (:kind row))]
                                                              [e (select-keys row fields)])))]))))))

;; Full lifetime laws need unavailable rows. L12 alone is meaningful on the
;; projected data subset; it makes no claim about hidden runtime internals.
(def invariant-components
  {:L1 #{:owners :scopes :reasons} :L2 #{:runs :owners :scopes}
   :L3 #{:reasons :tokens} :L4 #{:runs :registry :fdeps :releasing :caps :queue}
   :L5 #{:obligations :runs :fdeps :queue} :L6 #{:scopes :owners :obligations}
   :L7 #{:runs :reasons :owners} :L8 #{:tokens :reasons}
   :L9 #{:runs :lineage :obligations} :L10 #{:fdeps :obligations :queue :runs}
   :L11 #{:releasing :fdeps :queue} :L12 #{:entities}
   :L13 #{:runs :obligations :fdeps :releasing :pins :caps :cuts :queue :reasons}
   :L14 #{:pins :lineage} :L15 #{:scopes :runs :obligations :queue}
   :L16 #{:caps :admission} :L17 #{:caps :records} :L18 #{:records :caps}
   :L19 #{:caps :records} :L20 #{:fdeps :releasing :runs :obligations :queue}
   :L21 #{:registry :lineage} :L22 #{:cuts :admission :caps :queue}
   :L23 #{:owners :lineage} :L24 #{:obligations :waiters}})

(defn projection-invariants [projection]
  (let [enabled (set (for [[c opts] components :when (:enabled? opts)] c))]
    (vec (keep (fn [[id predicate]]
                 (when (set/subset? (get invariant-components id) enabled)
                   (inv/ev id (predicate
                               (if (= id :L12)
                                 (update projection :worlds
                                         #(into {} (for [[w row] %] [w (dissoc row :obligations)])))
                                 projection))))) inv/predicates))))

(defn model-deliveries [before state]
  (vec (for [ev (:events state) :when (= :host-delivery (:event ev))
             :let [w (:world ev)
                   ob (get-in before [:worlds w :obligations (:o ev)])
                   e (or (:e ev) (nth (:debtor ob) 2 nil))
                   source (or (m/read-source state w e) (m/read-source before w e))
                   row (or (m/ent state source e) (m/ent before source e))]]
         {:w w :e e :value (if (contains? ev :value) (:value ev) (:result row))})))

(defn replay
  "Every supported prefix edge is checked. First mismatch is a concrete prefix;
   no continuation after divergence, no dropping unsupported middle actions."
  ([actions] (replay (m/init-state) actions))
  ([initial actions]
   (let [driver (new-driver)]
     (try
       (loop [state initial remaining (seq actions) trace []]
         (if-let [a (first remaining)]
           (if-let [why (unsupported a)]
             {:status :skipped :reason why :action a :checked (count trace)}
             (let [{after :state refusal :refusal} (m/attempt state a)
                   start (count (:delivered @driver))
                   actual-refusal (try (binding [cps/*in-trampoline* false] (apply-action! driver a)) nil
                                       (catch Throwable e (error-type e)))
                   created (set (for [[_ context] (:contexts @driver)
                                      [_ node] (rtp/get-state context [:nodes])
                                      child (:created-spins node)] child))
                   projected {:worlds (into {} (for [[w rt] (:contexts @driver)]
                                                 [w (project rt (:ids @driver) created)]))}
                   expected (comparable after) actual (comparable projected)
                   delivered (subvec (:delivered @driver) start)
                   expected-delivered (model-deliveries state after)
                   bad (cond-> []
                         (not= expected actual) (conj {:kind :state :expected expected :actual actual})
                         (not= (get refusal :error) actual-refusal)
                         (conj {:kind :refusal :expected (:error refusal) :actual actual-refusal})
                         (not= expected-delivered delivered)
                         (conj {:kind :delivery :expected expected-delivered :actual delivered}))
                   invariant-errors (projection-invariants projected)
                   prefix (conj trace a)]
               (if (or (seq bad) (seq invariant-errors))
                 {:status :discrepancy :trace prefix :differences bad :invariants invariant-errors}
                 (recur after (next remaining) prefix))))
           {:status :passed :checked (count trace)}))
       (finally (close! driver))))))

(defn witness-actions [witness]
  (or (:actions witness) (get-in witness [:witness :actions])))

(defn witnesses []
  ;; Include all runs, including artifacts added after index.edn was written.
  (for [file (sort-by #(.getName %) (file-seq (io/file (io/resource check-io/witness-root))))
        :when (re-matches #"run.*\.edn" (.getName file))]
    [(.getName file) (witness-actions (check-io/read-witness (.getName file)))]))

(defn exhaustive-walks
  "Replay every edge of the finite supported subprofile. This is not a proof of
   the full model alphabet: unsupported transitions are outside this search."
  [options]
  (let [initial (m/init-state options) max-states 2000]
    (loop [frontier [[initial []]] seen #{(m/canonical initial)} walks []]
      (if (or (empty? frontier) (>= (count seen) max-states))
        {:status (if (empty? frontier) :exhausted :state-limit)
         :states (count seen) :edges (count walks) :pending (count frontier)
         :bounds options :max-states max-states :walks walks}
        (let [[s path] (first frontier)
              edges (for [a (concat (m/enabled s)
                                    (when (and (pos? (get options :signals 0))
                                               (nil? (m/ent s [:w 0] [:signal 0])))
                                      [{:t :t02 :w [:w 0] :e [:signal 0] :value false}]))
                          :when (nil? (unsupported a))]
                      [(:state (m/attempt s a)) (conj path a)])
              [fresh seen] (reduce (fn [[queue visited] [after _ :as edge]]
                                     (let [key (m/canonical after)]
                                       (if (contains? visited key) [queue visited]
                                           [(conj queue edge) (conj visited key)])))
                                   [[] seen] edges)]
          (recur (into (vec (rest frontier)) fresh) seen (into walks (map second edges))))))))

(defn coverage []
  {:actions action-support :components components
   :invariant-prerequisites invariant-components
   :enabled-invariants [{:id :L12 :scope :projected-data-only}]
   :limitations [:no-complete-L-predicate-yet :synchronous-delivery-versus-explicit-model-queue
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

(defn stamp-probe []
  (let [rt (ctx/create-execution-context :executor (ex/synchronous-executor))]
    (try
      (binding [ec/*execution-context* rt cps/*in-trampoline* false]
        (ygg/register! (g/gset "a3-stamp" {:store-config {:backend :memory :id (random-uuid)}} {:sync? true})
                       {:grade :linear
                        :intents (fn [_] [{:intent/id :stamp :footprint #{:stamp}}])
                        :parent-footprint (constantly #{})
                        :stamp (fn [_] (throw (ex-info "Scripted stamp failure" {:type ::stamp-error})))})
        (let [h (ygg/fork! {:sync? true})
              error (try (ygg/merge-fork! h {:sync? true}) nil (catch Throwable e (error-type e)))]
          {:trace [:register-failing-stamp :fork :merge]
           :classification :known-plan-item :step :F2
           :error error :disposition (ygg/fork-disposition h)
           :pending-stamps (count (rtp/get-state rt [::ygg/pending-stamps]))}))
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
    {:completion [{:t :t04 :w w :e e} {:t :t07 :w w :r r :value 42}]
     :errors [{:t :t04 :w w :e e}
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
  (mapv (fn [{:keys [kind expected actual] :as difference}]
          (if (= :state kind)
            {:kind kind :delta (vec (take 2 (data/diff expected actual)))}
            (select-keys difference [:kind :expected :actual]))) (:differences result)))

(defn minimize-discrepancy [result]
  (let [signature (discrepancy-key result)]
    (loop [actions (:trace result) i 0]
      (if (>= i (count actions)) (assoc result :minimal-trace actions :minimality :single-deletion)
          (let [candidate (vec (concat (subvec actions 0 i) (subvec actions (inc i))))
                replayed (replay candidate)]
            (if (and (= :discrepancy (:status replayed)) (= signature (discrepancy-key replayed)))
              (recur candidate 0)
              (recur actions (inc i))))))))

(defn check-all []
  (let [ws (into {} (for [[name actions] (witnesses)] [name (replay actions)]))
        profiles {:one-spin {:spins 1 :signals 0 :atoms 0}
                  :source-only {:spins 0 :signals 1 :atoms 0}}
        searches (into {} (for [[name options] profiles]
                            [name (exhaustive-walks
                                   (merge {:worlds 1 :world-ids 1 :generations 1 :scopes 0
                                           :handles 0 :cuts 0 :invocations 1
                                           :filters [:local] :invoke-modes [:callback]} options))]))
        walks (into {} (for [[name search] searches] [name (mapv replay (:walks search))]))
        generated (mapv (fn [seed]
                          (let [choices (gen/generate (gen/vector gen/nat 20) 20 seed)
                                walk (generative/random-walk (m/init-state) choices)]
                            {:seed seed :result (replay (mapv :action (:trace walk)))
                             :supported-result (replay (supported-generated-walk choices))})) (range 10))]
    {:coverage (coverage) :witnesses ws :profiles (assoc walks
                                                         :settlement [(replay [bfs/following bfs/seal bfs/prepare-op])]
                                                         :shared-cuts [(replay (cons bfs/following (bfs/cut-actions :frozen)))])
     :profile-limits (merge (into {} (for [[name search] searches] [name (dissoc search :walks)]))
                            {:settlement :unsupported :shared-cuts :unsupported})
     :scripted (into {} (for [[name actions] scripted-corpus] [name (replay actions)]))
     :generated generated
     :settlement-probes (settlement-probes) :frozen-probe (frozen-probe) :stamp-probe (stamp-probe) :gc-hook-probe (gc-hook-probe)
     :model-normative (into {} (for [name ["run6-F50.edn" "run6-F51.edn"]
                                     :let [actions (:actions (check-io/read-witness name))]]
                                 [name (bfs/violations (bfs/execute actions))]))}))

(defn -main [& [output]]
  (let [raw (check-all)
        results (concat (vals (:witnesses raw)) (vals (:scripted raw)) (mapcat val (:profiles raw))
                        (mapcat (juxt :result :supported-result) (:generated raw)))
        counts (frequencies (map :status results))
        findings (mapv (comp minimize-discrepancy first val)
                       (group-by discrepancy-key (filter #(= :discrepancy (:status %)) results)))
        report (assoc raw :counts counts :discrepancies findings)]
    (prn (coverage))
    (prn {:counts counts :witnesses (frequencies (map :status (vals (:witnesses report))))})
    (doseq [[name result] (:witnesses report)] (prn {:witness name :result result}))
    (when output (spit output (str (pr-str report) "\n")))
    (shutdown-agents)
    (when (or (pos? (get counts :discrepancy 0)) (some seq (vals (:model-normative report))))
      (System/exit 1))))
