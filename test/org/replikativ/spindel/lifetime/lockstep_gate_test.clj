(ns org.replikativ.spindel.lifetime.lockstep-gate-test
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.lifetime.lockstep :as l]
            [org.replikativ.spindel.lifetime.lockstep-manifests :as manifests]
            [clojure.set :as set]
            [org.replikativ.spindel.lifetime.model :as m]
            [clojure.test.check.generators :as gen]))

(def w [:w 0])
(def e [:spin 0])
(def child [:spin 1])
(def r [e 1])

(def ownership-trace
  [{:t :t12 :w w :scope [:scope 0] :parent [:root w]}
   {:t :t04 :w w :e e :mode :callback}
   {:t :t01 :w w :r r :e child :order 3}
   {:t :t04 :w w :scope [:scope 0] :e child :mode :callback}])

(deftest b1-compares-each-ownership-field
  (let [state (reduce m/step (m/init-state) ownership-trace)
        descriptors (update-vals l/components
                                 #(assoc % :enabled? (= :B1 (:step %))))]
    (is (= r (get-in state [:worlds w :entities child :owner])))
    (is (= [:scope 0] (get-in state [:worlds w :runs [child 1] :owner])))
    (with-redefs [l/components descriptors]
      (doseq [path [[:entities child :owner] [:entities child :creator]
                    [:entities child :order] [:runs [child 1] :owner]
                    [:scopes [:scope 0] :parent] [:scopes [:scope 0] :kind]
                    [:scopes [:scope 0] :status]]]
        (is (not= (l/comparable state)
                  (l/comparable (assoc-in state (into [:worlds w] path) :corrupt) false))
            (pr-str path))))))

(deftest b1-run-view-does-not-enable-b3-lifecycle
  (let [state (reduce m/step (m/init-state) ownership-trace)]
    (with-redefs [l/components (update-vals l/components #(assoc % :enabled? (= :B1 (:step %))))]
      (is (= (l/comparable state)
             (l/comparable (assoc-in state [:worlds w :runs [child 1] :status] :different) false)))
      (is (not= (l/comparable state)
                (l/comparable (assoc-in state [:worlds w :root] [:scope 999]) false))))))

(deftest converged-witness-corpus-includes-nested-runs
  (let [corpus (into {} (l/witnesses))]
    (is (<= 130 (count corpus)))
    (is (seq (corpus "run7/F52.edn")))
    (is (seq (corpus "run10/mixed-released.edn")))))

(defn passed-report [requirements]
  (let [result {:status :passed :actions [] :trace []
                :boundaries [{:constituents (mapv #(hash-map :action {:t %})
                                                  (:transitions requirements))}]}]
    {:coverage {:components (zipmap (:components requirements) (repeat {:enabled? true}))}
     :component-availability (zipmap (:components requirements) (repeat true))
     :witnesses (zipmap (:witnesses requirements) (repeat result))
     :scripted (zipmap (:scripted requirements) (repeat result))
     :generated (zipmap (:generated requirements) (repeat result))
     :regressions (zipmap (:regressions requirements) (repeat result))
     :profiles (zipmap (:profiles requirements) (repeat [result]))
     :profile-limits (zipmap (:profiles requirements) (repeat {:status :exhausted :edges 1}))}))

(deftest acceptance-rejects-relevant-result-failures
  (let [requirements {:transitions #{:t01 :t02 :t04 :t12} :components #{} :witnesses #{}
                      :profiles #{:ownership} :scripted #{:ownership}
                      :generated #{[:B1 0]} :regressions #{:completion}}
        report (passed-report requirements)]
    (is (= :passed (:status (l/acceptance report requirements))))
    (doseq [path [[:scripted :ownership] [:generated [:B1 0]] [:regressions :completion]]
            status [:discrepancy :skipped :truncated nil]]
      (is (= :failed (:status (l/acceptance (assoc-in report (conj path :status) status)
                                            requirements)))
          (pr-str [path status])))))

(deftest b1-requirements-include-changed-semantics
  (let [requirements (l/step-requirements :B1)]
    (is (every? (:transitions requirements) [:t01 :t02 :t04 :t12]))
    (is (contains? (:components requirements) :run-owners))
    (is (seq (:profiles requirements)))
    (is (seq (:scripted requirements)))
    (is (seq (:generated requirements)))
    (is (seq (:regressions requirements)))))

(deftest manifests-accumulate-and-preserve-pending-witnesses
  (doseq [[previous stage] (partition 2 1 (take 7 manifests/order))]
    (let [a (l/step-requirements previous) b (l/step-requirements stage)]
      (doseq [field [:transitions :components :scripted :regressions :generated :profiles :witnesses]]
        (is (set/subset? (field a) (field b)) (str stage " " field)))))
  (let [requirements (l/step-requirements :B1)]
    (is (seq (:pending-witnesses requirements)))
    (is (some #(contains? (:prerequisites %) :B4) (vals (:pending-witnesses requirements)))))
  (doseq [stage (drop 7 manifests/order)]
    (let [requirements (l/step-requirements stage)]
      (is (:stub? requirements))
      (is (= :failed (:status (l/acceptance (passed-report requirements) requirements)))))))

(deftest complete-ownership-traces-are-model-traces
  (doseq [[name actions] manifests/ownership-traces]
    (let [states (reductions (fn [state a]
                               (let [result (m/attempt state a)]
                                 (is (nil? (:refusal result)) (pr-str [name a result]))
                                 (:state result))) (m/init-state) actions)]
      (is (= (inc (count actions)) (count states)))
      (is (every? #(manifests/relevant-action? :B1 %) actions)))))

(defn legacy-macrostep [state a rejections]
  ;; Ownership records use the model's creation/invocation operations. The
  ;; control deliberately retains native pre-B3 cancellation and pre-B5
  ;; token acceptance; it must NOT conform on those later-stage cases.
  (cond
    (= :t11 (:t a))
    {:state (-> state
                (assoc-in [:worlds (:w a) :entities (first (:r a)) :completed?] true)
                (assoc-in [:worlds (:w a) :entities (first (:r a)) :result] {:error ::m/cancelled})
                (assoc-in [:worlds (:w a) :runs (:r a) :status] :completed))
     :deliveries []}

    (and (= :t01 (:t a)) (:tok a)
         (not= (:e a) (get-in state [:env :handles (:tok a) :spin] (:e a))))
    (l/model-macrostep state (dissoc a :tok) rejections)

    :else (l/model-macrostep state a rejections)))

(defn with-ownership-control [stage f]
  ;; Independent control state, with explicit legacy behaviors above.
  (let [required (l/step-requirements stage)
        descriptors (into {} (for [[id d] l/components]
                               [id (cond-> (assoc d :enabled? (contains? (:components required) id))
                                     (contains? (:components required) id)
                                     (assoc :available? #(and (map? (:worlds %))
                                                              (every? (fn [[_ w]]
                                                                        (every? map? (map w [:entities :scopes :runs])))
                                                                      (:worlds %)))))]))]
    (with-redefs [l/components descriptors
                  l/new-driver #(atom {:control-state (m/init-state) :delivered []})
                  l/close! (constantly nil)
                  l/projection (fn [driver]
                                 (let [s (:control-state @driver)
                                       entities (set (mapcat (comp keys :entities val) (:worlds s)))]
                                   (update s :worlds
                                           #(into {} (for [[w world] %]
                                                       [w (assoc world :entities
                                                                 (into {} (for [e entities
                                                                                :let [row (m/ent s (m/read-source s w e) e)]
                                                                                :when (and row (not= :fork (:kind row)))]
                                                                            [e row])))])))))
                  l/unsupported #(when-not (manifests/relevant-action? stage %)
                                   {:reason :later-stage :step (manifests/action-stage %)})
                  l/apply-action! (fn [driver a]
                                    (when-not (manifests/relevant-action? stage a)
                                      (throw (ex-info "Test adapter cannot execute later stages" {:action a})))
                                    (let [{:keys [state deliveries refusal]}
                                          (legacy-macrostep (:control-state @driver) a
                                                             (when (:throw a)
                                                               {[(:w a) (first (:r a))]
                                                                (:throw a)}))]
                                      (swap! driver #(-> % (assoc :control-state state) (update :delivered into deliveries)))
                                      (when refusal (throw (ex-info "Model refusal" {:type (:error refusal)})))))
                  l/settlement-probes (constantly :outside-manifest)
                  l/frozen-probe (constantly :outside-manifest)
                  l/stamp-probe (constantly :outside-manifest)
                  l/gc-hook-probe (constantly :outside-manifest)]
      (f required))))

(deftest ownership-control-with-legacy-semantics-satisfies-b1
  (with-ownership-control
    :B1
    (fn [requirements]
      (let [report (l/check-all :B1)
            accepted (l/acceptance report requirements)]
        (is (= :passed (:status accepted)) (pr-str accepted))
        (is (empty? (:model-normative report)))
        (is (= :detected (get-in report [:model-negative-controls "run7/stale-start-cancelling.edn" :status])))
        (is (not (contains? (:witnesses requirements) "run7/stale-start-cancelling.edn")))
        (is (= :exhausted (get-in report [:profile-limits :ownership-scopes :status])))
        (is (seq (get-in report [:profiles :ownership-scopes])))
        (doseq [kind [:scripted :generated :regressions]
                :let [name (first (kind requirements))]]
          (is (= :failed (:status (l/acceptance (assoc-in report [kind name :status] :discrepancy)
                                                requirements))) (pr-str [kind name])))
        (is (= :skipped (:status (l/replay [{:t :t13 :w w :scope [:root w]}]))))))))

(deftest generated-and-profile-walks-declare-observable-boundaries
  (with-ownership-control
    :B1
    (fn [_]
      (let [trace (conj (l/scripted-corpus :completion) {:t :t11 :w w :r r})]
        (is (= :skipped (:status (l/replay trace))))
        (is (= :passed (:status (l/replay (m/init-state) (l/scripted-corpus :completion) {:observable-boundaries? true}))))))))

(deftest profile-alphabets-do-not-shrink-with-adapter-availability
  (let [{:keys [stage alphabet bounds]} (manifests/profile-specs :ownership-scopes)]
    (with-redefs [l/unsupported (constantly {:step :B1 :reason :unavailable})]
      (let [search (l/exhaustive-walks (merge manifests/profile-defaults bounds) stage alphabet)]
        (is (= :exhausted (:status search)))
        (is (pos? (:edges search)))
        (is (some #(some (fn [a] (= :t12 (:t a))) %) (:walks search)))))))

(deftest semantic-prerequisites-keep-later-cases-pending
  (let [b1 (l/step-requirements :B1) b3 (l/step-requirements :B3) b5 (l/step-requirements :B5)]
    (doseq [name [:cancel :cancel-await]]
      (is (not (contains? (:scripted b1) name)))
      (is (= #{:B2 :B3} (get-in b1 [:pending-scripted name :prerequisites])))
      (is (contains? (:scripted b3) name)))
    (is (not (contains? (:profiles b1) :one-spin)))
    (is (seq (get-in b1 [:pending-profiles :one-spin :prerequisites])))
    (is (contains? (:profiles b5) :one-spin))
    (is (contains? (:generated b1) [:B1 0]))
    (is (contains? (:generated b5) [:B1-legacy 0]))
    (is (= #{:B5} (get-in b1 [:pending-generated [:B1-legacy 0] :prerequisites])))))

(deftest b1-domain-has-valid-handle-entity-associations
  (doseq [seed (range 10)
          :let [choices (gen/generate (gen/vector gen/nat 20) 20 seed)
                actions (l/stage-generated-walk :B1 choices)]]
    (reduce (fn [s a]
              (let [result (m/attempt s a)]
                (is (not= ::m/token-spin-mismatch (get-in result [:refusal :error])) (pr-str [seed a]))
                (:state result))) (m/init-state) actions)))

(deftest legacy-control-retains-later-divergences
  (let [start {:t :t04 :w w :e e}
        state (:state (legacy-macrostep (m/init-state) start {}))
        cancel {:t :t11 :w w :r r}
        token {:t :t01 :w w :e e :tok [:tok 0]}
        mismatch (assoc token :e child)
        state-with-token (:state (legacy-macrostep state token {}))]
    (is (not= (:state (l/model-macrostep state cancel {}))
              (:state (legacy-macrostep state cancel {}))))
    (is (= ::m/token-spin-mismatch (get-in (l/model-macrostep state-with-token mismatch {}) [:refusal :error])))
    (is (nil? (:refusal (legacy-macrostep state-with-token mismatch {}))))))

(deftest pending-cases-arrive-unchanged-and-prefixes-never-pass
  (let [b1 (l/step-requirements :B1) b5 (l/step-requirements :B5)]
    (doseq [kind [:scripted :generated :witnesses]
            [id entry] ((keyword (str "pending-" (name kind))) b1)]
      (is (= (:actions entry) (get-in b5 [:cases kind id :actions])) (pr-str [kind id])))
    (is (= (l/stage-generated-walk :B1-legacy (gen/generate (gen/vector gen/nat 20) 20 0))
           (get-in b1 [:pending-generated [:B1-legacy 0] :actions]))))
  (with-ownership-control :B1
    (fn [requirements]
      (let [report (l/check-all :B1)]
        (is (= :failed (:status (l/acceptance (assoc-in report [:scripted :owner-host :trace] []) requirements))))
        (doseq [changed [(update-in report [:profiles :ownership-scopes] pop)
                         (assoc-in report [:profiles :ownership-scopes 0 :trace] [])
                         (update-in report [:profiles :ownership-scopes 0] dissoc :actions)]]
          (is (= :failed (:status (l/acceptance changed requirements)))))
        (doseq [[script path] [[:owner-lexical [:entities child :owner]]
                               [:owner-lexical [:entities child :creator]]
                               [:owner-lexical [:entities child :order]]
                               [:owner-lexical [:runs [child 1] :owner]]
                               [:owner-scopes [:scopes [:scope 0] :parent]]
                               [:owner-scopes [:scopes [:scope 0] :kind]]
                               [:owner-scopes [:scopes [:scope 0] :status]]
                               [:owner-scopes [:root]]]]
          (let [project l/projection
                result (with-redefs [l/projection (fn [driver]
                                                   (let [state (project driver)]
                                                     (if (get-in state (into [:worlds w] path))
                                                       (assoc-in state (into [:worlds w] path) :corrupt) state)))]
                         (l/replay (manifests/ownership-traces script)))]
            (is (= :discrepancy (:status result)) (pr-str path))
            (is (= :failed (:status (l/acceptance (assoc-in report [:scripted script] result) requirements)))
                (pr-str path))))))))

(deftest tokenless-lifecycle-profile-is-pending-until-b5
  (let [b3 (l/step-requirements :B3) b5 (l/step-requirements :B5)]
    (is (not (contains? (:profiles b3) :run-lifecycle)))
    (is (= #{:B5} (get-in b3 [:pending-profiles :run-lifecycle :prerequisites])))
    (is (contains? (:profiles b5) :run-lifecycle))
    (is (= (get-in b3 [:pending-profiles :run-lifecycle :spec])
           (get-in b5 [:cases :profiles :run-lifecycle :spec])))))
