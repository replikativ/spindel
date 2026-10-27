(ns org.replikativ.spindel.lifetime.lockstep-manifests
  "Acceptance data, separate from adapter availability. A transition may change
   semantics at several stages. Historical walks are never shortened to fit.")

(def order [:A3 :B1 :B2 :B3 :B4 :B5 :B6 :C1 :C2 :D1 :E1 :E2 :E3 :F1 :F2])

(def historical-prerequisites
  ;; These complete walks cancel between T7 and its queued T8. The observable
  ;; boundary adapter cannot execute that interleaving before the D1 hook.
  {"run2-witness-dirty-cache.edn" #{:B3 :D1}
   "run3-witness-dirty-cache.edn" #{:B3 :D1}
   "run4-witness-dirty-cache.edn" #{:B3 :D1}
   "run5-witness-dirty-cache.edn" #{:B3 :D1}})

(def stages
  {:A3 {:changes #{:t01 :t02 :t04 :t05 :t07 :t08 :t11 :t19 :signal-write}
        :components #{:entities}
        :scripted #{:completion :errors :cancel :track :await :cancel-await :collections :nested :following}
        :regressions #{} :profiles #{:one-spin :source-only}}
   :B1 {:after :A3 :changes #{:t01 :t02 :t04 :t12}
        :components #{:scopes :owners :run-owners}
        :scripted #{:owner-host :owner-lexical :owner-signals :owner-join :owner-scopes}
        :regressions #{:completion :errors :track :await :collections :nested :following}
        :profiles #{:ownership-scopes}}
   :B2 {:after :B1 :changes #{:t05 :t06 :t08 :t35 :unsubscribe}
        :components #{:obligations :waiters} :scripted #{}
        :regressions #{:owner-host :owner-lexical :owner-signals :owner-join :owner-scopes}
        :profiles #{:obligation-registration}}
   :B3 {:after :B2 :changes #{:t07 :t09 :t10 :t11 :t15}
        :components #{:runs :reasons :dirty} :scripted #{}
        :regressions #{} :profiles #{:run-lifecycle}}
   :B4 {:after :B3 :changes #{:t13}
        :components #{} :scripted #{} :regressions #{} :profiles #{:scope-close}}
   :B5 {:after :B4 :changes #{:t01 :t04 :t05 :t16 :t17 :t18}
        :components #{:tokens} :scripted #{} :regressions #{} :profiles #{:incarnations}}
   :B6 {:after :B5 :changes #{:t02 :t03}
        :components #{} :scripted #{} :regressions #{} :profiles #{:keyed-sources}}
   :C1 {:after :B6 :stub? true :changes #{:t19 :t34} :components #{:registry :lineage :world-status}}
   :C2 {:after :C1 :stub? true :changes #{:t14 :t19} :components #{:entity-locality :pins}}
   :D1 {:after :C2 :stub? true :changes #{:t05 :t07 :t11 :t34 :t36 :t37}
        :components #{:fdeps :releasing :queue :environment}}
   :E1 {:after :D1 :stub? true :changes #{:t20 :t26} :components #{:admission}}
   :E2 {:after :E1 :stub? true :changes #{:t20q :t22 :t23 :t24 :t25} :components #{:cuts}}
   :E3 {:after :E2 :stub? true :changes #{:t21} :components #{}}
   :F1 {:after :E3 :stub? true :changes #{:t26 :t32 :t33} :components #{:caps}}
   :F2 {:after :F1 :stub? true :changes #{:t27 :t28 :t29 :t30 :t31} :components #{:records}}})

(def ownership-traces
  ;; Complete traces of T1/T2/T4/T12 from model.cljc. No T13 or unsubscribe
  ;; prerequisite, and no prefix extracted from a historical counterexample.
  (let [w [:w 0] root [:root w] e [:spin 0] r [e 1] child [:spin 1]
        s [:scope 0] child-scope [:scope 1]
        open {:t :t12 :w w :scope s :parent root}
        start {:t :t04 :w w :e e :mode :callback}
        lexical {:t :t01 :w w :r r :e child :tok [:tok 0] :order 3}]
    {:owner-host [open {:t :t01 :w w :scope s :e e :tok [:tok 0]}
                  {:t :t04 :w w :scope s :e e :tok [:tok 0] :mode :callback}]
     :owner-lexical [open start lexical
                     {:t :t04 :w w :scope s :e child :tok [:tok 0] :mode :callback}
                     ;; Existing non-predecessor creation cannot replace metadata.
                     (assoc lexical :order 9)]
     :owner-signals [open start
                     {:t :t02 :w w :e [:signal 0] :value :root}
                     {:t :t02 :w w :r r :e [:signal 1] :value :run}
                     {:t :t02 :w w :scope s :e [:signal 2] :value :explicit}
                     {:t :t02 :w w :scope s :kind :atom :e [:atom 0] :value :atom}]
     :owner-join [open start lexical
                  {:t :t04 :w w :r r :e child :mode :callback}
                  {:t :t04 :w w :scope s :e child :mode :callback}]
     :owner-scopes [open
                    {:t :t12 :w w :scope child-scope :parent s :kind :supervisor}
                    {:t :t12 :w w :scope [:scope 2] :parent child-scope :kind :render-root}
                    {:t :t12 :w w :scope [:scope 3] :parent root :kind :sci-component}
                    {:t :t04 :w w :scope child-scope :e e :mode :callback}]}))

(def profile-specs
  ;; Explicit finite alphabets, independent of the current adapter's support.
  ;; Unavailable edges must yield skipped results, never disappear from a gate.
  {:one-spin {:stage :A3 :alphabet #{:t01 :t04 :t07 :t11} :bounds {:spins 1 :signals 0 :atoms 0}}
   :source-only {:stage :A3 :alphabet #{:t02 :signal-write} :bounds {:spins 0 :signals 1 :atoms 0}}
   :ownership-scopes {:stage :B1 :alphabet #{:t04 :t12} :bounds {:spins 1 :signals 0 :atoms 0 :scopes 1}}
   :obligation-registration {:stage :B2 :alphabet #{:t02 :t04 :t05 :t06 :unsubscribe}
                             :bounds {:spins 1 :signals 1 :atoms 1}}
   :run-lifecycle {:stage :B3 :alphabet #{:t04 :t07 :t09 :t10 :t11 :t15}
                   :bounds {:spins 1 :signals 0 :atoms 0 :generations 2}}
   :scope-close {:stage :B4 :alphabet #{:t04 :t12 :t13} :bounds {:spins 1 :signals 0 :atoms 0 :scopes 1}}
   :incarnations {:stage :B5 :alphabet #{:t01 :t04 :t07 :t16 :t17 :t18}
                  :bounds {:spins 1 :signals 0 :atoms 0 :handles 1}}
   :keyed-sources {:stage :B6 :alphabet #{:t02 :t03 :t04}
                   :bounds {:spins 1 :signals 1 :atoms 0}}})

(def profile-defaults
  {:worlds 1 :world-ids 1 :generations 1 :scopes 0 :handles 0
   :cuts 0 :invocations 1 :host-registrations 1
   :filters [:local] :invoke-modes [:callback]})

(def generated-specs
  (let [seeds [0 1 2 3 4 5 6 7 8 9]
        bounds {:spins 2 :signals 1 :atoms 1 :scopes 2 :handles 1}]
    {:A3 {:seeds seeds :length 20 :bounds bounds}
     :B1 {:seeds seeds :length 20 :bounds bounds}
     :B2 {:seeds seeds :length 20 :bounds bounds}
     :B3 {:seeds seeds :length 20 :bounds (assoc bounds :generations 2)}
     :B4 {:seeds seeds :length 20 :bounds bounds}
     :B5 {:seeds seeds :length 20 :bounds (assoc bounds :handles 2)}
     :B6 {:seeds seeds :length 20 :bounds bounds}}))

(defn lineage [stage]
  (when-not (contains? stages stage)
    (throw (ex-info "Unknown implementation stage" {:stage stage})))
  (if-let [previous (get-in stages [stage :after])]
    (conj (lineage previous) stage) [stage]))

(defn action-stage
  "Latest semantic prerequisite of an action, including changes to old T ids.
   This is acceptance policy, not a claim that the adapter implements it."
  [a]
  (cond
    (and (= :t02 (:t a)) (:key a)) :B6
    (and (= :t02 (:t a)) (= :atom (:kind a))) :B1
    (= :causal-follow (get-in a [:filter :mode])) :D1
    (and (#{:t01 :t02 :t04} (:t a)) (:scope a) (not= :root (first (:scope a)))) :B1
    (and (= :t05 (:t a)) (= :entity (first (:debtor a)))
         (not= (:w a) (second (:debtor a)))) :D1
    (and (= :t05 (:t a)) (not (#{:track :await-once} (:kind a)))) :B2
    :else (get {:t01 :A3 :t02 :A3 :t04 :A3 :t05 :A3 :t07 :A3 :t08 :A3 :t11 :A3
                :t19 :A3 :signal-write :A3 :t12 :B1 :t06 :B2 :t35 :B2 :unsubscribe :B2
                :t09 :B3 :t10 :B3 :t15 :B3 :t13 :B4 :t16 :B5 :t17 :B5 :t18 :B5
                :t03 :B6 :t14 :C2 :t20 :E1 :t26 :E1 :t20q :E2 :t22 :E2 :t23 :E2
                :t24 :E2 :t25 :E2 :t21 :E3 :t32 :F1 :t33 :F1
                :t27 :F2 :t28 :F2 :t29 :F2 :t30 :F2 :t31 :F2} (:t a) :D1)))

(defn relevant-action? [stage a]
  (contains? (set (lineage stage)) (action-stage a)))
