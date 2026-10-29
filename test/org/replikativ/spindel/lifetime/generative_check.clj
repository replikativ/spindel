(ns org.replikativ.spindel.lifetime.generative-check
  (:require [org.replikativ.spindel.lifetime.check-io :as check-io]
            [clojure.test :refer [deftest is]]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [org.replikativ.spindel.lifetime.bfs-check :as bfs]
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.rooted-liveness-test :as rooted]
            [org.replikativ.spindel.lifetime.invariants :as inv]))

(defn random-walk
  "Choice vectors are shrunk by test.check (deletions and integer shrinking).
  Recompute the enabled alphabet on replay, so every shrink is a concrete trace.
  Every edge is checked, including refusals; never mask a known spec violation."
  [initial choices]
  (loop [state initial choices choices trace [] first-failure nil monitor #{}]
    (if (empty? choices)
      {:state state :trace trace :failure first-failure}
      (let [actions (vec (m/enabled state))
            action (nth actions (mod (first choices) (count actions)))
            {after :state refusal :refusal observation :observation} (m/attempt state action)
            edge {:before state :action action :after after :refusal refusal :observation observation}
            trace2 (conj trace edge)
            mon (bfs/advance-monitor monitor (if (or refusal observation) [] (:events after)))
            bad (concat (inv/check after) (inv/edge-check edge) (:errors mon))]
        (recur after (rest choices) trace2
               (or first-failure
                   (when (seq bad) {:index (count trace) :violations (vec bad)
                                    :actions (mapv :action trace2)}))
               (:seen mon))))))

(defn large-fixture
  "10 worlds, tree depth <=4, 50 invoked spins, 20 incarnations, 5-step record.
  Construction itself is checked and retained as part of the trace."
  []
  (let [parents [0 0 1 1 2 2 3 3 4]
        forks (for [[i parent] (map-indexed vector parents)
                    :let [v [:w (inc i)] w [:w parent]]]
                {:t :t19 :w w :v v :k [:cap i] :scope [:root w]})
        spins (mapcat (fn [i]
                        (let [w [:w (mod i 10)] e [:spin i] tok [:tok i]]
                          (concat
                           (when (< i 20) [{:t :t01 :w w :e e :tok tok}])
                           [{:t :t04 :w w :e e :tok (when (< i 20) tok) :mode :callback}])))
                      (range 50))
        settle [{:t :t26 :caller bfs/root :k [:cap 0] :op :large :kind :discard}
                {:t :t27 :k [:cap 0] :op :large :payload :p :bases {:a :base}
                 :steps (mapv (fn [i] {:id i :kind :stamp :system :a :recovery :retry}) (range 5))}]]
    (bfs/execute (m/init-state {:worlds 10 :world-ids 10 :spins 50 :generations 4 :scopes 4
                                :handles 20 :steps 5 :depth 1000})
                 (concat forks spins settle))))

(defn gc-replay [choices]
  ;; A GC schedule is a hyperproperty: compare identical non-GC actions with
  ;; original, duplicated, reversed and lost notifications. No cache reads are
  ;; admitted here; they could legitimately observe reclaimed idle caches.
  (let [initial (m/init-state)
        base [{:t :t01 :w bfs/w :e bfs/e :tok [:tok 0]}
              {:t :t04 :w bfs/w :e bfs/e :tok [:tok 0]}
              {:t :t01 :w bfs/w :e bfs/e :tok [:tok 1]}
              {:t :t07 :w bfs/w :r bfs/r} {:t :t08 :w bfs/w :e bfs/e}
              {:t :t16 :tok [:tok 0]} {:t :t16 :tok [:tok 1]}]
        state (:state (bfs/execute initial base))
        notifications (mapv (fn [choice] {:t :t17 :w bfs/w :e bfs/e :tok [:tok (mod choice 2)]}) choices)
        variants [notifications (reverse notifications) (concat notifications notifications) []]
        projections (map #(m/non-idle-projection (:state (bfs/execute state %))) variants)]
    (apply = projections)))

(deftest gc-retention-differential
  (let [report (tc/quick-check 100 (prop/for-all [choices (gen/vector gen/nat 0 20)]
                                                 (gc-replay choices)) :seed 5812)]
    (println "LIFETIME GC" report)
    (is (:pass? report))))

(defn- gc-observation [s]
  {:engine (m/non-idle-projection s)
   :environment (select-keys (:env s) [:threads :native :waiters])})

(defn- legal-notifications [s]
  (vec (for [[tok handle] (get-in s [:env :handles])
             :when (false? (:reachable? handle))
             w (:touched handle)]
         {:t :t17 :w w :e (:spin handle) :tok tok})))

(defn- interleaved-gc-replay [actions choices mode]
  (loop [s (m/init-state {:slices? true}) remaining actions choices (cycle (or (seq choices) [0]))
         observations []]
    (if-let [action (first remaining)]
      (let [{after :state :keys [refusal observation]} (m/attempt s action)
            edge {:before s :action action :after after :refusal refusal :observation observation}
            notifications (legal-notifications after)
            selected (when (seq notifications)
                       (nth notifications (mod (first choices) (count notifications))))
            schedule (case mode :lost [] :eager notifications
                           :delayed (if (zero? (mod (first choices) 3)) notifications [])
                           :duplicated (if selected [selected selected] []))
            after-gc (reduce (fn [before notification]
                               (let [after (m/step before notification)]
                                 (is (= (gc-observation before) (gc-observation after)))
                                 (is (empty? (inv/check after)))
                                 (is (empty? (inv/edge-check {:before before :action notification :after after})))
                                 after)) after schedule)]
        (is (empty? (inv/check after)))
        (is (empty? (inv/edge-check edge)))
        (recur after-gc (next remaining) (next choices)
               (conj observations {:state (gc-observation after-gc)
                                   :observation observation :refusal (some-> refusal :error)
                                   :events (if (or refusal observation) [] (:events after))})))
      observations)))

(deftest gc-schedules-interleave-with-foreign-cleanup-and-physical-return
  (let [foreign (rooted/foreign-owned-ancestor-actions)
        scenarios [(into (into (subvec foreign 0 14)
                               [{:t :t16 :tok :hp} {:t :t16 :tok :ha}])
                         (concat (subvec foreign 14)
                                 [{:t :queued :w rooted/w} {:t :queued :w rooted/w}
                                  {:t :queued :w rooted/v} {:t :t18 :w rooted/w}]))
                   [{:t :t01 :w rooted/w :e :physical :tok :hp}
                    {:t :t04 :w rooted/w :e :physical :tok :hp :mode :callback}
                    {:t :slice-enter :th :worker :w rooted/w :r [:physical 1]}
                    {:t :t07 :w rooted/w :r [:physical 1] :value 42}
                    {:t :t16 :tok :hp}
                    {:t :queued :w rooted/w}
                    {:t :join :w rooted/w :x [:physical 1] :timeout? true}
                    {:t :t38 :th :worker}
                    {:t :join :w rooted/w :x [:physical 1]}]
                   [{:t :t12 :w rooted/w :scope :resource :parent [:root rooted/w]}
                    {:t :t01 :w rooted/w :e :scoped :tok :hp}
                    {:t :t04 :w rooted/w :e :scoped :scope :resource :tok :hp :mode :callback}
                    {:t :t05 :w rooted/w :r [:scoped 1] :kind :timer :debtor [:host :executor]}
                    {:t :t16 :tok :hp}
                    {:t :t13 :w rooted/w :scope :resource}]]]
    (doseq [actions scenarios]
      (let [baseline (interleaved-gc-replay actions [] :lost)
            report (tc/quick-check
                    30 (prop/for-all [choices (gen/vector gen/nat 1 40)]
                                     (every? #(= baseline (interleaved-gc-replay actions choices %))
                                             [:eager :delayed :duplicated])) :seed 5820)]
        (is (:pass? report) (pr-str report))))))

(deftest generated-traces-with-physical-slices
  (let [initial (-> (m/init-state {:slices? true})
                    (m/step bfs/invoke)
                    (m/step {:t :slice-enter :th :worker :w bfs/w :r bfs/r}))
        report (tc/quick-check
                50 (prop/for-all [choices (gen/vector (gen/choose 0 100000) 1 100)]
                                 (nil? (:failure (random-walk initial choices))))
                :seed 5821 :max-size 100)]
    (println "LIFETIME PHYSICAL GENERATIVE" (dissoc report :result :shrunk))
    (is (:pass? report) (pr-str report))))

(defn- progress-frontiers
  "Exhaust a finite responding-environment profile. Repeated states, refused
   progress actions and depth truncation are failures, never maximal suffixes."
  [initial alphabet assumptions apply-action]
  (letfn [(walk [state trace seen]
            (let [actions (seq (alphabet state)) key (m/canonical state)
                  state-errors (inv/check state)]
              (cond
                (seq state-errors) [{:error :state-invariants :errors state-errors}]
                (contains? seen key) [{:error :progress-cycle :trace trace}]
                (> (count trace) 12) [{:error :depth-cut :trace trace}]
                (nil? actions)
                [{:errors
                  (vec (concat
                        (inv/check-trace trace (assoc assumptions :maximal? true))
                        ;; An empty trace still has an actual frontier state.
                        ;; Do not let an omitted alphabet certify it terminal.
                        (when (and (:adapters-answer? assumptions) (:crashes-stop? assumptions)
                                   (some #(#{:settling :incomplete} (:disposition (val %))) (m/all-caps state)))
                          [{:id :TL12 :evidence :unfinished-frontier}])
                        (when (and (:cut-boundaries? assumptions)
                                   (some #(m/active-cuts (:phase (val %))) (:cuts state)))
                          [{:id :TL13 :evidence :unfinished-frontier}])))}]
                :else
                (mapcat
                 (fn [action]
                   (let [{after :state :keys [refusal observation]} (apply-action state action)
                         edge {:before state :action action :after after :refusal refusal :observation observation}]
                     (if refusal [{:error :refused-progress :edge edge}]
                         (walk after (conj trace edge) (conj seen key))))) actions))))]
    (vec (walk initial [] #{}))))

(defn- answering-adapters [s]
  (for [[op record] (m/all-records s)
        :let [cap (m/cap s (:cap record))]
        :when (not (m/terminal (:disposition cap)))]
    (cond
      (= :incomplete (:disposition cap))
      {:t :t30 :op op :k (:cap record) :caller (:holder cap) :payload (:payload-hash record)}
      (every? #(= :done (:status %)) (:steps record)) {:t :t29 :op op}
      :else {:t :t28 :op op :i (first (keep-indexed #(when (not= :done (:status %2)) %1) (:steps record))) :outcome :ok})))

(deftest bounded-settlement-progress-after-adapters-answer-and-crashes-stop
  (let [setup (bfs/execute
               (mapcat (fn [i]
                         (let [k [:cap i] op [:op i]]
                           [{:t :t19 :w bfs/w :v [:w (inc i)] :k k :scope bfs/root :systems #{:a :b}}
                            {:t :t26 :k k :op op :caller bfs/root :kind :merge}
                            (assoc bfs/prepare-op :k k :op op)
                            {:t :t28 :op op :i 0 :outcome :unknown :committed? true}])) (range 2)))
        initial (:state setup)
        assumptions {:adapters-answer? true :crashes-stop? true}
        frontiers (progress-frontiers initial answering-adapters assumptions m/attempt)
        stalled (progress-frontiers initial answering-adapters assumptions
                                    (fn [s a] (if (= :t29 (:t a)) {:state (assoc s :events [])}
                                                  (m/attempt s a))))]
    ;; Every enabled recovery/response/finish ordering is explored, with no
    ;; further crashes or unanswered/failed adapter responses in this profile.
    (is (not-any? :refusal (:trace setup)))
    (is (empty? (bfs/violations setup)))
    (is (> (count frontiers) 1))
    (is (every? #(and (not (:error %)) (empty? (:errors %))) frontiers))
    (is (some #(= :progress-cycle (:error %)) stalled))
    (is (some #(= :TL12 (:id %))
              (:errors (first (progress-frontiers initial (constantly []) assumptions m/attempt)))))))

(deftest bounded-cut-progress-with-boundaries-or-deadline-abort
  (let [actions (bfs/cut-actions :frozen)
        initial (m/step (m/init-state) (first actions))
        alphabet (fn [s]
                   (when-let [next-action (get {:fenced (nth actions 1) :ready (nth actions 2)
                                                :captured (nth actions 3) :attached (nth actions 4)}
                                               (get-in s [:cuts [:cut 0] :phase]))]
                     [next-action {:t :t25 :c [:cut 0]}]))
        frontiers (progress-frontiers initial alphabet {:cut-boundaries? true} m/attempt)
        stalled (progress-frontiers initial alphabet {:cut-boundaries? true}
                                    (fn [s a] (if (#{:t24 :t25} (:t a)) {:state (assoc s :events [])}
                                                  (m/attempt s a))))]
    (is (= 5 (count frontiers)))
    (is (every? #(and (not (:error %)) (empty? (:errors %))) frontiers))
    (is (some #(= :progress-cycle (:error %)) stalled))
    (is (some #(= :TL13 (:id %))
              (:errors (first (progress-frontiers initial (constantly []) {:cut-boundaries? true} m/attempt)))))))

(deftest generated-lifetime-traces
  (let [started (System/nanoTime)
        property (prop/for-all [choices (gen/vector (gen/choose 0 100000) 1 100)]
                               (nil? (:failure (random-walk (m/init-state) choices))))
        report (tc/quick-check 50 property :seed 58 :max-size 100)
        smallest (or (get-in report [:shrunk :smallest]) (:fail report))
        witness (when smallest (:failure (random-walk (m/init-state) (first smallest))))]
    (println "LIFETIME GENERATIVE" (dissoc report :result :shrunk)
             :seconds (/ (- (System/nanoTime) started) 1e9))
    (println "LIFETIME SHRUNK" (pr-str witness))
    (check-io/write-report! "generative.edn"
                            (pr-str {:report (dissoc report :result :shrunk) :witness witness}))
    (is (:pass? report) (pr-str witness))))

(deftest larger-thousand-step-trace
  (let [started (System/nanoTime) fixture (large-fixture)
        choices (gen/generate (gen/vector (gen/choose 0 100000) 1000) 1000 5800)
        walk (random-walk (:state fixture) choices)
        whole (into (:trace fixture) (:trace walk))
        all-bad (vec (concat (mapcat #(inv/check (:after %)) whole) (inv/check-trace whole)))]
    (println "LIFETIME LARGE" {:worlds 10 :world-ids 10 :spins 50 :handles 20 :record-steps 5
                               :steps (count whole) :seconds (/ (- (System/nanoTime) started) 1e9)
                               :violations (frequencies (map :id all-bad))})
    (println "LIFETIME LARGE FIRST-EVIDENCE"
             (into {} (for [[id bad] (group-by :id all-bad)]
                        [id (first (:evidence (first bad)))])))
    (when-let [i (first (keep-indexed (fn [i edge]
                                        (when (and (seq (inv/l04 (:after edge)))
                                                   (empty? (inv/l04 (:before edge)))) i)) whole))]
      (println "LIFETIME LARGE FIRST-L4" {:index i :action (:action (nth whole i))
                                          :previous (mapv :action (take-last 5 (take i whole)))}))
    (doseq [edge whole :when (some #(= :TL6 (:id %)) (inv/edge-check edge))]
      (println "LIFETIME LARGE TL6-EDGE" (pr-str {:action (:action edge) :violations (inv/edge-check edge)})))
    (is (>= (count whole) 1000))
    (is (zero? (count all-bad)) (pr-str (take 3 all-bad)))))

(deftest following-fork-parent-churn
  (let [cycles 334
        initial (m/init-state {:worlds 2 :world-ids 2 :spins 2 :generations cycles
                               :invocations cycles :host-registrations cycles})
        setup [{:t :t02 :w bfs/w :e [:signal 0]} bfs/following
               {:t :t04 :w bfs/v :e bfs/e}
               {:t :t05 :w bfs/v :r bfs/r :kind :track :debtor [:entity bfs/w [:signal 0]]}]
        churn (mapcat (fn [i] [{:t :t04 :w bfs/w :e [:spin 1] :mode :callback}
                               {:t :t07 :w bfs/w :r [[:spin 1] (inc i)]}
                               {:t :t08 :w bfs/w :e [:spin 1]}]) (range cycles))
        result (bfs/execute initial (concat setup churn))]
    (is (>= (count (:trace result)) 1000))
    (is (not-any? :refusal (:trace result)))
    (is (every? #(= 1 (count (:fdeps (m/wr (:after %) bfs/w)))) (drop (count setup) (:trace result))))
    (is (empty? (bfs/violations result)) (pr-str (take 3 (bfs/violations result))))))

(deftest canonical-generated-traces
  (let [property
        (prop/for-all [choices (gen/vector (gen/choose 0 100000) 1 30)]
                      (let [walk (random-walk (m/init-state) choices)]
                        (every?
                         (fn [s]
                           (let [reordered (clojure.walk/postwalk
                                            #(cond (map? %) (into (array-map) (reverse (vec %)))
                                                   (set? %) (into #{} (reverse (vec %))) :else %) s)
                                 canonical (m/canonical s)]
                             (and (= canonical (m/canonical reordered))
                                  (= canonical (m/canonical canonical)))))
                         (map :after (:trace walk)))))
        result (tc/quick-check 50 property :seed 5805 :max-size 30)]
    (println "LIFETIME CANONICAL" (dissoc result :result :shrunk))
    (is (:pass? result) (pr-str result))))
