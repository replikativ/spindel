(ns org.replikativ.spindel.lifetime.generative-check
  (:require [org.replikativ.spindel.lifetime.check-io :as check-io]
            [clojure.test :refer [deftest is]]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [org.replikativ.spindel.lifetime.bfs-check :as bfs]
            [org.replikativ.spindel.lifetime.model :as m]
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
