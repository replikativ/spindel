(ns org.replikativ.spindel.lifetime-gates-check
  (:require [clojure.test :refer [deftest is run-tests]]
            [org.replikativ.spindel.lifetime-gate-rules :as gates]))

(defn stable-point [required]
  (let [observation {:heap-bytes 1000 :gc-completed? true :census (zipmap gates/census-paths (repeat 0))}
        point {:gc-stable? true :gc-completed? true :cleanup-complete? true :gc-wait-ms 1500
               :expected-empty required :observations [observation observation observation] :retained-bytes 1000}]
    (assoc point :keyword-intern-drained? true :pre-intern-gc point)))

(def fixture
  (merge (zipmap gates/metadata-fields (repeat :test))
         {:protocol-version gates/protocol-version :measurement-protocol gates/measurement-protocol
          :revision "base" :source-revision "base-src" :allocation :calling-thread-live-handles
          :processors 8 :host-observations [{:load 1.0 :uptime "test uptime" :foreign-high-cpu []}]
          :session {:id "test-session" :round 1 :position 0 :role :baseline}
          :large-parent (vec (for [mode [:root :following :frozen] path [:uncached-await :execution-event]
                                   :let [r {:mode mode :path path :parent-nodes 10000 :shape-warmup? false
                                            :operations 300 :checksum 45150 :ns-per-op 100 :bytes-per-op 100
                                            :nodes-at-start (if (= path :uncached-await) 10600 10300)}]]
                               (assoc r :samples [r r r])))
          :lifecycle (mapv (fn [k] (let [r {:lifecycle k :spins 5000 :warmup 2000
                                            :retained-handles (case k :L-child 14000 :L2-await 7002 7000)
                                            :checksum (case k :L2-await 12512500 :L2-track 12512500 12502500)
                                            :cleanup-calls 0 :us-per-spin 10 :kb-per-spin 1}]
                                     (assoc r :samples [r r r])))
                           [:L0 :L-child :L2-await :L2-track])
          :fork (into {} (for [[id dimensions] gates/fixture-dimensions
                               :let [sample (merge dimensions {:fixture id :operations 1000
                                                               :ns-per-op 100 :bytes-per-op 100 :post-fixture-gc (stable-point #{})})]]
                           [id (assoc sample :samples [sample sample sample])]))
          :enumeration (mapv (fn [k] {:kind k :cycles-per-second 100
                                      :points (mapv (fn [n] (assoc (stable-point gates/required-empty) :cycles n))
                                                    [10000 100000])}) [:fork :spin])}))

(defn evaluate [baseline candidate]
  (gates/evaluate baseline (update candidate :session assoc :role :candidate :position 1)))

(deftest gate-boundaries
  (is (every? :pass? (evaluate fixture fixture)))
  (doseq [candidate [(assoc-in fixture [:lifecycle 0 :us-per-spin] 11.01)
                     (assoc-in fixture [:lifecycle 0 :kb-per-spin] (+ 1 (/ 65.0 1024)))
                     (assoc-in fixture [:fork :large :ns-per-op] 151)
                     (assoc-in fixture [:fork :large :bytes-per-op] 151)
                     (assoc-in fixture [:fork :populated :ns-per-op] 101)
                     (assoc-in fixture [:fork :populated :bytes-per-op] 101)
                     (assoc-in fixture [:enumeration 0 :points 1 :retained-bytes] 1051)
                     (assoc-in fixture [:enumeration 1 :cycles-per-second] 89.9)
                     (assoc-in fixture [:enumeration 0 :points 1 :gc-stable?] false)]]
    (is (some #(false? (:pass? %)) (evaluate fixture candidate))))
  (is (:pass? (gates/ratio-gate :time 1.1 1.1)))
  (is (:pass? (gates/ratio-gate :bytes 64 64)))
  (is (:pass? (gates/ratio-gate :retained 1.05 1.05))))

(defn -main [& _]
  (let [r (run-tests 'org.replikativ.spindel.lifetime-gates-check)]
    (shutdown-agents)
    (when (pos? (+ (:fail r) (:error r))) (System/exit 1))))

(deftest incomplete-or-incomparable-is-not-green
  (is (thrown? clojure.lang.ExceptionInfo (evaluate fixture (assoc fixture :lifecycle []))))
  (is (thrown? clojure.lang.ExceptionInfo
               (evaluate (assoc fixture :machine "a") (assoc fixture :machine "b")))))

(deftest report-identity-mutations
  (doseq [candidate [(assoc fixture :fork (vec (vals (:fork fixture))))
                     (assoc fixture :fork (vec (reverse (vals (:fork fixture)))))
                     (assoc-in fixture [:fork :large] (get-in fixture [:fork :small]))
                     (assoc-in fixture [:fork :large :live-worlds] 1000)
                     (assoc fixture :java "another-jdk")
                     (assoc fixture :protocol-version 1)]]
    (is (thrown? clojure.lang.ExceptionInfo (evaluate fixture candidate))))
  (doseq [field gates/metadata-fields]
    (is (thrown? clojure.lang.ExceptionInfo (evaluate (dissoc fixture field) (dissoc fixture field))))
    (is (thrown? clojure.lang.ExceptionInfo (evaluate fixture (assoc fixture field :changed)))))
  (is (every? :pass? (evaluate fixture (assoc fixture :revision "candidate" :source-revision "candidate-src"))))
  (is (= (evaluate fixture fixture)
         (evaluate fixture (update fixture :fork #(into (sorted-map-by (fn [a b] (compare b a))) %))))))

(deftest retention-needs-gc-cleanup-and-heap-stability
  (let [sample {:heap-bytes 1000 :census {:pending 0 :retired 0} :gc-completed? true}
        observations [sample sample sample]]
    (is (gates/stable-observations? observations #{:pending :retired}))
    (is (not (gates/stable-observations? (assoc-in observations [2 :heap-bytes] 1100) #{:pending})))
    (is (not (gates/stable-observations? (mapv #(assoc-in % [:census :pending] 1) observations) #{:pending})))
    (is (not (gates/stable-observations? (assoc-in observations [2 :gc-completed?] false) #{:pending})))
    (is (not (gates/stable-observations? [sample sample] #{:pending})))
    (is (not (gates/stable-observations? observations #{:missing-index})))))

(deftest stored-stability-needs-observations
  (doseq [path [[:enumeration 0 :points 1 :observations]
                [:fork :small :samples 0 :post-fixture-gc :observations]]]
    (let [candidate (assoc-in fixture path [{:heap-bytes 1000 :gc-completed? true :census {}}])]
      (is (some #(false? (:pass? %)) (evaluate fixture candidate))))))

(deftest protocol-v3-and-intern-drain-required
  (is (= 3 gates/protocol-version))
  (is (not (gates/measurement-stable? (dissoc (stable-point #{}) :keyword-intern-drained?) #{})))
  (is (some #(false? (:pass? %))
            (evaluate fixture (assoc-in fixture [:enumeration 0 :points 1 :keyword-intern-drained?] false))))
  (is (thrown? clojure.lang.ExceptionInfo (evaluate fixture (assoc fixture :protocol-version 2)))))

(deftest lifecycle-liveness-is-required
  (doseq [candidate [(assoc fixture :allocation :calling-thread)
                     (assoc-in fixture [:lifecycle 0 :retained-handles] 0)
                     (assoc-in fixture [:lifecycle 1 :samples 0 :cleanup-calls] 1)
                     (assoc-in fixture [:lifecycle 0 :samples] [])
                     (assoc-in fixture [:lifecycle 2 :checksum] 0)]]
    (is (thrown? clojure.lang.ExceptionInfo (evaluate fixture candidate)))))

(deftest all-large-parent-gates-and-fixture-evidence-required
  (doseq [i (range 6) metric [:ns-per-op :bytes-per-op]]
    (let [results (evaluate fixture (assoc-in fixture [:large-parent i metric] 111))]
      (is (some #(and (= :large-parent (first (:gate %))) (false? (:pass? %))) results)))
    (is (every? :pass? (evaluate fixture (assoc-in fixture [:large-parent i metric] 110)))))
  (doseq [candidate [(dissoc fixture :large-parent)
                     (update fixture :large-parent pop)
                     (assoc-in fixture [:large-parent 0 :nodes-at-start] 600)
                     (assoc-in fixture [:large-parent 0 :samples 0 :checksum] 0)
                     (assoc-in fixture [:large-parent 0 :shape-warmup?] true)]]
    (is (thrown? clojure.lang.ExceptionInfo (evaluate fixture candidate)))))

(deftest overload-and-host-observations-fail-closed
  (is (every? :pass? (evaluate fixture (assoc-in fixture [:host-observations 0 :load] 4))))
  (doseq [candidate [(assoc-in fixture [:host-observations 0 :load] 4.01)
                     (assoc-in fixture [:host-observations 0 :load] -1)
                     (assoc fixture :host-observations [])
                     (update-in fixture [:host-observations 0] dissoc :uptime)
                     (update-in fixture [:host-observations 0] dissoc :foreign-high-cpu)]]
    (is (thrown? clojure.lang.ExceptionInfo (evaluate fixture candidate)))))

(deftest stored-or-unpaired-reports-cannot-pass-relative-gates
  (let [candidate (assoc fixture :session {:id "test-session" :round 1 :position 1 :role :candidate})]
    (is (every? :pass? (gates/evaluate fixture candidate)))
    (doseq [bad [(assoc-in candidate [:session :id] "older-session")
                 (assoc-in candidate [:session :round] 2)
                 (assoc-in candidate [:session :position] 2)
                 (assoc-in candidate [:session :role] :baseline)
                 (dissoc candidate :session)]]
      (is (thrown? clojure.lang.ExceptionInfo (gates/evaluate fixture bad))))))

(deftest malformed-numbers-do-not-pass
  (doseq [v [nil ##NaN ##Inf -1 0]]
    (is (thrown? clojure.lang.ExceptionInfo
                 (evaluate fixture (assoc-in fixture [:lifecycle 0 :us-per-spin] v))))))
