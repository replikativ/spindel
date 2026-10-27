(ns org.replikativ.spindel.lifetime-gates-check
  (:require [clojure.test :refer [deftest is run-tests]]
            [org.replikativ.spindel.lifetime-gate-rules :as gates]))

(defn stable-point [required]
  (let [observation {:heap-bytes 1000 :gc-completed? true :census (zipmap gates/census-paths (repeat 0))}]
    {:gc-stable? true :gc-completed? true :cleanup-complete? true :gc-wait-ms 1500
     :expected-empty required :observations [observation observation observation] :retained-bytes 1000}))

(def fixture
  (merge (zipmap gates/metadata-fields (repeat :test))
         {:protocol-version gates/protocol-version :measurement-protocol gates/measurement-protocol
          :revision "base" :source-revision "base-src"
          :lifecycle (mapv (fn [k] {:lifecycle k :us-per-spin 10 :kb-per-spin 1})
                           [:L0 :L-child :L2-await :L2-track])
          :fork (into {} (for [[id dimensions] gates/fixture-dimensions
                               :let [sample (merge dimensions {:fixture id :operations 1000
                                                               :ns-per-op 100 :bytes-per-op 100 :post-fixture-gc (stable-point #{})})]]
                           [id (assoc sample :samples [sample sample sample])]))
          :enumeration (mapv (fn [k] {:kind k :cycles-per-second 100
                                      :points (mapv (fn [n] (assoc (stable-point gates/required-empty) :cycles n))
                                                    [10000 100000])}) [:fork :spin])}))

(deftest gate-boundaries
  (is (every? :pass? (gates/evaluate fixture fixture)))
  (doseq [candidate [(assoc-in fixture [:lifecycle 0 :us-per-spin] 11.01)
                     (assoc-in fixture [:lifecycle 0 :kb-per-spin] (+ 1 (/ 65.0 1024)))
                     (assoc-in fixture [:fork :large :ns-per-op] 151)
                     (assoc-in fixture [:fork :large :bytes-per-op] 151)
                     (assoc-in fixture [:fork :populated :ns-per-op] 101)
                     (assoc-in fixture [:fork :populated :bytes-per-op] 101)
                     (assoc-in fixture [:enumeration 0 :points 1 :retained-bytes] 1051)
                     (assoc-in fixture [:enumeration 1 :cycles-per-second] 89.9)
                     (assoc-in fixture [:enumeration 0 :points 1 :gc-stable?] false)]]
    (is (some #(false? (:pass? %)) (gates/evaluate fixture candidate))))
  (is (:pass? (gates/ratio-gate :time 1.1 1.1)))
  (is (:pass? (gates/ratio-gate :bytes 64 64)))
  (is (:pass? (gates/ratio-gate :retained 1.05 1.05))))

(defn -main [& _]
  (let [r (run-tests 'org.replikativ.spindel.lifetime-gates-check)]
    (shutdown-agents)
    (when (pos? (+ (:fail r) (:error r))) (System/exit 1))))

(deftest incomplete-or-incomparable-is-not-green
  (is (thrown? clojure.lang.ExceptionInfo (gates/evaluate fixture (assoc fixture :lifecycle []))))
  (is (thrown? clojure.lang.ExceptionInfo
               (gates/evaluate (assoc fixture :machine "a") (assoc fixture :machine "b")))))

(deftest report-identity-mutations
  (doseq [candidate [(assoc fixture :fork (vec (vals (:fork fixture))))
                     (assoc fixture :fork (vec (reverse (vals (:fork fixture)))))
                     (assoc-in fixture [:fork :large] (get-in fixture [:fork :small]))
                     (assoc-in fixture [:fork :large :live-worlds] 1000)
                     (assoc fixture :java "another-jdk")
                     (assoc fixture :protocol-version 1)]]
    (is (thrown? clojure.lang.ExceptionInfo (gates/evaluate fixture candidate))))
  (doseq [field gates/metadata-fields]
    (is (thrown? clojure.lang.ExceptionInfo (gates/evaluate (dissoc fixture field) (dissoc fixture field))))
    (is (thrown? clojure.lang.ExceptionInfo (gates/evaluate fixture (assoc fixture field :changed)))))
  (is (every? :pass? (gates/evaluate fixture (assoc fixture :revision "candidate" :source-revision "candidate-src"))))
  (is (= (gates/evaluate fixture fixture)
         (gates/evaluate fixture (update fixture :fork #(into (sorted-map-by (fn [a b] (compare b a))) %))))))

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
      (is (some #(false? (:pass? %)) (gates/evaluate fixture candidate))))))
