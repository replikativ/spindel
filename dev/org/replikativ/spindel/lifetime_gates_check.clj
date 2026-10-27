(ns org.replikativ.spindel.lifetime-gates-check
  (:require [clojure.test :refer [deftest is run-tests]]
            [org.replikativ.spindel.lifetime-gate-rules :as gates]))

(def fixture
  {:lifecycle (mapv (fn [k] {:lifecycle k :us-per-spin 10 :kb-per-spin 1})
                    [:L0 :L-child :L2-await :L2-track])
   :fork [{:ns-per-op 100 :bytes-per-op 100}
          {:ns-per-op 100 :bytes-per-op 100}
          {:ns-per-op 100 :bytes-per-op 100}]
   :enumeration (mapv (fn [k] {:kind k :cycles-per-second 100
                               :points [{:cycles 10000 :gc-stable? true :retained-bytes 1000} {:cycles 100000 :gc-stable? true :retained-bytes 1000}]}) [:fork :spin])})

(deftest gate-boundaries
  (is (every? :pass? (gates/evaluate fixture fixture)))
  (doseq [candidate [(assoc-in fixture [:lifecycle 0 :us-per-spin] 11.01)
                     (assoc-in fixture [:lifecycle 0 :kb-per-spin] (+ 1 (/ 65.0 1024)))
                     (assoc-in fixture [:fork 1 :ns-per-op] 151)
                     (assoc-in fixture [:fork 1 :bytes-per-op] 151)
                     (assoc-in fixture [:fork 2 :ns-per-op] 101)
                     (assoc-in fixture [:fork 2 :bytes-per-op] 101)
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
