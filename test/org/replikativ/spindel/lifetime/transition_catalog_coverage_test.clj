(ns org.replikativ.spindel.lifetime.transition-catalog-coverage-test
  (:require [clojure.set :as set]
            [clojure.test :as test :refer [deftest is]]
            [org.replikativ.spindel.lifetime.model :as m]
            [org.replikativ.spindel.lifetime.transition-catalog :as catalog]
            [org.replikativ.spindel.engine.computation-invalidation-test]
            [org.replikativ.spindel.engine.public-cancellation-model-test]
            [org.replikativ.spindel.engine.signal-publication-model-test]
            [org.replikativ.spindel.engine.deferred-model-test]
            [org.replikativ.spindel.lifetime.managed-cells-test]
            [org.replikativ.spindel.lifetime.mailbox-model-test]
            [org.replikativ.spindel.lifetime.operation-model-test]
            [org.replikativ.spindel.lifetime.timer-model-test]
            [org.replikativ.spindel.lifetime.release-model-test]))

(def fixture-namespaces
  '[org.replikativ.spindel.engine.computation-invalidation-test
    org.replikativ.spindel.engine.public-cancellation-model-test
    org.replikativ.spindel.engine.signal-publication-model-test
    org.replikativ.spindel.engine.deferred-model-test
    org.replikativ.spindel.lifetime.managed-cells-test
    org.replikativ.spindel.lifetime.mailbox-model-test
    org.replikativ.spindel.lifetime.operation-model-test
    org.replikativ.spindel.lifetime.timer-model-test
    org.replikativ.spindel.lifetime.release-model-test])

(defn- current-test-name []
  (when-let [v (first test/*testing-vars*)]
    (let [{:keys [ns name]} (meta v)]
      (symbol (str (ns-name ns)) (str name)))))

(deftest resource-transition-catalog-has-executed-evidence
  (is (empty? (catalog/errors (set (keys m/transitions)))))
  (let [observed (atom {:accepted #{} :refusals #{}})
        original-step m/step
        tests (for [namespace fixture-namespaces
                    v (vals (ns-publics namespace)) :when (:test (meta v))] v)]
    (is (seq tests))
    ;; These are pure model/kernel fixture tests, with no recursive harness
    ;; imports. with-redefs restores the original model entry point on every exit.
    (with-redefs [m/step
                  (fn [s action]
                    (try
                      (let [after (original-step s action)]
                        (when (catalog/all-transitions (:t action))
                          (swap! observed update :accepted conj (:t action)))
                        after)
                      (catch clojure.lang.ExceptionInfo e
                        (when (= s (:state (ex-data e)))
                          (swap! observed update :refusals conj
                                 {:transition (:t action) :test (current-test-name)
                                  :error (:error (ex-data e)) :unchanged? true}))
                        (throw e))))]
      (test/test-vars tests))
    (let [accepted (:accepted @observed)
          required (set/difference catalog/resource-transitions (set (keys catalog/refusal-only)))
          covered (set/intersection accepted catalog/resource-transitions)]
      (println "LIFETIME RESOURCE-TRANSITION-COVERAGE" (pr-str covered))
      (is (= required covered)
          (pr-str {:missing (set/difference required covered)
                   :unexpected-positive (set/difference covered required)}))
      (doseq [[transition {:keys [test error]}] catalog/refusal-only]
        (is (contains? (:refusals @observed)
                       {:transition transition :test test :error error :unchanged? true})
            (str "Missing named unchanged-state refusal evidence: " transition " " test))))))
