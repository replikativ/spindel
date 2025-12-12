(ns is.simm.spindel.test-config
  "Test configuration that runs before all tests.

  By default, suppresses all logging during tests to avoid verbose output.

  To enable logging:
  - Set env var SPINDEL_TEST_LOG=true for all logging
  - Set env var SPINDEL_TEST_LOG=ns1,ns2 for specific namespaces
  - Call (enable-test-logging!) from REPL"
  (:require [is.simm.spindel.log :as log]))

(def ^:private test-log-config
  "Parse SPINDEL_TEST_LOG environment variable.
  Returns nil (disabled), :all (all logging), or set of namespace symbols."
  (when-let [v (System/getenv "SPINDEL_TEST_LOG")]
    (if (= v "true")
      :all
      (set (map symbol (clojure.string/split v #","))))))

(defn enable-test-logging!
  "Enable logging during tests.
  Optional min-level defaults to :debug."
  ([] (enable-test-logging! :debug))
  ([min-level]
   (log/configure! {:min-level min-level})))

(defn disable-test-logging!
  "Disable logging during tests (set to :fatal level)."
  []
  (log/configure! {:min-level :fatal}))

;; Initialize logging based on environment
(if test-log-config
  (do
    (println "Test logging enabled via SPINDEL_TEST_LOG")
    (enable-test-logging!))
  (disable-test-logging!))
