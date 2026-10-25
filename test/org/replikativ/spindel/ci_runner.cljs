(ns org.replikativ.spindel.ci-runner
  "CI-only console threshold; retain shadow's CLI, reporting and exit status."
  {:dev/always true}
  (:require [shadow.test.env :as env]
            [shadow.test.node :as node]
            [taoensso.trove :as trove]
            [taoensso.trove.console :as console]))

(defn main [& args]
  (trove/set-log-fn! (console/get-log-fn {:min-level :warn}))
  ;; Expand test discovery in this runner, after shadow has compiled the tests.
  (env/reset-test-data! (env/get-test-data))
  (node/execute-cli (node/parse-args args)))
