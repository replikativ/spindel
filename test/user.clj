(ns user
  "Auto-loaded namespace for test configuration.

  Configures logging to be quiet by default during tests.

  To enable logging for debugging:
  - Set env var SPINDEL_TEST_LOG=true
  - Or call (is.simm.spindel.test-config/enable-test-logging!) from REPL"
  (:require [is.simm.spindel.test-config]))

;; test-config handles all initialization at load time
