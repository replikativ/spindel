(ns org.replikativ.spindel.test-async
  "Async test utilities for spindel.

  Provides await-drain for waiting for reactive event processing to complete."
  (:require [org.replikativ.spindel.runtime.impl.simple :as simple]))

(defn await-drain
  "Wait for async drain to complete on the given execution context.

  Waits until all pending events are processed and the event queue is empty.
  This is essential for tests that trigger signal changes and need to verify
  the resulting state after reactive propagation.

  Args:
    context - Execution context (from ctx/create-execution-context)
    timeout-ms - Optional timeout in milliseconds (default 5000)

  Returns: true if drain completed, false if timed out"
  ([context]
   (await-drain context 5000))
  ([context timeout-ms]
   (simple/await-drain-complete! context :timeout-ms timeout-ms)))
