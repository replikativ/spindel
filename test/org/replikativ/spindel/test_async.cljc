(ns org.replikativ.spindel.test-async
  "Async test utilities for spindel.

  Provides await-drain for waiting for reactive event processing to complete."
  (:require [org.replikativ.spindel.engine.impl.simple :as simple]))

(defn await-drain
  "Wait for async drain to complete on the given execution context.

  Waits until all pending events are processed and the event queue is empty.
  This is essential for tests that trigger signal changes and need to verify
  the resulting state after reactive propagation.

  STRICT: throws ex-info if drain does not complete within `timeout-ms`.
  Previously this silently returned `false` on timeout and most callers
  ignored the return value, hiding load-related races behind a fixed
  budget. Throwing surfaces those races as actual test failures.

  Args:
    context    - Execution context (from ctx/create-execution-context)
    timeout-ms - Optional timeout in milliseconds (default 5000)

  Returns: true on successful drain.
  Throws:  ex-info {:type ::drain-timeout :context-fork-id …} on timeout."
  ([context]
   (await-drain context 5000))
  ([context timeout-ms]
   (or (simple/await-drain-complete! context :timeout-ms timeout-ms)
       (throw (ex-info (str "await-drain did not complete within " timeout-ms "ms")
                       {:type ::drain-timeout
                        :context-fork-id (:fork-id context)
                        :timeout-ms timeout-ms})))))
