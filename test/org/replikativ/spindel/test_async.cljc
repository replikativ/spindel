(ns org.replikativ.spindel.test-async
  "Async test utilities for spindel.

  Provides `await-drain` for waiting for reactive event processing to complete,
  plus a `deftest-async`/`<?`/`sync?` trio (ported from `yggdrasil.test-async`)
  for portable tests over the partial-cps `async+sync` substrate: ONE test body
  runs synchronously on the JVM (durable ops opened `:sync? true` return values)
  and as a single partial-cps `async` block on cljs (each durable op suspends on
  konserve IO). Wrap ONLY genuinely-async ops in `<?` (on cljs `await` on a
  non-CPS value errors); thread `sync?` into the durable factory's `:sync?`."
  (:require [org.replikativ.spindel.engine.impl.simple :as simple]
            #?(:clj  [clojure.test]
               :cljs [cljs.test])
            [is.simm.partial-cps.async])
  #?(:cljs (:require-macros [org.replikativ.spindel.test-async]
                            [is.simm.partial-cps.async])))

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

;; =============================================================================
;; Portable async-test trio (partial-cps async+sync) — see yggdrasil.test-async
;; =============================================================================

(defn- cljs-env? [env] (some? (:ns env)))

(def sync?
  "Platform default sync-mode for durable ops: `true` (blocking values) on the
   JVM, `false` (partial-cps CPS) on cljs. Thread into a durable factory's
   `:sync?` so the record carries the right mode."
  #?(:clj true :cljs false))

#?(:clj
   (defmacro <?
     "Resolve an async durable op portably. On cljs, `await` the partial-cps CPS
      (valid only inside a `deftest-async` body's `async` block). On the JVM the op
      already returned its value (sync mode) so this is identity. Wrap ONLY async
      ops — awaiting a plain value errors on cljs."
     [x]
     (if (cljs-env? &env)
       `(is.simm.partial-cps.async/await ~x)
       x)))

#?(:clj
   (defmacro deftest-async
     "Like `clojure.test/deftest`, but the body may use `<?` to resolve async
      durable (partial-cps) ops uniformly. On the JVM the body runs synchronously in
      a plain `deftest` (`<?` is identity). On cljs the body is driven as ONE
      partial-cps `async` block under `cljs.test/async`, so each `<?` suspends on
      konserve IO and the test completes via `done`."
     [tname & body]
     (if (cljs-env? &env)
       `(cljs.test/deftest ~tname
          (cljs.test/async done#
                           ;; Reset `*in-trampoline*` at this foreign-driver boundary so the
                           ;; next cljs.test block self-trampolines (see yggdrasil.test-async).
                           (let [done!# (fn []
                                          (binding [is.simm.partial-cps.async/*in-trampoline* false]
                                            (done#)))]
                             ((is.simm.partial-cps.async/async
                               (try ~@body
                                    (catch :default e#
                                      (cljs.test/is false (str "deftest-async threw: "
                                                               (or (.-message e#) e#) "\n"
                                                               (.-stack e#))))))
                              (fn [_#] (done!#))
                              (fn [e#]
                                (cljs.test/is false (str "deftest-async rejected: "
                                                         (or (.-message e#) e#) "\n"
                                                         (when (and e# (.-stack e#)) (.-stack e#))))
                                (done!#))))))
       `(clojure.test/deftest ~tname ~@body))))
