(ns org.replikativ.spindel.engine.delayed-test
  "Regression for the real-time delayed-spin stranding bug.

   `schedule-delayed!` arms an executor timer for `delay-ms`. The timer
   callback used to run `process-delayed-spins!`, which RE-derived
   readiness from `(current-time)`: `(<= fire-time now)`. A `setTimeout`
   (or JVM timer) can fire ~1 ms before the wall clock agrees the delay
   elapsed — so the entry whose own timer just fired was deemed not-ready
   and stranded permanently (it has no other trigger). A stranded `sleep`
   is a `debounce`/`timeout` that never completes — the ~50 % CLJS
   rate-control flake.

   `fire-delayed-spin!` fixes it: the executor timer that fires for an
   entry runs THAT entry authoritatively, with no wall-clock re-check.
   The wall-clock comparison stays only on the virtual-time path
   (`advance-virtual-time!`), where `current-time` is set explicitly."
  (:require #?(:clj  [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.executor :as executor]
            [org.replikativ.spindel.engine.impl.delayed :as delayed]))

(deftest real-timer-fires-its-entry-regardless-of-wall-clock
  ;; A synchronous executor runs execute-after! / execute! inline, so the
  ;; whole schedule → timer → fire → run chain completes deterministically
  ;; within schedule-delayed!.
  (let [ec  (ctx/create-execution-context {:executor (executor/synchronous-executor)})
        ran (atom false)]
    (try
      (delayed/set-time-mode! ec :real)
      ;; A 100 s delay: when the (synchronous) timer callback runs, the
      ;; wall clock is ~100 s short of fire-time. The old
      ;; process-delayed-spins! recheck — (<= fire-time now) — would strand
      ;; this entry; fire-delayed-spin! must run it anyway, because the
      ;; timer firing IS the signal that the delay elapsed.
      (delayed/schedule-delayed! ec 100000 (fn [] (reset! ran true)))
      (is (true? @ran)
          "a delayed spin must fire when its executor timer fires — not be re-gated on wall-clock time")
      (finally
        (ctx/stop-context! ec)))))
