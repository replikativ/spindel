(ns org.replikativ.spindel.engine.timer-disposal-test
  "Regression for resource-timer disposal (engine-sharpening Step B2).

  A `sleep` (a `:resource` spin) arms an executor timer via
  `schedule-delayed!`. The timer handle — a JVM `ScheduledFuture` or a
  JS `setTimeout` id — used to be discarded: `execute-after!`'s return
  value was dropped, so a completed or cancelled `sleep` left a pending
  `setTimeout` / `ScheduledFuture` that only `alive-fn` later swallowed.

  The fix: `execute-after!` returns its handle, `schedule-delayed!`
  retains it in `[:engine/timer-handles spin-id]`, and the handle is
  cancelled — `clearTimeout` / `ScheduledFuture.cancel` — when the
  delayed spin fires, is cancelled, or its context stops.

  Each test arms a 100 s timer (which never fires within the test) on a
  real executor, then exercises one disposal path. The cross-platform
  assertion is the `[:engine/timer-handles]` state invariant; on the JVM
  the test also asserts the concrete `ScheduledFuture` is cancelled,
  which `clearTimeout` does not expose on JS."
  (:require #?(:clj  [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.impl.delayed :as delayed]))

;; A long delay so the armed timer never fires during the test — only
;; the explicit disposal path under test releases it.
(def ^:private long-delay-ms 100000)

(defn- timer-handle [ec spin-id]
  (rtp/get-state ec [:engine/timer-handles spin-id]))

#?(:clj
   (defn- jvm-cancelled? [handle]
     ;; schedule-delayed! arms via ScheduledExecutorService.schedule,
     ;; whose return is a ScheduledFuture — cancellation is observable.
     (and (instance? java.util.concurrent.Future handle)
          (.isCancelled ^java.util.concurrent.Future handle))))

(deftest schedule-delayed-retains-the-timer-handle
  (testing "schedule-delayed! retains the armed timer handle in :engine/timer-handles"
    (let [ec (ctx/create-execution-context)]
      (try
        (delayed/set-time-mode! ec :real)
        (let [spin-id (delayed/schedule-delayed! ec long-delay-ms (fn [] nil))]
          (is (some? (timer-handle ec spin-id))
              "the armed timer handle must be retained, not discarded"))
        (finally
          (ctx/stop-context! ec))))))

(deftest cancel-delayed-spin-releases-the-timer-handle
  (testing "cancel-delayed-spin! detaches and cancels the pending timer"
    (let [ec (ctx/create-execution-context)]
      (try
        (delayed/set-time-mode! ec :real)
        (let [spin-id (delayed/schedule-delayed! ec long-delay-ms (fn [] nil))
              handle  (timer-handle ec spin-id)]
          (is (some? handle) "handle retained while pending")
          (delayed/cancel-delayed-spin! ec spin-id)
          (is (nil? (timer-handle ec spin-id))
              "a cancelled delayed spin must leave no timer handle behind")
          #?(:clj
             (is (jvm-cancelled? handle)
                 "the underlying ScheduledFuture must be cancelled")))
        (finally
          (ctx/stop-context! ec))))))

(deftest stop-context-cancels-all-pending-timers
  (testing "stop-context! cancels and clears every pending timer handle"
    (let [ec (ctx/create-execution-context)]
      (delayed/set-time-mode! ec :real)
      (let [id-a (delayed/schedule-delayed! ec long-delay-ms (fn [] nil))
            id-b (delayed/schedule-delayed! ec long-delay-ms (fn [] nil))
            handle-a (timer-handle ec id-a)
            handle-b (timer-handle ec id-b)]
        (is (= 2 (count (rtp/get-state ec [:engine/timer-handles])))
            "both timers retained while the context is alive")
        (ctx/stop-context! ec)
        (is (empty? (rtp/get-state ec [:engine/timer-handles]))
            "stop-context! must clear all retained timer handles")
        #?(:clj
           (do
             (is (jvm-cancelled? handle-a))
             (is (jvm-cancelled? handle-b))))))))

(deftest cancel-all-timers-counts-released-handles
  (testing "cancel-all-timers! reports how many handles it released and empties the map"
    (let [ec (ctx/create-execution-context)]
      (try
        (delayed/set-time-mode! ec :real)
        (dotimes [_ 3]
          (delayed/schedule-delayed! ec long-delay-ms (fn [] nil)))
        (is (= 3 (delayed/cancel-all-timers! ec)))
        (is (empty? (rtp/get-state ec [:engine/timer-handles]))
            ":engine/timer-handles is empty after cancel-all-timers!")
        ;; Idempotent — nothing left to release.
        (is (zero? (delayed/cancel-all-timers! ec)))
        (finally
          (ctx/stop-context! ec))))))

(deftest fired-delayed-spin-leaves-no-leaked-handle
  (testing "a fired delayed spin removes its own timer handle"
    (let [ec (ctx/create-execution-context)]
      (try
        (delayed/set-time-mode! ec :real)
        (let [spin-id (delayed/schedule-delayed! ec long-delay-ms (fn [] nil))
              handle  (timer-handle ec spin-id)]
          (is (some? handle) "handle retained while pending")
          ;; Simulate the executor timer firing for this entry — the same
          ;; call schedule-delayed! hands to execute-after! as the timer
          ;; callback. fire-delayed-spin! must detach AND cancel the
          ;; handle (the timer has fired, so the cancel is a harmless
          ;; resource release — the entry must not leak either way).
          (delayed/fire-delayed-spin! ec (:executor ec) spin-id)
          (is (nil? (timer-handle ec spin-id))
              "a fired delayed spin must not leak its timer handle")
          #?(:clj
             (is (jvm-cancelled? handle)
                 "the fired entry's ScheduledFuture is released")))
        (finally
          (ctx/stop-context! ec))))))
