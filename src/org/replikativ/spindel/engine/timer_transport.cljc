(ns org.replikativ.spindel.engine.timer-transport
  "Internal capture-free timer transport for the native engine.

  Engine registrations own logical revocation, callback admission and physical
  return. This layer only requests a delay and hands readiness to a neutral
  worker. A cancelled platform handle does not prove that queued or running
  wrappers have disappeared. Supplied callbacks must contain only weak engine
  references and immutable IDs; no application bindings are captured here."
  (:require [org.replikativ.spindel.engine.executor :as executor]
            [org.replikativ.spindel.engine.fault :as fault])
  #?(:clj (:import [java.util.concurrent ForkJoinPool])))

(def ^:no-doc default-transport
  ;; The common pool is borrowed, shared and never closed by a native world.
  ;; Direct execute deliberately bypasses PExecutor's binding capture. The
  ;; single daemon delay service only submits work, never drains a world.
  {:schedule executor/schedule-native-delay!
   :cancel executor/cancel-timer-handle!
   :submit #?(:clj (fn [task] (.execute (ForkJoinPool/commonPool) ^Runnable task))
              :cljs (fn [task] (task)))})

(defn ^:no-doc schedule-native-timer!
  "Schedule a weak-ID readiness callback using an internal transport.

  A transport supplies :schedule (delay-ms dispatch), :submit (worker), and
  :cancel (handle). Test drivers may retain inert wrappers and invoke them
  after cancellation: engine admission must make revoked IDs harmless.
  Submission rejection reports a fault and invokes failed(error) once, unless
  the worker already entered ready. The engine must fence both weak-ID callbacks.
  A throw from ready only reports a fault; it never changes the chosen outcome.
  Scheduling failures propagate to the installer, which owns its physical frame."
  [transport delay-ms ready failed]
  (let [submit (:submit transport)
        entered? (atom false)
        worker (executor/guard-task
                (fn [] (when (compare-and-set! entered? false true) (ready))))
        dispatch (executor/guard-task
                  (fn []
                    (try (submit worker)
                         (catch #?(:clj Throwable :cljs :default) error
                           #?(:clj (when (instance? InterruptedException error)
                                     (.interrupt (Thread/currentThread))))
                           (fault/report-fault! ::fault/executor-task-fault {:error error :site :native-timer-submit})
                           (when (compare-and-set! entered? false true)
                             ((executor/guard-task (fn [] (failed error)))))))))]
    ((:schedule transport) delay-ms dispatch)))

(defn ^:no-doc cancel-native-timer!
  "Request platform cancellation without claiming physical task shutdown."
  [transport handle]
  ((:cancel transport) handle)
  nil)
