(ns org.replikativ.spindel.lifetime.measurement-protocol-test
  (:require [clojure.test :refer [deftest is]]
            [is.simm.partial-cps.async :as cps]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.executor :as ex]
            [org.replikativ.spindel.enum-bench :as enumeration]
            [org.replikativ.spindel.lifecycle-bench :as lifecycle]
            [org.replikativ.spindel.large-parent-bench :as large]
            [org.replikativ.spindel.lifetime-gates-check :as checks]
            [org.replikativ.spindel.lifetime-gate-rules :as rules]
            [org.replikativ.spindel.lifetime-gates :as runner]
            [org.replikativ.spindel.lifetime-load-monitor :as load]
            [org.replikativ.spindel.fork-bench :as fork]
            [clojure.java.shell :as shell]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.engine.core :as ec]))

(deftest measurement-gate-regressions
  ;; Include the pure CLI gate suite in the ordinary JVM test run.
  (clojure.test/test-all-vars 'org.replikativ.spindel.lifetime-gates-check))

(deftest checkpoint-drains-once-between-stabilizations
  (let [stabilize (ns-resolve 'org.replikativ.spindel.enum-bench 'stabilize-gc!)
        drain (ns-resolve 'org.replikativ.spindel.enum-bench 'drain-keyword-interns!)]
    (if (and stabilize drain)
      (let [calls (atom [])]
        (with-redefs-fn {stabilize (fn [_] (swap! calls conj :gc) (checks/stable-point #{}))
                         drain #(swap! calls conj :intern)}
          #(let [point (enumeration/full-gc! nil)]
             (is (= [:gc :intern :gc] @calls))
             (is (:keyword-intern-drained? point))
             (is (rules/gc-stable? (:pre-intern-gc point) #{})))))
      (is false "Checkpoint has no intern-table drain"))))

(deftest lifecycle-keeps-children-and-warmup-handles
  (let [r (lifecycle/run-one :L-child 5 2)]
    (is (= 14 (:retained-handles r)))
    (is (= 0 (:cleanup-calls r)))
    (is (= 15 (:checksum r)))))

(deftest lifecycle-rejects-foreign-cleanup
  (with-redefs-fn {#'org.replikativ.spindel.lifecycle-bench/body-fn
                   (fn [& _]
                     (fn [i]
                       (simple/full-cleanup-spin! ec/*execution-context* :foreign)
                       (simple/full-cleanup-spin! ec/*execution-context* :foreign (constantly true))
                       i))}
    #(let [error (try (lifecycle/run-one :L0 1 0)
                      nil
                      (catch clojure.lang.ExceptionInfo e e))]
       (is (instance? clojure.lang.ExceptionInfo error))
       (when error
         (is (re-find #"Cleanup contaminated" (ex-message error)))
         (is (= 2 (:cleanup-calls (ex-data error))))))))

(deftest large-parent-fixtures-keep-live-parent
  ;; Small operation batch; covers native root/following/frozen paths without
  ;; turning correctness tests into the 10k-node performance measurement.
  (doseq [mode [:root :following :frozen] path [:uncached-await :execution-event]]
    (let [root (ctx/create-execution-context :executor (ex/synchronous-executor))]
      (try
        (binding [ec/*execution-context* root cps/*in-trampoline* false]
          (let [handles (mapv large/fresh-spin (range 3))
                _ (doseq [s handles] @s)
                world (if (= mode :root) root (ctx/fork-context root :mode mode))]
            (try
              (let [r (large/run-batch world path 2)]
                (is (= 3 (:checksum r)))
                (is (= (+ 3 (if (= path :uncached-await) 4 2)) (:nodes-at-start r))))
              (finally (when-not (identical? world root) (ctx/close-context! world))))
            (java.lang.ref.Reference/reachabilityFence handles)))
        (finally (ctx/close-context! root))))))

(deftest window-probes-bracket-work-even-when-it-throws
  (let [events (atom []) active (atom nil)]
    (binding [load/*observe!* (fn [window phase] (swap! events conj [window phase @active]))
              load/*window* "fixture" load/*active-window* active]
      (is (= :result (load/timed #(do (is (= "fixture" @active)) :result))))
      (is (thrown? Exception (load/timed #(throw (Exception. "test"))))))
    (is (= [["fixture" :start nil] ["fixture" :end nil]
            ["fixture" :start nil] ["fixture" :end nil]] @events))
    (is (nil? @active))))

(deftest probes-run-outside-counters-and-only-for-retained-work
  (let [events (atom [])]
    (binding [load/*observe!* (fn [window phase] (swap! events conj [window phase]))
              load/*window* "tiny"]
      (is (= 2 (:operations (fork/measure 2 (fn [i] (swap! events conj [:work i])))))))
    (is (= [["tiny" :start] [:work 0] [:work 1] ["tiny" :end]] @events))
    (reset! events [])
    (with-redefs [enumeration/full-gc! (constantly nil)]
      (binding [load/*observe!* (fn [window phase] (swap! events conj [window phase]))
                load/*window* "lifecycle"]
        (is (= 3 (:retained-handles (lifecycle/run-one :L0 2 1))))))
    (is (= [["lifecycle" :start] ["lifecycle" :end]] @events))))

(deftest runner-observes-both-monitors-with-role-and-window
  (let [observations (atom []) calls (atom [])]
    (with-redefs [shell/sh (fn [& args] (swap! calls conj args) {:exit 0})
                  runner/host-observation (fn [] {:load 1 :uptime "u" :foreign-high-cpu []})]
      (runner/observe! observations :candidate "fixture" :start))
    (is (= "fixture" (:window (first @observations))))
    (is (= :start (:phase (first @observations))))
    (is (contains? (first @observations) :role))
    (is (= ["python3" "dev/lifetime_gate_session.py" "observe"] (take 3 (first @calls))))))
