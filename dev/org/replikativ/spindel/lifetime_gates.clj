(ns org.replikativ.spindel.lifetime-gates
  "Session entry: exclusive.sh LABEL python3 dev/lifetime_gate_session.py OUTPUT.
   Worker modes: measure output.edn | check paired-baseline.edn candidate.edn.
   A baseline is a measurement, never an exemption from absolute gates."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.java.shell :as shell]
            [clojure.string :as str]
            [org.replikativ.spindel.enum-bench :as enumeration]
            [org.replikativ.spindel.fork-bench :as fork]
            [org.replikativ.spindel.lifecycle-bench :as lifecycle]
            [org.replikativ.spindel.large-parent-bench :as large-parent]
            [org.replikativ.spindel.lifetime-gate-rules :as rules]
            [org.replikativ.spindel.lifetime-load-monitor :as load]))

(defn host-observation []
  (let [pid (.pid (java.lang.ProcessHandle/current))
        processes (str/split-lines (:out (shell/sh "ps" "-eo" "pid=,pcpu=,comm=" "--sort=-pcpu")))]
    {:at (str (java.time.Instant/now))
     :uptime (str/trim (:out (shell/sh "uptime")))
     :load (.getSystemLoadAverage (java.lang.management.ManagementFactory/getOperatingSystemMXBean))
     :foreign-high-cpu (vec (filter (fn [line]
                                      (let [[p cpu] (str/split (str/trim line) #"\s+")]
                                        (and (not= (str pid) p) (>= (Double/parseDouble cpu) 50.0)))) processes))}))

(declare observe!)

(defn measure-report! [output observations]

  (when-not (and (= (* 3 1024 1024 1024) (.maxMemory (Runtime/getRuntime)))
                 (.exists (io/file "/tmp/claude-1000/jvm.lock/owner")))
    (throw (ex-info "Measurements require exclusive.sh and -J-Xmx3g" {})))
  (let [revision (or (System/getenv "SPINDEL_BENCH_REVISION") "HEAD")
        metadata {:revision (str/trim (:out (shell/sh "git" "rev-parse" revision)))
                  :source-revision (str/trim (:out (shell/sh "git" "rev-parse" (str revision ":src"))))
                  :runtime-base (str/trim (:out (shell/sh "git" "log" "-1" "--format=%h" revision "--" "src")))
                  :machine (.getHostName (java.net.InetAddress/getLocalHost))
                  :os (System/getProperty "os.name") :arch (System/getProperty "os.arch")
                  :java (System/getProperty "java.version") :java-vendor (System/getProperty "java.vendor")
                  :os-version (System/getProperty "os.version")
                  :jvm-options (vec (.getInputArguments (java.lang.management.ManagementFactory/getRuntimeMXBean)))
                  :protocol-version rules/protocol-version :measurement-protocol rules/measurement-protocol
                  :max-heap-bytes (.maxMemory (Runtime/getRuntime))
                  :processors (.availableProcessors (Runtime/getRuntime))
                  :session {:id (System/getenv "SPINDEL_BENCH_SESSION")
                            :round (Long/parseLong (System/getenv "SPINDEL_BENCH_ROUND"))
                            :position (Long/parseLong (System/getenv "SPINDEL_BENCH_POSITION"))
                            :role (keyword (System/getenv "SPINDEL_BENCH_ROLE"))}
                  :executor :synchronous :allocation :calling-thread-live-handles
                  :admission :exclusive :measured-at (str (java.time.Instant/now))}
        ;; Warm every lifecycle shape before collecting any sample. Repeated
        ;; samples use median time, rather than counting class loading as work.
        _ (doseq [k [:L0 :L-child :L2-await :L2-track]] (lifecycle/run-one k (get-in rules/measurement-protocol [:lifecycle :warm-shapes]) 2000))
        life (mapv (fn [k]
                     (let [samples (mapv (fn [i] (binding [load/*window* (pr-str [:lifecycle k i])]
                                                     (lifecycle/run-one k 5000 2000))) (range 3))
                           r (assoc (nth (sort-by :us-per-spin samples) 1)
                                    :kb-per-spin (second (sort (map :kb-per-spin samples))))]
                       (prn r) (flush) (assoc r :samples samples))) [:L0 :L-child :L2-await :L2-track])
        large (large-parent/benchmark)
        forks (fork/benchmark)
        enums (enumeration/benchmark)
        _ (observe! observations (get-in metadata [:session :role]) "worker" :end)
        report (assoc metadata :lifecycle life :large-parent large :fork forks :enumeration enums
                      :host-observations @observations
                      :record-only? true)]
    (io/make-parents output)
    (spit output (str (pr-str report) "\n"))
    report))

(defn observe! [observations role window phase]
  ;; The controller probe is a separate process reading host load/ps itself.
  ;; Both probes finish before timed counters start, or after they stop.
  (let [external (shell/sh "python3" "dev/lifetime_gate_session.py" "observe"
                           (System/getenv "SPINDEL_BENCH_HOST_LOG") (name role) window (name phase)
                           (str (.pid (java.lang.ProcessHandle/current))))]
    (when-not (zero? (:exit external))
      (throw (ex-info "Controller window observation failed" external)))
    (swap! observations conj (assoc (host-observation) :window window :phase phase :role role))))

(defn measure! [output]
  (let [observations (atom [])
        role (keyword (System/getenv "SPINDEL_BENCH_ROLE"))
        active-window (atom nil)
        running? (atom true)]
    (observe! observations role "worker" :start)
    (let [monitor (future
                    (while @running?
                      (Thread/sleep 5000)
                      (when @running?
                        (swap! observations conj (assoc (host-observation) :window (or @active-window "worker") :phase :sample :role role)))))]
      (try
        (binding [load/*observe!* (partial observe! observations role)
                  load/*active-window* active-window]
          (measure-report! output observations))
        (finally (reset! running? false) @monitor)))))

(defn -main [& [mode baseline-file candidate-file]]
  (case mode
    "measure" (measure! baseline-file)
    "check" (let [results (rules/evaluate (edn/read-string (slurp baseline-file))
                                          (edn/read-string (slurp candidate-file)))]
              (doseq [r results] (prn r))
              (shutdown-agents)
              (when-not (every? :pass? results) (System/exit 1))))
  (shutdown-agents))
