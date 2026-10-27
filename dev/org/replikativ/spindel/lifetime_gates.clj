(ns org.replikativ.spindel.lifetime-gates
  "Run under exclusive.sh with -J-Xmx3g -M:bench -m ...lifetime-gates
   measure output.edn | check baseline.edn candidate.edn.
   A baseline is a measurement, never an exemption from absolute gates."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.java.shell :as shell]
            [clojure.string :as str]
            [org.replikativ.spindel.enum-bench :as enumeration]
            [org.replikativ.spindel.fork-bench :as fork]
            [org.replikativ.spindel.lifecycle-bench :as lifecycle]
            [org.replikativ.spindel.lifetime-gate-rules :as rules]))

(defn measure! [output]
  (when-not (and (= (* 3 1024 1024 1024) (.maxMemory (Runtime/getRuntime)))
                 (.exists (io/file "/tmp/claude-1000/jvm.lock/owner")))
    (throw (ex-info "Measurements require exclusive.sh and -J-Xmx3g" {})))
  (let [metadata {:revision (str/trim (:out (shell/sh "git" "rev-parse" "HEAD")))
                  :source-revision (str/trim (:out (shell/sh "git" "rev-parse" "HEAD:src")))
                  :runtime-base (str/trim (:out (shell/sh "git" "log" "-1" "--format=%h" "--" "src")))
                  :machine (.getHostName (java.net.InetAddress/getLocalHost))
                  :os (System/getProperty "os.name") :arch (System/getProperty "os.arch")
                  :java (System/getProperty "java.version") :java-vendor (System/getProperty "java.vendor")
                  :os-version (System/getProperty "os.version")
                  :jvm-options (vec (.getInputArguments (java.lang.management.ManagementFactory/getRuntimeMXBean)))
                  :protocol-version rules/protocol-version :measurement-protocol rules/measurement-protocol
                  :max-heap-bytes (.maxMemory (Runtime/getRuntime))
                  :processors (.availableProcessors (Runtime/getRuntime))
                  :executor :synchronous :allocation :calling-thread
                  :admission :exclusive :measured-at (str (java.time.Instant/now))}
        ;; Warm every lifecycle shape before collecting any sample. Repeated
        ;; samples use median time, rather than counting class loading as work.
        _ (doseq [k [:L0 :L-child :L2-await :L2-track]] (lifecycle/run-one k 1000 1000))
        life (mapv (fn [k]
                     (let [samples (vec (repeatedly 3 #(lifecycle/run-one k 5000 2000)))
                           r (nth (sort-by :us-per-spin samples) 1)]
                       (prn r) (flush) (assoc r :samples samples))) [:L0 :L-child :L2-await :L2-track])
        forks (fork/benchmark)
        enums (enumeration/benchmark)
        report (assoc metadata :lifecycle life :fork forks :enumeration enums)
        gates (rules/evaluate report report)
        report (assoc report :gates gates)]
    (io/make-parents output)
    (spit output (str (pr-str report) "\n"))
    (doseq [gate gates] (prn gate))
    report))

(defn -main [& [mode baseline-file candidate-file]]
  (case mode
    "measure" (measure! baseline-file)
    "check" (let [results (rules/evaluate (edn/read-string (slurp baseline-file))
                                          (edn/read-string (slurp candidate-file)))]
              (doseq [r results] (prn r))
              (shutdown-agents)
              (when-not (every? :pass? results) (System/exit 1))))
  (shutdown-agents))
