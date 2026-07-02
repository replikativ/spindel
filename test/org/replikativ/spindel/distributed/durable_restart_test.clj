(ns org.replikativ.spindel.distributed.durable-restart-test
  "Durability guarantee for the sync substrate: a CRDT flushed to a file-backed store
   is fully readable after a COLD RESTART — a fresh store handle (empty caches) reopened
   from the same path, and (the strongest form) a fresh OS process that never touched
   the write. This is the 'everything is stored' half of the unified model: konserve-sync
   ships content-addressed nodes + the `:crdt/roots` head cell, and reopening resolves
   the whole value from disk, not from any in-memory cache."
  (:require [clojure.test :refer [deftest testing is]]
            [clojure.java.io :as io]
            [clojure.java.shell :refer [sh]]
            [yggdrasil.convergent.gset :as g]))

(defn- temp-dir [prefix]
  (.getAbsolutePath (io/file (System/getProperty "java.io.tmpdir")
                             (str prefix "-" (System/currentTimeMillis) "-" (rand-int 100000)))))

(defn- rm-rf [path]
  (let [d (io/file path)]
    (when (.exists d) (doseq [f (reverse (file-seq d))] (.delete f)))))

(deftest fresh-handle-reopen-reads-back
  (testing "a flushed file-backed G-Set is readable from a BRAND-NEW store handle
            (fresh KonserveStorage + PSS caches) reopened from the same path — no
            in-process cache is masking the on-disk state"
    (let [path (temp-dir "restart-fh")
          id   #uuid "d0000000-0000-0000-0000-0000000000e1"
          cfg  {:backend :file :path path :id id}]
      (try
        ;; phase 1: write + flush, then DROP every reference to the store.
        (let [g1 (-> (g/gset (str id) {:store-config cfg} {:sync? true})
                     (g/conj :alpha) (g/conj :beta) (g/conj :gamma) (g/flush!))]
          (is (= #{:alpha :beta :gamma} (g/elements g1)) "written value holds all three"))
        ;; phase 2: a COMPLETELY fresh G-Set over a fresh store opened from the path.
        ;; g/gset with store-config opens a new konserve store (new storage, empty cache)
        ;; and loads :crdt/roots from disk — so this read cannot come from phase-1 state.
        (let [g2 (g/gset (str id) {:store-config cfg} {:sync? true})]
          (is (= #{:alpha :beta :gamma} (g/elements g2))
              "reopened value reconstructs identically from disk"))
        (finally (rm-rf path))))))

;; The write form run in a SEPARATE `clojure` process (fresh JVM) against ../yggdrasil,
;; so the test JVM never touches the nodes/caches — a real cross-process durability proof.
(defn- write-in-subprocess-form [id path]
  (pr-str
   `(do (require '[yggdrasil.convergent.gset :as ~'g])
        (-> (~'g/gset ~(str id) {:store-config {:backend :file :path ~path :id ~id}} {:sync? true})
            (~'g/conj :one) (~'g/conj :two) (~'g/conj :three) (~'g/flush!))
        (println "SUBPROC-WROTE"))))

(deftest separate-process-write-then-read
  (testing "a fresh JVM writes + flushes the G-Set; THIS JVM (which never saw the write)
            reopens from the path and reads it back — no shared in-memory cache anywhere"
    (let [path (temp-dir "restart-sp")
          id   #uuid "d0000000-0000-0000-0000-0000000000e2"
          cfg  {:backend :file :path path :id id}
          ;; run the writer in ../yggdrasil so it uses yggdrasil's own classpath.
          {:keys [exit out err]} (sh "clojure" "-M" "-e" (write-in-subprocess-form id path)
                                     :dir "../yggdrasil")]
      (try
        (is (zero? exit) (str "subprocess writer exited cleanly; out=" out " err=" err))
        (is (re-find #"SUBPROC-WROTE" (str out)) "subprocess reported it wrote")
        (let [g (g/gset (str id) {:store-config cfg} {:sync? true})]
          (is (= #{:one :two :three} (g/elements g))
              "this JVM read the OTHER process's flushed G-Set from disk"))
        (finally (rm-rf path))))))
