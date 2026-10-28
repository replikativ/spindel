(ns org.replikativ.spindel.lifetime.check-io
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]))

(def witness-root "org/replikativ/spindel/lifetime/witnesses/")

(defn read-witness [name]
  (edn/read-string (slurp (io/resource (str witness-root name)))))

(defn write-report!
  "Reports go to stdout by default. Set LIFETIME_OUTPUT_DIR to retain EDN."
  [name data]
  (when-let [directory (System/getenv "LIFETIME_OUTPUT_DIR")]
    (let [file (io/file directory name)]
      (io/make-parents file)
      (spit file data))))
