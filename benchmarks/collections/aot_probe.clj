(ns aot-probe
  (:require [collection-bench :as bench]
            [clojure.data.json :as json])
  (:import [java.nio.file Files]))

(defn probe [n]
  (let [vars (mapv #(symbol (str "v" %)) (range n))
        body (list 'let (vec (mapcat (fn [v i] [v (list 'await (list 'step i))]) vars (range n))) (last vars))
        lowered (bench/lower body)
        directory (.toFile (Files/createTempDirectory "collection-aot-probe-"
                                                      (make-array java.nio.file.attribute.FileAttribute 0)))]
    (try
      (binding [*compile-files* true *compile-path* (.getPath directory)]
        (bench/compile-lowered lowered))
      {:sites n :class-file-export :ok}
      (catch Exception error
        (let [cause (last (take-while some? (iterate ex-cause error)))]
          {:sites n :class-file-export :failed
           :error-class (str (class cause)) :message (.getMessage cause)}))
      (finally
        (doseq [file (reverse (file-seq directory))] (.delete file))))))

(defn -main [output]
  (spit output (json/write-str (mapv probe [8 32 96])))
  (shutdown-agents))
