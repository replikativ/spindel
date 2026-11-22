;; Naming pass, the gate (babashka): after the substitution, no old name is left.
;;
;;   cd formal && bb dev/naming/stale.clj
;;
;; Looks for whole-symbol occurrences of the old names of notes/renames.edn (those that are not
;; also new names) in src/, test/, README.md and notes/ (not notes/history, not the map itself),
;; with the substitution's own reading of the text: a local, a constructor in a pattern and an
;; English word outside backticks are not the name. README's "Old kernel names" section is the one
;; place that may name them.
(require '[clojure.edn :as edn] '[clojure.java.io :as io] '[clojure.string :as str])
(load-file "dev/naming/lex.clj")
(load-file "dev/naming/scope.clj")
(def ren (edn/read-string (slurp "notes/renames.edn")))
(def m (into {} (for [k [:definitions :theorems :generated] [o v] (ren k)] [(str o) (str v)])))
(def m (merge m (into {} (for [[o v] (:clojure-vars ren)] [(str o) (str v)]))))
(def keyset (set (remove (set (vals m)) (keys m))))
(def ctor-shorts (set (for [[n k] (:constants (edn/read-string (slurp "dev/naming/out/model.edn"))) :when (= k :ctor)]
                        (last (str/split n #"\.")))))
(def prose-words #{"post" "finish" "retire" "dispatch" "raw" "inv" "marks" "live" "chain" "admit" "transition"})
(defn files-under [dir ext]
  (->> (file-seq (io/file dir)) (filter #(and (.isFile %) (str/ends-with? (str %) ext))) (map str) sort))
(def files (concat (files-under "src" ".clj") (files-under "test" ".clj") ["README.md"]
                   (->> (mapcat #(files-under "notes" %) [".md" ".clj" ".edn"])
                        (remove #(or (str/includes? % "notes/history/") (str/ends-with? % "notes/renames.edn"))))))
(defn old-names-section
  "[start end) of README's section headed 'Old kernel names', or nil."
  [f s]
  (when (= f "README.md")
    (let [a (.indexOf ^String s "\n## Old kernel names")]
      (when-not (neg? a)
        (let [b (.indexOf ^String s "\n## " (int (+ a 5)))] [a (if (neg? b) (count s) b)])))))
(def hits
  (vec (for [f files
             :let [s (slurp f) code? (boolean (re-find #"\.(clj|edn)$" f))
                   regs (if code? (lex/regions s) (lex/md-regions s))
                   sc (when code? (scope/offsets s))
                   idx (lex/line-index s) sec (old-names-section f s)]
             {:keys [name start kind backtick?]} (lex/occurrences s regs keyset)
             :when (not (and sec (<= (first sec) start) (< start (second sec))))
             :when (if (= kind :code)
                     (case (get sc start) :local false :constructor (not (ctor-shorts name)) true)
                     (not (and (prose-words name) (not backtick?))))]
         [f (lex/line-at idx start) name start])))
;; --fix: replace what is left (the same replacement `renames.clj --apply` makes from a clean tree)
(when (some #{"--fix"} *command-line-args*)
  (doseq [[f hs] (group-by first hits)]
    (let [sb (StringBuilder. ^String (slurp f))]
      (doseq [[_ _ n start] (sort-by #(nth % 3) > hs)] (.replace sb (int start) (int (+ start (count n))) ^String (m n)))
      (spit f (str sb))))
  (println "fixed" (count hits)) (System/exit 0))
(doseq [[f l n] (take 200 hits)] (println (str f ":" l) n "->" (m n)))
(println "old names left:" (count hits) "in" (count (distinct (map first hits))) "files")
(System/exit (if (empty? hits) 0 1))
