;; Ansatz 0.2.654 match syntax (ansatz PR #446): a mechanical migration of the literal match forms.
;;
;;   bb dev/ansatz-bump/migrate_match.clj [--apply] FILE-OR-DIR...
;;
;; Every list whose head is the symbol `match` is classified:
;;   :bracketed  (match d [p1 r1] [p2 r2] ...)          -> (match d p1 r1 p2 r2 ...)
;;               every arm a vector of two forms; the brackets go, a vector belonging to the
;;               pattern stays ((match [a b] [[p q] r]) -> (match [a b] [p q] r)); the
;;               continuation lines of a multi-line arm lose the one column the bracket took
;;   :explicit   (match d T R (ctor body) (ctor [fs] body) ...) -> (match-as d T R ...)
;;               clauses unchanged; continuation lines aligned past the head move right by 3
;;   anything else is reported as unclassified and left alone (an arm that is an unquote or a
;;   splice, a single-element vector discriminant, a malformed clause, an already-flat match).
;; A directory argument covers its .clj/.cljc files; an .edn file is read only when named.
;; `match` inside a string literal is reported (a string-built form), never edited.
;;
;; Text is edited in place: formatting and comments outside the deleted brackets are kept. The
;; result is checked: reading the edited text gives exactly the forms the same rewrite gives on the
;; read original. Without --apply it only reports.
(require '[rewrite-clj.zip :as z] '[rewrite-clj.node :as n] '[rewrite-clj.parser :as p]
         '[clojure.string :as str] '[clojure.java.io :as io] '[clojure.walk :as walk])

(def apply? (some #{"--apply"} *command-line-args*))
(def roots (remove #{"--apply"} *command-line-args*))

(defn real-children [node] (remove n/whitespace-or-comment? (n/children node)))
(defn sym-node? [node s] (and (= :token (n/tag node)) (= s (n/sexpr node))))
(defn arm-vector? [node] (and (= :vector (n/tag node)) (= 2 (count (real-children node)))))
(defn uneval? [node] (= :uneval (n/tag node)))

(defn clause-ok? [node]
  (and (= :list (n/tag node))
       (let [cs (real-children node)]
         (or (= 2 (count cs))
             (and (= 3 (count cs)) (= :vector (n/tag (second cs))))))))

(defn classify [node]
  (let [[_ discr & arms] (real-children node)]
    (cond
      (or (nil? discr) (empty? arms)) [:unclassified "no discriminant or no arms"]
      (some uneval? arms) [:unclassified "an arm is #_-commented"]
      (some #(#{:unquote :unquote-splicing} (n/tag %)) arms) [:unclassified "an arm is an unquote/splice"]
      (every? arm-vector? arms)
      (if (and (= :vector (n/tag discr)) (= 1 (count (real-children discr))))
        [:unclassified "single-element vector discriminant (its pattern meaning changed)"]
        [:bracketed])
      (and (not= :vector (n/tag (first arms))) (>= (count arms) 3) (every? clause-ok? (drop 2 arms)))
      [:explicit]
      :else [:unclassified "neither all [pattern result] arms nor an explicit typed form"])))

(defn context [zloc]
  (loop [z (z/up zloc) acc []]
    (if (nil? z) acc
        (recur (z/up z) (if (#{:syntax-quote :quote :unquote :unquote-splicing :fn} (z/tag z)) (conj acc (z/tag z)) acc)))))

(defn line-starts [^String s]
  (into [0] (keep-indexed (fn [i c] (when (= c \newline) (inc i)))) s))
(defn offset [starts [row col]] (+ (nth starts (dec row)) (dec col)))

(defn string-spans
  "Offsets [start end) of every string/regex literal: no edit may fall inside one."
  [zroot starts]
  (loop [zl zroot acc []]
    (if (z/end? zl) acc
        (let [nd (z/node zl)
              acc (if (or (#{:regex :multi-line} (n/tag nd))
                          (and (= :token (n/tag nd)) (string? (try (n/sexpr nd) (catch Exception _ nil)))))
                    (let [[a b] (z/position-span zl)] (conj acc [(offset starts a) (offset starts b)]))
                    acc)]
          (recur (z/next* zl) acc)))))

(defn in-spans? [spans i] ; spans: a sorted map start -> end
  (when-let [[_ b] (first (rsubseq spans <= i))] (< i b)))

(defn scan [^String s]
  (let [starts (line-starts s)
        root (z/of-string s {:track-position? true})
        spans (into (sorted-map) (string-spans root starts))]
    (loop [zl root found []]
      (if (z/end? zl) {:found found :spans spans :starts starts}
          (let [nd (z/node zl)
                found (if (and (= :list (n/tag nd)) (seq (real-children nd)) (sym-node? (first (real-children nd)) 'match))
                        (conj found {:span (z/position-span zl) :zloc zl :class (classify nd) :ctx (context zl)})
                        found)]
            (recur (z/next zl) found))))))

;; ---- the edit: a set of deletions/insertions at offsets
(defn edits-for [{:keys [zloc class span]} starts spans ^String s]
  (case (first class)
    :bracketed
    (let [arms (->> (z/down zloc) (iterate z/right) (take-while some?) (drop 2))]
      (mapcat (fn [az]
                (let [[a b] (z/position-span az)
                      o1 (offset starts a) o2 (dec (offset starts b))
                      nls (filter #(and (= \newline (.charAt s %)) (not (in-spans? spans %))) (range o1 o2))]
                  (concat [[:del o1 1] [:del o2 1]]
                          (for [nl nls :when (= \space (.charAt s (inc nl)))] [:dedent (inc nl) 1]))))
              arms))
    :explicit
    (let [[a b] span o1 (offset starts a) o2 (offset starts b)
          head-col (- (+ o1 1 (count "match ")) (nth starts (dec (first a))))
          nls (filter #(and (= \newline (.charAt s %)) (not (in-spans? spans %))) (range o1 o2))
          indents (for [nl nls] [(inc nl) (count (take-while #{\space} (subs s (inc nl))))])
          shift? (and (seq indents) (every? (fn [[_ k]] (>= k head-col)) indents))]
      (concat [[:ins (+ o1 1 (count "match")) "-as"]]
              (when shift? (for [[ls _] indents] [:ins ls "   "]))))
    nil))

(defn apply-edits [^String s edits]
  (let [dels (reduce (fn [m [k o x]] (case k :del (assoc m o true) m)) {} edits)
        dedents (reduce (fn [m [k o x]] (case k :dedent (update m o (fnil + 0) x) m)) {} edits)
        ins (reduce (fn [m [k o x]] (case k :ins (update m o str x) m)) {} edits)
        sb (StringBuilder.)]
    (loop [i 0 skip 0]
      (if (>= i (count s)) (str sb)
          (let [c (.charAt s i)
                skip (if-let [d (dedents i)] (+ skip d) skip)]
            (when-let [x (ins i)] (.append sb x))
            (cond
              (dels i) (recur (inc i) skip)
              (and (pos? skip) (= c \space)) (recur (inc i) (dec skip))
              :else (do (.append sb c) (recur (inc i) 0))))))))

;; ---- the check: the same rewrite on the read forms
(defn migrate-form [x]
  (walk/postwalk
   (fn [y]
     (if (and (seq? y) (= 'match (first y)))
       (let [[_ d & arms] y]
         (cond (and (seq arms) (every? #(and (vector? %) (= 2 (count %))) arms)
                    (not (and (vector? d) (= 1 (count d)))))
               (apply list 'match d (mapcat identity arms))
               (and (>= (count arms) 3) (not (vector? (first arms))))
               (apply list 'match-as d arms)
               :else y))
       y))
   x))

(defn forms [s] ; #(...) reads with fresh argument names: normalise them
  (map #(try (walk/postwalk (fn [y] (if (and (symbol? y) (re-matches #"(p\d+|rest)__\d+#" (str y)))
                                      (symbol (str/replace (str y) #"__\d+#" "__#")) y))
                            (n/sexpr %))
             (catch Exception e [:unreadable (n/string %)]))
       (real-children (p/parse-string-all s))))

(defn clj-files "a named file as it is; a directory: its .clj and .cljc files" [root]
  (if (.isFile (io/file root)) [root]
      (->> (file-seq (io/file root)) (filter #(re-find #"\.(clj|cljc)$" (str %))) (map str) sort)))

(def totals (atom {}))
(doseq [f (mapcat clj-files roots)]
  (let [s (slurp f)
        {:keys [found spans starts]} (scan s)
        edits (mapcat #(edits-for % starts spans s) found)
        out (apply-edits s edits)
        strs (for [[a b] spans :let [t (subs s a b)] :when (re-find #"\(match[\s)]" t)]
               (inc (count (filter #{\newline} (subs s 0 a)))))]
    (doseq [{:keys [class ctx span]} found]
      (swap! totals update [(first class) (if (seq ctx) (vec (distinct ctx)) :literal)] (fnil inc 0))
      (when (= :unclassified (first class))
        (println "UNCLASSIFIED" (str f ":" (ffirst span)) (second class) (when (seq ctx) ctx))))
    (doseq [l strs] (swap! totals update [:in-string] (fnil inc 0)) (println "IN-STRING" (str f ":" l)))
    (when (not= s out)
      (let [want (map migrate-form (forms s)) got (forms out)]
        (if (= want got)
          (do (println "migrated" f (count (filter #(#{:bracketed :explicit} (first (:class %))) found)))
              (when apply? (spit f out)))
          (do (println "CHECK FAILED, not written:" f)
              (swap! totals update [:check-failed] (fnil inc 0))))))))
(println "totals" (into (sorted-map-by #(compare (str %1) (str %2))) @totals))
