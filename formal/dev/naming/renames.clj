;; Naming pass, step 2 (babashka, no JVM): compute the rename map, check it, and dry-run the
;; substitution. Nothing is written to the sources.
;;
;;   cd formal && bb dev/naming/renames.clj            ; needs dev/naming/out/model.edn (dump.clj)
;;
;; Reads   dev/naming/rules.edn        the decisions: exact renames, parts, stems
;;         dev/naming/out/model.edn    every constant of the loaded model, the bundles, the tree's tables
;;         src/ test/ README.md notes/ the text the substitution will run over (and ../src ../test ../docs
;;                                     for names cited outside formal/)
;; Writes  notes/renames.edn           the map and the edits to name-generating lines
;;         dev/naming/out/report.txt   checks, counts and the dry run
;;         dev/naming/out/*.tsv        the tables behind the report
(ns renames
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.pprint :as pp]
            [clojure.set :as set]
            [clojure.string :as str]
            [edamame.core :as ed]))

(load-file "dev/naming/lex.clj")
(load-file "dev/naming/scope.clj")

(def model (edn/read-string (slurp "dev/naming/out/model.edn")))
(def rules (edn/read-string (slurp "dev/naming/rules.edn")))
(def C (:constants model))                                   ; name -> kind
(def ns-of (into {} (for [[n names] (:added model) x names] [x (str n)])))
(def report (atom []))
(defn say [& xs] (let [s (str/join " " xs)] (swap! report conj s) (println s)))

;; ---------------------------------------------------------------------------------------------
;; Sources
;; ---------------------------------------------------------------------------------------------

(defn files-under [dir ext]
  (->> (file-seq (io/file dir)) (filter #(and (.isFile %) (str/ends-with? (str %) ext))) (map str) sort))
(def src-files (files-under "src" ".clj"))
(def test-files (files-under "test" ".clj"))
(def doc-files (concat ["README.md"]
                       (->> (concat (files-under "notes" ".md") (files-under "notes" ".clj") (files-under "notes" ".edn"))
                            (remove #(or (str/includes? % "notes/history/") (str/ends-with? % "notes/renames.edn"))))))
(def text (memoize slurp))
(def line-idx (memoize (fn [f] (lex/line-index (text f)))))

(def parse
  (memoize
   (fn [f]
  (ed/parse-string-all (text f) {:all true :auto-resolve name :readers (fn [_] identity) :features #{:clj}
                                 :read-cond :allow}))))
(def decl-heads '#{a/theorem a/defn a/structure a/inductive ansatz.core/theorem ansatz.core/defn})
(defn decl-forms [x]
  (cond (and (seq? x) (decl-heads (first x)) (symbol? (second x))) (cons x (mapcat decl-forms (drop 2 x)))
        (coll? x) (mapcat decl-forms (if (map? x) (mapcat identity x) x))
        :else nil))
;; name -> {:kind :file :form} for every declaration written out in a source file (also inside a
;; quoted form or a `do`); a macro template's name is not a symbol of the environment and drops out
(def hand
  (into {} (for [f src-files, d (decl-forms (parse f)) :let [n (str (second d))] :when (contains? C n)]
             [n {:kind (keyword (name (first d))) :file f :form d}])))
(def undotted (remove #(str/includes? % ".") (keys C)))
(def generated (set (remove hand undotted)))
(def defs (set (filter #(#{:def :ind} (C %)) undotted)))    ; definitions, structures, inductives

(defn mentions? [sym x] (boolean (some #{sym} (tree-seq coll? #(if (map? %) (mapcat identity %) (seq %)) x))))
(def base-old (name (:old (:base rules))))
(def base-new (name (:new (:base rules))))
(def base-nss #{"spindel.v2.edits" "spindel.v2.step" "spindel.v2.rule" "spindel.v2.engine"})

(defn base-stem
  "X of a base lemma named inv-X, X-inv or X-inv-sample."
  [n]
  (cond (str/starts-with? n "inv-") (subs n 4)
        (str/ends-with? n "-inv-sample") (subs n 0 (- (count n) 11))
        (str/ends-with? n "-inv") (subs n 0 (- (count n) 4))))

;; the base lemmas: theorems named inv-X / X-inv / X-inv-sample whose statement is about the base
;; invariant. Written out: the statement mentions inv-sample. Generated in a base namespace (the
;; table macros of edits and engine) or by the tree (raw0's branches): by construction.
(def tree-derived (set (map str (:tree-derived model))))
(def base-lemmas
  (set (for [n undotted
             :when (and (= :thm (C n)) (base-stem n)
                        (if-let [h (hand n)]
                          (let [[_ _ binders stmt] (:form h)] (mentions? (symbol base-old) [binders stmt]))
                          (or (tree-derived n) (base-nss (ns-of n)))))]
         n)))

;; ---------------------------------------------------------------------------------------------
;; The rename function
;; ---------------------------------------------------------------------------------------------

(def exact (into {} (for [[k v] (:exact rules)] [(str k) (str v)])))
(def parts (into {} (for [[k v] (:parts rules)] [(str k) (str (:new v))])))
(def stems (into {} (for [[k v] (:stems rules)] [(str k) (str v)])))
(def keep-names (set (map str (:keep rules))))
;; prefixes a definition's name follows: parts, the members campaigns, and the listed definitions
(def family-stems (into {} (for [[k v] (:family-stems rules)] [(str k) (str v)])))
(def def-families (set (map str (:def-families rules))))
(def rule-of (atom {}))                                      ; old -> the rule that renamed it

(defn toks [n] (str/split n #"-"))
(defn untoks [ts] (str/join "-" ts))

(declare rename-def)
(def seg-hits (atom {}))                                   ; [old run, new run] -> the names it rewrote

(defn seg
  "Rewrite a name token by token: the longest run of hyphen tokens that is a definition (or a part,
  or a stem) is replaced by its new name; other tokens stay. `self` (the name itself) never matches
  as a whole."
  ([n] (seg n nil))
  ([n self]
   (let [ts (vec (toks n)) k (count ts)]
     (loop [i 0 out []]
       (if (>= i k)
         (untoks out)
         (let [hit (first (for [j (range k i -1)
                                :let [s (untoks (subvec ts i j))]
                                :when (and (not= s self)
                                           (or (contains? defs s) (contains? stems s)))]
                            [j s]))]
           (if-let [[j s] hit]
             (let [v (if (contains? defs s) (rename-def s) (stems s))]
               (when (not= v s) (swap! seg-hits update [s v] (fnil conj []) n))
               (recur j (conj out v)))
             (recur (inc i) (conj out (ts i))))))))))

(def rename-def
  (memoize
   (fn [d]
     (cond (exact d) (exact d)
           (parts d) (parts d)
           (keep-names d) d
           :else
           ;; a definition named after a part, a link or a stem follows its prefix (gl-rest, h3-cur,
           ;; casc-tail); nothing else in a definition's name is rewritten
           (let [ts (vec (toks d))
                 hit (first (for [j (range (dec (count ts)) 0 -1)
                                  :let [p (untoks (subvec ts 0 j))]
                                  :when (or (parts p) (family-stems p) (def-families p))]
                              [j p]))
                 spell {"casc" "cascade" "src" "source" "blk" "blocked"}]
             (cond hit (let [[j p] hit] (untoks (cons (or (parts p) (family-stems p) (exact p)) (subvec ts j))))
                   (spell (first ts)) (untoks (cons (spell (first ts)) (rest ts)))
                   :else d))))))

;; -- generated names: the generators' rules, old and new

(defn old-copy-name [prefix pred base]
  (cond (str/starts-with? base "inv-") (str prefix (subs base 4))
        (str/ends-with? base "-inv-sample") (str (subs base 0 (- (count base) 11)) "-" pred)
        (str/ends-with? base "-inv") (str (subs base 0 (- (count base) 4)) "-" pred)
        :else (str base "-" pred)))
;; the new rule, one case: the part's name takes the place of the base's
(defn new-copy-name [new-pred new-base] (str/replace-first new-base base-new new-pred))

(defn old-pres-name [base] (str "pres-" (or (base-stem base) base)))
(defn new-pres-name [new-base]
  (str "pres-" (-> new-base (str/replace-first (str base-new "-") "") (str/replace-first (str "-" base-new) ""))))

(declare rename)

(defn rename-base
  "A base lemma: well-formed-<X>, X the definition it is about, spelled as the definition is now."
  [n]
  (cond (exact n) (exact n)
        (tree-derived n) (str base-new "-" (rename-def "raw0") "-" (subs n 5 (- (count n) 4)))   ; raw0-<item>-inv
        :else (str base-new "-" (seg (base-stem n)))))

;; old copy name -> [new-pred base]: the model's own record (the bundles' lemma maps) ...
(def copies
  (into {} (for [b (:bundles model) [base l] (:renames b)
                 :let [pred (str (:pred b)) cn (old-copy-name (:prefix b) pred (str base))]
                 :when (and (= cn (str l)) (contains? C cn))]
             [cn [(parts pred) (str base)]])))
;; ... and every other constant with the shape of a copy: an alias the tree gives a part's own proof
;; of a base lemma (`aliases!`), or a hand lemma named like a copy (step-gl, raw-g7)
(def copy-shaped
  (into {} (for [b (:bundles model) base base-lemmas
                 :let [pred (str (:pred b)) cn (old-copy-name (:prefix b) pred base)]
                 :when (and (contains? C cn) (not (copies cn)))]
             [cn [(parts pred) base]])))
;; a part's own proof of a base lemma, registered under another name than the copy's: [own copy-name]
(def own-proofs
  (vec (for [b (:bundles model) [base l] (:renames b)
             :let [pred (str (:pred b)) cn (old-copy-name (:prefix b) pred (str base))]
             :when (and (not= cn (str l)) (hand (str l)))]
         [(str l) cn])))
(def pres-of (into {} (for [b base-lemmas] [(old-pres-name b) b])))

(defn mini-copy
  "A copy made by one of the two private copiers (inv.rank-step: rk-X / X-rk; progress.casc:
  bc-X / X-bc): [base new-part] or nil."
  [n]
  (some (fn [[pre suf part file]]
          (let [base (cond (str/starts-with? n pre) (str "inv-" (subs n (count pre)))
                           (str/ends-with? n suf) (str (subs n 0 (- (count n) (count suf))) "-inv"))
                base (or (when (base-lemmas base) base)
                         (when (and base (str/ends-with? base "-inv"))
                           (let [b2 (str base "-sample")] (when (base-lemmas b2) b2))))]
            (when (and base (or (not (hand n)) (str/ends-with? (:file (hand n)) (str "/" file)))) [base part])))
        [["rk-" "-rk" (rename-def "inv-rank") "rank_step.clj"] ["bc-" "-bc" (rename-def "bc") "casc.clj"]]))

(def links ["p3b" "p3c" "p3d" "p3e" "p3f" "p3g" "p3h" "p3i" "p3j" "p3k" "p3l" "p3la" "p3m"])
(def stage-re #"^h(9|1[0-8])-(.+)$")

;; the exemption API's aliases (pres.exempt/defexempt): <part>-exempt-<role>[-<site>], <part> the
;; part's name without its own -exempt
(def site-names {"kw" "view"})
(def exempt-alias
  (into {} (for [[part {:keys [lemmas]}] (:exempt model), [role site _ al] lemmas
                 :let [p (str/replace (parts (str part)) #"-exempt$" "")]]
             [(str al) (str p "-exempt-" (name role) (when site (str "-" (site-names (str site) (str site)))))])))
(defn rule! [n r v] (swap! rule-of assoc n r) v)

(def rename
  (memoize
   (fn [n]
     (let [k (C n)]
       (cond
         (exact n) (rule! n :exact (exact n))
         (parts n) (rule! n :part (parts n))
         (keep-names n) n
         (#{:def :ind} k) (let [v (rename-def n)] (if (= v n) n (rule! n :def-prefix v)))
         (base-lemmas n) (rule! n :base (rename-base n))
         (copies n) (let [[p b] (copies n)] (rule! n :copy (new-copy-name p (rename b))))
         (copy-shaped n) (let [[p b] (copy-shaped n)] (rule! n (if (hand n) :copy-shape :alias) (new-copy-name p (rename b))))
         ;; inv.i10's -r wrappers of the exempt form's copies: <copy>-r
         (and (generated n) (str/ends-with? n "-r") (copies (subs n 0 (- (count n) 2))))
         (rule! n :copy-r (str (rename (subs n 0 (- (count n) 2))) "-r"))
         (exempt-alias n) (rule! n :exempt-api (exempt-alias n))
         (mini-copy n) (let [[b p] (mini-copy n)] (rule! n :mini-copy (new-copy-name p (rename b))))
         ;; inv.rank-step's own lemmas about inv-rank: rk-<x>, <x>-rk
         (and (hand n) (str/ends-with? (:file (hand n)) "/rank_step.clj") (re-matches #"rk-.+|.+-rk" n))
         (let [x (if (str/starts-with? n "rk-") (subs n 3) (subs n 0 (- (count n) 3)))]
           (rule! n :rank (str (rename-def "inv-rank") "-" (if (= x "sample") base-new (seg x)))))
         (str/includes? n "@") (let [[a p] (str/split n #"@")]
                                 (rule! n :pres (str (new-pres-name (rename (pres-of a))) "@" (parts p))))
         (and (pres-of n) (generated n)) (rule! n :pres (new-pres-name (rename (pres-of n))))
         :else
         (let [ts (toks n)
               v (cond
                   ;; <bundle>-sample: the bundle implies the base
                   (and (= "sample" (last ts)) (> (count ts) 1))
                   (str (seg (untoks (butlast ts))) "-" base-new)
                   ;; <pred>-rest-kw, <pred>-kw: the predicate is a function of the part's view
                   (and (= "kw" (last ts)) (> (count ts) 1) (not (#{"of"} (last (butlast ts)))))
                   (str (seg (untoks (butlast ts))) "-frame")
                   ;; <lemma>-o: the part's own proof of a composite
                   (and (= "o" (last ts)) (> (count ts) 1))
                   (str (seg (untoks (butlast ts))) "-hand")
                   ;; <link>-<earlier link>
                   (and (= 2 (count ts)) (every? (set links) ts))
                   (let [[a b] ts]
                     (if (= (inc (.indexOf ^java.util.List links b)) (.indexOf ^java.util.List links a))
                       (str (rename-def a) "-prev")
                       (str (rename-def a) "-implies-" (rename-def b))))
                   ;; a members-campaign lemma hNN-<x>[-h3]: current-members-<x>
                   (re-matches stage-re n)
                   (let [x (nth (re-matches stage-re n) 2)
                         x (if (str/ends-with? x "-h3") (subs x 0 (- (count x) 3)) x)]
                     (str (parts "h3") "-" (seg x)))
                   :else (seg n))]
           (if (= v n) n (rule! n (cond (re-matches stage-re n) :stage (= v (seg n)) :seg :else :suffix) v))))))))

;; ---------------------------------------------------------------------------------------------
;; step.clj legacy (decision 18): the largest set of step.clj declarations, grown from the roots,
;; that nothing outside the set references.
;; ---------------------------------------------------------------------------------------------

(defn syms-of [form] (set (map str (filter symbol? (tree-seq coll? #(if (map? %) (mapcat identity %) (seq %)) form)))))
(def refs (into {} (for [[n {:keys [form]}] hand] [n (disj (syms-of (drop 2 form)) n)])))
(def legacy
  (let [step-decls (set (for [[n {:keys [file]}] hand :when (str/ends-with? file "v2/step.clj")] n))
        roots (set (map str (:legacy-roots rules)))]
    (loop [L roots]
      (let [more (set (for [n step-decls :when (and (not (L n)) (= :theorem (:kind (hand n))) (some L (refs n)))] n))]
        (if (seq more) (recur (into L more)) L)))))
;; who else names a legacy declaration: any source or test form outside the set
(def ctor-shorts (set (for [[n k] C :when (= k :ctor)] (last (str/split n #"\.")))))
(def legacy-users
  (let [L legacy]
    (vec (for [f (concat src-files test-files)
               form (parse f)
               :let [nm (when (and (seq? form) (decl-heads (first form))) (str (second form)))]
               :when (not (L nm))
               :let [hit (seq (filter L (syms-of form)))]
               :when hit
               ;; a homonym is not a reference: a constructor of another inductive (SysReach.retire),
               ;; a Clojure function a test file defines itself (inv_test's run-items)
               :let [own (set (map (comp str second) (filter #(and (seq? %) ('#{defn defn- def} (first %))) (parse f))))
                     real (remove #(or (own %) (and (ctor-shorts %) (not (str/ends-with? f "v2/step.clj")))) hit)]]
           {:file f :form (or nm (pr-str (take 2 (if (seq? form) form [form])))) :names (vec (sort hit))
            :real (vec (sort real))}))))

;; ---------------------------------------------------------------------------------------------
;; The map
;; ---------------------------------------------------------------------------------------------

(def renamed-raw (into (sorted-map) (for [n undotted :when (not (legacy n)) :let [v (rename n)] :when (not= v n)] [n v])))

;; Collisions the rules resolve:
;;  - a hand lemma whose new name is a generated copy's or alias's new name is the part's own proof of
;;    that composite: <name>-hand (decision 10);
;;  - two hand lemmas of different members campaigns merged into one prefix: both take their
;;    namespace's topic word, current-members-<topic>-<x> (decision 15).
(defn topic [n] (some-> (hand n) :file (str/replace #"^.*/([a-z_0-9]+)\.clj$" "$1") (str/replace "_" "-")))
(def renamed
  (let [by-new (group-by val renamed-raw)
        cm (parts "h3")
        fix (fn [n v]
              (let [others (remove #{n} (map key (by-new v)))]
                (cond (empty? others) v
                      (and (hand n) (= :theorem (:kind (hand n))) (some generated others))
                      (do (swap! rule-of assoc n :own-proof-hand) (str v "-hand"))
                      (and (re-matches stage-re n) (every? hand others) (str/starts-with? v (str cm "-")))
                      (do (swap! rule-of assoc n :stage-topic) (str cm "-" (topic n) (subs v (count cm))))
                      :else v)))]
    (into (sorted-map) (for [[n v] renamed-raw] [n (fix n v)]))))

(def new-names (set (vals renamed)))
(def keyset* (set (keys renamed)))
(def kind-of (fn [n] (cond (hand n) (if (= :theorem (:kind (hand n))) :hand-theorem :hand-definition)
                           (= :thm (C n)) :generated-theorem :else :generated-definition)))

;; ---------------------------------------------------------------------------------------------
;; Checks
;; ---------------------------------------------------------------------------------------------

(def problems (atom []))
(defn problem! [k & xs] (swap! problems conj (into [k] xs)))

;; 1. no two old names map to one new name
(doseq [[v ns] (group-by val renamed) :when (> (count ns) 1)] (problem! :two-old-one-new v (mapv key ns)))
;; 2. every new name is free: not a constant that stays (a definition, a theorem, a constructor's
;;    or structure's qualified name), not an Init name in scope, not a clojure.core var (a/defn
;;    interns a var), not an Ansatz tactic
(def staying (set (remove #(or (renamed %) (legacy %)) (keys C))))
(def dotted-heads (set (map #(first (str/split % #"\.")) (filter #(str/includes? % ".") (keys C)))))
(def core-vars (set (map str (keys (ns-publics 'clojure.core)))))
(def tactics
  (let [f (io/file (System/getProperty "user.home") "Development/ansatz/src/ansatz/core.clj")]
    (if (.exists f) (set (map second (re-seq #"(?m)^\s+'([a-z_!?*-]+)\s+\(fn \[ps" (slurp f)))) #{})))
(doseq [[o v] renamed]
  (when (staying v) (problem! :new-name-taken o v))
  (when (contains? (:init model) v) (problem! :new-name-in-init o v))
  (when (and (#{:def :ind} (C o)) (core-vars v)) (problem! :new-name-in-clojure-core o v))
  (when (tactics v) (problem! :new-name-is-a-tactic o v))
  (when (and (dotted-heads v) (not (dotted-heads o)) (not (renamed v))) (problem! :new-name-is-a-qualifier o v)))
;; 3. a new name that is the old name of another renamed constant is a swap: fine only because the
;;    substitution is simultaneous. Listed.
(doseq [[part {:keys [lemmas]}] (:exempt model), [_ site] lemmas
        :when (and site (keyset* (str site)) (not (site-names (str site))))]
  (problem! :exempt-site-is-a-renamed-name part site))
(def swaps (vec (for [[o v] renamed :when (or (renamed v) (legacy v))] [o v (if (legacy v) :freed-by-deletion :freed-by-rename)])))
;; 4. prefix nesting (proposal e4): a part's exempt form is <part>-exempt, the exemption API's
;;    lemmas are <part>-exempt-<role>[-<site>]. No lemma copied for the exempt form may start with
;;    a role word, and no base lemma may be named well-formed-exempt-...
(def roles #{"break" "repair" "mono" "loop" "exit" "transport"})
(doseq [b base-lemmas :let [x (subs (rename b) (min (count (rename b)) (inc (count base-new))))]
        :when (or (roles (first (toks x))) (= "exempt" (first (toks x))))]
  (problem! :base-lemma-starts-with-a-role-word b (rename b)))
(doseq [[o v] renamed, p (vals parts)
        :when (and (str/ends-with? p "-exempt") (str/starts-with? v (str p "-")) (roles (first (toks (subs v (inc (count p)))))))
        :when (not (str/includes? o "-exempt-"))]
  (problem! :exempt-form-lemma-looks-like-the-api o v))
;; 5. stale tokens in new names
(def stale (set (map str (:stale-tokens rules))))
(def stale-hits (vec (for [[o v] renamed :when (some stale (toks (first (str/split v #"@"))))] [o v])))
(def stale-unrenamed
  (vec (sort (for [n undotted :when (and (not (renamed n)) (not (legacy n)) (some stale (toks (first (str/split n #"@")))))] n))))

;; ---------------------------------------------------------------------------------------------
;; Dry run of the simultaneous whole-symbol substitution
;; ---------------------------------------------------------------------------------------------

(def keyset (set (keys renamed)))
(def prose-words #{"post" "finish" "retire" "dispatch" "raw" "inv" "marks" "live" "chain" "admit" "transition"})

(defn top-forms
  "[start end] of every top-level form of Clojure source s: a form starts at a `(` in column 0 of
  a code region and runs to the next one."
  [s regs]
  (let [m (re-matcher #"(?m)^\(" s)
        starts (loop [out []] (if (.find m) (recur (conj out (.start m))) out))
        code-starts (let [cs (filterv (fn [[k]] (= k :code)) regs)]
                      ;; merge-walk: starts and regions are both sorted
                      (loop [ss starts rs cs out []]
                        (cond (or (empty? ss) (empty? rs)) out
                              (< (first ss) (second (first rs))) (recur (rest ss) rs out)
                              (>= (first ss) (nth (first rs) 2)) (recur ss (rest rs) out)
                              :else (recur (rest ss) rs (conj out (first ss))))))]
    (mapv vector code-starts (concat (rest code-starts) [(count s)]))))

(declare local-binding-pos*)
(def local-binding-pos (memoize (fn [form nm] (local-binding-pos* form nm))))
(defn local-binding-pos*
  "The first position in form text where `nm` is bound as a local (a binder `nm :- T`, or a name
  introduced by have/intro/intros/rename_i/cases/case), or nil."
  [form nm]
  (let [q (java.util.regex.Pattern/quote nm)
        b "(?<![A-Za-z0-9*+!_?<>=$%&|'./:#-])" e "(?![A-Za-z0-9*+!_?<>=$%&|'./-])"
        pats [(re-pattern (str b q e "\\s+:-\\s"))
              (re-pattern (str "\\((?:have|intro|intros|rename_i|cases|obtain|rcases|induction)\\s+(?:[^()\\s]+\\s+)*?" q e))
              (re-pattern (str "\\(case\\s+\\[[^\\]]*?" b q e))]]
    (some->> (keep #(let [m (re-matcher % form)] (when (.find m) (.start m))) pats) seq (apply min))))

(defn classify-text
  "The textual fallback (a symbol the reader gave no position, e.g. inside a syntax-quote)."
  [s occ form-range]
  (let [{:keys [name start kind]} occ
        before (subs s (max 0 (- start 12)) start)]
    (cond
      (and (ctor-shorts name) (re-find #"(\[\(|\(case \[|\[)$" before)) :constructor
      (and form-range
           (when-let [p (local-binding-pos (subs s (first form-range) (second form-range)) name)]
             (>= (- start (first form-range)) p))) :local
      :else :subst)))

(def unscoped (atom []))                                     ; code occurrences the scope scan did not place
(def disagree (atom []))
(defn classify
  "What the substitution does with one occurrence: :subst, or a reason to leave it. In code the scope
  scan (scope.clj) decides: a local or a constructor in a pattern is not the global of that name."
  [f s occ form-range sc]
  (let [{:keys [name start kind backtick?]} occ]
    (cond
      (= kind :code)
      (let [t (classify-text s occ form-range)
            w (case (get sc start)
                :local :local
                :constructor (if (ctor-shorts name) :constructor :local)
                :global :subst
                (do (swap! unscoped conj [f start name]) t))]
        (when (not= w t) (swap! disagree conj [f start name w t]))
        w)
      (and (prose-words name) (not backtick?)) :prose-word
      :else :subst)))

(defn dry-run [f]
  (let [s (text f)
        md? (not (re-find #"\.(clj|edn)$" f))
        regs (if md? (lex/md-regions s) (lex/regions s))
        forms (when-not md? (top-forms s regs))
        sc (when-not md? (scope/offsets s))
        idx (lex/line-index s)
        occs (sort-by :start (lex/occurrences s regs keyset))]
    ;; occurrences and forms are both in text order
    (loop [os occs fs forms out (transient [])]
      (if-let [occ (first os)]
        (let [fs (drop-while (fn [[_ b]] (<= b (:start occ))) fs)
              fr (when-let [[a b] (first fs)] (when (<= a (:start occ)) [a b]))]
          (recur (rest os) fs (conj! out (assoc occ :file f :line (lex/line-at idx (:start occ)) :what (classify f s occ fr sc)))))
        (persistent! out)))))

(def scope-files (concat src-files test-files doc-files))
(def occs (vec (mapcat dry-run scope-files)))

;; string literals that build names: a string with no space that starts or ends with a hyphen (or is
;; one name) and contains a renamed name or a stale token as a whole hyphen token
(def base-form-re #"^(inv-|-inv|-inv-sample|-sample|-kw|-o|-rk|rk-|bc-|-bc)$")
(def built
  (vec (for [f (concat src-files test-files)
             :let [s (text f)]
             [kind a b] (lex/regions s)
             :when (= kind :string)
             :let [str-body (subs s (inc a) (dec b))]
             :when (and (<= 2 (count str-body) 40) (not (re-find #"\s|/|log-sample" str-body))
                        (or (re-matches base-form-re str-body)
                            (and (or (str/starts-with? str-body "-") (str/ends-with? str-body "-") (keyset str-body))
                                 (some #(or (keyset %) (stale %) (parts %)) (cons (str/replace str-body #"^-|-$" "") (toks str-body))))))]
         {:file f :line (lex/line-at (line-idx f) a) :string str-body})))
;; lines that compute a name from another name's characters
(def computed
  (vec (for [f src-files
             [i l] (map-indexed vector (str/split-lines (text f)))
             :when (re-find #"\(subs \(name|starts-with\? s \"inv-|ends-with\? s \"-inv|str/replace \(subs" l)]
         {:file f :line (inc i) :text (str/trim l)})))

;; names cited outside formal/
(def outside
  (let [fs (->> ["../src" "../test" "../docs" "../README.md" "../doc" "../notes" "../dev"]
                (mapcat #(let [f (io/file %)] (cond (.isDirectory f) (filter (fn [x] (.isFile x)) (file-seq f)) (.isFile f) [f])))
                (filter #(re-find #"\.(clj|cljc|cljs|md|edn|txt)$" (str %))) (map str) sort)]
    (vec (for [f fs :let [s (text f) md? (not (re-find #"\.clj[cs]?$" f))]
               occ (lex/occurrences s (if md? (lex/md-regions s) (lex/regions s)) keyset)
               ;; outside formal/ a bare word is only a citation in backticks or next to formal vocabulary
               :when (or (:backtick? occ) (str/includes? (:name occ) "-") (re-find #"\d" (:name occ)))]
           (assoc occ :file f :line (lex/line-at (line-idx f) (:start occ)))))))

;; the oracle's names (the engine session owns oracle_test.clj): old -> new, with counts
(def oracle-files (filter #(re-find #"oracle(_test)?\.clj$" %) test-files))
(def oracle-names
  (into (sorted-map)
        (for [[n os] (group-by :name (filter #(and ((set oracle-files) (:file %)) (= :subst (:what %))) occs))]
          [n {:new (renamed n) :by-file (frequencies (map #(last (str/split (:file %) #"/")) os))}])))

;; ---------------------------------------------------------------------------------------------
;; Output
;; ---------------------------------------------------------------------------------------------

(def by-kind (group-by (comp kind-of key) renamed))
(defn sm [kvs] (into (sorted-map) kvs))

;; the edits to name-generating lines: the hand-listed ones, plus one per bundle (the prefix string
;; of its mk-bundle call), located in the text
(def bundle-prefix-edits
  (vec (for [b (sort-by (comp str :pred) (:bundles model))
             :let [old (:prefix b) new (str (parts (str (:pred b))) "-")
                   at (first (filter #(= old (:string %)) built))]]
         {:file (:file at) :line (:line at) :old (pr-str old) :new (pr-str new)
          :why (str "mk-bundle prefix of " (:pred b) " -> " (parts (str (:pred b))))})))
(doseq [e bundle-prefix-edits :when (nil? (:file e))] (problem! :bundle-prefix-not-found e))
(def generator-edits
  (vec (concat (edn/read-string (slurp "dev/naming/generator-edits.edn")) bundle-prefix-edits)))
;; every hand-listed edit must still match its line
(doseq [{:keys [file line old] :as e} (edn/read-string (slurp "dev/naming/generator-edits.edn"))
        :let [l (nth (str/split-lines (text file)) (dec line) "")]
        :when (not (str/includes? l old))]
  (problem! :generator-edit-does-not-match (select-keys e [:file :line :old])))

;; a tree lemma's name pres-<x>@<part> is not a readable symbol (`@` is deref): written as a string
(defn edn-name [n] (if (str/includes? n "@") (pr-str n) n))
(binding [*print-length* nil *print-level* nil]
  (spit "notes/renames.edn"
        (with-out-str
          (println ";; The rename map of the naming pass. GENERATED by formal/dev/naming/renames.clj from")
          (println ";; formal/dev/naming/rules.edn and a load of the model; edit the rules, not this file.")
          (println ";;   :definitions, :theorems   hand-written declarations, old -> new (the substitution's keys)")
          (println ";;   :deleted                  step.clj legacy, removed with its lemmas (no reference outside the set)")
          (println ";;   :generator-edits          lines that build names; generated names follow from these")
          (println ";;   :generated                what the generators then produce, old -> new (for the gate:")
          (println ";;                             every old statement must be found under its new name)")
          (println ";;                             (names with an @, the tree's pres-<x>@<part>, are strings)")
          (println ";;   :swaps                    new names that are old names of other entries: substitute simultaneously")
          (println "{:base" (pr-str (:base rules)))
          (doseq [[k title] [[:hand-definition :definitions] [:hand-theorem :theorems]]]
            (println (str " " title))
            (println " {" )
            (doseq [[o v] (sm (by-kind k))] (println (str "  " (edn-name o) " " (edn-name v))))
            (println " }"))
          (println " :deleted")
          (println (str " [" (str/join "\n  " (sort legacy)) "]"))
          (println " :swaps")
          (println (str " [" (str/join "\n  " (map pr-str swaps)) "]"))
          (println " :generator-edits")
          (pp/pprint generator-edits)
          (println " :generated")
          (println " {")
          (doseq [[o v] (sm (concat (by-kind :generated-theorem) (by-kind :generated-definition)))] (println (str "  " (edn-name o) " " (edn-name v))))
          (println " }}"))))

(defn tsv [f rows] (spit (str "dev/naming/out/" f) (str/join "\n" (map #(str/join "\t" %) rows))))
(tsv "renamed.tsv" (for [[o v] renamed] [o v (name (kind-of o)) (name (@rule-of o :?)) (or (some-> (hand o) :file) (ns-of o))]))
(tsv "occurrences.tsv" (for [o occs] [(:file o) (:line o) (:name o) (name (:kind o)) (name (:what o)) (if (:dotted? o) "dotted" "")]))
(tsv "unscoped.tsv" (for [[f st n] @unscoped] [f (lex/line-at (line-idx f) st) n]))
(tsv "disagree.tsv" (for [[f st n w t] @disagree] [f (lex/line-at (line-idx f) st) n (name w) (name t)]))
(tsv "outside.tsv" (for [o outside] [(:file o) (:line o) (:name o) (renamed (:name o))]))
(tsv "built.tsv" (for [o built] [(:file o) (:line o) (:string o)]))
(tsv "computed.tsv" (for [o computed] [(:file o) (:line o) (:text o)]))

(say "== model")
(say "constants" (count C) (pr-str (frequencies (vals C))) "| undotted" (count undotted)
     "| written out" (count hand) (pr-str (frequencies (map :kind (vals hand)))) "| generated" (count generated))
(say "base lemmas" (count base-lemmas) "| bundles" (count (:bundles model)) "| tree tables" (count (:tree-parts model)))
(say "\n== the map")
(doseq [k [:hand-definition :hand-theorem :generated-definition :generated-theorem]]
  (say (format "%-22s renamed %5d of %5d" (name k) (count (by-kind k)) (count (filter #(= k (kind-of %)) undotted)))))
(say "by rule" (pr-str (into (sorted-map) (frequencies (map #(@rule-of % :?) (keys renamed))))))
(spit "dev/naming/out/seg-hits.txt"
      (str/join "\n" (for [[[o v] ns] (sort-by (comp - count val) @seg-hits)]
                       (str o " -> " v "  x" (count (distinct ns)) "  " (str/join " " (take 6 (distinct ns)))))))
(say "deleted (step.clj legacy)" (count legacy) (pr-str (sort legacy)))
(say "references to the legacy set from outside it:" (count legacy-users))
(doseq [u legacy-users] (say "  " (:file u) (:form u) (pr-str (:names u)) (if (seq (:real u)) (str "REFERENCE " (pr-str (:real u))) "homonym only")))
(say "\n== checks")
(say "problems" (count @problems) (pr-str (frequencies (map first @problems))))
(doseq [p (sort-by (comp str first) @problems)] (say "  " (pr-str p)))
(say "swaps (need the simultaneous substitution)" (count swaps))
(doseq [s swaps] (say "  " (pr-str s)))
(say "new names with a stale token" (count stale-hits) (pr-str (take 40 stale-hits)))
(say "names with a stale token that no rule renames" (count stale-unrenamed) (pr-str (take 200 stale-unrenamed)))
(say "\n== dry run (nothing written)")
(let [sub (filter #(= :subst (:what %)) occs)]
  (say "occurrences that change" (count sub) "in" (count (distinct (map :file sub))) "files;"
       "by context" (pr-str (frequencies (map :kind sub))))
  (say "by tree" (pr-str (into (sorted-map) (frequencies (map #(cond (str/starts-with? (:file %) "src") :src
                                                                      (re-find #"oracle" (:file %)) :test-oracle
                                                                      (str/starts-with? (:file %) "test") :test
                                                                      :else :docs) sub)))))
  (say "left alone" (pr-str (frequencies (map :what (remove #(= :subst (:what %)) occs)))))
  (say "keys never seen in the text (generated or built names)" (count (remove (set (map :name occs)) (keys renamed)))
       "of which hand-written" (pr-str (vec (filter hand (remove (set (map :name occs)) (keys renamed)))))))
(say "strings that build names" (count built) "| lines that compute a name" (count computed))
(say "cited outside formal/" (count outside) (pr-str (frequencies (map :file outside))))
(say "oracle names" (count oracle-names))
(doseq [[o {:keys [new by-file]}] oracle-names] (say "  " o "->" new (pr-str by-file)))
(spit "dev/naming/out/report.txt" (str/join "\n" @report))
(when (seq @problems) (println "PROBLEMS:" (count @problems)))
