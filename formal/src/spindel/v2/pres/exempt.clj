(ns ^:ansatz/lean spindel.v2.pres.exempt
  "Exemption forms: violations deferred within a step (formal/notes/proof-layout.md, option D).

  One world-step is a transaction: `inv` holds at commit, before and after the step. Inside the step a
  part may be violated for named ids and restored before the step ends (a deferred constraint). A
  part that is ever deferred has an exempt form Q[X]: the part with the ids in X exempt. X is the set
  of pending deferred violations; it is empty at commit (Q = Q[empty]). The API, per part:

    break   Q[X] w -> Q[X + new ids] (e w)          an edit opens deferred violations
    repair  Q[X + k] w -> fact about k -> Q[X] (e' w)   a later edit of the same step closes one
    mono    Q[X] w -> X within Y -> Q[Y] w           more exemptions are weaker
    loop    a loop invariant whose exempt set is ghost state (a function of the worklist)
    exit    the loop ends with its ghost part empty (P4: the worklist empties)
    transport  Q[X] is kept by the edits between a break and its repair (a view frame)

  The forms were written one campaign at a time, so their lemmas have campaign names. `defexempt`
  records a part's form and gives each existing lemma a uniform alias `<part>-exempt-<role>[-<site>]`:
  a theorem with the same statement, proved by the original. Nothing is re-proved; the aliases are
  an index with uniform names. `forms` keeps the table (`exempt-table` prints it)."
  (:require [clojure.string :as str]
            [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]))

;; part -> {:form :ids :commit :doc :lemmas [[role site original alias] ...]}
(defonce forms (atom {}))

(defn- lookup [s] (.lookup ^ansatz.kernel.Env @a/ansatz-env (name/from-string (str s))))

(defn alias!
  "Add theorem `new` with the statement of theorem `old`, proved by `old` (kernel-checked)."
  [new old]
  (let [ci (or (lookup old) (throw (ex-info (str "exempt: no theorem " old) {:old old})))]
    (swap! a/ansatz-env env/check-constant
           (env/mk-thm (name/from-string (str new)) [] (.type ^ansatz.kernel.ConstantInfo ci)
                       (e/const' (name/from-string (str old)) [])))
    new))

(defn defexempt
  "Record the exempt form of `part` and alias its lemmas. Roles :break, :repair, :transport take
  {site original}; :mono, :loop, :exit take one original (or nil)."
  [part & {:keys [form ids commit doc break repair mono loop exit transport]}]
  (let [one (fn [role orig] (when orig [[role nil orig]]))
        many (fn [role m] (for [[site orig] (sort-by key m)] [role site orig]))
        entries (concat (one :mono mono) (many :break break) (many :repair repair)
                        (many :transport transport) (one :loop loop) (one :exit exit))
        lemmas (vec (for [[role site orig] entries
                          :let [al (symbol (str part "-exempt-" (name role) (when site (str "-" site))))]]
                      (do (alias! al orig) [role site orig al])))]
    (swap! forms assoc part {:form form :ids ids :commit commit :doc doc :lemmas lemmas})
    part))

(defn exempt-table
  "The recorded exempt forms, one line per lemma."
  []
  (str/join "\n"
            (for [[part {:keys [form ids commit lemmas]}] (sort-by key @forms)
                  line (cons (str part ": " form " (" ids "; at commit " commit ")")
                             (for [[role site orig al] lemmas]
                               (str "  " (name role) (when site (str " " site)) ": " orig " = " al)))]
              line)))
