;; Naming pass: which symbols of a source file are locals, constructors in a pattern, or references
;; to a global name. A whole-symbol substitution must leave the first two alone: `h3`, `ch`, `gk`,
;; `post` are also names of hypotheses, binders, Clojure locals and Item constructors.
;; Loaded by renames.clj (babashka). Reads forms with edamame, which records each symbol's position.
(ns scope
  (:require [clojure.string :as str]
            [edamame.core :as ed]))

(defn parse-located [s]
  (ed/parse-string-all s {:all true :auto-resolve name :readers (fn [_] identity) :features #{:clj} :read-cond :allow}))

(def clj-let-heads '#{let let* loop loop* when-let if-let when-some if-some binding with-open with-redefs
                      for doseq dotimes with-local-vars})
(def clj-fn-heads '#{fn fn* defn defn- defmacro})
(def binder-tactics '#{have intro intros rename_i obtain rcases})
(def decl-heads '#{a/theorem a/defn ansatz.core/theorem ansatz.core/defn})

(defn- syms-in [x] (filter symbol? (tree-seq coll? #(if (map? %) (mapcat identity %) (seq %)) x)))
(defn- typed-binder-names
  "Names of a binder vector [a :- T, b :- U]: the symbols directly before `:-`."
  [v]
  (for [[a b] (partition 2 1 v) :when (and (symbol? a) (= :- b))] a))
(defn- typed-binders? [v] (and (vector? v) (some #{:-} v)))

(defn scan
  "Every symbol of source text s with a recorded position: [{:sym :row :col :what}], :what one of
  :global, :local, :constructor."
  [s]
  (let [out (atom [])
        emit (fn [sym what] (when-let [m (meta sym)] (when (:row m) (swap! out conj {:sym sym :row (:row m) :col (:col m) :what what}))))]
    (letfn [(use! [x env]                                    ; a symbol in use position
              (emit x (if (contains? env (name x)) :local :global)))
            (bind! [x] (emit x :local))
            (targets [t] (remove #{'&} (syms-in t)))
            (add [env names] (into env (map name names)))
            ;; walk x, return the env its bindings leave for the following siblings
            (walk [x env]
              (cond
                (symbol? x) (do (use! x env) env)
                ;; a map of quoted data (a contract: {:binders [x :- T] :statement (...)}): the binder
                ;; vectors among its values scope over the other values
                (map? x) (let [unq (fn [v] (if (and (seq? v) (= 'quote (first v))) (second v) v))
                               env2 (reduce (fn [e v] (if (typed-binders? (unq v)) (walk-binders (unq v) e) e)) env (vals x))]
                           (doseq [[k v] x] (walk k env2) (when-not (typed-binders? (unq v)) (walk v env2)))
                           env)
                (set? x) (do (doseq [y x] (walk y env)) env)
                (vector? x) (cond (typed-binders? x) (walk-binders x env)
                                  ;; [some.ns :as alias]: the alias is not a name of the model
                                  (some #{:as} x) (do (doseq [[a b] (partition 2 1 (cons nil x))]
                                                        (if (and (= :as a) (symbol? b)) (bind! b) (walk b env)))
                                                      env)
                                  :else (reduce (fn [e y] (walk y e) e) env x))
                (seq? x) (walk-list x env)
                :else env))
            (walk-seq [xs env] (reduce (fn [e y] (walk y e)) env xs))      ; siblings see earlier bindings
            (walk-binders [v env]                                         ; returns env with the names
              (loop [xs (seq v) env env]
                (if-let [[a b c & more] xs]
                  (if (and (symbol? a) (= :- b))
                    (do (bind! a) (walk c env) (recur (seq more) (add env [a])))
                    (do (walk a env) (recur (next xs) env)))
                  env)))
            (walk-pattern [p env]                                         ; a match/case pattern
              (cond (symbol? p) (do (emit p :constructor) env)
                    (seq? p) (do (when (symbol? (first p)) (emit (first p) :constructor))
                                 (reduce (fn [e y] (if (symbol? y) (do (bind! y) (add e [y])) (walk-pattern y e))) env (rest p)))
                    (vector? p) (do (when (symbol? (first p)) (emit (first p) :constructor))
                                    (doseq [y (rest p) :when (symbol? y)] (bind! y))
                                    (add env (filter symbol? (rest p))))
                    :else env))
            (walk-list [x env]
              (let [h (first x)]
                (cond
                  ;; (quote x), (syntax-quote x), (unquote x): look through
                  ('#{quote syntax-quote unquote unquote-splicing clojure.core/unquote clojure.core/unquote-splicing var deref} h)
                  (do (walk-seq (rest x) env) env)

                  (decl-heads h)
                  (let [[_ nm binders & more] x]
                    (when (symbol? nm) (emit nm :global))
                    (let [env2 (if (vector? binders) (walk-binders binders env) (do (walk binders env) env))]
                      (walk-seq more env2))
                    env)

                  (= 'a/inductive h)                                      ; constructors are declared here
                  (let [[_ nm & more] x]
                    (when (symbol? nm) (emit nm :global))
                    (doseq [c more]
                      (if (and (seq? c) (symbol? (first c)))
                        (do (emit (first c) :constructor) (walk-seq (rest c) env))
                        (walk c env)))
                    env)

                  (clj-let-heads h)
                  (let [[_ bv & body] x]
                    (if (vector? bv)
                      (let [env2 (loop [ps (partition-all 2 bv) env env]
                                   (if-let [[t v] (first ps)]
                                     (cond (= :let t) (recur (concat (partition-all 2 v) (rest ps)) env)
                                           (keyword? t) (do (walk v env) (recur (rest ps) env))
                                           :else (do (walk v env) (doseq [y (targets t)] (bind! y))
                                                     (recur (rest ps) (add env (targets t)))))
                                     env))]
                        (walk-seq body env2))
                      (walk-seq (rest x) env))
                    env)

                  (clj-fn-heads h)
                  (let [more (rest x)
                        more (if (symbol? (first more)) (do (when ('#{defn defn- defmacro} h) (emit (first more) :global)) (rest more)) more)
                        more (drop-while #(or (string? %) (map? %)) more)
                        arities (if (vector? (first more)) [more] (filter seq? more))]
                    (doseq [[params & body] arities]
                      (if (typed-binders? params)
                        (walk-seq body (walk-binders params env))
                        (do (doseq [y (targets params)] (bind! y))
                            (walk-seq body (add env (targets params))))))
                    env)

                  (= 'letfn h)
                  (let [[_ fns & body] x
                        env2 (add env (map first fns))]
                    (doseq [f fns] (walk-list (cons 'fn f) env2))
                    (walk-seq body env2)
                    env)

                  (= 'catch h)
                  (let [[_ cls e & body] x] (when (symbol? e) (bind! e)) (walk-seq body (if (symbol? e) (add env [e]) env)) env)

                  ;; (match x [pattern body] ...)
                  (= 'match h)
                  (let [[_ scrut & clauses] x]
                    (walk scrut env)
                    (doseq [c clauses]
                      (if (and (vector? c) (= 2 (count c)))
                        (walk (second c) (walk-pattern (first c) env))
                        (walk c env)))
                    env)

                  ;; (forall [x :- T] body), (exists ...), (fn [x :- T] body) are covered by walk-binders
                  ;; through the vector case, with the names visible in the following siblings

                  ;; tactics that name what they introduce
                  (= 'have h)
                  (let [[_ nm & more] x] (walk-seq more env) (if (symbol? nm) (do (bind! nm) (add env [nm])) env))
                  (binder-tactics h)
                  (let [names (filter symbol? (take-while #(not (seq? %)) (rest x)))
                        more (drop-while #(not (seq? %)) (rest x))]
                    (walk-seq more env)
                    (doseq [y names] (bind! y))
                    (doseq [y (rest x) :when (vector? y) z (syms-in y)] (bind! z))
                    (add env (concat names (mapcat syms-in (filter vector? (rest x))))))
                  ('#{cases induction} h)                               ; (cases h term): h names the equation
                  (let [[_ a & more] x]
                    (if (and (symbol? a) (seq more))
                      (do (walk-seq more env) (bind! a) (add env [a]))
                      (do (walk-seq (rest x) env) env)))
                  ('#{case case'} h)                                    ; (case [ctor a b] tactic...): scoped
                  (let [[_ pat & body] x]
                    (walk-seq body (walk-pattern pat env))
                    env)

                  :else (walk-seq x env))))]
      (doseq [form (parse-located s)] (walk form #{}))
      @out)))

(defn offsets
  "{offset what} for the symbols of s: the offset of the symbol's name part (after a namespace
  alias and slash)."
  [s]
  (let [starts (vec (cons 0 (map inc (keep-indexed (fn [i c] (when (= c \newline) i)) s))))]
    (into {} (for [{:keys [sym row col what]} (scan s)
                   :let [off (+ (starts (dec row)) (dec col))
                         off (if-let [n (namespace sym)] (+ off (count n) 1) off)
                         ;; generator code that builds a proof term: (list 'lemma 'w F 'h2 'h0 'h1 'h3).
                         ;; A quoted hN next to other quoted hypothesis names is a hypothesis.
                         line (when (and (= what :global) (re-matches #"h\d+" (name sym)) (pos? off) (= \' (.charAt ^String s (dec off))))
                                (subs s (starts (dec row)) (let [e (.indexOf ^String s "\n" (int off))] (if (neg? e) (count s) e))))
                         what (if (and line (> (count (re-seq #"'h\d+(?![A-Za-z0-9-])" line)) 1)) :local what)]]
               [off what]))))
