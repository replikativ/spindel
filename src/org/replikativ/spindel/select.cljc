(ns org.replikativ.spindel.select
  "Selections of savepoint sites: which sites an operation acts on.

  A selector is a predicate over a site descriptor
  `{:address a :path p :site s}` — the address the site ran under, its
  readable path (see `addressing/site-address+path!`) and its site kind.
  `regenerate`, block moves, and interventions take selectors, so a caller
  names sites the way it named them in the program: `(id :mu)`,
  `(path [:step :* :x])`, `(prefix [:step])`.")

(defn describe
  "The descriptor of a trace entry (`address` + entry) or of a savepoint
  (`sp` alone)."
  ([sp]
   {:address (:savepoint/address sp) :path (:savepoint/path sp) :site (:savepoint/site sp)})
  ([address entry]
   {:address address :path (:path entry) :site (:site entry)}))

(defn selects?
  "Whether `selector` selects the site described by `descriptor`."
  [selector descriptor]
  (boolean (selector descriptor)))

(defn id
  "The site named `x` (its `:id`, scalar or hierarchical vector)."
  [x]
  (fn [{:keys [address]}] (= x address)))

(defn addresses
  "The sites with these addresses."
  [addrs]
  (let [s (set addrs)] (fn [{:keys [address]}] (contains? s address))))

(defn- element-matches? [pattern-element element]
  (or (= :* pattern-element) (= pattern-element element)))

(defn path
  "The sites whose path matches `pattern` element by element; `:*` matches
  any one element. `(path [:step :* :x])` selects `[:step 3 :x]`."
  [pattern]
  (fn [{p :path}]
    (and (= (count pattern) (count p))
         (every? true? (map element-matches? pattern p)))))

(defn prefix
  "The sites whose path starts with `pattern` (`:*` as in `path`): Gen's
  selection of a whole namespace, `(prefix [:step])`."
  [pattern]
  (fn [{p :path}]
    (and (<= (count pattern) (count p))
         (every? true? (map element-matches? pattern p)))))

(defn site
  "The sites of kind `kind` (e.g. `:inference/choose`)."
  [kind]
  (fn [{s :site}] (= kind s)))

(def all (constantly true))
(def none (constantly false))

(defn union [& selectors]
  (fn [d] (boolean (some #(% d) selectors))))

(defn intersection [& selectors]
  (fn [d] (every? #(% d) selectors)))

(defn complement* [selector]
  (fn [d] (not (selector d))))
