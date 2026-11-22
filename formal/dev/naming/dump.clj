;; Naming pass, step 1 (JVM): load the whole model and dump what the rename map is computed from.
;;
;;   cd formal && clojure -Sdeps '{:aliases {:nm {:jvm-opts ["-Xmx1g" "-Xss16m"]}}}' -M:nm dev/naming/dump.clj OUT.edn
;;
;; OUT.edn = {:constants {name kind}      every constant the model adds (kind: :thm :def :ind :ctor :rec :other)
;;            :init      #{name}          Init names with no "." (the ones a kebab-case name could meet)
;;            :init-count n
;;            :bundles   [{:var :pred :params :prefix :extra :renames :copied}]   every pres.part bundle
;;            :tree-parts, :tree-derived, :part-views, :footprints, :views, :exempt   the generators' registries
;;            :added     [[ns [name ...]] ...]   the constants each namespace adds, in load order
;;            :order     [ns ...]}
(require '[clojure.java.io :as io] '[clojure.string :as str])
(def out (first *command-line-args*))
(def files (->> (file-seq (io/file "src/spindel")) (filter #(str/ends-with? (str %) ".clj"))))
(defn ns-form [f] (with-open [r (java.io.PushbackReader. (io/reader f))] (read r)))
(defn sym-deps [form]
  (let [req (some #(when (and (seq? %) (= :require (first %))) (rest %)) form)]
    (->> (flatten (map #(if (coll? %) (seq %) [%]) req))
         (filter symbol?) (filter #(str/starts-with? (str %) "spindel.")) set)))
(def graph (into {} (for [f files :let [fm (ns-form f)]] [(second fm) (disj (sym-deps fm) (second fm))])))
(defn topo [g]
  (loop [done [] seen #{} todo (sort (keys g))]
    (if (empty? todo) done
      (let [ready (filter #(every? seen (get g %)) todo)]
        (when (empty? ready) (throw (ex-info "cycle" {:todo todo})))
        (recur (into done ready) (into seen ready) (remove (set ready) todo))))))
(def order (topo graph))
(require '[ansatz.core :as a])
(a/load-init!)
(defn cname [c] (str (.name ^ansatz.kernel.ConstantInfo c)))
(def init-names (set (map cname (.allConstants ^ansatz.kernel.Env @a/ansatz-env))))
;; per namespace: the constants it adds (in load order), so a name's file is known
(def added (atom []))
(doseq [n order]
  (let [before (set (map cname (.allConstants ^ansatz.kernel.Env @a/ansatz-env)))]
    (require n)
    (swap! added conj [n (vec (sort (remove before (map cname (.allConstants ^ansatz.kernel.Env @a/ansatz-env)))))])
    (println "loaded" n) (flush)))
(def env @a/ansatz-env)
(defn kind [^ansatz.kernel.ConstantInfo c]
  (cond (.isThm c) :thm (.isInduct c) :ind (.isCtor c) :ctor (.isRecursor c) :rec (.isDef c) :def :else :other))
(def constants (into (sorted-map) (for [c (.allConstants ^ansatz.kernel.Env env) :when (not (init-names (cname c)))] [(cname c) (kind c)])))
(defn bundle? [v] (and (map? v) (contains? v :pred) (contains? v :prefix) (contains? v :renames)))
(defn plain [x] (cond (instance? clojure.lang.IDeref x) (plain @x)
                      (map? x) (into {} (for [[k v] x] [(plain k) (plain v)]))
                      (set? x) (set (map plain x))
                      (coll? x) (mapv plain x)
                      (fn? x) :fn
                      :else x))
(def bundles
  (vec (for [n (all-ns) :when (str/starts-with? (str (ns-name n)) "spindel.")
             [s v] (ns-interns n) :when (and (bound? v) (bundle? @v))]
         (let [b @v] {:var (symbol (str (ns-name n)) (str s)) :pred (:pred b) :params (:params b) :prefix (:prefix b)
                      :extra (plain (:extra-args b)) :renames (plain (:renames b)) :copied (plain (:copied b))}))))
(defn reg [nsym vsym] (some-> (ns-resolve (the-ns nsym) vsym) deref plain))
(binding [*print-length* nil *print-level* nil]
  (spit out (pr-str {:constants constants
                     :added @added
                     :init (set (remove #(str/includes? % ".") init-names))
                     :init-count (count init-names)
                     :bundles bundles
                     :tree-parts (reg 'spindel.v2.pres.tree 'parts)
                     :tree-derived (vec (keys (reg 'spindel.v2.pres.tree 'derived)))
                     :part-views (reg 'spindel.v2.pres.part 'parts)
                     :footprints (reg 'spindel.v2.pres.frames 'footprints)
                     :views (reg 'spindel.v2.pres.frames 'views)
                     :exempt (reg 'spindel.v2.pres.exempt 'forms)
                     :order order})))
(println "DUMPED" (count constants) "constants," (count bundles) "bundles")
(shutdown-agents)
(System/exit 0)
