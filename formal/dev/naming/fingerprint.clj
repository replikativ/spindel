;; Naming pass, the gate (JVM): load the whole model and write a name-independent fingerprint of
;; every constant's statement.
;;
;;   cd formal && clojure -Sdeps '{:aliases {:nm {:jvm-opts ["-Xmx1g" "-Xss16m"]}}}' -M:nm \
;;       dev/naming/fingerprint.clj OUT.edn
;;
;; fp(theorem)     = hash(type)                      the proof is ignored
;; fp(definition)  = hash(type, value)
;; fp(inductive)   = hash(type, constructor types)
;; fp(constructor) = hash(fp(its inductive), its index);  fp(recursor) = hash(fp(its inductive))
;; where every constant reference inside is replaced by the fingerprint of the constant it names
;; (a reference to the constant being fingerprinted: a fixed marker), and binder names are dropped.
;; No name enters, so a pure rename keeps every fingerprint. Run it before and after the
;; substitution; compare.clj maps the first output's names through notes/renames.edn.
(require '[clojure.java.io :as io] '[clojure.string :as str] '[clojure.edn :as edn])
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
(require '[ansatz.core :as a] '[ansatz.kernel.expr :as e])
(import '[ansatz.kernel Expr Env ConstantInfo Name])
(a/load-init!)
(defn cname [c] (str (.name ^ConstantInfo c)))
(def init-names (set (map cname (.allConstants ^Env @a/ansatz-env))))
(def t0 (System/currentTimeMillis))
(doseq [n (topo graph)] (require n) (println "loaded" n) (flush))
(def load-seconds (quot (- (System/currentTimeMillis) t0) 1000))
(def ^Env env @a/ansatz-env)

(def memo (java.util.HashMap.))
(declare fp)
(defn ser [^Expr x]
  (case (e/tag x)
    :bvar [:b (e/bvar-idx x)]
    :sort [:s (str (e/sort-level x))]
    :const [:c (fp (e/const-name x)) (mapv str (e/const-levels x))]
    :app [:a (ser (e/app-fn x)) (ser (e/app-arg x))]
    :lam [:l (ser (e/lam-type x)) (ser (e/lam-body x))]
    :forall [:f (ser (e/forall-type x)) (ser (e/forall-body x))]
    :let [:z (ser (e/let-type x)) (ser (e/let-value x)) (ser (e/let-body x))]
    :lit-nat [:n (str (e/lit-nat-val x))]
    :lit-str [:t (e/lit-str-val x)]
    :mdata (ser (e/mdata-expr x))
    :proj [:p (fp (e/proj-type-name x)) (e/proj-idx x) (ser (e/proj-struct x))]
    [:? (str (e/tag x))]))
(defn ci ^ConstantInfo [n] (.lookup env (if (instance? Name n) n (Name/fromString (str n)))))
(defn fp [n]
  (let [k (str n)]
    (or (.get memo k)
        (do (.put memo k (hash [:self]))                          ; a reference to itself
            (let [c (ci n)
                  h (if (nil? c) (hash [:missing])
                        (hash
                         (cond
                           (.isThm c) [:thm (ser (.type c))]
                           (.isInduct c) [:ind (ser (.type c)) (mapv #(ser (.type (ci %))) (.ctors c))]
                           (.isCtor c) [:ctor (fp (.inductName c)) (.cidx c)]
                           (.isRecursor c) [:rec (fp (subs k 0 (.lastIndexOf k ".")))]
                           (and (.isDef c) (.value c)) [:def (ser (.type c)) (ser (.value c))]
                           :else [:other (str (.tag c)) (ser (.type c))])))]
              (.put memo k h) h)))))
(def names (sort (remove init-names (map cname (.allConstants env)))))
(def fps (into (sorted-map) (for [n names] [n (fp n)])))
(binding [*print-length* nil *print-level* nil]
  (spit out (pr-str {:fp fps :count (count names) :load-seconds load-seconds})))
(println "FINGERPRINTS" (count names) "constants, load" load-seconds "s")
(shutdown-agents)
(System/exit 0)
