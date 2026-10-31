(ns diagnose-lowering
  (:require [clojure.java.io :as io]
            [collection-bench :as bench]
            [is.simm.partial-cps.ioc]
            [is.simm.partial-cps.async]))

(defn load-reference [path]
  (let [scope (or (find-ns 'collection-bench-reference) (create-ns 'collection-bench-reference))]
    (binding [*ns* scope]
      (refer 'clojure.core)
      (alias 'ioc 'is.simm.partial-cps.ioc)
      (alias 'async 'is.simm.partial-cps.async)
      (with-open [reader (java.io.PushbackReader. (io/reader path))]
        (loop []
          (let [form (read {:read-cond :allow :features #{:clj} :eof ::done} reader)]
            (when-not (= ::done form)
              (cond
                (and (seq? form) (= 'do (first form))
                     (some #(and (seq? %) (= 'def (first %)) (= 'hof-names (second %))) (rest form)))
                (eval form)
                (and (seq? form) (= 'defn (first form)) (= 'build-cps-fn (second form)))
                (eval form))
              (recur))))))
    (ns-resolve scope 'build-cps-fn)))

(defn canonical [form & [metadata?]]
  (let [names (atom {})]
    (letfn [(visit [x]
              (let [value (cond
                            (and (symbol? x) (nil? (namespace x)) (re-find #"\d" (name x)))
                            (or (get @names x)
                                (let [name (symbol (str "generated-" (count @names)))]
                                  (swap! names assoc x name) name))
                            (list? x) (apply list (map visit x))
                            (vector? x) (mapv visit x)
                            (map? x) (into {} (map (fn [[k v]] [(visit k) (visit v)])) x)
                            (set? x) (set (map visit x))
                            (seq? x) (doall (map visit x))
                            :else x)
                    compiler-meta (when metadata?
                                    (select-keys (meta x) [:tag :rettag :once :volatile-mutable
                                                           :unsynchronized-mutable]))]
                (if (seq compiler-meta) [:compiler-meta value compiler-meta] value)))]
      (visit form))))

(defn compare-lowering [reference-path]
  (let [reference (load-reference reference-path)]
    (binding [*ns* (the-ns 'collection-bench)]
      (into {}
            (for [kind [:loop-vector :loop-sum :pure-mapv]
                  :let [body (get bench/forms kind)
                        before (reference (list body) is.simm.partial-cps.async/breakpoints {'xs true 'step true})
                        after (bench/lower body)]]
              [kind {:alpha-equivalent? (= (canonical before) (canonical after))
                     :compiler-meta-equivalent? (= (canonical before true) (canonical after true))
                     :before-nodes (count (tree-seq coll? seq before))
                     :after-nodes (count (tree-seq coll? seq after))}])))))

(defn within-jvm [reference-path]
  (let [reference (load-reference reference-path)
        body (get bench/forms :loop-sum)
        before (binding [*ns* (the-ns 'collection-bench)]
                 (bench/compile-lowered (reference (list body) is.simm.partial-cps.async/breakpoints
                                                  {'xs true 'step true})))
        after (bench/compile-task body)
        a (bench/synchronous-runner before (vec (range 1024)))
        b (bench/synchronous-runner after (vec (range 1024)))]
    {:reference (bench/benchmark a {}) :candidate (bench/benchmark b {})
     :reference-again (bench/benchmark a {})}))

(defn identical-clones [n]
  (mapv (fn [id]
          (let [factory (bench/compile-task (get bench/forms :loop-sum))
                runner (bench/synchronous-runner factory (vec (range 1024)))]
            {:clone id :result (bench/benchmark runner {})})) (range n)))
