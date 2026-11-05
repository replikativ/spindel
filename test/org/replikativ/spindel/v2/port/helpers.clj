(ns org.replikativ.spindel.v2.port.helpers
  (:require [clojure.test :refer [is]]
            [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.verify :as verify]))

(defn checked-fixture [f]
  (let [divergences (atom [])
        w (v2/world {:verify? true :hook (verify/checking-hook divergences)})]
    (try
      (binding [v2/*world* w] (f))
      (finally
        (v2/release-world! w)
        (is (empty? @divergences)
            (str "Rule R divergences: " (vec (take 3 @divergences))))))))

(defn outcome [h]
  (try [:ok (v2/value h 5000 ::timeout)] (catch Throwable e [:err e])))

(defn wait-until [pred]
  (let [deadline (+ (System/nanoTime) 5000000000)]
    (loop []
      (cond (pred) true
            (> (System/nanoTime) deadline) false
            :else (do (Thread/sleep 5) (recur))))))

(defn api [sym]
  ;; Missing public operations are executable gap assertions, not load errors.
  (let [f (or (ns-resolve 'org.replikativ.spindel.v2.core sym)
              (do (require 'org.replikativ.spindel.v2.combinators)
                  (ns-resolve 'org.replikativ.spindel.v2.combinators sym)))]
    (is (some? f) (str "Missing v2 public API: " sym))
    f))

(defmacro hot-spin [& body]
  ;; Old eager-reactivity tests hold explicit demand on v2 computations.
  `(let [h# (v2/spin ~@body)]
     (v2/observe! h# (fn [_# _err?#]))
     h#))
