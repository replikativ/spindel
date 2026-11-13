(ns org.replikativ.spindel.v2.port.support
  (:require [clojure.test :refer [is]]
            [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.verify :as verify]))

(def ^:dynamic *divergences* nil)
(def ^:dynamic *observed* nil)

(defn vworld []
  (v2/world {:verify? true :hook (verify/checking-hook *divergences*)}))

(defn checking [f]
  (binding [*divergences* (atom []) *observed* (atom #{})]
    (f)
    (is (empty? @*divergences*)
        (str "Rule R divergences: " (vec (take 3 @*divergences*))))))

(defmacro with-world [[w] & body]
  `(let [~w (vworld)]
     (try (binding [v2/*world* ~w] ~@body)
          (finally (v2/release-world! ~w)))))

(defn outcome [h]
  (try [:ok (v2/value h 2000 ::timeout)]
       (catch Throwable e [:err e])))

(defn check-result [h on-success on-error]
  (let [[tag v] (outcome h)]
    ((if (= tag :ok) on-success on-error) v)))

(defn observed-value
  "Keep reactive test roots demanded across writes, using one observation
   per handle. Unlike a one-shot host read, this tests hot propagation."
  [h]
  (when-not (contains? @*observed* h)
    (swap! *observed* conj h)
    (v2/observe! h (fn [_ _])))
  (v2/value h 2000 ::timeout))

(defn wait-until [f]
  (loop [n 0]
    (cond (f) true (>= n 400) false
          :else (do (Thread/sleep 5) (recur (inc n))))))

(defn required-api [sym]
  ;; Missing public helpers remain executable gaps, without a substitute
  ;; implementation in the test suite or a compile-time unresolved var.
  (or (ns-resolve 'org.replikativ.spindel.v2.core sym)
      (ns-resolve 'org.replikativ.spindel.v2.combinators sym)
      (do (require 'org.replikativ.spindel.v2.result) (ns-resolve 'org.replikativ.spindel.v2.result sym))
      (throw (ex-info (str "Missing v2 public API: " sym) {:missing-api sym}))))
