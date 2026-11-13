(ns org.replikativ.spindel.v2.port.support2
  (:require [clojure.test :refer [is]]
            [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.verify :as verify]))

(defn fixture [f]
  (let [divergences (atom [])
        w (v2/world {:verify? true :hook (verify/checking-hook divergences)})]
    (binding [v2/*world* w]
      (try (f)
           (finally
             (v2/release-world! w)
             (is (empty? @divergences)
                 (str "Rule R divergences: " (vec (take 3 @divergences)))))))))

(defn outcome [h]
  (try [:ok (v2/value h 2000 ::timeout)]
       (catch Exception e [:err e])))

(defn result [h] (second (outcome h)))

(defn wait-until [f]
  (let [deadline (+ (System/nanoTime) 2000000000)]
    (loop []
      (cond (f) true
            (> (System/nanoTime) deadline) false
            :else (do (Thread/sleep 5) (recur))))))
