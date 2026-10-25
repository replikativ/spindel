(ns org.replikativ.spindel.dom.test-helpers
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.spin.combinators :as comb]
            [org.replikativ.spindel.spin.cps :refer-macros [spin]]))

(defn wait-until
  "Yield every 10 ms until pred succeeds, or fail with a named 2-second deadline."
  [description pred]
  (spin
   (let [deadline (+ (js/performance.now) 2000)]
     (loop []
       (cond
         (pred) true
         (>= (js/performance.now) deadline)
         (throw (ex-info (str "Timed out waiting for " description) {}))
         :else (do (await (comb/sleep 10)) (recur)))))))
