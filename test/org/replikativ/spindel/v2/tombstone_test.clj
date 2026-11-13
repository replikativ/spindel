(ns org.replikativ.spindel.v2.tombstone-test
  "§3.2: a run in cleanup keeps its computation as a tombstone. A cancelled blocking computation
  whose worker has not joined stays a row until the worker returns, whether its last handle is
  dropped or its world is released; Rule R by counts agrees with the reference at every commit."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is]]
            [org.replikativ.spindel.v2.core :as v2 :refer [task await]]
            [org.replikativ.spindel.v2.combinators :as comb]
            [org.replikativ.spindel.v2.verify :as verify]))

(defn- run [how]
  (let [div (atom [])
        w (v2/world {:verify? true :hook (verify/checking-hook div)})
        started (promise) interrupted (promise) go (promise)]
    (binding [v2/*world* w]
      (let [b (comb/blocking (fn [] (deliver started true)
                               (try (Thread/sleep 30000)
                                    (catch InterruptedException _
                                      (deliver interrupted true)
                                      ;; the worker returns late, so its join is late
                                      (deref go 5000 nil)))))
            t (task (await b))]
        (is (true? (deref started 5000 false)))
        (v2/cancel-task! t)
        (is (true? (deref interrupted 5000 false)))
        (case how :world (v2/release-world! w) :handle (v2/release! b))
        (is (empty? @div) "while the worker has not joined")
        (deliver go true)
        (let [left (v2/release-world! w)
              deadline (+ (System/nanoTime) 5000000000)]
          (while (and (pos? (left)) (< (System/nanoTime) deadline)) (Thread/sleep 5))
          (is (zero? (left)) "nothing is left once the worker joined")
          (is (empty? @div)))))))

(deftest world-released-before-the-worker-joins (run :world))
(deftest last-handle-dropped-before-the-worker-joins (run :handle))
