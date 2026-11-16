;; C0 async-sequence log samples for the oracle (samples 18-21): each world's own log.
;; From the repository root: clojure -M:bench -i formal/test/spindel/v2/oracle/gen/samples-seq.clj
(ns samples-seq
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.v2.core :as v2 :refer [task await aseq]]
            [org.replikativ.spindel.v2.verify :as verify]
            [clojure.pprint]))

(def dir "formal/test/spindel/v2/oracle/")
(defn dump! [path l] (spit path (with-out-str (clojure.pprint/pprint l))) [path (count l) (frequencies (map (comp first :item) l))])
(defn vworld [acc] (v2/world {:verify? true :hook (verify/projecting-hook (verify/checking-hook acc))}))
(defn walk [p] (task (loop [p p acc []] (if-let [[v nx] (await p)] (recur nx (conj acc v)) acc))))

;; 18: a pull sequence of two elements read by two tasks: one realization per element, shared;
;; the second reader finds the realized links.
(let [acc (atom []) w (vworld acc)]
  (binding [v2/*world* w]
    (let [xs (aseq [n 0] (when (< n 2) [n (inc n)]))
          a (walk xs)
          b (walk xs)]
      (prn (v2/value a 2000 :timeout) (v2/value b 2000 :timeout))
      (prn (dump! (str dir "log-sample-18.edn") (verify/log w)))
      (prn :divergences @acc))))

;; 19: a fork while an element's realizer is parked on an offload. The parent's realizer finishes;
;; in the child it ends with ::forked at the child's first turn, the link stays unrealized and,
;; demanded by the child's copy of the reader, a new realizer starts there.
(let [acc (atom []) w (vworld acc) gate (promise)]
  (binding [v2/*world* w]
    (let [xs (aseq [n 0] (when (< n 1) [(v2/offload (fn [] (deref gate 5000 :late))) (inc n)]))
          r (task (first (await xs)))
          _ (v2/value (v2/signal 0) 200 nil)
          child (v2/fork! w)]
      (binding [v2/*world* child] (v2/value-async (v2/in-world child r) (fn [_ _])))
      (Thread/sleep 100)
      (deliver gate :v)
      (prn (v2/value r 2000 :timeout) (binding [v2/*world* child] (v2/value (v2/in-world child r) 2000 :timeout)))
      (Thread/sleep 100)
      (v2/value (v2/signal 0) 200 nil)
      (prn (dump! (str dir "log-sample-19-parent.edn") (verify/log w)))
      (prn (dump! (str dir "log-sample-19-child.edn") (verify/log child)))
      (prn :divergences @acc))))

;; 20: a stream read by a task in each world: appends after the fork go to the world that makes
;; them; each world closes its stream and its reader ends.
(let [acc (atom []) w (vworld acc)]
  (binding [v2/*world* w]
    (let [s (v2/stream)
          _ (v2/append! s :before)
          r (walk (v2/position s))
          _ (v2/value (v2/signal 0) 200 nil)
          child (v2/fork! w)
          cs (v2/in-world child s)]
      (v2/append! s :parent)
      (v2/append! cs :child)
      (v2/close! s)
      (v2/close! cs)
      (prn (v2/value r 2000 :timeout) (binding [v2/*world* child] (v2/value (v2/in-world child r) 2000 :timeout)))
      (prn (dump! (str dir "log-sample-20-parent.edn") (verify/log w)))
      (prn (dump! (str dir "log-sample-20-child.edn") (verify/log child)))
      (prn :divergences @acc))))

;; 21: a reader cancelled while the element it demanded is being realized (the realizer awaits a
;; deferred): the realization continues (it belongs to the root scope) and a later reader gets it.
(let [acc (atom []) w (vworld acc)]
  (binding [v2/*world* w]
    (let [d (v2/deferred)
          xs (aseq [n 0] (when (< n 1) [(await d) (inc n)]))
          r1 (task (first (await xs)))
          _ (v2/value (v2/signal 0) 200 nil)]
      (v2/cancel-task! r1)
      (v2/deliver! d :v)
      (let [r2 (task (first (await xs)))]
        (prn (v2/value r2 2000 :timeout)))
      (prn (dump! (str dir "log-sample-21.edn") (verify/log w)))
      (prn :divergences @acc))))

(shutdown-agents)
(System/exit 0)
