;; Oracle sample 1, reconstructed from its legacy log (no generator in the repository): a
;; computation tracks a signal, is observed, the signal is written, the observer is withdrawn.
;; Samples 2 and 3 were sample 4's scenario; sample 4 is their regeneration.
;; From the repository root: clojure -M:bench -i formal/test/spindel/v2/oracle/gen/samples-legacy-1.clj
(ns samples-legacy-1
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.v2.core :as v2 :refer [spin track]]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.verify :as verify]
            [clojure.pprint]))

(def dir "formal/test/spindel/v2/oracle/")
(defn dump! [path l] (spit path (with-out-str (clojure.pprint/pprint l))) [path (count l) (frequencies (map (comp first :item) l))])
(defn vworld [acc] (v2/world {:verify? true :hook (verify/projecting-hook (verify/checking-hook acc))}))
(defn settle [] (Thread/sleep 50))

(let [acc (atom []) w (vworld acc)]
  (binding [v2/*world* w]
    (let [s (v2/signal 1)
          c (spin (* 2 (iv/get-new (track s))))
          seen (atom [])
          unobserve (v2/observe! c (fn [v _] (swap! seen conj v)))]
      (settle)
      (v2/write! s 2)
      (settle)
      (unobserve)
      (Thread/sleep 50)
      (prn :sample-1 @seen)
      (prn (dump! (str dir "log-sample-1.edn") (verify/log w)))
      (prn :divergences @acc))))

(shutdown-agents)
(System/exit 0)
