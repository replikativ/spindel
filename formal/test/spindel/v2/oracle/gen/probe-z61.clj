;; Engine probes for Z#61 (await-all fail-fast) and the group-await fast path, written by the formal
;; side to check the model against the engine (engine-v2 3600588); not numbered samples.
;;  1  a computation awaits `any` over two signals: the fast path stops at the first (the second's dep
;;     edge stays armed; no invalidation of the computation)
;;  2  a task awaits `all` over a task that fails later and a task parked on a deferred: the failure
;;     resumes the awaiter at once and the parked member task is cancelled (a loser)
;;  3  as 2 with the failed task already complete: the fast path completes the `all` at once
;;  4  a computation awaits `all` over a failed computation and two signals: the fast path stops at
;;     the failure (the signals' dep edges stay armed, unread)
;; From the repository root: clojure -M:bench -i formal/test/spindel/v2/oracle/gen/probe-z61.clj
(ns probe-z61
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.v2.core :as v2 :refer [task await spin track]]
            [org.replikativ.spindel.v2.verify :as verify]
            [clojure.pprint]))
(def dir "formal/test/spindel/v2/oracle/")
(defn dump! [path l] (spit path (with-out-str (clojure.pprint/pprint l))) [path (count l) (frequencies (map (comp first :item) l))])
(defn vworld [acc] (v2/world {:verify? true :hook (verify/projecting-hook (verify/checking-hook acc))}))
(defn settle [] (Thread/sleep 60))

;; P1: a computation awaits any over two signals (both read at once): first fills, the second?
(let [acc (atom []) w (vworld acc)]
  (binding [v2/*world* w]
    (let [s1 (v2/signal 1) s2 (v2/signal 2)
          c (spin (v2/await-any [s1 s2]))]
      (prn :p1 (v2/value c 2000 :timeout))
      (settle)
      (prn (dump! (str dir "log-probe-z61-1.edn") (verify/log w)))
      (prn :p1-div @acc))))

;; P2: a task awaits all over [failing task, long task]: fail-fast, the long task is a loser
(let [acc (atom []) w (vworld acc)]
  (binding [v2/*world* w]
    (let [d (v2/deferred) e (v2/deferred)
          t (task (let [a (task (do (await d) (throw (ex-info "boom" {}))))
                        b (task (await e))]
                    (try (v2/await-all [a b]) (catch Exception x :failed))))]
      (settle)
      (v2/deliver! d 1)
      (prn :p2 (v2/value t 2000 :timeout))
      (settle)
      (prn (dump! (str dir "log-probe-z61-2.edn") (verify/log w)))
      (prn :p2-div @acc))))

;; P3: a task awaits all over [already-failed task, long task] (fast path)
(let [acc (atom []) w (vworld acc)]
  (binding [v2/*world* w]
    (let [e (v2/deferred)
          t (task (let [a (task (throw (ex-info "boom" {})))
                        _ (try (await a) (catch Exception _ nil))
                        b (task (await e))]
                    (try (v2/await-all [a b]) (catch Exception x :failed))))]
      (prn :p3 (v2/value t 2000 :timeout))
      (settle)
      (prn (dump! (str dir "log-probe-z61-3.edn") (verify/log w)))
      (prn :p3-div @acc))))

;; P4: a computation awaits all over [signal, failing computation] (fast path in a computation)
(let [acc (atom []) w (vworld acc)]
  (binding [v2/*world* w]
    (let [s1 (v2/signal 1)
          f (spin (throw (ex-info "bad" {})))
          _ (try (v2/value f 2000 :timeout) (catch Exception _ nil))
          s2 (v2/signal 2)
          c (spin (try (v2/await-all [f s1 s2]) (catch Exception x :failed)))]
      (prn :p4 (v2/value c 2000 :timeout))
      (settle)
      (prn (dump! (str dir "log-probe-z61-4.edn") (verify/log w)))
      (prn :p4-div @acc))))
