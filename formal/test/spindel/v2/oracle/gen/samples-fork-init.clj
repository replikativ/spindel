;; Host forks with `:init-state` (spec §8.1 F, sample 66): each world's own log.
;;
;; 66  root: a signal, an observed computation, a task parked on a deferred. Then
;;     (1) a host fork whose initializer throws: the child id it was given stays unused (an
;;         allocator gap), no item;
;;     (2) an ordinary allocation (a signal);
;;     (3) a host fork with an initializer (:child); the child writes the signal and delivers
;;         the deferred, so its copy of the task completes;
;;     (4) from inside one host item of the root: a task spawned, then a host fork of the root
;;         (H1, the held-gate path, :held); the held child runs its copy of the new task and
;;         completes its copy of the parked one on its own delivery.
;;     The replay checks the family's allocator alignment around the refused fork (1)-(3):
;;     every world replays with no divergence and no resync.
;;
;; From the worktree root (one -Xmx1g JVM):
;;   clojure -J-Xmx1g -M:bench -i formal/test/spindel/v2/oracle/gen/samples-fork-init.clj
(ns samples-fork-init
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.v2.core :as v2 :refer [task spin await track]]
            [org.replikativ.spindel.v2.verify :as verify]
            [org.replikativ.spindel.incremental.interval :as iv]
            [clojure.pprint]))

(def dir "formal/test/spindel/v2/oracle/")
(defn dump! [path l]
  (spit path (with-out-str (clojure.pprint/pprint l)))
  [path (count l) (frequencies (map (comp first :item) l))])
(defn vworld [acc] (v2/world {:verify? true :hook (verify/projecting-hook (verify/checking-hook acc))}))

;; 66
(let [acc (atom []) w (vworld acc)]
  (binding [v2/*world* w]
    (let [s (v2/signal 1)
          c (spin (* 2 (iv/get-new (track s))))
          _ (v2/observe! c (fn [_ _]))
          d (v2/deferred)
          t (task (await d))
          refused (try (v2/fork! w {:init-state (fn [_ _] (throw (ex-info "init failed" {})))})
                       (catch Exception e (ex-message e)))
          _ (v2/signal 2)
          child (v2/fork! w {:init-state (fn [s _] (assoc s :k 1))})
          _ (v2/write! (v2/in-world child s) 5)
          _ (v2/deliver! (v2/in-world child d) :child)
          held (v2/host-call! w (fn []
                                  (binding [v2/*world* w] (task (+ 1 2)))
                                  (v2/fork! w {:init-state (fn [s _] (assoc s :k 2))})))]
      (prn :66-refused refused)
      (prn :66-child (binding [v2/*world* child] [(v2/value (v2/in-world child t) 2000 :timeout)
                                                   (v2/value (v2/in-world child c) 2000 :timeout)
                                                   (v2/world-state child)]))
      (v2/deliver! (v2/in-world held d) :held)
      (prn :66-held (binding [v2/*world* held] [(v2/value (v2/in-world held t) 2000 :timeout)
                                                 (v2/world-state held)]))
      (v2/deliver! d :root)
      (prn :66-root [(v2/value t 2000 :timeout) (v2/world-state w)])
      (Thread/sleep 100)
      (prn (dump! (str dir "log-sample-66-root.edn") (verify/log w)))
      (prn (dump! (str dir "log-sample-66-child.edn") (verify/log child)))
      (prn (dump! (str dir "log-sample-66-held.edn") (verify/log held)))
      (prn :66-divergences @acc))))
