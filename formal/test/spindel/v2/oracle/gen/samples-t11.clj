;; Z#81 no re-entry inside a running finally clause: oracle log samples 63-65 (engine-v2, the T11 running-clause
;; fix). A dep edge registered while the run executes a finally clause restarts the body on invalidation; before,
;; T11 resumed the new run inside a clause it never entered and its end committed an orphan finally-leave.
;;
;; 63  w: a computation's finally clause tracks a signal and, at 1, awaits an unresolved deferred. Writing 1 reruns
;;     it from the body; its clause's await is refused (B8: the new run does run a clause), the deferred is
;;     delivered afterwards.
;; 64  w: a computation's finally clause awaits a live computation (no suspension); that computation's change
;;     invalidates it at the site inside the clause, and the rerun starts from the body.
;; 65  w: a task calls `leave-finalizer!` with no running clause: a refused [:finally-leave r]; the task fails.
;;
;; From the repository root (one -Xmx1g JVM):
;;   clojure -J-Xmx1g -Sdeps '{:paths ["src" "test"]}' -M -i formal/test/spindel/v2/oracle/gen/samples-t11.clj
;; Generated logs are registered in oracle_test.clj (`running-clause-specs`).
(ns samples-t11
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await]]
            [org.replikativ.spindel.v2.verify :as verify]
            [org.replikativ.spindel.incremental.interval :as iv]
            [clojure.pprint]))

(def dir "formal/test/spindel/v2/oracle/")
(defn dump! [path l]
  (spit path (with-out-str (clojure.pprint/pprint l)))
  [path (count l) (frequencies (map (comp first :item) l))])
(defn vworld [acc] (v2/world {:verify? true :hook (verify/projecting-hook (verify/checking-hook acc))}))
(defn- in [w g] (binding [v2/*world* w] (g)))

(defn finish! [n w acc]
  (v2/release-world! w)
  (assert (true? (v2/await-complete w 2000 :timeout)) "the world completes")
  (prn (dump! (str dir "log-sample-" n "-w.edn") (verify/log w)))
  (prn :sample n :divergences @acc))

;; 63
(let [acc (atom []) w (vworld acc) seen (atom [])
      [s d c] (in w #(let [s (v2/signal 0) d (v2/deferred)]
                       [s d (spin (try :v
                                       (finally
                                         (let [x (iv/get-new (track s))]
                                           (when (= 1 x) (await d))))))]))]
  (v2/observe! c (fn [v err?] (swap! seen conj [(if err? (:spindel/invalid (ex-data v)) v) err?])))
  (Thread/sleep 50)
  (v2/write! s 1)
  (Thread/sleep 50)
  (assert (= [[:v false] [:finalizer true]] @seen) "the rerun's await in its clause is refused")
  (v2/deliver! d :late)
  (Thread/sleep 50)
  (finish! 63 w acc))

;; 64
(let [acc (atom []) w (vworld acc) runs (atom 0)
      [s c] (in w #(let [s (v2/signal 0)
                         inner (spin (iv/get-new (track s)))]
                     (v2/observe! inner (fn [_ _]))
                     [s (spin (try (swap! runs inc) :v (finally (await inner))))]))]
  (v2/observe! c (fn [_ _]))
  (Thread/sleep 50)
  (v2/write! s 1)
  (Thread/sleep 50)
  (assert (= 2 @runs) "the rerun started from the body")
  (finish! 64 w acc))

;; 65
(let [acc (atom []) w (vworld acc)
      t (in w #(task (v2/leave-finalizer!) :unreached))
      r (try (v2/value t 2000 :timeout) (catch clojure.lang.ExceptionInfo e (:spindel/invalid (ex-data e))))]
  (assert (= :finally-leave r) "the task fails with the refusal")
  (finish! 65 w acc))

(shutdown-agents)
