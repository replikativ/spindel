;; Oracle samples 4 and 5, reconstructed from their logs (engine a28563d had no generator in
;; the repository). Same scenario and item sequence; regenerated for [:finally-leave r].
;; From the repository root: clojure -M:bench -i formal/test/spindel/v2/oracle/gen/samples-legacy-4-5.clj
(ns samples-legacy-4-5
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.v2.core :as v2 :refer [task await spin track take!]]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.verify :as verify]
            [clojure.pprint]))

(def dir "formal/test/spindel/v2/oracle/")
(defn dump! [path l] (spit path (with-out-str (clojure.pprint/pprint l))) [path (count l) (frequencies (map (comp first :item) l))])
(defn vworld [acc] (v2/world {:verify? true :hook (verify/projecting-hook (verify/checking-hook acc))}))
(defn settle [] (Thread/sleep 50))

;; 4: a task spawns a child that takes from a mailbox, awaits an observed-later computation and a
;; deferred together, then awaits the child inside a try/finally; the host observes the
;; computation, writes its signal, delivers the deferred and posts to the mailbox. Then a task
;; parked inside try/finally on its own deferred is cancelled, and the observer is withdrawn.
(let [acc (atom []) w (vworld acc)]
  (binding [v2/*world* w]
    (let [s (v2/signal 2)
          c (spin (* 2 (iv/get-new (track s))))
          d (v2/deferred)
          mb (v2/mailbox)
          t (task (let [k (task (take! mb))]
                    (v2/await-all [c d])
                    (try (await k) (finally nil))))]
      (settle)
      (let [unobserve (v2/observe! c (fn [_ _]))]
        (v2/write! s 3)
        (settle)
        (v2/deliver! d :d)
        (settle)
        (v2/post! mb :m)
        (prn :sample-4 (v2/value t 2000 :timeout))
        (let [t2 (task (let [e (v2/deferred)] (try (await e) (finally nil))))]
          (settle)
          (v2/cancel-task! t2)
          (settle)
          (unobserve)))
      (Thread/sleep 50)
      (prn (dump! (str dir "log-sample-4.edn") (verify/log w)))
      (prn :divergences @acc))))

;; 5: a task makes a signal and a mailbox and returns them; a computation tracks the signal;
;; a second task opens a scope with two children awaiting a deferred, detaches one to the root,
;; awaits a third child and returns the detached one; the scope's close cancels the other.
(let [acc (atom []) w (vworld acc)]
  (binding [v2/*world* w]
    (let [d (v2/deferred)
          [sig mb] (v2/value (task [(v2/signal 5) (v2/mailbox)]) 2000 :timeout)
          c (spin (iv/get-new (track sig)))
          u (v2/observe! c (fn [_ _]))
          _ (settle)
          _ (v2/write! sig 6)
          _ (v2/post! mb :late)
          t2 (task (v2/with-scope
                     (task (await d))
                     (let [b (task (await d))]
                       (v2/detach! b (v2/root-scope v2/*world*))
                       (await (task :x))
                       b)))
          b (v2/value t2 2000 :timeout)]
      (v2/deliver! d :d)
      (prn :sample-5 (v2/value b 2000 :timeout))
      (u)
      (Thread/sleep 50)
      (prn (dump! (str dir "log-sample-5.edn") (verify/log w)))
      (prn :divergences @acc))))

(shutdown-agents)
(System/exit 0)
