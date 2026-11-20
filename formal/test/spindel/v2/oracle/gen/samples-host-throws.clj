;; Z#78 host throws: oracle log samples 61-62 (engine-v2 a1e7b88, PR #316). A queued host item or a host
;; callback that throws belongs to its caller: the thread that drives the turn reports it and the turn goes on.
;; The model has no host exceptions (a throwing item commits nothing); these samples pin that the items after
;; the throw still commit, in the order they were queued.
;;
;; 61  w: while w's gate is held, a `send-world!` item that throws is queued, then (from other threads) a host
;;     write, a `send-world!` item that writes, and a host task start; then the gate is released. The drainer
;;     processes all four in one turn: no item for the throw, then [:write s 1], [:write s 2], [:spawn-top ..].
;; 62  w: two observers of a signal, the first throws on every delivery; three writes. Every write commits and the
;;     second observer sees every value; the writer never receives the observer's exception.
;;
;; From the repository root, with the engine's `src` first on the classpath (one -Xmx1g JVM), e.g.
;;   clojure -J-Xmx1g -Sdeps '{:paths ["../spindel-v2-aseq/src" "../spindel-v2-aseq/test"]}' -M \
;;     -i formal/test/spindel/v2/oracle/gen/samples-host-throws.clj
;; Generated logs are registered in oracle_test.clj (`host-throw-specs`).
(ns samples-host-throws
  (:require [org.replikativ.spindel.v2.core :as v2 :refer [task]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.host :as hs]
            [org.replikativ.spindel.v2.verify :as verify]
            [clojure.pprint]))

(def dir "formal/test/spindel/v2/oracle/")
(defn dump! [path l]
  (spit path (with-out-str (clojure.pprint/pprint l)))
  [path (count l) (frequencies (map (comp first :item) l))])
(defn vworld [acc] (v2/world {:verify? true :hook (verify/projecting-hook (verify/checking-hook acc))}))
(defn- f [^objects row i] (aget row (int i)))
(defn- queued [w] (count (seq (f w rw/W-INGRESS))))
(defn- wait-until [g] (loop [n 400] (or (g) (when (pos? n) (Thread/sleep 5) (recur (dec n))))))
(defn- in [w g] (binding [v2/*world* w] (g)))

(defn- under-gate
  "`(g)` while holding `w`'s gate, without running a turn; queued work is
   handed off afterwards (H2)."
  [w g]
  (let [lk (f w rw/W-LOCK)]
    (hs/lock! lk)
    (try (g) (finally (hs/unlock! lk) (#'v2/handoff! w)))))

(defn finish! [n w acc]
  (prn (dump! (str dir "log-sample-" n "-w.edn") (verify/log w)))
  (prn :sample n :divergences @acc))

;; 61
(let [acc (atom []) w (vworld acc)
      s (in w #(v2/signal 0))
      t0 (v2/value (in w #(task :warm)) 2000 :timeout)]
  (under-gate
   w
   (fn []
     (v2/send-world! w (fn [] (throw (ex-info "a sent item throws" {:sample 61}))))
     @(future (v2/write! s 1))
     (v2/send-world! w (fn [] (v2/write! s 2)))
     @(future (in w #(task :after)))
     (assert (= 4 (queued w)) "four items queued behind the gate")))
  (wait-until #(zero? (queued w)))
  (Thread/sleep 100)
  (assert (= 2 (v2/value s)) "both writes after the throw committed")
  (assert (= :warm t0))
  (v2/release-world! w)
  (v2/await-complete w 2000 :timeout)
  (finish! 61 w acc))

;; 62
(let [acc (atom []) w (vworld acc)
      s (in w #(v2/signal 0))
      seen (atom [])]
  (v2/observe! s (fn [_ _] (throw (ex-info "an observer throws" {:sample 62}))))
  (v2/observe! s (fn [v _] (swap! seen conj v)))
  (Thread/sleep 50)
  (doseq [v [1 2 3]]
    (v2/write! s v)
    (Thread/sleep 30))
  (wait-until #(= 3 (last @seen)))
  (assert (= 3 (last @seen)) "the second observer saw every value")
  (v2/release-world! w)
  (v2/await-complete w 2000 :timeout)
  (finish! 62 w acc))

(shutdown-agents)
(System/exit 0)
