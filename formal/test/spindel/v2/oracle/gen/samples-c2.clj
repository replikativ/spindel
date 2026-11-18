;; C2 log samples for the oracle (samples 39-42, spec Z#74): seal, resolver merge, transfer.
;; 39  seal: host changes queued before the seal and processed after it are refused in the item
;;     ({:accepted false}); a queued observe makes no item.
;; 40  resolver merge: a throwing resolver and a refusing one refuse the whole merge; a value
;;     resolver merges (the conflicting source takes the resolver's value).
;; 41  §9 guard: a merge is refused while the child has a run parked on an armed timer; once the
;;     run retired (its write after the seal is a body write, accepted), the merge succeeds.
;; 42  transfer: m (owned by k1's root scope) moves to k2; k1 completes without m; closing k2
;;     releases m. No world item; the sidecar has per world :owner (the id of the world whose
;;     obligation it is), :kids (pending obligations) and :holder-live (its owner's holder).
;; From the repository root: clojure -M:bench -i formal/test/spindel/v2/oracle/gen/samples-c2.clj
(ns samples-c2
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.v2.core :as v2 :refer [task await]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.host :as hs]
            [org.replikativ.spindel.v2.verify :as verify]
            [clojure.pprint]))

(def dir "formal/test/spindel/v2/oracle/")
(defn dump! [path l] (spit path (with-out-str (clojure.pprint/pprint l))) [path (count l) (frequencies (map (comp first :item) l))])
(defn vworld [acc] (v2/world {:verify? true :hook (verify/projecting-hook (verify/checking-hook acc))}))
(defn- f [^objects row i] (aget row (int i)))
(defn- wait-until [g] (loop [n 400] (or (g) (when (pos? n) (Thread/sleep 5) (recur (dec n))))))
(defn- queued [w] (count (seq (f w rw/W-INGRESS))))

(defn- under-gate [w g]
  (let [lk (f w rw/W-LOCK)]
    (hs/lock! lk)
    (try (g) (finally (hs/unlock! lk) (#'v2/handoff! w)))))

(defn- obs [^objects w]
  (under-gate
   w
   (fn []
     {:released? (boolean (f w rw/W-RELEASED))
      :complete? (v2/complete? w)
      :sealed? (v2/sealed? w)
      :owner (some-> (#'v2/owner-world w) (f rw/ID))
      :kids (if-let [k (f w rw/W-KIDS)] (hs/kids-count k) 0)
      :holder-live (when-let [h (f w rw/W-HOLDER)] (not (#'v2/holder-dead? h)))})))

(defn checkpoint! [sidecar worlds step]
  (Thread/sleep 60)
  (swap! sidecar conj {:step step
                       :log-length (into (sorted-map) (map (fn [[n w]] [n (count (verify/log w))])) worlds)
                       :obs (into (sorted-map) (map (fn [[n w]] [n (obs w)])) worlds)}))

(defn finish! [n worlds sidecar acc]
  (doseq [[nm w] worlds]
    (prn (dump! (str dir "log-sample-" n "-" (name nm) ".edn") (verify/log w))))
  (when sidecar
    (spit (str dir "log-sample-" n "-observations.edn") (with-out-str (clojure.pprint/pprint @sidecar))))
  (prn :sample n :divergences @acc))

;; 39
(let [acc (atom []) w (vworld acc)]
  (binding [v2/*world* w]
    (let [s (v2/signal 1) m (v2/mailbox)
          child (v2/fork! w {:mergeable? true})
          cs (v2/in-world child s) cm (v2/in-world child m)
          lk (f child rw/W-LOCK)
          seen (promise)]
      (v2/write! cs 2)
      (hs/lock! lk)
      (let [sealer (future (v2/seal! child))]
        (wait-until #(= 1 (queued child)))
        ;; admitted before the seal runs, processed after it
        (let [ops [(future (v2/write! cs 3))
                   (future (v2/post! cm :x))
                   (future (v2/observe! cs (fn [v err?] (deliver seen [(:spindel/sealed (ex-data v)) err?]))))]]
          (wait-until #(= 4 (queued child)))
          (hs/unlock! lk)
          (#'v2/handoff! child)
          @sealer
          (run! deref ops)))
      (prn :39-observe (deref seen 2000 :timeout) :value (v2/value cs 1000 :timeout))
      (finish! 39 {:parent w :child child} nil acc))))

;; 40
(let [acc (atom []) w (vworld acc)]
  (binding [v2/*world* w]
    (let [s (v2/signal 1) t (v2/signal 10)
          child (v2/fork! w {:mergeable? true})]
      (v2/write! (v2/in-world child s) 2)
      (v2/write! (v2/in-world child t) 13)
      (v2/write! t 11)
      (v2/seal! child)
      (let [cl (verify/log child)
            r1 (v2/merge! w child {:resolve (fn [_ _ _ _] (throw (ex-info "boom" {})))})
            r2 (v2/merge! w child {:resolve (fn [_ _ _ _] :org.replikativ.spindel.v2.core/refuse)})
            r3 (v2/merge! w child {:resolve (fn [_ base pv cv] (+ pv (- cv base)))})]
        (prn :40 [r1 r2 r3] (mapv v2/value [s t]))
        (Thread/sleep 100)
        (prn (dump! (str dir "log-sample-40-child.edn") cl))
        (finish! 40 {:parent w} nil acc)))))

;; 41
(let [acc (atom []) w (vworld acc)]
  (binding [v2/*world* w]
    (let [s (v2/signal 1)
          child (v2/fork! w {:mergeable? true})
          cs (v2/in-world child s)
          t (binding [v2/*world* child] (task (v2/sleep 150) (v2/write! cs 11) :woke))]
      (v2/write! cs 10)
      (v2/seal! child)
      (let [r1 (v2/merge! w child)
            _ (v2/value t 2000 :timeout)
            _ (wait-until #(zero? (long (f child rw/W-RUNS))))
            cl (verify/log child)
            r2 (v2/merge! w child)]
        (prn :41 [r1 r2] (v2/value s))
        (Thread/sleep 100)
        (prn (dump! (str dir "log-sample-41-child.edn") cl))
        (finish! 41 {:parent w} nil acc)))))

;; 42
(let [acc (atom []) w (vworld acc) sidecar (atom [])]
  (binding [v2/*world* w]
    (let [k1 (v2/fork! w) k2 (v2/fork! w)
          m (v2/fork! w {:owner k1})
          worlds {:root w :k1 k1 :k2 k2 :m m}]
      (checkpoint! sidecar worlds :before)
      (prn :42-transfer (v2/transfer! m k2))
      (checkpoint! sidecar worlds :transferred)
      (v2/release-world! k1)
      (v2/await-complete k1 2000 :timeout)
      (checkpoint! sidecar worlds :k1-released)
      (v2/release-world! k2)
      (v2/await-complete k2 2000 :timeout)
      (checkpoint! sidecar worlds :k2-released)
      (finish! 42 worlds sidecar acc))))

(shutdown-agents)
