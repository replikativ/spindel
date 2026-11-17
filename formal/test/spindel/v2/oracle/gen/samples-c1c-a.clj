;; C1c stage A log samples for the oracle (samples 29-33, spec Z#70): task and scope
;; completion is derived state, never a log item. Each world's own log plus a
;; `log-sample-N-observations.edn` sidecar, [{:step kw :log-length {world n} :obs {world {...}}}],
;; recorded at host checkpoints. Per world:
;;   :complete? :released? :runs :kids :token       as in samples-c1.clj
;;   :tasks  {id {:done? :retired? :materialized? :srow-present? :complete?}}  every task seen
;;           so far (:retired? = no unretired run; :materialized? = its run scope was ever made;
;;           :srow-present? = that row still exists)
;;   :scopes {id {:open? :present? :complete?}}     every scope seen so far
;;   :pending-joins                                 live host joins: registered, not yet
;;                                                  delivered, not withdrawn
;; From the repository root: clojure -M:bench -i formal/test/spindel/v2/oracle/gen/samples-c1c-a.clj
(ns samples-c1c-a
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

(defn- obs
  "The world's observations; `seen` (an atom {world-id {id row}}) keeps every task and
   scope row met so far, so removed ones are still reported."
  [^objects w seen]
  ((fn [g] (if (f w rw/W-RELEASED) (g) (v2/call-in! w g)))   ; released: read once complete
   (fn []
     (let [reg (f w rw/W-REG)
           live (into {} (map (fn [[id row]] [id row])) reg)
           wid (f w rw/ID)
           _ (swap! seen update wid merge
                    (into {} (filter (fn [[_ row]] (#{rw/T-TASK rw/T-SCOPE} (f row rw/TYPE)))) live))
           rows (get @seen wid)
           present? (fn [row] (contains? live (f row rw/ID)))]
       {:complete? (v2/complete? w)
        :released? (boolean (f w rw/W-RELEASED))
        :runs (long (or (f w rw/W-RUNS) 0))
        :kids (when-let [k (f w rw/W-KIDS)] (hs/kids-count k))
        :token (when-let [^java.util.concurrent.atomic.AtomicReference c (f w rw/W-KID-TOKEN)]
                 (let [v (.get c)] (cond (nil? v) :none (= :done v) :done :else :installed)))
        :tasks (into (sorted-map)
                     (for [[id row] rows :when (= rw/T-TASK (f row rw/TYPE))]
                       [id {:done? (boolean (f row rw/K-DONE))
                            :retired? (nil? (f row rw/K-RUN))
                            :materialized? (some? (f row rw/K-SROW))
                            :srow-present? (boolean (when-let [s (f row rw/K-SROW)] (present? s)))
                            :complete? (boolean (f row rw/K-COMPLETE))}]))
        :scopes (into (sorted-map)
                      (for [[id row] rows :when (= rw/T-SCOPE (f row rw/TYPE))]
                        [id {:open? (boolean (f row rw/S-OPEN))
                             :present? (present? row)
                             :complete? (boolean (f row rw/S-COMPLETE))}]))
        :pending-joins (count (filter (comp hs/flag? first) (mapcat val (f w rw/W-JOIN-SUBS))))}))))

(defn checkpoint! [sidecar seen worlds step]
  (Thread/sleep 60)
  (doseq [[_ w] worlds]
    (when (f w rw/W-RELEASED) (assert (v2/await-complete w 2000 false) "a released world is read once complete")))
  (swap! sidecar conj {:step step
                       :log-length (into (sorted-map) (map (fn [[n w]] [n (count (verify/log w))])) worlds)
                       :obs (into (sorted-map) (map (fn [[n w]] [n (obs w seen)])) worlds)}))

(defn finish! [n worlds sidecar acc]
  (doseq [[nm w] worlds]
    (prn (dump! (str dir "log-sample-" n "-" (name nm) ".edn") (verify/log w))))
  (spit (str dir "log-sample-" n "-observations.edn") (with-out-str (clojure.pprint/pprint @sidecar)))
  (prn :sample n :divergences @acc))

(defn- stubborn
  "Host work that ignores interruption until `stop` is delivered."
  [stop started]
  (fn []
    (deliver started true)
    (loop [] (when-not (realized? stop) (try (Thread/sleep 5) (catch InterruptedException _)) (recur)))
    :stopped))

;; 29: a task that never materializes its run scope (it creates nothing): complete at its
;; retirement; a host join after that fires at once.
(let [acc (atom []) sc (atom []) seen (atom {}) w (vworld acc) ws {:w w}]
  (binding [v2/*world* w]
    (let [t (task (+ 1 2))]
      (prn :sample-29 (v2/value t 2000 :timeout))
      (checkpoint! sc seen ws :settled)
      (prn :sample-29-joined (v2/await-joined t 2000 :timeout))
      (checkpoint! sc seen ws :joined)
      (finish! 29 ws sc acc))))

;; 30: a task opens an explicit scope; in it a child spawns a grandchild doing host work that
;; ignores interruption, then returns without awaiting it (Q10 cancels the grandchild, whose
;; run stays in cleanup). The scope closes, the task returns, and it stays incomplete
;; (the closed scope, the child's run scope and the grandchild stay) until the host work stops.
(let [acc (atom []) sc (atom []) seen (atom {}) w (vworld acc) ws {:w w}
      stop (promise) started (promise)]
  (binding [v2/*world* w]
    (let [go (v2/deferred)
          t (task (v2/with-scope
                    (await (task (task (v2/offload (stubborn stop started))) (await go) :child)))
                  :parent)
          joined (promise)]
      (deref started 2000 nil)
      (v2/on-joined t #(deliver joined true))
      (checkpoint! sc seen ws :grandchild-started)
      (v2/deliver! go :go)
      (prn :sample-30 (v2/value t 2000 :timeout))
      (checkpoint! sc seen ws :parent-settled)
      (deliver stop true)
      (prn :sample-30-joined (deref joined 2000 :timeout))
      (checkpoint! sc seen ws :grandchild-retired)
      (finish! 30 ws sc acc))))

;; 31a: a host join on a task parked on a deferred, then release-world!: T21 cancels the task,
;; which completes, and the join is delivered (before world completion).
(let [acc (atom []) sc (atom []) seen (atom {}) w (vworld acc) ws {:w w}]
  (binding [v2/*world* w]
    (let [d (v2/deferred)
          t (task (await d))
          joined (promise)]
      (v2/on-joined t #(deliver joined true))
      (checkpoint! sc seen ws :join-pending)
      (v2/release-world! w)
      (prn :sample-31a-joined (deref joined 2000 :timeout))
      (v2/await-complete w 2000 :timeout)
      (checkpoint! sc seen ws :released)
      (finish! "31a" ws sc acc))))

;; 31b: abandonment. An unborn instance's copy of a task parked at a savepoint never runs; a
;; host join on it stays pending until the instance is released and completes, and is then
;; delivered with the world.
(let [acc (atom []) sc (atom []) seen (atom {}) w (vworld acc) pubs (atom {})]
  (v2/install-handlers! w {:default (fn [p] (swap! pubs assoc (:payload p) p))})
  (binding [v2/*world* w]
    (let [t (task [:resumed (v2/savepoint :choose :b)])]
      (loop [n 0] (when (and (< n 400) (not (get @pubs :b))) (Thread/sleep 5) (recur (inc n))))
      (let [pub (get @pubs :b)
            i (v2/instantiate pub)
            ws {:parent w :instance i}
            joined (promise)]
        (v2/on-joined (v2/in-world i t) #(deliver joined true))
        (checkpoint! sc seen ws :join-pending-unborn)
        (v2/release-world! i)
        (prn :sample-31b-joined (deref joined 2000 :timeout))
        (checkpoint! sc seen ws :instance-complete)
        (v2/abandon! pub)
        (v2/release-world! w)
        (v2/await-complete w 2000 :timeout)
        (checkpoint! sc seen ws :released)
        (finish! "31b" ws sc acc)))))

;; 32: on-joined registered after release on a task already complete: delivered at once
;; (internal admission, no item).
(let [acc (atom []) sc (atom []) seen (atom {}) w (vworld acc) ws {:w w}]
  (binding [v2/*world* w]
    (let [t (task :done)]
      (prn :sample-32 (v2/value t 2000 :timeout))
      (checkpoint! sc seen ws :settled)
      (v2/release-world! w)
      (v2/await-complete w 2000 :timeout)
      (checkpoint! sc seen ws :released)
      (let [joined (promise)]
        (v2/on-joined t #(deliver joined true))
        (prn :sample-32-joined (deref joined 2000 :timeout)))
      (checkpoint! sc seen ws :joined-after-release)
      (finish! 32 ws sc acc))))

;; 33: withdrawal. Two host joins on a parked task; one is withdrawn (a host-side flag, no
;; item, no gate). :pending-joins counts live joins only; completion delivers the live one, and
;; the withdrawn one never fires.
(let [acc (atom []) sc (atom []) seen (atom {}) w (vworld acc) ws {:w w}]
  (binding [v2/*world* w]
    (let [d (v2/deferred)
          t (task (await d))
          kept (promise)
          dropped (atom 0)
          withdraw (v2/on-joined t #(swap! dropped inc))]
      (v2/on-joined t #(deliver kept true))
      (checkpoint! sc seen ws :two-joins)
      (withdraw)
      (checkpoint! sc seen ws :one-withdrawn)
      (v2/deliver! d :d)
      (prn :sample-33 (deref kept 2000 :timeout) :withdrawn-fired @dropped)
      (checkpoint! sc seen ws :complete)
      (finish! 33 ws sc acc))))

(shutdown-agents)
(System/exit 0)
