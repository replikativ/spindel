;; C1c stage B log samples for the oracle (samples 34-38, spec Z#72): owned-fork counts.
;; New items: `[:owned-done s child]` (the owner, once its counted child completed or was
;; collected) and `[:normalize]` (a fork's first turn, an instance's activation: the counts it
;; inherited are drained). Sidecar as in samples-c1c-a.clj, plus per world:
;;   :owned     {scope n}  W-OWNED-N, counts > 0 only
;;   :normalize #{scope}   W-NORMALIZE, the owner scopes inherited and not yet drained
;; Worlds are read under their gate without a turn (a host item would be a fork's first turn),
;; so a fork's undrained W-NORMALIZE is visible.
;; From the repository root: clojure -M:bench -i formal/test/spindel/v2/oracle/gen/samples-c1c-b.clj
(ns samples-c1c-b
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

(defn- under-gate
  "`(g)` while holding `w`'s gate, without running a turn; queued work is
   handed off afterwards (H2)."
  [w g]
  (let [lk (f w rw/W-LOCK)]
    (hs/lock! lk)
    (try (g) (finally (hs/unlock! lk) (#'v2/handoff! w)))))

(defn- obs
  "The world's observations; `seen` (an atom {world-id {id row}}) keeps every task and
   scope row met so far, so removed ones are still reported."
  [^objects w seen]
  (under-gate
   w
   (fn []
     (let [live (into {} (f w rw/W-REG))
           wid (f w rw/ID)
           _ (swap! seen update wid merge
                    (into {} (filter (fn [[_ row]] (#{rw/T-TASK rw/T-SCOPE} (f row rw/TYPE)))) live))
           ;; a fork's write copies an inherited row: read this world's version of each
           rows (into {} (map (fn [[id row]] [id (#'v2/peek-row w row)])) (get @seen wid))
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
        :pending-joins (count (filter (comp hs/flag? first) (mapcat val (f w rw/W-JOIN-SUBS))))
        :owned (into (sorted-map) (map (fn [[sid [_ n]]] [sid n])) (f w rw/W-OWNED-N))
        :normalize (into (sorted-set) (keys (f w rw/W-NORMALIZE)))}))))

(defn checkpoint! [sidecar seen worlds step]
  (Thread/sleep 60)
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

(defmacro forking-task
  "A task whose `(fork)` child runs `child-body` (inline: effects must stay lexical in the
   body); the parent delivers the child to `kid` (as `(wrap child)`), awaits `pgate` and
   returns :parent. The child is counted on the parent run's scope."
  [kid wrap pgate child-body]
  `(task (let [[side# child#] (v2/fork)]
           (if (= side# :child)
             ~child-body
             (do (deliver ~kid (~wrap child#)) (await ~pgate) :parent)))))

;; 34: a task forks; its child does host work that ignores interruption. The task returns
;; while the child runs: its run scope closes (the child is released, F2) but stays, kept by
;; the count, and the task is done but not complete. The child completes once the host work
;; stops: the owner runs [:owned-done s child], the scope goes and the task completes.
(let [acc (atom []) sc (atom []) seen (atom {}) w (vworld acc) kid (promise) stop (promise) started (promise)]
  (binding [v2/*world* w]
    (let [pgate (v2/deferred)
          t (forking-task kid identity pgate (v2/offload (stubborn stop started)))
          child (deref kid 2000 nil)
          _ (deref started 2000 nil)
          ws {:parent w :child child}]
      (checkpoint! sc seen ws :child-running)
      (v2/deliver! pgate :go)
      (prn :sample-34 (v2/value t 2000 :timeout))
      (checkpoint! sc seen ws :task-returned)
      (deliver stop true)
      (v2/await-complete child 2000 :timeout)
      (checkpoint! sc seen ws :owned-done)
      (v2/release-world! w)
      (v2/await-complete w 2000 :timeout)
      (checkpoint! sc seen ws :released)
      (finish! 34 ws sc acc))))

;; 35: a counted child parks on an external operation that ignores cancellation and whose
;; complete! is dropped. The task returns: the child is released but cannot finish, and once
;; nothing holds it, it is collected (C1 R2): kid-collected! -> [:owned-done s child]. The
;; child's log is taken before it is dropped; the parent is not released (the model does not
;; see the collection, so it would keep the parent incomplete).
(let [acc (atom []) sc (atom []) seen (atom {}) w (vworld acc) kid (promise) parked (promise)
      ws (atom nil) child-log (atom nil)]
  (binding [v2/*world* w]
    (let [pgate (v2/deferred)
          t (forking-task kid (fn [c] (java.lang.ref.WeakReference. c)) pgate
                          (v2/external (fn [_complete!] (deliver parked true) nil)))
          ^java.lang.ref.WeakReference probe (deref kid 2000 nil)
          _ (deref parked 2000 nil)]
      (reset! ws {:parent w :child (.get probe)})
      (checkpoint! sc seen @ws :child-parked)
      (v2/deliver! pgate :go)
      (prn :sample-35 (v2/value t 2000 :timeout))
      (Thread/sleep 60)
      ;; released but not complete: read without the completion wait
      (swap! sc conj {:step :task-returned
                      :log-length (into (sorted-map) (map (fn [[n w]] [n (count (verify/log w))])) @ws)
                      :obs (into (sorted-map) (map (fn [[n w]] [n (obs w seen)])) @ws)})
      (reset! child-log (verify/log (:child @ws)))
      ;; the rows met so far reach the child through its runs: drop them with it
      (swap! seen dissoc (f (:child @ws) rw/ID))
      (reset! ws {:parent w})
      (prn :sample-35-collected
           (loop [n 0] (cond (nil? (.get probe)) true (> n 80) false
                             :else (do (System/cleanup-runs-exist) (Thread/sleep 25) (recur (inc n))))))
      (checkpoint! sc seen @ws :collected)
      (prn (dump! (str dir "log-sample-35-child.edn") @child-log))
      (finish! 35 @ws sc acc))))

;; 36: two host forks of the parent while its count keeps a closed scope (the state of 34 at
;; :task-returned). Each inherits the scope in W-NORMALIZE. :touched gets a host item first
;; (its first turn drains: [:normalize]); :untouched is released before any turn (Q15: on the
;; fast path the release runs first, then the turn's drain, then completion). Then the
;; parent's own child completes ([:owned-done]).
(let [acc (atom []) sc (atom []) seen (atom {}) w (vworld acc) kid (promise) stop (promise) started (promise)]
  (binding [v2/*world* w]
    (let [pgate (v2/deferred)
          t (forking-task kid identity pgate (v2/offload (stubborn stop started)))
          child (deref kid 2000 nil)
          _ (deref started 2000 nil)
          _ (v2/deliver! pgate :go)
          _ (prn :sample-36 (v2/value t 2000 :timeout))
          touched (v2/fork! w)
          untouched (v2/fork! w)
          ws {:parent w :child child :touched touched :untouched untouched}]
      (checkpoint! sc seen ws :forked)
      (v2/call-in! touched (fn [] :touched))
      (checkpoint! sc seen ws :touched)
      (v2/release-world! untouched)
      (v2/await-complete untouched 2000 :timeout)
      (checkpoint! sc seen ws :untouched-released)
      (v2/release-world! touched)
      (v2/await-complete touched 2000 :timeout)
      (deliver stop true)
      (v2/await-complete child 2000 :timeout)
      (checkpoint! sc seen ws :owned-done)
      (v2/release-world! w)
      (v2/await-complete w 2000 :timeout)
      (checkpoint! sc seen ws :released)
      (finish! 36 ws sc acc))))

;; 37 (Q16): the parent is released and its counted child completes (W-KIDS reaches 0) while
;; the parent's last run holds the gate; the run retires and the release runs before
;; [:owned-done], and the parent completes only after it.
(let [acc (atom []) sc (atom []) seen (atom {}) w (vworld acc) kid (promise) go (promise) spinning (promise)]
  (binding [v2/*world* w]
    (let [pg (v2/deferred)
          t (task (let [[side child] (v2/fork)]
                    (if (= side :child)
                      (await (v2/deferred))
                      (do (deliver kid child)
                          (await pg)
                          ;; resumed on the delivering host thread: it holds the gate
                          (deliver spinning true)
                          (loop [] (when-not (realized? go) (Thread/sleep 5) (recur)))
                          :parent))))
          child (deref kid 2000 nil)
          ws {:parent w :child child}]
      (checkpoint! sc seen ws :forked)
      (future (v2/deliver! pg 1))
      (deref spinning 2000 nil)
      (v2/release-world! w)
      (v2/release-world! child)
      (v2/await-complete child 2000 :timeout)
      (Thread/sleep 50)
      (prn :sample-37-kids-before-retire (hs/kids-count (f w rw/W-KIDS))
           :queued (mapv :item (verify/log w)))
      (deliver go true)
      (v2/await-complete w 2000 :timeout)
      (checkpoint! sc seen ws :complete)
      (finish! 37 ws sc acc))))

;; 38: a savepoint taken while the parent's count keeps a closed scope: the basis, and so the
;; instance, inherits it in W-NORMALIZE; the instance drains it at activation ([:normalize]).
(let [acc (atom []) sc (atom []) seen (atom {}) w (vworld acc) kid (promise) stop (promise) started (promise)
      pubs (atom {})]
  (v2/install-handlers! w {:default (fn [p] (swap! pubs assoc (:payload p) p))})
  (binding [v2/*world* w]
    (let [pgate (v2/deferred)
          t (forking-task kid identity pgate (v2/offload (stubborn stop started)))
          child (deref kid 2000 nil)
          _ (deref started 2000 nil)
          _ (v2/deliver! pgate :go)
          _ (prn :sample-38 (v2/value t 2000 :timeout))
          b (task (inc (v2/savepoint :choose :b)))
          _ (loop [n 0] (when (and (< n 400) (not (get @pubs :b))) (Thread/sleep 5) (recur (inc n))))
          p (get @pubs :b)
          i (v2/instantiate p)
          ws {:parent w :child child :instance i}]
      (checkpoint! sc seen ws :instantiated)
      (v2/activate! i 1)
      (prn :sample-38-instance (binding [v2/*world* i] (v2/value (v2/in-world i b) 2000 :timeout)))
      (checkpoint! sc seen ws :activated)
      (deliver stop true)
      (v2/await-complete child 2000 :timeout)
      (v2/abandon! p)
      (v2/release-world! i)
      (v2/await-complete i 2000 :timeout)
      (v2/release-world! w)
      (v2/await-complete w 2000 :timeout)
      (checkpoint! sc seen ws :released)
      (finish! 38 ws sc acc))))

(shutdown-agents)
