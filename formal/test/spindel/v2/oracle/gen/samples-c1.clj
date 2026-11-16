;; C1 log samples for the oracle (samples 22-27): each world's own log, plus a
;; `log-sample-N-observations.edn` sidecar. World completion and child tokens are
;; derived state, never log items; the sidecar records them at host checkpoints:
;;   [{:step kw :log-length {world-name n} :obs {world-name {...}}} ...]
;; :log-length is the length of that world's log at the checkpoint. Per world:
;; :complete? :released? :runs (unretired runs, W-RUNS) :kids (owned child
;; obligations, nil before the first) :token (its own kid cell: :none = not yet
;; accepted, :installed = accepted by its owner, :done = completed or collected and
;; acknowledged; nil for a world nobody can own, such as a fresh root).
;; From the repository root: clojure -M:bench -i formal/test/spindel/v2/oracle/gen/samples-c1.clj
(ns samples-c1
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.v2.core :as v2 :refer [task await spin track]]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.host :as hs]
            [org.replikativ.spindel.v2.verify :as verify]
            [clojure.pprint]))

(def dir "formal/test/spindel/v2/oracle/")
(defn dump! [path l] (spit path (with-out-str (clojure.pprint/pprint l))) [path (count l) (frequencies (map (comp first :item) l))])
(defn vworld
  ([acc] (vworld acc {}))
  ([acc opts] (v2/world (merge {:verify? true :hook (verify/projecting-hook (verify/checking-hook acc))} opts))))

(defn- obs [^objects w]
  {:complete? (v2/complete? w)
   :released? (boolean (aget w rw/W-RELEASED))
   :runs (long (or (aget w rw/W-RUNS) 0))
   :kids (when-let [k (aget w rw/W-KIDS)] (hs/kids-count k))
   :token (when-let [^java.util.concurrent.atomic.AtomicReference c (aget w rw/W-KID-TOKEN)]
            (let [v (.get c)] (cond (nil? v) :none (= :done v) :done :else :installed)))})

(defn checkpoint!
  "Records the observations of `worlds` ({name world}) after the host step `step`,
   once the worlds have had a moment to settle."
  [sidecar worlds step]
  (Thread/sleep 60)
  (swap! sidecar conj {:step step
                       :log-length (into (sorted-map) (map (fn [[n w]] [n (count (verify/log w))])) worlds)
                       :obs (into (sorted-map) (map (fn [[n w]] [n (obs w)])) worlds)}))

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

;; 22 (T14): a host [:cancel r] on a run whose scope holds a task, a nested explicit scope
;; with its own task, and a fork made by the run's `(fork)` effect (owned by the run's
;; scope). One :cancel item; the subtree (both scoped tasks, the fork) is derived.
(let [acc (atom []) sc (atom []) w (vworld acc) kid (promise) parked (promise)]
  (binding [v2/*world* w]
    (let [t (task (let [[side _child] (v2/fork)]
                    (if (= side :child)
                      (await (v2/deferred))
                      (v2/with-scope
                        (task (await (v2/deferred)))
                        (v2/with-scope
                          (task (await (v2/deferred)))
                          (deliver kid _child)
                          (deliver parked true)
                          (await (v2/deferred)))))))
          child (deref kid 2000 nil)
          _ (deref parked 2000 nil)
          ws {:parent w :child child}]
      (checkpoint! sc ws :parked)
      (v2/cancel-task! t)
      (checkpoint! sc ws :cancelled)
      (v2/release-world! w)
      (v2/await-complete w 2000 :timeout)
      (checkpoint! sc ws :released)
      (finish! 22 ws sc acc))))

;; 23a: a host fork whose owner's gate is busy at fork time; the child is released and
;; completes before its owner accepts it, then the owner is released and completes.
(let [acc (atom []) sc (atom []) src (vworld acc) _ (binding [v2/*world* src] (v2/signal 0))
      owner (v2/fork! src) hold (promise) holding (promise)]
  (future (v2/host-call! owner (fn [] (deliver holding true) (deref hold 5000 nil) nil)))
  (deref holding 2000 nil)
  (let [child (v2/fork! src {:owner owner})
        ws {:src src :owner owner :child child}]
    (checkpoint! sc ws :forked-owner-busy)
    (v2/release-world! child)
    (v2/await-complete child 2000 :timeout)
    (checkpoint! sc ws :child-complete)
    (deliver hold true)
    (checkpoint! sc ws :owner-free)
    (v2/release-world! owner)
    (v2/await-complete owner 2000 :timeout)
    (v2/release-world! src)
    (v2/await-complete src 2000 :timeout)
    (checkpoint! sc ws :all-released)
    (finish! "23a" ws sc acc)))

;; 23b: an instance activated (born, owned by its owner's root scope), released at once;
;; it completes and acknowledges its owner, which then completes at release.
(let [acc (atom []) sc (atom []) w (vworld acc) pubs (atom {})]
  (v2/install-handlers! w {:default (fn [p] (swap! pubs assoc (:payload p) p))})
  (binding [v2/*world* w]
    (task [:resumed (v2/savepoint :choose :b)])
    (loop [n 0] (when (and (< n 400) (not (get @pubs :b))) (Thread/sleep 5) (recur (inc n))))
    (let [pub (get @pubs :b)
          i (v2/instantiate pub)
          ws {:parent w :instance i}]
      (checkpoint! sc ws :instantiated)
      (v2/activate! i :x)
      (checkpoint! sc ws :activated)
      (v2/release-world! i)
      (v2/await-complete i 2000 :timeout)
      (checkpoint! sc ws :instance-complete)
      (v2/abandon! pub)
      (v2/release-world! w)
      (v2/await-complete w 2000 :timeout)
      (checkpoint! sc ws :released)
      (finish! "23b" ws sc acc))))

;; 24: an unborn instance released before activation: nothing in it ever ran; it is
;; complete at once, a later activate! is refused ("world released"), and the owner completes.
(let [acc (atom []) sc (atom []) w (vworld acc) pubs (atom {})]
  (v2/install-handlers! w {:default (fn [p] (swap! pubs assoc (:payload p) p))})
  (binding [v2/*world* w]
    (task [:resumed (v2/savepoint :choose :b)])
    (loop [n 0] (when (and (< n 400) (not (get @pubs :b))) (Thread/sleep 5) (recur (inc n))))
    (let [pub (get @pubs :b)
          i (v2/instantiate pub)
          ws {:parent w :instance i}]
      (checkpoint! sc ws :instantiated)
      (v2/release-world! i)
      (v2/await-complete i 2000 :timeout)
      (checkpoint! sc ws :released-unborn)
      (prn :sample-24-activate (try (v2/activate! i :x) :accepted (catch Exception e (ex-message e))))
      (checkpoint! sc ws :activate-after-release)
      (v2/abandon! pub)
      (v2/release-world! w)
      (v2/await-complete w 2000 :timeout)
      (checkpoint! sc ws :released)
      (finish! 24 ws sc acc))))

;; 25 (W4): a cancelled run whose finally awaits a pending deferred: the await is refused
;; and the run ends with the refusal, [:complete r 2 [:opaque v]].
(let [acc (atom []) sc (atom []) w (vworld acc) started (promise)]
  (binding [v2/*world* w]
    (let [d (v2/deferred)
          t (task (try (deliver started true) (await (v2/deferred))
                       (finally (await d))))
          ws {:w w}]
      (deref started 2000 nil)
      (checkpoint! sc ws :parked)
      (v2/cancel-task! t)
      (prn :sample-25-result (try (v2/value t 2000 :timeout) (catch Exception e (ex-data e))))
      (checkpoint! sc ws :cancelled)
      (v2/release-world! w)
      (v2/await-complete w 2000 :timeout)
      (checkpoint! sc ws :released)
      (finish! 25 ws sc acc))))

;; 25b (W4, normal entry): a run whose body returned and whose finally awaits a pending
;; deferred: the await is refused and the run fails with it, [:complete r 2 [:opaque v]].
;; (On cancellation entry, 25, the refusal is raised the same way but the run is already
;; settled as cancelled: it retires through :finalize without a :complete item.)
(let [acc (atom []) sc (atom []) w (vworld acc) ws {:w w}]
  (binding [v2/*world* w]
    (let [d (v2/deferred)
          t (task (try :body (finally (await d))))]
      (prn :sample-25b-result (try (v2/value t 2000 :timeout) (catch Exception e (ex-data e))))
      (checkpoint! sc ws :failed)
      (v2/release-world! w)
      (v2/await-complete w 2000 :timeout)
      (checkpoint! sc ws :released)
      (finish! "25b" ws sc acc))))

;; 26a (await-op): cancelled before its start ran (an executor holds the start); the op
;; never starts.
(let [acc (atom []) sc (atom [])
      held (java.util.concurrent.LinkedBlockingQueue.)
      ex (reify java.util.concurrent.Executor (execute [_ r] (.add held r)))
      run-held! #(loop [] (when-let [r (.poll held)] (.run ^Runnable r) (recur)))
      starts (atom 0)
      w (vworld acc {:executor ex})
      ws {:w w}]
  (binding [v2/*world* w]
    (let [t (task (v2/await-op (fn [res _] (swap! starts inc) (res :ran))))]
      (v2/cancel-task! t)
      (run-held!)
      (checkpoint! sc ws :cancelled-before-start)
      (v2/release-world! w)
      (dotimes [_ 20] (run-held!) (Thread/sleep 5))
      (checkpoint! sc ws :released)
      (prn :sample-26a-starts @starts)
      (finish! "26a" ws sc acc))))

;; 26b: cancelled after its start: the op's on-cancel hook runs; the run settles promptly;
;; the world completes only after the op settled.
(let [acc (atom []) sc (atom []) w (vworld acc) stop (promise) started (promise) ws {:w w}]
  (binding [v2/*world* w]
    (let [t (task (v2/await-op (fn [res _]
                                 (v2/on-cancel! (fn [] (deliver stop true)))
                                 (deliver started true)
                                 (future (deref stop 5000 nil) (Thread/sleep 50) (res :late)))))]
      (deref started 2000 nil)
      (checkpoint! sc ws :started)
      (v2/cancel-task! t)
      (try (v2/value t 2000 :timeout) (catch Exception _ nil))
      (v2/release-world! w)
      (v2/await-complete w 2000 :timeout)
      (checkpoint! sc ws :released)
      (finish! "26b" ws sc acc))))

;; 26c: an op that resolved during its start (the run is done) but whose start still waits
;; for its stop hook: release cancels it and the world completes after the hook.
(let [acc (atom []) sc (atom []) w (vworld acc) stop (promise) ws {:w w}]
  (binding [v2/*world* w]
    (let [t (task (v2/await-op (fn [res _]
                                 (v2/on-cancel! (fn [] (deliver stop true)))
                                 (res :early)
                                 (deref stop 5000 nil))))]
      (prn :sample-26c-result (v2/value t 2000 :timeout))
      (checkpoint! sc ws :run-done-op-running)
      (v2/release-world! w)
      (v2/await-complete w 2000 :timeout)
      (checkpoint! sc ws :released)
      (finish! "26c" ws sc acc))))

;; 27 (W1): release with an unretired run (an offload that ignores interruption); the
;; world completes at that run's T13 retirement after the offload returns.
(let [acc (atom []) sc (atom []) w (vworld acc) stop (promise) started (promise) ws {:w w}]
  (binding [v2/*world* w]
    (let [t (task (v2/offload (stubborn stop started)))]
      (deref started 2000 nil)
      (checkpoint! sc ws :running)
      (v2/release-world! w)
      (try (v2/value t 2000 :timeout) (catch Exception _ nil))
      (checkpoint! sc ws :released-runs-left)
      (deliver stop true)
      (v2/await-complete w 2000 :timeout)
      (checkpoint! sc ws :complete)
      (finish! 27 ws sc acc))))

;; 28 (ansatz C1 stage B, question 5): T21 cancels an observed computation's run, whose
;; cleanup slice tries to observe and pin another computation c2 and writes a signal c2
;; tracks. The observe and pin are refused (no new root after release; Z#40 allows the
;; write), c2 never runs, and the world completes after the slice.
(let [acc (atom []) sc (atom []) w (vworld acc) seen (atom []) ws {:w w}]
  (binding [v2/*world* w]
    (let [s (v2/signal 0)
          c2 (spin (* 10 (iv/get-new (track s))))
          attempt (fn [label f] (try (f) [label :accepted] (catch Exception e [label (ex-message e)])))
          c (spin (try (await (v2/deferred))
                       (finally
                         (swap! seen conj (attempt :observe #(v2/observe! c2 (fn [_ _]))))
                         (swap! seen conj (attempt :pin #(v2/pin! c2)))
                         (swap! seen conj (attempt :write #(v2/write! s 5))))))
          _ (v2/observe! c (fn [_ _]))]
      (v2/value (v2/signal 0) 200 nil)
      (checkpoint! sc ws :parked)
      (v2/release-world! w)
      (v2/await-complete w 2000 :timeout)
      (checkpoint! sc ws :released)
      (prn :sample-28-seen @seen)
      (finish! 28 ws sc acc))))

(shutdown-agents)
(System/exit 0)
