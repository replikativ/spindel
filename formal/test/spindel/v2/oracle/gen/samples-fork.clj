;; Fork and savepoint log samples for the layer-2 oracle (samples 14-16): each world's own log.
;; From the repository root: clojure -M:bench -i formal/test/spindel/v2/oracle/gen/samples-fork.clj
(require 'org.replikativ.spindel.v2.group-test 'clojure.pprint)
(in-ns 'org.replikativ.spindel.v2.group-test)
(def dir "formal/test/spindel/v2/oracle/")
(defn dump! [path l] (spit path (with-out-str (clojure.pprint/pprint l))) [path (count l) (frequencies (map (comp first :item) l))])

;; 14: host fork of a world holding a signal, an observed computation, a task parked on a timer
;; and a task parked on an offload. The child's first turn settles the offload with err ::forked
;; (the timer stays armed), then the child writes the signal.
(let [acc (atom [])
      w (v2/world {:verify? true :hook (verify/projecting-hook (verify/checking-hook acc))})
      hold (promise)]
  (binding [v2/*world* w]
    (let [s (v2/signal 1)
          c (spin (* 2 (iv/get-new (track s))))
          u (v2/observe! c (fn [_ _]))
          t1 (task (v2/sleep 60000) :never)
          t2 (task (try (v2/offload (fn [] (deref hold 5000 nil) :held)) (catch Throwable _ :forked)))
          _ (v2/value (v2/signal 0) 200 nil)
          child (v2/fork! w)
          cs (v2/in-world child s)]
      (v2/write! cs 5)
      (binding [v2/*world* child] (v2/value (v2/in-world child t2) 2000 :timeout))
      (deliver hold true)
      (v2/value t2 2000 :timeout)
      (v2/cancel-task! t1)
      (binding [v2/*world* child] (v2/cancel-task! (v2/in-world child t1)))
      (Thread/sleep 100)
      (v2/value (v2/signal 0) 200 nil)
      (prn (dump! (str dir "log-sample-14-parent.edn") (verify/log w)))
      (prn (dump! (str dir "log-sample-14-child.edn") (verify/log child)))
      (prn :divergences @acc))))
;; 15: the `(fork)` effect in a task body. The parent continues its slice with [:parent child];
;; in the child the same run is resumed at the effect with [:child nil]. Both write the signal;
;; the parent parks on a deferred, so its run scope (the fork's owner, F2) stays open until the
;; child's copy completed; the parent's completion then releases the child.
(let [acc (atom [])
      w (v2/world {:verify? true :hook (verify/projecting-hook (verify/checking-hook acc))})
      kid (promise)]
  (binding [v2/*world* w]
    (let [s (v2/signal 1)
          c (spin (* 2 (iv/get-new (track s))))
          u (v2/observe! c (fn [_ _]))
          gate (v2/deferred)
          t (task (let [[side child] (v2/fork)]
                    (v2/write! s (if (= side :child) 20 10))
                    (when (= side :parent) (deliver kid child) (await gate))
                    side))
          child (deref kid 2000 nil)]
      (v2/value (v2/in-world child t) 2000 :timeout)
      (v2/value (v2/in-world child c) 2000 :timeout)
      (let [cl (verify/log child)]
        (v2/deliver! gate :done)
        (v2/value t 2000 :timeout)
        (Thread/sleep 100)
        (prn (dump! (str dir "log-sample-15-parent.edn") (verify/log w)))
        (prn (dump! (str dir "log-sample-15-child.edn") cl))
        (prn (dump! (str dir "log-sample-15-child-released.edn") (verify/log child)))
        (prn :divergences @acc)))))
;; 16: savepoints. Task a parks at a savepoint and is resumed in place; task b parks at one whose
;; publication is instantiated twice (activated with 1 and 2) and then abandoned; task c is parked
;; at a third savepoint when the instances are made, so in each instance it fails with ::forked.
(let [acc (atom [])
      w (v2/world {:verify? true :hook (verify/projecting-hook (verify/checking-hook acc))})
      pubs (atom {})]
  (v2/install-handlers! w {:now (fn [p] (v2/resume! p (* 10 (:payload p))))
                           :default (fn [p] (swap! pubs assoc (:payload p) p))})
  (binding [v2/*world* w]
    (let [x (v2/signal 100)
          a (task (inc (v2/savepoint :now 4)))
          _ (v2/value a 1000 :timeout)
          c (task (try (v2/savepoint :hold :c) (catch Exception e (if (:spindel/forked (ex-data e)) :forked :other))))
          b (task (+ (v2/savepoint :choose :b) (iv/get-new (track x))))
          _ (v2/value (v2/signal 0) 200 nil)
          p (get @pubs :b)
          i1 (doto (v2/instantiate p) (v2/activate! 1))
          i2 (doto (v2/instantiate p) (v2/activate! 2))]
      (doseq [i [i1 i2]] (binding [v2/*world* i] (v2/value (v2/in-world i b) 1000 :timeout) (v2/value (v2/in-world i c) 1000 :timeout)))
      (v2/abandon! p)
      (v2/abandon! (get @pubs :c))
      (try (v2/value b 1000 :timeout) (catch Exception _ nil))
      (Thread/sleep 100)
      (v2/value (v2/signal 0) 200 nil)
      (prn (dump! (str dir "log-sample-16-parent.edn") (verify/log w)))
      (prn (dump! (str dir "log-sample-16-inst1.edn") (verify/log i1)))
      (prn (dump! (str dir "log-sample-16-inst2.edn") (verify/log i2)))
      (prn :divergences @acc))))
(shutdown-agents)
