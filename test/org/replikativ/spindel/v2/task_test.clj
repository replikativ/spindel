(ns org.replikativ.spindel.v2.task-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await offload]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.verify :as verify]
            [org.replikativ.spindel.incremental.interval :as iv]))

(def ^:dynamic *divergences* nil)

(defn- vworld []
  (v2/world {:verify? true :hook (verify/checking-hook *divergences*)}))

(defmacro checked [& body]
  `(binding [*divergences* (atom [])]
     ~@body
     (is (empty? @*divergences*) (str "Rule R divergences: " (vec (take 3 @*divergences*))))))

(defn- census [w]
  (let [fr (v2/call-in! w #(frequencies (map (fn [r] (aget ^objects r rw/TYPE)) (vals (aget ^objects w rw/W-REG)))))]
    {:comps (get fr rw/T-COMP 0) :tasks (get fr rw/T-TASK 0) :runs (get fr rw/T-RUN 0)
     :edges (get fr rw/T-EDGE 0) :acts (get fr rw/T-ACT 0) :scopes (get fr rw/T-SCOPE 0)
     :sources (get fr rw/T-SOURCE 0)}))

(defn- outcome [h]
  (try (let [v (v2/value h 100 ::pending)] (if (= ::pending v) [:pending] [:ok v]))
       (catch Exception e [:err (or (ex-data e) e)])))

(deftest top-level-task
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [t (task (+ 1 2))]
         (is (= 3 (v2/value t)))
         (is (= 1 (:tasks (census w))) "kept for its handle")
         (v2/release! t)
         (is (= 0 (:tasks (census w))))
         (is (= 0 (:runs (census w)))))))))

(deftest task-awaits-computation-once
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [x (v2/signal 2)
             runs (atom 0)
             c (spin (* 10 (iv/get-new (track x))))
             t (task (swap! runs inc) (await c))]
         (is (= 20 (v2/value t)))
         (v2/write! x 3)
         (is (= 20 (v2/value t)) "a task's await does not re-run on change")
         (is (= 1 @runs)))))))

(deftest task-awaits-child-task
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [t (task (let [k (task 5)] (+ 1 (await k))))]
         (is (= 6 (v2/value t)))
         (verify/gc-settle! w)
         (is (= {:tasks 1 :runs 0} (select-keys (census w) [:tasks :runs]))
             "the child is gone; the outer task stays for its live handle")
         (is (= 6 (v2/value t))))))))

(deftest parked-task-on-deferred
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [d (v2/deferred)
             t (task (* 2 (await d)))]
         (is (= ::pending (v2/value t 50 ::pending)) "not finished yet")
         (v2/deliver! d 21)
         (is (= 42 (v2/value t)))
         (is (= 0 (:edges (census w))) "the wait edge was consumed"))))))

(deftest children-are-cancelled-at-completion
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [d (v2/deferred)
             child (atom nil)
             t (task (reset! child (task (await d))) :done)]
         (is (= :done (v2/value t)))
         (is (= [:err {}] (update (outcome @child) 1 (constantly {}))) "Q10: the unawaited child was cancelled")
         (is (= 0 (:edges (census w))) "its wait edge went with it")
         (is (= 0 (:runs (census w)))))))))

(deftest host-cancel
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [d (v2/deferred)
             t (task (await d))]
         (v2/cancel-task! t)
         (is (= :err (first (outcome t))))
         (v2/deliver! d 1)
         (is (= 0 (:edges (census w)))))))))

(deftest computation-awaits-deferred
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [d (v2/deferred)
             c (spin (inc (await d)))
             seen (atom [])
             u (v2/observe! c (fn [v _] (swap! seen conj v)))]
         (is (= [] @seen))
         (v2/deliver! d 1)
         (is (= [2] @seen))
         (is (= 1 (:edges (census w))) "only the observe edge; the final deferred's dep edge is gone")
         (u))))))

(deftest computation-tasks-are-adopted-and-cancelled
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [x (v2/signal 0)
             gate (v2/deferred)
             starts (atom 0)
             c (spin (let [v (iv/get-new (track x))
                           k (task (swap! starts inc) (await gate) v)]
                       (quot v 10)))
             u (v2/observe! c (fn [_ _]))]
         (is (= 1 @starts))
         (v2/write! x 1)
         (is (= 2 @starts) "changed captures replace the task")
         (u)
         (is (= 0 (:runs (census w))) "demotion cancels the computation's tasks")
         (is (= 0 (:edges (census w)))))))))

(deftest explicit-scope-cancels-its-tasks
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [d (v2/deferred)
             log (atom [])
             t (task (let [r (v2/with-scope
                               (task (try (await d) (finally (swap! log conj :inner))))
                               (await (task :yield))   ; the inner task starts and parks first
                               :scoped)]
                       (swap! log conj :after)
                       r))]
         (is (= :scoped (v2/value t 1000 ::timeout)))
         (is (= [:after :inner] @log)
             "the scope's task was cancelled at scope exit; its cleanup slice runs next (T14)")
         (is (= 0 (:runs (census w)))))))))

(deftest detach-outlives-the-creator
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [d (v2/deferred)
             child (atom nil)
             t (task (reset! child (v2/detach! (task (await d)) (v2/root-scope w))) :parent-done)]
         (is (= :parent-done (v2/value t 1000 ::timeout)))
         (v2/deliver! d :late)
         (is (= :late (v2/value @child 1000 ::timeout)) "the detached child was not cancelled"))))))

(deftest explicit-scope-cancels-its-tasks
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [d (v2/deferred)
             log (atom [])
             t (task (let [r (v2/with-scope
                               (task (try (await d) (finally (swap! log conj :inner))))
                               (await (task :yield))   ; the inner task starts and parks first
                               :scoped)]
                       (swap! log conj :after)
                       r))]
         (is (= :scoped (v2/value t 1000 ::timeout)))
         (is (= [:after :inner] @log)
             "the scope's task was cancelled at scope exit; its cleanup slice runs next (T14)")
         (is (= 0 (:runs (census w)))))))))

(deftest detach-outlives-the-creator
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [d (v2/deferred)
             child (atom nil)
             t (task (reset! child (v2/detach! (task (await d)) (v2/root-scope w))) :parent-done)]
         (is (= :parent-done (v2/value t 1000 ::timeout)))
         (v2/deliver! d :late)
         (is (= :late (v2/value @child 1000 ::timeout)) "the detached child was not cancelled"))))))

(deftest task-owned-sources-close-at-retirement
  ;; Z#18 (strict ownership): a source created by a task run is owned by its
  ;; run scope and closed when that run retires, even if it was handed out.
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [out (atom nil)
             t (task (reset! out (v2/signal 1)) :done)]
         (is (= :done (v2/value t 1000 ::timeout)))
         (v2/write! @out 2)
         (is (= 1 (v2/value @out)) "the closed signal refused the write"))))))

(defn- hold-until [started p]
  ;; an offload that acknowledges its cancellation only once `p` is delivered
  (fn []
    (deliver started true)
    (while (not (realized? p)) (try (Thread/sleep 1) (catch InterruptedException _)))
    :held))

(defn i1-detach-trace!
  "Z#52 (the model's I1 counterexample): a cleanup entry keeps its run scope's
   current ancestors. Run R of an inner task stays in cleanup on an offload;
   its outer task is detached into an explicit scope, which then closes."
  [w hold]
  (let [sa (promise) inner (promise) started (promise)
        ga (v2/deferred) gk (v2/deferred)
        a (task (let [s (v2/open-scope!)]
                  (deliver sa s)
                  (await ga)
                  (v2/close-scope-fx! s)
                  :a))
        k (task (deliver inner (task (v2/signal 0) (offload (hold-until started hold))))
                (await gk))]
    (deref started 1000 nil)
    (v2/cancel-task! (deref inner 1000 nil))      ; inner run: cleanup, waits on the ack
    (v2/detach! k (deref sa 1000 nil))            ; k's run scope moves under the explicit scope
    (v2/deliver! ga :close)                       ; closing it cancels k
    (v2/value a 1000 ::timeout)
    {:a a :k k}))

(deftest cleanup-retains-current-ancestors
  (checked
   (let [w (vworld) hold (promise)]
     (binding [v2/*world* w]
       (let [{:keys [a k]} (i1-detach-trace! w hold)]
         (is (= [:ok :a] (outcome a)))
         (is (= :spindel/cancelled (first (keys (second (outcome k))))))
         (is (= 5 (:scopes (census w)))
             "the inner run scope and its current chain stay: k's run scope, the explicit scope, a's run scope, root")
         (deliver hold true)
         (Thread/sleep 100)
         (v2/value (v2/signal 0) 100 nil)
         (is (= 1 (:scopes (census w))) "the ack retires the inner run and the chain goes"))))))
