(ns org.replikativ.spindel.v2.sci.gate-test
  "A slice never waits on an interpreter's gate (B7, H2). SCI's forks and
   retirement take the gate exclusively; evaluations hold it shared, also
   while they wait on a task. The adapter takes it without waiting, barging
   past a queued fork; while a fork or retirement holds it, or the resolver
   still prepares the interpreter, the run parks and the slice is retried."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.sci :as v2sci]
            [org.replikativ.spindel.v2.sci.support :as s :refer [checked ev v]]
            [sci.core :as sci])
  (:import [java.util.concurrent.locks ReentrantReadWriteLock]))

(defn- gate ^ReentrantReadWriteLock [ctx]
  (.-gate ^sci.impl.world.DenseWorld (:sci.impl/world ctx)))

(defn- hold-exclusively
  "Holds `ctx`'s gate exclusively on another thread, as a fork in progress
   does; returns the fn that releases it."
  [ctx]
  (let [g (.writeLock (gate ctx)) held (promise) release (promise)
        t (Thread/startVirtualThread (fn [] (.lock g) (deliver held true) @release (.unlock g)))]
    @held
    (fn [] (deliver release true) (.join t))))

(deftest a-queued-fork-does-not-stall-a-slice
  ;; an evaluation holds the gate while it waits on a task; a fork of the
  ;; interpreter queues behind it; the delivery runs the task's slice inline.
  ;; Before, the slice waited behind the queued fork: all three were stuck
  ;; and the world stalled
  (checked
   (let [w (s/vworld)
         d (binding [v2/*world* w] (v2/deferred))
         p (s/interpreter {:bindings {'d d}})
         g (gate p)
         _ (ev w p "(def t (task (await d) :resumed))")
         evaluation (future (ev w p "[:evaluated @t]"))]
     (is (s/wait-until #(pos? (.getReadLockCount g))) "the evaluation holds the gate")
     (let [fork (future (sci/fork p))]
       (is (s/wait-until #(.hasQueuedThreads g)) "the fork waits for the gate")
       (let [delivery (future (v2/deliver! d :x) :delivered)]
         (is (= :delivered (deref delivery 2000 ::stuck)) "the inline slice did not wait")
         (is (= [:evaluated :resumed] (deref evaluation 2000 ::stuck)))
         (is (map? (deref fork 2000 ::stuck)) "the fork proceeds once the evaluation returns")))
     (v2/release-world! w))))

(deftest a-held-gate-parks-the-run
  (checked
   (let [w (s/vworld)
         d (binding [v2/*world* w] (v2/deferred))
         p (s/interpreter {:bindings {'d d}})
         t (ev w p "(def seen (atom [])) (task (let [x (await d)] (swap! seen conj x) @seen))")
         release (hold-exclusively p)]
     (is (= :delivered (deref (future (v2/deliver! d :x) :delivered) 2000 ::stuck))
         "the slice did not wait for the gate")
     (is (= ::pending (v2/value t 100 ::pending)) "the run parked")
     (release)
     (is (= [:x] (v t)) "and resumed once the gate was free")
     (v2/release-world! w)
     (is (not= ::timeout (v2/await-complete w 2000 ::timeout))))))

(deftest a-cancellation-that-cannot-wait-drops-the-finalizers
  ;; the defined outcome when a cancelled run's cleanup would have to wait for
  ;; the gate: the run cannot park while it unwinds, so its SCI finalizers
  ;; are dropped and it retires; nothing waits
  (checked
   (let [w (s/vworld)
         d (binding [v2/*world* w] (v2/deferred))
         p (s/interpreter {:bindings {'d d}})
         t (ev w p "(def cleaned (atom 0)) (task (try (await d) (finally (swap! cleaned inc))))")
         release (hold-exclusively p)]
     (is (= :cancelled (deref (future (v2/cancel-task! t) :cancelled) 2000 ::stuck)))
     (is (v2/cancelled? (try (v2/value t 2000 ::timeout) (catch Exception e e))))
     (release)
     (is (= 0 (sci/eval-string* p "@cleaned")) "the finalizer was dropped")
     (v2/release-world! w)
     (is (not= ::timeout (v2/await-complete w 2000 ::timeout)) "the run retired"))))

(deftest a-pending-interpreter-parks-the-run
  ;; the resolver may prepare an interpreter off the slice (a lazy sci/fork):
  ;; it returns a pending value, the run parks and asks again when it is
  ;; realized
  (checked
   (let [w (s/vworld)
         d (binding [v2/*world* w] (v2/deferred))
         p (s/interpreter {:bindings {'d d}})
         registry (atom {w p})
         _ (v2sci/set-resolver! p (fn [w _] (get @registry w)))
         t (ev w p "(def state (atom [])) (task (let [x (await d)] (swap! state conj x) @state))")
         child (v2/fork! w)
         prepared (promise)]
     (swap! registry assoc child prepared)
     (v2/deliver! (v2/in-world child d) :child)
     (is (= ::pending (v2/value (v2/in-world child t) 100 ::pending)) "parked while the interpreter is prepared")
     (let [c (sci/fork p)]
       (swap! registry assoc child c)
       (deliver prepared c)
       (is (= [:child] (v (v2/in-world child t))))
       (is (= [:child] (sci/eval-string* c "@state")) "on the prepared interpreter's heap")
       (is (= [] (sci/eval-string* p "@state"))))
     (v2/release-world! child)
     (v2/release-world! w))))
