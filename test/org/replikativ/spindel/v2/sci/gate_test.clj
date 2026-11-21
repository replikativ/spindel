(ns org.replikativ.spindel.v2.sci.gate-test
  "A slice never waits on an interpreter (B7, H2). With replikativ SCI
   >= 0.15.59-replikativ.9 evaluation holds no lock a fork or retirement
   waits for, so forks of an interpreter whose evaluations wait on tasks, or
   whose code runs in slices, stall nothing; finalizers still run."
  (:require [clojure.test :refer [deftest is]]
            [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.sci :as v2sci]
            [org.replikativ.spindel.v2.sci.support :as s :refer [checked ev v]]
            [sci.core :as sci]))

(deftest a-fork-during-an-evaluation-stalls-nothing
  ;; an evaluation waits on a task; a fork of the interpreter, from another
  ;; thread and from inside that evaluation's code, returns at once; the
  ;; delivery runs the task's slice inline. Before (SCI .7) the slice waited
  ;; behind the queued fork and all three were stuck
  (checked
   (let [w (s/vworld)
         d (binding [v2/*world* w] (v2/deferred))
         entered (promise)
         self (promise)
         p (s/interpreter {:bindings {'d d}
                           :namespaces {'host {'entered (fn [] (deliver entered true) nil)
                                               'fork-self (fn [] (map? (sci/fork @self)))}}})
         _ (deliver self p)
         _ (ev w p "(def t (task (await d) :resumed))")
         evaluation (future (ev w p "(host/entered) [:evaluated (host/fork-self) @t]"))]
     (is (true? (deref entered 2000 false)) "the evaluation is running")
     (is (map? (deref (future (sci/fork p)) 2000 ::stuck)) "a fork from another thread returns at once")
     (is (= :delivered (deref (future (v2/deliver! d :x) :delivered) 2000 ::stuck)) "the inline slice did not wait")
     (is (= [:evaluated true :resumed] (deref evaluation 2000 ::stuck)) "a fork from inside the evaluation too")
     (v2/release-world! w))))

(deftest a-turn-running-sci-code-while-a-fork-is-taken-stalls-nothing
  ;; q6: a slice of SCI code holds the world gate; meanwhile a top-level
  ;; `swap!` with an SCI fn queues behind it (another thread's turn runs it)
  ;; and the interpreter is forked. Before, a reader blocked behind the fork
  ;; and the world stalled
  (checked
   (let [w (s/vworld)
         [d sig] (binding [v2/*world* w] [(v2/deferred) (v2/signal 0)])
         busy (promise)
         p (s/interpreter {:bindings {'d d 'sig sig}
                           :namespaces {'host {'busy (fn [ms] (deliver busy true) (Thread/sleep (long ms)))}}})
         u (ev w p "(task (await d) (host/busy 300) :busy-done)")
         delivery (future (v2/deliver! d :go) :delivered)
         _ (is (true? (deref busy 2000 false)) "the slice runs SCI code")
         swap (future (ev w p "[:swapped (swap! sig (fn [x] (inc x)))]"))
         fork (future (sci/fork p))]
     (is (map? (deref fork 2000 ::stuck)) "the fork did not wait for the slice")
     (is (= :delivered (deref delivery 2000 ::stuck)))
     (is (= [:swapped 1] (deref swap 2000 ::stuck)))
     (is (= :busy-done (v u)))
     (is (= 5 (binding [v2/*world* w] (v2/value (v2/task 5) 1000 ::stalled))) "the world is live")
     (v2/release-world! w))))

(deftest a-cancellation-during-forks-runs-the-finalizers
  ;; the cleanup slice enters the interpreter while it is being forked: its
  ;; SCI finalizer runs (before, with the gate held, it was dropped)
  (checked
   (let [w (s/vworld)
         d (binding [v2/*world* w] (v2/deferred))
         p (s/interpreter {:bindings {'d d}})
         t (ev w p "(def cleaned (atom 0)) (task (try (await d) (finally (swap! cleaned inc))))")
         started (promise)
         forking (future (dotimes [i 50] (when (= i 1) (deliver started true)) (sci/retire! (sci/fork p))) :forked)]
     (is (true? (deref started 2000 false)))
     (v2/cancel-task! t)
     (is (v2/cancelled? (try (v2/value t 2000 ::timeout) (catch Exception e e))))
     (is (= :forked (deref forking 5000 ::stuck)))
     (is (= 1 (sci/eval-string* p "@cleaned")) "the finalizer ran once")
     (v2/release-world! w)
     (is (not= ::timeout (v2/await-complete w 2000 ::timeout)) "the run retired"))))

(deftest a-resolver-may-fork-lazily-in-the-slice
  ;; the resolver forks the interpreter the first time a world asks, inside
  ;; the slice, while an evaluation of the source waits on the run
  (checked
   (let [w (s/vworld)
         d (binding [v2/*world* w] (v2/deferred))
         p (s/interpreter {:bindings {'d d}})
         registry (atom {w p})
         _ (v2sci/set-resolver! p (fn [world interpreter]
                                    (or (get @registry world)
                                        (get (swap! registry assoc world (sci/fork interpreter)) world))))
         t (ev w p "(def state (atom [])) (def t (task (let [x (await d)] (swap! state conj x) @state))) t")
         child (v2/fork! w)
         evaluation (future (ev w p "[:parent @t]"))]
     (v2/deliver! (v2/in-world child d) :child)
     (is (= [:child] (v (v2/in-world child t))) "resumed on a lazily forked interpreter")
     (is (= [:child] (sci/eval-string* (get @registry child) "@state")))
     (is (= [] (sci/eval-string* p "@state")) "the source heap is untouched")
     (v2/deliver! d :parent)
     (is (= [:parent [:parent]] (deref evaluation 2000 ::stuck)))
     (v2/release-world! child)
     (v2/release-world! w))))
