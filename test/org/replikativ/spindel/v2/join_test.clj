(ns org.replikativ.spindel.v2.join-test
  "C1c stage A (c1c-task-joins-design.md v4, c1c-options-evaluation.md): a task is
   complete when it is done, its run has retired and its run scope's subtree is
   gone (child tasks still unwinding, explicit scopes). Hosts wait for it with
   `on-joined` / `await-joined`."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [task await]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.verify :as verify]))

(def ^:dynamic *divergences* nil)

(defn- vworld []
  (v2/world {:verify? true :hook (verify/checking-hook *divergences*)}))

(defmacro checked [& body]
  `(binding [*divergences* (atom [])]
     ~@body
     (is (empty? @*divergences*) (str "Rule R divergences: " (vec (take 3 @*divergences*))))))

(defn- stubborn
  "Host work that ignores interruption until `stop` is delivered."
  [stop started]
  (fn []
    (deliver started true)
    (loop [] (when-not (realized? stop) (try (Thread/sleep 5) (catch InterruptedException _)) (recur)))
    :stopped))

(defn- row [h] (aget ^objects (.-cell ^org.replikativ.spindel.v2.core.Handle h) 0))

(defn- complete-world-state
  "Read once `w` is complete (nothing runs): the registered tasks that are not
   complete, the scopes left, and the given task handles that are not complete.
   The runtime counterpart of the model's theorem: a complete born world has every
   task and every non-root scope complete (Z#70)."
  [^objects w hs]
  (let [rows (vals (aget w rw/W-REG))
        kind (fn [^objects r] (aget r rw/TYPE))]
    {:incomplete-tasks (count (filter #(and (= rw/T-TASK (kind %)) (not (aget ^objects % rw/K-COMPLETE))) rows))
     :scopes (mapv #(aget ^objects % rw/S-KIND) (filter #(= rw/T-SCOPE (kind %)) rows))
     :incomplete-handles (count (remove #(aget ^objects (row %) rw/K-COMPLETE) hs))}))

(deftest a-complete-born-world-has-every-task-complete
  (checked
   (let [w (vworld) stop (promise) started (promise)]
     (binding [v2/*world* w]
       (let [d (v2/deferred)
             hs (atom [])
             keep! (fn [h] (swap! hs conj h) h)
             ;; nested explicit scope with a child and a grandchild parked on d
             _a (keep! (task (v2/with-scope (keep! (task (keep! (task (await d))) (await d))) (await d))))
             ;; a child detached to the root
             b (keep! (task (keep! (v2/detach! (task (await d)) (v2/root-scope v2/*world*))) :b))
             ;; a computation-owned task
             c (v2/spin (await (keep! (task :c))))
             _ (v2/observe! c (fn [_ _]))
             ;; a run that stays in cleanup after release until its host work stops
             _e (keep! (task (v2/offload (stubborn stop started))))]
         (deref started 2000 nil)
         (is (= :b (v2/value b 2000 ::timeout)))
         (v2/release-world! w)
         (is (= ::timeout (v2/await-complete w 100 ::timeout)) "e's run is still in cleanup")
         (deliver stop true)
         (is (true? (v2/await-complete w 2000 ::timeout)))
         (is (= {:incomplete-tasks 0 :scopes [:root] :incomplete-handles 0}
                (complete-world-state w @hs))
             "every task is complete and the root is the only scope left"))))))

(deftest a-finished-task-is-joined
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [t (task (+ 1 2))]
         (is (= 3 (v2/value t 2000 ::timeout)))
         (is (true? (v2/await-joined t 2000 ::timeout)))
         (let [p (promise)]
           (v2/on-joined t #(deliver p :late))
           (is (= :late (deref p 2000 ::timeout)) "a late registration fires at once")))))))

(deftest a-join-waits-for-a-child-still-unwinding
  (checked
   (let [w (vworld) stop (promise) started (promise)]
     (binding [v2/*world* w]
       ;; the parent returns without awaiting its child: Q10 cancels the child,
       ;; whose host work ignores the interruption
       (let [go (v2/deferred)
             t (task (task (v2/offload (stubborn stop started))) (await go) :parent)]
         (deref started 2000 nil)
         (v2/deliver! go :go)
         (is (= :parent (v2/value t 2000 ::timeout)) "settlement does not wait")
         (is (= ::timeout (v2/await-joined t 100 ::timeout)) "the child is still unwinding")
         (deliver stop true)
         (is (true? (v2/await-joined t 2000 ::timeout)) "joined once the child has retired"))))))

(deftest a-join-waits-for-an-explicit-scope
  (checked
   (let [w (vworld) stop (promise) started (promise)]
     (binding [v2/*world* w]
       (let [go (v2/deferred)
             t (task (v2/with-scope (task (v2/offload (stubborn stop started)))
                       (await go))
                     :parent)]
         (deref started 2000 nil)
         (v2/deliver! go :go)
         (is (= :parent (v2/value t 2000 ::timeout)))
         (is (= ::timeout (v2/await-joined t 100 ::timeout)) "the closed scope keeps its unwinding task")
         (deliver stop true)
         (is (true? (v2/await-joined t 2000 ::timeout))))))))

(deftest a-detached-child-does-not-hold-its-parent
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [d (v2/deferred)
             child (promise)
             t (task (deliver child (v2/detach! (task (await d)) (v2/root-scope v2/*world*))) :parent)]
         (is (= :parent (v2/value t 2000 ::timeout)))
         (is (true? (v2/await-joined t 2000 ::timeout)) "the child now belongs to the root")
         (is (= ::timeout (v2/await-joined @child 100 ::timeout)))
         (v2/deliver! d :d)
         (is (true? (v2/await-joined @child 2000 ::timeout))))))))

(deftest a-withdrawn-join-does-not-fire
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [d (v2/deferred)
             t (task (await d))
             fired (atom 0)
             withdraw (v2/on-joined t #(swap! fired inc))
             p (promise)]
         (v2/on-joined t #(deliver p true))
         (withdraw)
         (v2/deliver! d :d)
         (is (true? (deref p 2000 ::timeout)))
         (is (zero? @fired)))))))

(deftest a-join-is-accepted-after-release
  (checked
   (let [w (vworld) stop (promise) started (promise)]
     (binding [v2/*world* w]
       (let [t (task (v2/offload (stubborn stop started)))]
         (deref started 2000 nil)
         (v2/release-world! w)
         (let [p (promise)]
           (v2/on-joined t #(deliver p true))
           (is (= ::timeout (deref p 100 ::timeout)) "the run is still in cleanup")
           (deliver stop true)
           (is (true? (deref p 2000 ::timeout)))
           (is (true? (v2/await-complete w 2000 ::timeout)))))))))

(deftest a-fork-does-not-inherit-host-joins
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [d (v2/deferred)
             t (task (await d))
             parent-fired (promise)]
         (v2/on-joined t #(deliver parent-fired true))
         (let [c (v2/fork! w)
               child-fired (promise)]
           (v2/on-joined (v2/in-world c t) #(deliver child-fired true))
           (v2/deliver! (v2/in-world c d) :d)
           (is (true? (deref child-fired 2000 ::timeout)) "the fork's copy completes")
           (is (= ::timeout (deref parent-fired 100 ::timeout)) "the parent's task still waits")
           (v2/deliver! d :d)
           (is (true? (deref parent-fired 2000 ::timeout)))
           (v2/release-world! c)))))))

(deftest an-unborn-instance-abandons-its-joins
  (checked
   (let [w (vworld) pubs (atom {})]
     (v2/install-handlers! w {:default (fn [p] (swap! pubs assoc (:payload p) p))})
     (binding [v2/*world* w]
       (let [t (task [:resumed (v2/savepoint :choose :b)])]
         (loop [n 0] (when (and (< n 400) (not (get @pubs :b))) (Thread/sleep 5) (recur (inc n))))
         (let [pub (get @pubs :b)
               i (v2/instantiate pub)
               p (promise)]
           (v2/on-joined (v2/in-world i t) #(deliver p true))
           (is (= ::timeout (deref p 100 ::timeout)) "unborn: its copy never runs")
           (v2/release-world! i)
           (is (true? (deref p 2000 ::timeout)) "delivered with the world's completion")
           (v2/abandon! pub)))))))

(deftest detach-into-another-worlds-scope-is-refused
  (checked
   (let [a (vworld) b (vworld)
         sb (promise)
         gate (binding [v2/*world* b] (v2/deferred))]
     (binding [v2/*world* b]
       (task (let [s (v2/open-scope!)] (deliver sb s) (await gate) (v2/close-scope-fx! s))))
     (binding [v2/*world* a]
       (let [d (v2/deferred)
             k (task (await d))]
         (v2/detach! k (deref sb 2000 nil))
         (is (some #(and (= :detach (first (:item %))) (false? (:accepted %))) (verify/log a))
             "refused: the scope is not in this world")
         (v2/deliver! d :d)
         (is (true? (v2/await-joined k 2000 ::timeout)))))
     (binding [v2/*world* b] (v2/deliver! gate :go)))))
