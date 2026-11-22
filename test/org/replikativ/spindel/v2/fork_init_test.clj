(ns org.replikativ.spindel.v2.fork-init-test
  "Host fork with a private initial world state (`fork!` `:init-state`) and
   publication after acceptance (spec §8.1 F, H1); `instantiate` publishes
   an instance with all its birth fields set. The races are made
   deterministic: the family's atom maintenance is run synchronously on its
   own thread at registration, and the worlds' executor runs handoffs in
   the submitting thread."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [task await]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.host :as hs]
            [org.replikativ.spindel.v2.lifetime :as lt]
            [org.replikativ.spindel.v2.verify :as verify]))

(def ^:dynamic *divergences* nil)

(defn- vworld
  ([] (vworld {}))
  ([opts] (v2/world (merge {:verify? true :hook (verify/checking-hook *divergences*)} opts))))

(defmacro checked [& body]
  `(binding [*divergences* (atom [])]
     ~@body
     (is (empty? @*divergences*) (str "Rule R divergences: " (vec (take 3 @*divergences*))))))

(defn- wait-until [f]
  (loop [n 0] (cond (f) true (> n 400) false :else (do (Thread/sleep 5) (recur (inc n))))))

(def caller-runs
  "An executor that runs a handoff in the submitting thread."
  (reify java.util.concurrent.Executor
    (execute [_ r] (.run ^Runnable r))))

(defn- on-thread
  "Runs `f` on a fresh thread named `nm` and waits for it."
  [nm f]
  (let [t (Thread. ^Runnable f ^String nm)]
    (.start t)
    (.join t 5000)
    nil))

(defmacro with-synchronous-maintenance
  "The family's atom maintenance runs at once, on its own thread, while the
   requesting thread waits: a registration with a stale sweep generation
   enters the new world before the registering call returns."
  [& body]
  `(with-redefs [hs/metadata-later! (fn ([f#] (on-thread "test-maintenance" f#))
                                      ([f# _#] (on-thread "test-maintenance" f#)))]
     ~@body))

(defn- stale-generation!
  "Advances the family's atom-sweep generation past every copy: a world
   registered next requests maintenance at once (lifetime/register-world!)."
  [w]
  (swap! (:generation (aget ^objects w rw/W-FAMILY)) inc))

(defn- member? [w id]
  (some? (hs/mget (:worlds (aget ^objects w rw/W-FAMILY)) id)))

(defn- committed? [w id]
  (boolean (some #(= [:fork-host id] (:item %)) (verify/log w))))

(defn- next-id [w] (#'v2/peek-id w))

(defn- recorder
  "A task body's record: [world-id world-state thread-name]."
  []
  (let [cw (v2/current-world)]
    [(v2/world-id cw) (v2/world-state cw) (.getName (Thread/currentThread))]))

(deftest init-state-is-seen-by-the-first-slice-under-early-maintenance
  (checked
   (let [w (vworld {:executor caller-runs})
         seen (atom [])]
     (stale-generation! w)
     (let [c (with-synchronous-maintenance
               ;; the fork from a host item of w, which first starts a task:
               ;; the child inherits it as runnable work
               (v2/host-call! w (fn []
                                  (binding [v2/*world* w]
                                    (task (swap! seen conj (let [r (recorder)] (conj r (committed? w (first r)))))))
                                  (v2/fork! w {:init-state (fn [s _] (assoc s :k :init))}))))
           cid (v2/world-id c)
           mine (filterv #(= cid (first %)) @seen)]
       (is (= 1 (count mine)) "the child's copy of the task ran once")
       (is (= "test-maintenance" (nth (first mine) 2))
           "the child was entered by the family's maintenance, at registration")
       (is (true? (nth (first mine) 3)) "after the parent committed the fork")
       (is (= {:k :init} (second (first mine))) "its first slice sees the initial state")
       (is (= {} (v2/world-state w)) "the parent's state is unchanged")
       (is (= {:k :init} (v2/world-state c)))))))

(deftest a-default-owner-fork-is-published-after-its-commit
  (checked
   (let [obs (atom [])
         w (v2/world {:verify? true
                      :hook (fn [w item]
                              (when (= :fork-host (first item))
                                (swap! obs conj [:observer (second item) (member? w (second item))])))})
         register lt/register-world!
         regs (atom [])
         c (with-redefs [lt/register-world! (fn [family x id & more]
                                              (swap! regs conj [:register id (committed? w id)])
                                              (apply register family x id more))]
             (v2/fork! w))
         cid (v2/world-id c)]
     (is (= [[:observer cid false]] @obs) "no family membership at the commit")
     (is (= [[:register cid true]] @regs) "registered once, after the commit")
     (is (member? w cid))
     (testing "the (fork) effect's child and a savepoint basis are registered as before"
       (let [regs (atom [])
             pubs (atom [])]
         (v2/install-handlers! w {:s (fn [p] (swap! pubs conj p))})
         (with-redefs [lt/register-world! (fn [family x id & more]
                                            (swap! regs conj id)
                                            (apply register family x id more))]
           (binding [v2/*world* w]
             (let [t (task (let [[side child] (v2/fork)] (if (= side :parent) (v2/world-id child) side)))
                   s (task (v2/savepoint :s 1))]
               (is (some #{(v2/value t 2000 ::timeout)} @regs) "the effect's child")
               (is (wait-until #(= 1 (count @pubs))))
               (is (some #{(v2/world-id (:basis (first @pubs)))} @regs) "the basis")
               (v2/abandon! (first @pubs))
               (is (:spindel/cancelled (ex-data (try (v2/value s 2000 ::timeout) (catch Exception e e)))))))))))))

(deftest a-throwing-initializer-leaves-only-an-id-gap
  (checked
   (let [w (vworld)
         state (fn [] {:epoch (aget ^objects w rw/W-EPOCH)
                       :tokens (some-> (aget ^objects w rw/W-TOKENS) count) :log (count (verify/log w))})
         before (state)
         n (next-id w)
         got (atom nil)
         e (try (v2/fork! w {:init-state (fn [s ctx]
                                           (reset! got [s ctx])
                                           (throw (ex-info "init failed" {::init true})))})
                nil
                (catch clojure.lang.ExceptionInfo e e))]
     (is (::init (ex-data e)) "the initializer's throw is the fork's")
     (is (= [{} {:world-id n}] @got) "called with the source state and the child's id")
     (is (= (inc n) (next-id w)) "the child's id stays unused")
     (is (= before (state)) "no epoch step, MVCC token or log item")
     (let [s (binding [v2/*world* w] (v2/signal 1))
           _ (is (= (+ 2 n) (next-id w)) "an ordinary allocation takes the next id")
           c (v2/fork! w {:init-state (fn [s {:keys [world-id]}] (assoc s :id world-id))})]
       (is (= (+ 2 n) (v2/world-id c)) "the next fork takes the id after it")
       (is (= [:fork-host (v2/world-id c)] (:item (peek (verify/log w)))))
       (is (= {:id (v2/world-id c)} (v2/world-state c)) "the initializer saw the child's own id")
       (is (= 1 (v2/value (v2/in-world c s) 1000 ::timeout)))))))

(deftest a-throwing-observer-does-not-undo-an-accepted-fork
  (let [w (v2/world {:verify? true
                     :hook (fn [_ item]
                             (when (= :fork-host (first item)) (throw (ex-info "observer failed" {}))))})
        seen (atom [])
        err (java.io.StringWriter.)
        c (binding [*err* err]
            (v2/host-call! w (fn []
                               (binding [v2/*world* w] (task (swap! seen conj (recorder))))
                               (v2/fork! w {:init-state (fn [s _] (assoc s :k :init))}))))
        cid (v2/world-id c)]
    (is (some? cid) "the fork returns the child")
    (is (committed? w cid) "the fork is accepted")
    (is (member? w cid) "and published")
    (is (wait-until #(some (fn [[id]] (= cid id)) @seen)) "the child was handed off")
    (is (= {:k :init} (second (first (filter #(= cid (first %)) @seen)))))
    (is (re-find #"commit observer failed" (str err)) "the observer's throw is reported")))

(deftest a-fork-queued-before-a-release-is-refused
  (checked
   (let [w (vworld)
         lk (aget ^objects w rw/W-LOCK)
         queued #(count (seq (aget ^objects w rw/W-INGRESS)))]
     (hs/lock! lk)
     (let [n (next-id w)
           f (future (try (v2/fork! w {:init-state (fn [s _] (assoc s :k 1))}) (catch Throwable t t)))]
       (is (wait-until #(= 1 (queued))) "the fork is admitted and queued")
       (#'v2/release-world* w)               ; T21 first
       (hs/unlock! lk)
       (#'v2/process! w)
       (let [r (deref f 2000 ::timeout)]
         (is (:spindel/released (ex-data r)) "the fork is refused when its item runs")
         (is (= n (next-id w)) "no child id")
         (is (not-any? #(= :fork-host (first (:item %))) (verify/log w))))))))

(deftest a-fork-from-a-host-item-never-enters-the-child-under-the-parent-gate
  (checked
   (let [parent (promise)
         nested (atom 0)
         ex (reify java.util.concurrent.Executor
              (execute [_ r]
                (when (and (realized? parent) (hs/held? (aget ^objects @parent rw/W-LOCK)))
                  (swap! nested inc))
                (.run ^Runnable r)))
         w (vworld {:executor ex})
         seen (atom [])]
     (deliver parent w)
     (let [c (v2/host-call! w (fn []
                                (binding [v2/*world* w] (task (swap! seen conj (recorder))))
                                (v2/fork! w {:init-state (fn [s _] (assoc s :k :init))})))
           cid (v2/world-id c)]
       (is (zero? @nested) "no handoff runs under the parent's gate")
       (is (wait-until #(some (fn [[id]] (= cid id)) @seen)) "the child runs after the gate")
       (is (= {:k :init} (second (first (filter #(= cid (first %)) @seen)))))))))

(defn- release-refusing-observer
  "A commit observer that throws at every T21 (`[:release-world]`), after
   checking Rule R."
  []
  (let [check (verify/checking-hook *divergences*)]
    (fn [w item]
      (check w item)
      (when (= :release-world (first item)) (throw (ex-info "observer failed" {}))))))

(deftest a-fork-whose-insertion-fails-is-released-unpublished
  (checked
   (let [w (v2/world {:verify? true :hook (release-refusing-observer)})
         register lt/register-world!
         n (next-id w)                       ; the child's id
         e (binding [*err* (java.io.StringWriter.)]
             (with-redefs [lt/register-world! (fn [family x id & more]
                                                ;; fails before the registry insertion
                                                (when (= id n) (throw (ex-info "registry full" {})))
                                                (apply register family x id more))]
               (try (v2/fork! w) nil (catch clojure.lang.ExceptionInfo e e))))
         c (:child (ex-data e))]
     (is (:spindel/unpublished (ex-data e)) "surfaced to the caller, with the child")
     (is (committed? w (v2/world-id c)) "the fork stays accepted")
     (is (not (member? w (v2/world-id c))) "no family membership")
     (is (true? (v2/await-complete c 2000 ::timeout))
         "the child is released and completes, although the observer throws at its T21")
     (binding [*err* (java.io.StringWriter.)] (v2/release-world! w))
     (is (true? (v2/await-complete w 2000 ::timeout)) "the owner's obligation ended"))))

(def ^:private objects-class (Class/forName "[Ljava.lang.Object;"))

(defn- world-row? [x] (and (instance? objects-class x) (= rw/T-WORLD (aget ^objects x rw/TYPE))))

(deftest a-failure-after-insertion-is-the-published-childs
  ;; the insertion publishes the child (maintenance enters it at once), then
  ;; the sweep request fails: the fork returns its published child, whose
  ;; collection action was installed before the insertion
  (checked
   (let [w (vworld {:executor caller-runs})
         seen (atom [])
         err (java.io.StringWriter.)
         on-collect hs/on-collect!
         actions (atom {})
         fail-once (atom true)
         _ (stale-generation! w)
         c (with-redefs [hs/metadata-later! (fn [f & _]
                                              (on-thread "test-maintenance" f)
                                              (when (compare-and-set! fail-once true false)
                                                (throw (ex-info "scheduler down" {}))))
                         hs/on-collect! (fn [x action]
                                          (when (and (world-row? x) (not (identical? x w)))
                                            (swap! actions assoc (aget ^objects x rw/ID)
                                                   [action (member? w (aget ^objects x rw/ID))]))
                                          (on-collect x action))]
             (binding [*err* err]
               (v2/host-call! w (fn []
                                  (binding [v2/*world* w] (task (swap! seen conj (recorder))))
                                  (v2/fork! w {:init-state (fn [s _] (assoc s :k :init))})))))
         cid (v2/world-id c)
         [action member-at-install] (get @actions cid)]
     (is (false? @fail-once) "the sweep request failed")
     (is (= [[cid {:k :init} "test-maintenance"]] (filterv #(= cid (first %)) @seen))
         "maintenance entered the child at its publication")
     (is (member? w cid) "the fork returned its published child")
     (is (committed? w cid))
     (is (re-find #"fork publication failed" (str err)) "the failure is reported")
     (is (false? member-at-install) "the collection action was installed before the insertion")
     (action)                                ; the child's collection
     (is (not (member? w cid)) "its collection removes its registry entry")
     (is (= :done (.get ^java.util.concurrent.atomic.AtomicReference (aget ^objects c rw/W-KID-TOKEN)))
         "and acknowledges its owner"))))

(deftest a-failed-collection-action-leaves-the-child-unpublished
  ;; sol's probe: a child whose collection action cannot be installed must
  ;; not strand its owner
  (checked
   (let [w (vworld)
         on-collect hs/on-collect!
         e (with-redefs [hs/on-collect! (fn [x action]
                                          (if (and (world-row? x) (not (identical? x w)))
                                            (throw (ex-info "cleaner failed" {}))
                                            (on-collect x action)))]
             (try (v2/fork! w) nil (catch clojure.lang.ExceptionInfo e e)))
         c (:child (ex-data e))]
     (is (:spindel/unpublished (ex-data e)) "a failure before the insertion: unpublished")
     (is (not (member? w (v2/world-id c))) "never in the registry")
     (is (true? (v2/await-complete c 2000 ::timeout)) "the child is released and completes")
     (v2/release-world! w)
     (is (true? (v2/await-complete w 2000 ::timeout)) "the owner is acknowledged and completes"))))

(deftest a-throwing-observer-cannot-block-a-release
  (binding [*divergences* (atom [])]
    (let [w (v2/world {:verify? true :hook (release-refusing-observer)})]
      (binding [*err* (java.io.StringWriter.)] (v2/release-world! w))
      (is (true? (v2/await-complete w 2000 ::timeout)) "T21 commits and the world completes"))))

(deftest the-release-observer-sees-the-released-world
  (let [seen (atom [])
        w (v2/world {:verify? true
                     :hook (fn [w item]
                             (when (= :release-world (first item))
                               (swap! seen conj (aget ^objects w rw/W-RELEASED))))})]
    (v2/release-world! w)
    (is (= [true] @seen) "T21 is complete when its observer runs")
    (is (true? (v2/await-complete w 2000 ::timeout)))))

(deftest the-checking-harness-records-its-own-errors
  (let [acc (atom [])]
    ((verify/checking-hook acc) (object-array 1) [:x])
    (is (= [[[:x] true]] (mapv (juxt :item (comp some? :observer-error)) @acc))
        "a check that throws is a divergence, not an empty list")))

(deftest a-failing-report-cannot-interrupt-a-fork
  (let [w (v2/world {:verify? true
                     :hook (fn [_ item] (when (= :fork-host (first item)) (throw (ex-info "observer failed" {}))))})
        closed (proxy [java.io.Writer] []
                 (write [& _] (throw (java.io.IOException. "Stream closed")))
                 (flush [] (throw (java.io.IOException. "Stream closed")))
                 (close []))
        c (binding [*err* closed] (v2/fork! w))]
    (is (member? w (v2/world-id c)) "published and returned")
    (is (committed? w (v2/world-id c)))))

(deftest a-queued-forks-child-is-handed-off-after-the-source-gate
  ;; the fork's reply is delivered from inside the drainer's turn; the
  ;; waiting caller must not run the child while that turn holds the gate
  (checked
   (let [w (vworld {:executor caller-runs})
         ^java.util.concurrent.locks.ReentrantLock lk (aget ^objects w rw/W-LOCK)
         queued #(count (seq (aget ^objects w rw/W-INGRESS)))
         seen (atom [])
         entered (promise)
         go (promise)]
     (hs/lock! lk)
     ;; under the held gate: created at once, runnable, not run
     (binding [v2/*world* w]
       (task (swap! seen conj [(v2/world-id (v2/current-world)) (.isLocked lk)])))
     (let [fork (future (v2/fork! w {:init-state (fn [s _] (assoc s :k 1))}))
           _ (is (wait-until #(= 1 (queued))) "the fork is queued")
           next-item (future (v2/host-call! w (fn [] (deliver entered true) (deref go 5000 nil))))
           _ (is (wait-until #(= 2 (queued))) "and an item after it")
           _ (hs/unlock! lk)
           drainer (future (#'v2/process! w))
           _ (is (deref entered 5000 false) "the drainer is inside the next item")
           c (deref fork 5000 ::timeout)
           cid (v2/world-id c)]
       (is (= [] (filterv #(= cid (first %)) @seen))
           "the caller's reply did not run the child while the drainer holds the gate")
       (deliver go true)
       @drainer @next-item
       (is (wait-until #(some (fn [[id]] (= cid id)) @seen)))
       (is (= [[cid false]] (filterv #(= cid (first %)) @seen)) "the child ran after the gate was released")))))

(deftest separate-owner-forks-refuse-init-state
  (let [w (v2/world) o (v2/fork! w)]
    (is (= :init-state (:spindel/invalid (ex-data (try (v2/fork! w {:owner o :init-state identity}) nil
                                                       (catch clojure.lang.ExceptionInfo e e))))))
    (is (some? (v2/world-id (v2/fork! w {:owner o}))) "without it, unchanged")
    (is (= {:a 1} (v2/world-state (v2/fork! w {:owner w :init-state (fn [s _] (assoc s :a 1))})))
        "the source itself is the default owner")))

(deftest instantiate-publishes-an-unborn-instance
  (checked
   (let [w (vworld {:executor caller-runs})
         pubs (atom [])
         seen (atom [])]
     (v2/install-handlers! w {:s (fn [p] (swap! pubs conj p))})
     ;; one host item starts two tasks: the first publishes at its savepoint
     ;; while the second is still runnable, so the basis inherits it
     (v2/host-call! w (fn []
                        (binding [v2/*world* w]
                          (task (v2/savepoint :s nil) (swap! seen conj (conj (recorder) :resumed)))
                          (task (swap! seen conj (recorder))))))
     (is (= 1 (count @pubs)))
     (stale-generation! w)
     (let [i (with-synchronous-maintenance
               (v2/instantiate (first @pubs) nil #(assoc % :k :init)))
           iid (v2/world-id i)
           mine #(filterv (fn [r] (= iid (first r))) @seen)]
       (is (member? w iid) "published")
       (is (= [] (mine)) "maintenance at registration runs no inherited work: the instance is unborn")
       (is (= {:k :init} (v2/world-state i)))
       (v2/activate! i :go)
       (is (= #{[iid {:k :init}]} (set (map #(subvec % 0 2) (mine))))
           "after activation the inherited work runs, and sees the initial state")
       (is (= 2 (count (mine))))
       (v2/abandon! (first @pubs))))))

(deftest a-nested-fork-of-another-world-hands-off-after-the-enclosing-gate
  ;; a host item of `a` forks `b` (the claim path, which runs b's turn under
  ;; a's gate): b's after-gate work waits for a's gate too
  (checked
   (let [a (vworld)
         b (vworld {:executor caller-runs})
         ^java.util.concurrent.locks.ReentrantLock la (aget ^objects a rw/W-LOCK)
         lb (aget ^objects b rw/W-LOCK)
         seen (atom [])]
     ;; under b's held gate: created at once, runnable, not run
     (hs/lock! lb)
     (binding [v2/*world* b]
       (task (swap! seen conj [(v2/world-id (v2/current-world)) (.isLocked la)])))
     (hs/unlock! lb)
     (let [c (v2/host-call! a (fn [] (v2/fork! b)))
           cid (v2/world-id c)]
       (is (wait-until #(some (fn [[id]] (= cid id)) @seen)))
       (is (= [[cid false]] (filterv #(= cid (first %)) @seen))
           "the child ran after a's gate was released, not under it")))))

(deftest a-savepoint-basis-never-runs
  ;; the basis is published while a sibling task is still runnable in its
  ;; copy, and its stale sweep generation has maintenance enter it at once
  (checked
   (let [w (vworld {:executor caller-runs})
         pubs (atom [])
         seen (atom [])]
     (v2/install-handlers! w {:s (fn [p] (swap! pubs conj p))})
     (stale-generation! w)
     (with-synchronous-maintenance
       (v2/host-call! w (fn []
                          (binding [v2/*world* w]
                            (task (v2/savepoint :s nil) :after)
                            (task (swap! seen conj (recorder)))))))
     (let [p (first @pubs)
           bid (v2/world-id (:basis p))]
       (is (member? w bid) "the basis is registered")
       (is (= [] (filterv #(= bid (first %)) @seen)) "no work runs in the basis")
       (testing "an instance of it runs the inherited work once activated"
         (let [i (doto (v2/instantiate p) (v2/activate! :go))]
           (is (wait-until #(some (fn [[id]] (= (v2/world-id i) id)) @seen)))))
       (v2/abandon! p)))))
