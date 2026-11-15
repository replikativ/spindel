(ns org.replikativ.spindel.v2.fork-test
  "M5 stage 1b: copy-on-write forks (§8.1, design v3)."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await]]
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

(defn- wait-until [f]
  (loop [n 0] (cond (f) true (> n 500) false :else (do (Thread/sleep 5) (recur (inc n))))))

(deftest fork-isolation
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [x (v2/signal 1)
             c (spin (* 10 (iv/get-new (track x))))
             seen-p (atom [])
             _ (v2/observe! c (fn [v _] (swap! seen-p conj v)))
             child (v2/fork! w)
             cx (v2/in-world child x)
             cc (v2/in-world child c)
             seen-c (atom [])
             _ (v2/observe! cc (fn [v _] (swap! seen-c conj v)))]
         (is (= [10] @seen-p))
         (is (= [10] @seen-c) "the child sees the fork-time state")
         (v2/write! cx 2)
         (is (= [10 20] @seen-c) "the child recomputes on its own write")
         (is (= [10] @seen-p) "the parent's observer is not called by the child (Z#45)")
         (is (= 10 (v2/value c)) "the parent is unchanged")
         (v2/write! x 3)
         (is (= [10 30] @seen-p))
         (is (= 20 (v2/value cc)) "the child is unchanged by the parent's write"))))))

(deftest releasing-a-fork-does-not-call-the-parent-s-callbacks
  ;; Z#45 at T21: the revoked roots a fork inherited belong to the parent's
  ;; host, which is not told the fork was released
  (let [w (v2/world) pubs (atom []) seen (atom [])]
    (v2/install-handlers! w {:s (fn [p] (swap! pubs conj p))})
    (let [t (binding [v2/*world* w] (task (v2/sleep 30) (inc (v2/savepoint :s nil))))
          c (binding [v2/*world* w] (spin 1))]
      (v2/observe! t (fn [v err?] (swap! seen conj [:task v err?])))
      (v2/observe! c (fn [v err?] (swap! seen conj [:comp v err?])))
      (is (wait-until #(seq @pubs)))
      (let [host-fork (v2/fork! w)
            inst (doto (v2/instantiate (first @pubs)) (v2/activate! 41))]
        (is (= 42 (v2/value (v2/in-world inst t) 1000 ::timeout)))
        (v2/release-world! inst)
        (v2/release-world! host-fork)
        (Thread/sleep 50)
        (is (= [[:comp 1 false]] @seen) "only the parent's own deliveries")
        (v2/resume! (first @pubs) 1)
        (is (= 2 (v2/value t 1000 ::timeout)))
        (v2/release-world! w)
        (Thread/sleep 50)
        (is (= [[:comp 1 false] [:task 2 false]] (take 2 @seen)))))))

(deftest parking-in-a-fork-copies-no-inherited-observe-edge
  ;; an instance parking again reads its task's out-edges to find blocked
  ;; creditors; the observe edges it inherited (Z#45) are only read, so they
  ;; stay shared with the parent instead of being copied into every fork
  (let [w (v2/world) pubs (atom [])]
    (v2/install-handlers! w {:s (fn [p] (swap! pubs conj p))})
    ;; observed before its first savepoint, so the publication and every
    ;; instance inherit the five observe edges
    (let [t (binding [v2/*world* w] (task (v2/sleep 50) (let [a (v2/savepoint :s 0)] (v2/savepoint :s a))))]
      (dotimes [_ 5] (v2/observe! t (fn [_ _])))
      (is (wait-until #(seq @pubs)))
      (let [inst (doto (v2/instantiate (first @pubs)) (v2/activate! 1))]
        (is (wait-until #(= 2 (count @pubs))) "the instance parks at its next savepoint")
        (is (zero? (count (filter #(and (== rw/T-EDGE (long (aget ^objects % rw/TYPE)))
                                        (== rw/EK-OBSERVE (long (aget ^objects % rw/E-KIND))))
                                  (vals (aget ^objects inst rw/W-FWD))))))
        (v2/release-world! inst)
        (v2/release-world! w)))))

(deftest repeated-forks
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [x (v2/signal 1)
             c (spin (+ 100 (iv/get-new (track x))))
             _ (v2/observe! c (fn [_ _]))
             a (v2/fork! w)
             _ (v2/write! (v2/in-world a x) 2)
             b (v2/fork! a)
             _ (v2/write! (v2/in-world b x) 3)]
         (is (= 101 (v2/value c)))
         (is (= 102 (v2/value (v2/in-world a c))))
         (is (= 103 (v2/value (v2/in-world b c))))
         (v2/write! (v2/in-world a x) 4)
         (is (= 104 (v2/value (v2/in-world a c))))
         (is (= 103 (v2/value (v2/in-world b c))) "a grandchild is isolated from its parent's later writes"))))))

(deftest parked-task-forks
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [d (v2/deferred)
             t (task (* 2 (await d)))
             child (v2/fork! w)]
         (v2/deliver! (v2/in-world child d) 21)
         (is (= 42 (v2/value (v2/in-world child t) 1000 ::timeout)) "the child's copy of the task resumes")
         (is (= ::pending (v2/value t 50 ::pending)) "the parent's task still waits")
         (v2/deliver! d 5)
         (is (= 10 (v2/value t 1000 ::timeout))))))))

(deftest fork-churn-leaves-the-parent-alone
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [x (v2/signal 0)
             c (spin (iv/get-new (track x)))
             _ (v2/observe! c (fn [_ _]))
             before (count (vals (aget ^objects w rw/W-REG)))]
         (dotimes [i 200]
           (let [f (v2/fork! w)]
             (v2/write! (v2/in-world f x) i)
             (assert (= i (v2/value (v2/in-world f c))))))
         (is (= before (count (vals (aget ^objects w rw/W-REG)))) "forks never add rows to the parent")
         (is (= 0 (v2/value c))))))))

(deftest fork-effect-in-a-task
  ;; D3/Q4: the parent continues with [:parent child]; the child's copy of
  ;; the run resumes at the effect with [:child nil].
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [x (v2/signal 1)
             out (promise)
             gate (v2/deferred)
             t (task (let [[side child] (v2/fork)]
                       (v2/write! x (if (= side :child) 20 10))
                       (when (= side :parent) (deliver out child))
                       (when (= side :parent) (await gate))
                       side))
             child (deref out 1000 nil)]
         (is (some? child))
         (is (= 10 (v2/value x)) "the parent wrote 10")
         (is (= :child (v2/value (v2/in-world child t) 1000 ::timeout))
             "the child's copy resumed with the child-side result")
         (is (= 20 (v2/value (v2/in-world child x))) "and wrote in the child")
         (v2/deliver! gate :done)
         (is (= :parent (v2/value t 1000 ::timeout)))
          ;; F2: the fork is owned by the task's run scope, released when it retires
         (is (wait-until #(aget ^objects child rw/W-RELEASED)) "the task's end releases its fork"))))))

(deftest dormant-resources-in-a-fork
  ;; §8.1: a timer re-arms in the fork; an offload fails with err ::forked.
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [release (promise)
             sleeper (task (v2/sleep 50) :woke)
             waiter (task (try (v2/offload #(deref release 5000 :late))
                               (catch Exception e (if (:spindel/forked (ex-data e)) :forked (throw e)))))
             child (v2/fork! w)]
         (is (= :woke (v2/value (v2/in-world child sleeper) 2000 ::timeout)) "the timer re-armed in the child")
         (is (= :forked (v2/value (v2/in-world child waiter) 2000 ::timeout)) "the offload has no counterpart in the child")
         (is (= :woke (v2/value sleeper 2000 ::timeout)))
         (deliver release :done)
         (is (= :done (v2/value waiter 2000 ::timeout)) "the parent's offload is unaffected"))))))

(deftest idle-validity-reads-the-child-copy
  ;; reactivation compares each validity version against this world's copy of
  ;; the debtor, not the frozen basis row
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [x (v2/signal 1)
             c (spin (* 10 (iv/get-new (track x))))
             unobserve (v2/observe! c (fn [_ _]))]
         (unobserve)                                   ; c is idle with validity [x 1]
         (let [child (v2/fork! w)
               cx (v2/in-world child x)
               cc (v2/in-world child c)
               seen (atom [])]
           (v2/write! cx 2)
           (v2/observe! cc (fn [v _] (swap! seen conj v)))
           (is (= [20] @seen) "the child's write invalidates the idle result")
           (is (= 10 (v2/value c)) "the parent keeps its own")))))))

(deftest releasing-a-fork-leaves-an-untouched-inherited-source-to-its-parent
  ;; T21's handle revocation acts on the fork's own copy, never on the
  ;; basis row it shares with its parent
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [s (v2/signal :b)
             c (v2/fork! w)]
         (v2/release-world! c)
         (is (= :b @s))
         (reset! s :c)
         (is (= :c @s))))
     (v2/release-world! w))))

(deftest a-body-may-fork-another-world
  (checked
   (let [w (vworld) other (vworld)]
     (binding [v2/*world* other] (v2/signal 1))
     (binding [v2/*world* w]
       (let [t (task (let [c (v2/fork! other)]
                       (v2/release-world! c)
                       :forked))]
         (is (= :forked (v2/value t 2000 ::timeout)))
         (is (thrown? Exception (v2/value (task (v2/fork! w)) 2000 ::timeout))
             "its own world: refused, use the (fork) effect")))
     (v2/release-world! other)
     (v2/release-world! w))))

(deftest a-host-fork-may-name-its-owner
  ;; F2 with another owner: the fork outlives the world it copies and is
  ;; released with its owner
  (let [root (v2/world)
        a (v2/fork! root)
        x (binding [v2/*world* a] (v2/signal 1))
        b (v2/fork! a {:owner root})
        c (v2/fork! a)]
    (v2/release-world! a)
    (Thread/sleep 50)
    (is (= 1 (v2/value (v2/in-world b x))) "b is owned by root: it outlives a")
    (is (thrown? Exception (v2/value (v2/in-world c x))) "c is owned by a: released with it")
    (v2/release-world! root)
    (Thread/sleep 50)
    (is (thrown? Exception (v2/value (v2/in-world b x))) "released with its owner")
    (is (thrown? clojure.lang.ExceptionInfo (v2/fork! root {:owner (v2/world)})) "an unrelated owner")))

(defn- holding-the-gate
  "Starts a slice of `w` that holds its gate for `ms`; returns once it runs."
  [w ms]
  (let [entered (promise)]
    (future (binding [v2/*world* w] (task (deliver entered true) (Thread/sleep ms))))
    (deref entered 1000 false)))

(deftest host-forks-of-a-busy-world-wait-for-their-fork
  ;; R5: a host fork is a host call; it used to return nil (and fail) when
  ;; another thread held the world's gate
  (let [w (v2/world)]
    (holding-the-gate w 200)
    (let [forks (mapv deref (doall (repeatedly 8 #(future (v2/fork! w)))))]
      (is (every? some? forks))
      (is (= 8 (count (set forks))))
      (run! v2/release-world! forks))
    (v2/release-world! w)))

(deftest a-body-forking-a-busy-world-is-refused
  ;; B7: a body of another world may not wait for the world it forks
  (let [w (v2/world) other (v2/world)]
    (holding-the-gate w 300)
    (let [r (v2/value (binding [v2/*world* other]
                        (task (try (v2/fork! w) :forked
                                   (catch clojure.lang.ExceptionInfo e (:spindel/invalid (ex-data e))))))
                      2000 ::timeout)]
      (is (= :busy r)))
    (Thread/sleep 350)
    (is (= :forked (v2/value (binding [v2/*world* other]
                               (task (v2/release-world! (v2/fork! w)) :forked))
                             2000 ::timeout))
        "an idle world forks at once")
    (v2/release-world! other)
    (v2/release-world! w)))

;; Rows inherited from the fork's basis must be resolved before they are written:
;; a basis row is shared with the other world.

(deftest a-computation-parked-at-the-fork-resumes-in-both-worlds
  (doseq [order [[:child :parent] [:parent :child]]]
    (testing (str "delivered " order)
      (checked
       (let [w (vworld)]
         (binding [v2/*world* w]
           (let [d (v2/deferred)
                 c (spin [:got (await d)])
                 seen-p (atom [])
                 _ (v2/observe! c (fn [v _] (swap! seen-p conj v)))
                 child (v2/fork! w)
                 seen-c (atom [])
                 _ (v2/observe! (v2/in-world child c) (fn [v _] (swap! seen-c conj v)))]
             (doseq [who order]
               (if (= who :child) (v2/deliver! (v2/in-world child d) :child) (v2/deliver! d :parent)))
             (is (wait-until #(and (seq @seen-p) (seq @seen-c))))
             (is (= [[:got :parent]] @seen-p))
             (is (= [[:got :child]] @seen-c))
             (v2/release-world! child)))
         (v2/release-world! w))))))

(deftest a-mailbox-waiter-at-the-fork-is-served-in-both-worlds
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [mb (v2/mailbox)
             t (task (v2/take! mb))
             child (v2/fork! w)]
         ((v2/in-world child mb) :child)
         (mb :parent)
         (is (= :child (v2/value (v2/in-world child t) 1000 ::timeout)))
         (is (= :parent (v2/value t 1000 ::timeout)))
         (v2/release-world! child)))
     (v2/release-world! w))))

(deftest a-run-retiring-in-a-fork-closes-only-the-fork-s-sources
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [box (atom nil)
             d (v2/deferred)
             t (task (let [s (v2/signal 0)] (reset! box s) (await d) :done))
             _ (wait-until #(some? @box))
             s @box
             child (v2/fork! w)]
         (v2/deliver! (v2/in-world child d) :go)
         (is (= :done (v2/value (v2/in-world child t) 1000 ::timeout)))
         (v2/write! s 1)
         (is (= 1 (v2/value s)) "the parent's source stays open")
         (v2/deliver! d :go)
         (is (= :done (v2/value t 1000 ::timeout)))
         (v2/release-world! child)))
     (v2/release-world! w))))

(deftest an-explicit-scope-open-at-the-fork-closes-in-each-world
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [d (v2/deferred)
             t (task (v2/with-scope (let [v (await d)] (await (task [:sub v])))))
             child (v2/fork! w)]
         (v2/deliver! (v2/in-world child d) :c)
         (is (= [:sub :c] (v2/value (v2/in-world child t) 1000 ::timeout)))
         (v2/deliver! d :p)
         (is (= [:sub :p] (v2/value t 1000 ::timeout)) "the child's scope close did not close the parent's")
         (v2/release-world! child)))
     (v2/release-world! w))))
