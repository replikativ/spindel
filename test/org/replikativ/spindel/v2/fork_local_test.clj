(ns org.replikativ.spindel.v2.fork-local-test
  "Z#77: a fork-local task (`task-with {:fork-local true}`) and every task
   its runs create under their scopes are retired in every fork of their
   world at the fork's first gate entry (T28): nothing of theirs runs there
   (no slice, finalizer, timer, resource), their tasks fail with ::forked
   (:spindel/fork-local) for the inherited waiters, and the sources their
   scopes own close. Everything else is inherited live.

   `*mark*` false runs the same scenarios with plain tasks: the assertions
   marked NEGATIVE then fail (today's inheritance), which is how each test is
   checked against the behaviour it changes."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [task task-with await]]
            [org.replikativ.spindel.v2.verify :as verify]))

(def ^:dynamic *mark* true)

(def ^:dynamic *divergences* nil)
(defn- vworld [] (v2/world {:verify? true :hook (verify/checking-hook *divergences*)}))
(defmacro checked [& body]
  `(binding [*divergences* (atom [])]
     ~@body
     (is (empty? @*divergences*) (str "Rule R divergences: " (vec (take 3 @*divergences*))))))

(defn- wid [] (v2/world-id (v2/current-world)))
(defn- in-child? [c [_ id]] (= id (v2/world-id c)))
(defn- settle [] (Thread/sleep 60))
(defn- done! [& ws]
  (doseq [w (reverse ws)] (v2/release-world! w))
  (doseq [w ws] (is (true? (v2/await-complete w 3000 ::timeout)))))

(defmacro ltask
  "A fork-local task, or a plain one when `*mark*` is false."
  [& body]
  `(task-with {:fork-local *mark*} ~@body))

(deftest a-local-loop-does-not-tick-in-a-fork
  (checked
   (doseq [entry [:task-start :swap-world :stream-append]]
     (testing (str "entered by " entry)
       (let [log (atom [])
             w (vworld)
             s (binding [v2/*world* w] (v2/stream))
             _ (binding [v2/*world* w]
                 (ltask (loop [] (v2/sleep 15) (swap! log conj [:tick (wid)]) (recur))))
             _ (Thread/sleep 50)
             c (v2/fork! w)]
         (case entry
           :task-start (binding [v2/*world* c] (task :x))
           :swap-world (v2/swap-world! c assoc :x 1)
           :stream-append (v2/append! (v2/in-world c s) 1))
         (Thread/sleep 120)
         (is (not-any? #(in-child? c %) @log) "NEGATIVE: no tick in the child")
         (is (some #(= [:tick (v2/world-id w)] %) @log) "the parent keeps ticking")
         (done! c w))))))

(deftest a-local-run-mid-offload-runs-nothing-in-a-fork
  (checked
   (let [log (atom [])
         w (vworld)
         h (binding [v2/*world* w]
             (ltask (try (v2/offload (fn [] (Thread/sleep 150) :reply))
                         (swap! log conj [:replied (wid)])
                         (catch Throwable e (swap! log conj [:caught (wid) (ex-data e)]))
                         (finally (swap! log conj [:finally (wid)])))))
         _ (settle)
         c (v2/fork! w)]
     (v2/swap-world! c assoc :x 1)
     (let [r (try (v2/value (v2/in-world c h) 1000 ::timeout)
                  (catch clojure.lang.ExceptionInfo e (ex-data e)))]
       (is (= {:spindel/forked true :spindel/fork-local true} r) "NEGATIVE: the child's copy is retired"))
     (Thread/sleep 250)
     (is (not-any? #(in-child? c %) @log) "NEGATIVE: no catch or finally in the child")
     (is (= [[:replied (v2/world-id w)] [:finally (v2/world-id w)]] @log) "the parent replies")
     (done! c w))))

(deftest an-untouched-fork-runs-no-local-finalizer-at-release
  (checked
   (let [log (atom [])
         w (vworld)
         d (binding [v2/*world* w] (v2/deferred))
         _ (binding [v2/*world* w]
             (ltask (try (await d) (finally (swap! log conj [:finally (wid)])))))
         _ (settle)
         c (v2/fork! w)]
     (v2/release-world! c)
     (is (true? (v2/await-complete c 3000 ::timeout)))
     (is (not-any? #(in-child? c %) @log) "NEGATIVE: no finalizer in the released child")
     (v2/deliver! d 1)
     (settle)
     (is (= [[:finally (v2/world-id w)]] @log))
     (done! w))))

(deftest the-fork-effect-retires-local-siblings
  (checked
   (let [log (atom [])
         w (vworld)
         d (binding [v2/*world* w] (v2/deferred))
         _ (binding [v2/*world* w]
             (ltask (try (await d) (finally (swap! log conj [:sibling-finally (wid)])))))
         _ (settle)
         child (promise)
         _ (binding [v2/*world* w]
             (task (let [[side c] (v2/fork)]
                     (if (= :parent side)
                       (do (deliver child c) (await d))   ; its scope owns the child (F2)
                       (swap! log conj [:child-side (wid)])))))
         c (deref child 1000 ::timeout)]
     (settle)
     (is (some #(= [:child-side (v2/world-id c)] %) @log) "the forker resumes in the child")
     (v2/release-world! c)
     (is (true? (v2/await-complete c 3000 ::timeout)))
     (is (not-any? #(= [:sibling-finally (v2/world-id c)] %) @log) "NEGATIVE: no sibling finalizer in the child")
     (v2/deliver! d 1)
     (done! w))))

(deftest unmarked-work-is-inherited-live
  (checked
   (let [log (atom [])
         w (vworld)
         d (binding [v2/*world* w] (v2/deferred))
         h (binding [v2/*world* w] (task (let [v (await d)] (swap! log conj [:got v (wid)]) v)))
         _ (binding [v2/*world* w] (task (v2/sleep 250) (swap! log conj [:timer (wid)])))
         _ (settle)
         c (v2/fork! w)]
     (v2/deliver! (v2/in-world c d) 7)
     (is (= 7 (v2/value (v2/in-world c h) 1000 ::timeout)) "the child's copy resumes")
     (Thread/sleep 400)
     (is (some #(= [:got 7 (v2/world-id c)] %) @log))
     (is (some #(= [:timer (v2/world-id c)] %) @log) "the timer re-arms in the child")
     (v2/deliver! d 1)
     (done! c w))))

(deftest cancel-before-the-first-turn-finds-the-task-retired
  (checked
   (let [log (atom [])
         w (vworld)
         d (binding [v2/*world* w] (v2/deferred))
         lh (binding [v2/*world* w]
              (ltask (try (await d) (finally (swap! log conj [:loop-finally (wid)])))))
         _ (binding [v2/*world* w]
             (task (try (await lh)
                        (catch Throwable e (swap! log conj [:waiter (wid) (ex-data e)])))))
         _ (settle)
         c (v2/fork! w)]
     (v2/cancel-task! (v2/in-world c lh))
     (settle)
     (is (not-any? #(= [:loop-finally (v2/world-id c)] %) @log) "NEGATIVE: no finalizer in the child")
     (is (some #(= [:waiter (v2/world-id c) {:spindel/forked true :spindel/fork-local true}] %) @log)
         "NEGATIVE: the unmarked waiter gets ::forked (fork-local), not ::cancelled")
     (v2/deliver! d 1)
     (done! c w))))

(deftest waiters-and-joins-in-the-fork
  (checked
   (let [w (vworld)
         d (binding [v2/*world* w] (v2/deferred))
         lh (binding [v2/*world* w] (ltask (await d)))
         _ (settle)
         host-calls (atom 0)
         _ (v2/value-async lh (fn [_ _] (swap! host-calls inc)))
         c (v2/fork! w)
         joined (promise)]
     (v2/on-joined (v2/in-world c lh) #(deliver joined true))
     (is (true? (deref joined 1000 ::timeout)) "NEGATIVE: the retired task is complete in the child")
     (is (zero? @host-calls) "the parent's host wait is not called by the child")
     (is (= ::timeout (v2/await-joined lh 50 ::timeout)) "the parent's task is unaffected")
     (v2/deliver! d 1)
     (is (true? (v2/await-joined lh 1000 ::timeout)))
     (settle)
     (is (= 1 @host-calls))
     (done! c w))))

(deftest the-mark-is-structured
  (checked
   (let [w (vworld)
         res (promise)
         _ (binding [v2/*world* w]
             (task-with {:fork-local true}
                        (let [a (task 1)
                              b (v2/with-scope (task 2))
                              comp-task (promise)
                              cr (v2/spin (deliver comp-task (task 3)) 0)]
                          (await cr)
                          (deliver res [a b @comp-task])
                          (await (v2/deferred)))))
         [a b ct] (deref res 1000 ::timeout)]
     (is (true? (v2/fork-local? a)) "a child of a fork-local run")
     (is (true? (v2/fork-local? b)) "a child inside its explicit scope")
     (is (false? (v2/fork-local? ct)) "a task of a computation it created is not")
     (is (false? (v2/fork-local? (binding [v2/*world* w] (task 1)))))
     (testing "the option in a computation body is refused"
       (is (= :fork-local
              (:spindel/invalid
               (binding [v2/*world* w]
                 (v2/value (v2/spin (try (task-with {:fork-local true} 1) nil
                                         (catch clojure.lang.ExceptionInfo e (ex-data e))))
                           1000 ::timeout))))))
     (testing "unknown options are refused"
       (is (thrown? clojure.lang.ExceptionInfo (binding [v2/*world* w] (task-with {:nope 1} 1)))))
     (done! w))))

(deftest refusals
  (checked
   (let [w (vworld)]
     (testing "(fork) in a fork-local run"
       (is (= :fork-local
              (binding [v2/*world* w]
                (v2/value (task-with {:fork-local true}
                                     (try (v2/fork) nil
                                          (catch clojure.lang.ExceptionInfo e (:spindel/invalid (ex-data e)))))
                          1000 ::timeout)))))
     (testing "detach of an unmarked task into a fork-local scope"
       (let [scope (promise) inner (promise) d (binding [v2/*world* w] (v2/deferred))]
         (binding [v2/*world* w]
           (task-with {:fork-local true}
                      (let [s (v2/open-scope!)] (deliver scope s) (await d) (v2/close-scope-fx! s))))
         (binding [v2/*world* w]
           (task (deliver inner (task (await d))) (await d)))
         (let [k (deref inner 1000 ::timeout)]
           (v2/detach! k (deref scope 1000 ::timeout))
           (settle)
           (is (some #(and (= :detach (first (:item %))) (false? (:accepted %))) (verify/log w)) "refused")
           (is (false? (v2/fork-local? k)) "it stays unmarked"))
         (v2/deliver! d 1)))
     (testing "a local task detached to the root keeps its mark and is retired in a later fork"
       (let [log (atom []) inner (promise) d (binding [v2/*world* w] (v2/deferred))]
         (binding [v2/*world* w]
           (task-with {:fork-local true}
                      (deliver inner (task (try (await d) (finally (swap! log conj [:fin (wid)])))))
                      (await d)))
         (let [k (deref inner 1000 ::timeout)]
           (v2/detach! k (v2/root-scope w))
           (is (true? (v2/fork-local? k)))
           (let [c (v2/fork! w)]
             (v2/release-world! c)
             (is (true? (v2/await-complete c 3000 ::timeout)))
             (is (not-any? #(= [:fin (v2/world-id c)] %) @log))))
         (v2/deliver! d 1)))
     (done! w))))

(deftest savepoints-of-a-local-run
  (checked
   (let [w (vworld)
         pubs (atom [])
         _ (v2/install-handlers! w {:sp (fn [pub] (swap! pubs conj pub))})
         h (binding [v2/*world* w] (task-with {:fork-local true} (inc (v2/savepoint :sp 1))))]
     (settle)
     (let [pub (first @pubs)]
       (is (true? (:fork-local pub)))
       (is (= :fork-local (:spindel/invalid (try (v2/instantiate pub) nil
                                                 (catch clojure.lang.ExceptionInfo e (ex-data e))))))
       (is (= :fork-local (:spindel/invalid (try (v2/consume pub 1) nil
                                                 (catch clojure.lang.ExceptionInfo e (ex-data e))))))
       (v2/resume! pub 41)
       (is (= 42 (v2/value h 1000 ::timeout)) "in-place resume still works"))
     (done! w))))

(deftest forks-of-forks-and-instances
  (checked
   (testing "a fork entered, then forked: the grandchild retires what the child started"
     (let [log (atom [])
           w (vworld)
           d (binding [v2/*world* w] (v2/deferred))
           _ (binding [v2/*world* w] (ltask (try (await d) (finally (swap! log conj [:a (wid)])))))
           _ (settle)
           c (v2/fork! w)
           _ (binding [v2/*world* c] (ltask (try (await (v2/in-world c d)) (finally (swap! log conj [:b (wid)])))))
           _ (settle)
           gc (v2/fork! c)]
       (v2/release-world! gc)
       (is (true? (v2/await-complete gc 3000 ::timeout)))
       (is (not-any? #(in-child? gc %) @log) "NEGATIVE")
       (v2/deliver! (v2/in-world c d) 1)
       (v2/deliver! d 1)
       (settle)
       (is (= #{[:a (v2/world-id w)] [:b (v2/world-id c)]} (set @log)))
       (done! c w)))
   (testing "an instance of an unmarked publication retires a local sibling"
     (let [log (atom [])
           w (vworld)
           pubs (atom [])
           _ (v2/install-handlers! w {:sp (fn [pub] (swap! pubs conj pub))})
           d (binding [v2/*world* w] (v2/deferred))
           _ (binding [v2/*world* w] (ltask (try (await d) (finally (swap! log conj [:sib (wid)])))))
           _ (settle)
           h (binding [v2/*world* w] (task (inc (v2/savepoint :sp 1))))
           _ (settle)
           pub (first @pubs)
           inst (v2/instantiate pub)]
       (v2/activate! inst 10)
       (is (= 11 (v2/value (v2/in-world inst h) 1000 ::timeout)))
       (v2/release-world! inst)
       (is (true? (v2/await-complete inst 3000 ::timeout)))
       (is (not-any? #(in-child? inst %) @log) "NEGATIVE: the sibling is retired in the instance")
       (v2/resume! pub 1)
       (v2/deliver! d 1)
       (done! w)))))

(deftest sources-of-the-subtree-close-in-the-fork
  (checked
   (let [w (vworld)
         mb (promise)
         d (binding [v2/*world* w] (v2/deferred))
         _ (binding [v2/*world* w]
             (ltask (deliver mb (v2/mailbox)) (await d)))
         m (deref mb 1000 ::timeout)
         taker (binding [v2/*world* w]
                 (task (try (v2/take! m) (catch Throwable e (ex-data e)))))
         _ (settle)
         c (v2/fork! w)]
     (v2/swap-world! c assoc :x 1)
     (is (= {:spindel/closed true} (v2/value (v2/in-world c taker) 1000 ::timeout))
         "NEGATIVE: the subtree's mailbox closes in the child, its taker wakes")
     (is (= ::timeout (v2/value taker 50 ::timeout)) "the parent's taker still waits")
     (v2/post! m :x)
     (is (= :x (v2/value taker 1000 ::timeout)))
     (v2/deliver! d 1)
     (done! c w))))

(deftest a-never-entered-mergeable-fork-merges
  (checked
   (let [w (vworld)
         sig (binding [v2/*world* w] (v2/signal 0))
         d (binding [v2/*world* w] (v2/deferred))
         _ (binding [v2/*world* w] (ltask (await d)))
         _ (settle)
         c (v2/fork! w {:mergeable? true})]
     (v2/write! (v2/in-world c sig) 5)
     (v2/seal! c)
     (is (true? (v2/merge! w c)) "NEGATIVE: quiescent once its local run is retired")
     (v2/deliver! d 1)
     (done! w))))

(deftest census-after-retirement
  (checked
   (let [w (vworld)
         d (binding [v2/*world* w] (v2/deferred))
         hs (binding [v2/*world* w] (vec (for [_ (range 20)] (ltask (v2/with-scope (await d))))))]
     (settle)
     (dotimes [_ 50]
       (let [c (v2/fork! w)]
         (v2/swap-world! c assoc :x 1)
         (v2/release-world! c)
         (is (true? (v2/await-complete c 3000 ::timeout)))))
     (v2/deliver! d 1)
     (doseq [h hs] (is (true? (v2/await-joined h 1000 ::timeout))))
     (done! w))))

(deftest stress-forks-race-local-completions
  (checked
   (dotimes [i 100]
     (let [log (atom [])
           w (vworld)
           _ (binding [v2/*world* w]
               (ltask (try (v2/offload (fn [] (Thread/sleep (rand-int 3)) :x))
                           (v2/sleep (rand-int 3))
                           (finally (swap! log conj [:fin (wid)])))))
           _ (Thread/sleep (rand-int 4))
           c (v2/fork! w)]
       (when (even? i) (v2/swap-world! c assoc :x 1))
       (done! c w)
       (is (not-any? #(in-child? c %) @log) "NEGATIVE")))))

(defn- waiters [c h]
  (v2/host-call! c #(.size ^java.util.ArrayDeque
                     (aget ^objects (v2/row-of (v2/in-world c h)) org.replikativ.spindel.v2.rows/X-WAITERS))))

(deftest a-retired-consuming-waiter-leaves-the-fifo
  (checked
   (let [w (vworld)
         m (binding [v2/*world* w] (v2/mailbox))
         sem (binding [v2/*world* w] (v2/semaphore 1))
         d (binding [v2/*world* w] (v2/deferred))
         _ (binding [v2/*world* w] (task (v2/acquire! sem) (await d) (v2/sem-release! sem)))   ; holds the permit
         _ (settle)
         _ (binding [v2/*world* w] (ltask (v2/take! m)))
         _ (binding [v2/*world* w] (ltask (v2/acquire! sem)))
         _ (settle)
         c (v2/fork! w)]
     (v2/swap-world! c assoc :x 1)
     (is (zero? (waiters c m)) "NEGATIVE: the mailbox FIFO lets go of the retired taker")
     (is (zero? (waiters c sem)) "NEGATIVE: the semaphore FIFO lets go of the retired acquirer")
     (is (= 1 (waiters w m)) "the parent's taker still waits")
     (v2/post! m :x)
     (v2/deliver! d 1)
     (done! c w))))

(deftest a-collected-alias-in-an-untouched-fork-follows-retirement
  (checked
   (let [w (vworld)
         s (binding [v2/*world* w] (v2/signal 0))
         d (binding [v2/*world* w] (v2/deferred))
         _ (binding [v2/*world* w] (ltask (await d)))
         _ (settle)
         c (v2/fork! w)]
     ((fn [] (v2/in-world c s) nil))          ; an alias nobody keeps
     (loop [i 0]
       (when (and (< i 100) (empty? (verify/log c)))
         (System/gc) (Thread/sleep 20) (recur (inc i))))
     (is (seq (verify/log c)) "the alias was collected")
     (is (= [:retire-local] (:item (first (verify/log c))))
         "the fork's first item is its retirement, before the T19 bookkeeping")
     (v2/deliver! d 1)
     (done! c w))))
