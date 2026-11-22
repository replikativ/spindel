(ns org.replikativ.spindel.v2.sci.budget-test
  "The hard budget abort of v2.sci (`:slice-budget-ms`, spec Z#80): a
   runaway activation fails its run with an ordinary error, its open finally
   regions close in the model's order, and no SCI code of the run runs
   afterwards. `busy` spins for 3 s, far past the 100 ms budget, so without
   the abort each run would complete normally."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.sci :as v2sci]
            [org.replikativ.spindel.v2.sci.support :as s :refer [checked ev v outcome]]
            [org.replikativ.spindel.v2.verify :as verify]
            [sci.core :as sci]))

(def ^:private budget-ms 100)

(defn- interpreter
  "An interpreter with the budget on; abandonment reports go to `reports`."
  [reports bindings]
  (let [p (s/interpreter {:interrupt-fn v2sci/check-budget!
                          :bindings bindings
                          :namespaces {'host {'now (fn [] (System/currentTimeMillis))}}}
                         {:slice-budget-ms budget-ms
                          :on-abandon (fn [r] (swap! reports conj r))})]
    (sci/eval-string* p "(defn busy [] (let [end (+ (host/now) 3000)] (loop [] (when (< (host/now) end) (recur))) :done))")
    p))

(defn- budget-error? [[tag data]]
  (and (= :failed tag) (= ::v2sci/budget-exceeded (:type data)) (true? (:hard data))))

(defn- completes? [w]
  (v2/release-world! w)
  (true? (v2/await-complete w 5000 ::timeout)))

(defn- no-handoff-left? []
  (nil? (.get ^ThreadLocal @#'v2sci/handing-off)))

(deftest an-effect-free-loop-in-a-top-level-task-fails-the-run
  (checked
   (let [w (s/vworld)
         reports (atom [])
         p (interpreter reports {})
         t (ev w p "(task (busy))")]
     (is (budget-error? (outcome t)))
     (is (completes? w) "the run retired")
     (is (s/wait-until #(= 1 (count @reports))))
     (is (= {:regions 0 :budget-ms budget-ms} (select-keys (first @reports) [:regions :budget-ms])))
     (is (identical? w (:world (first @reports)))))))

(deftest a-loop-inside-try-finally-across-an-effect
  (checked
   (let [w (s/vworld)
         d (binding [v2/*world* w] (v2/deferred))
         reports (atom [])
         p (interpreter reports {'d d})
         t (ev w p "(def fin (atom 0)) (task (try (await d) (busy) (finally (swap! fin inc))))")]
     (v2/deliver! d :go)
     (is (budget-error? (outcome t)))
     (is (no-handoff-left?))
     (is (s/wait-until #(= 1 (count @reports))))
     (is (= 1 (:regions (first @reports))) "the open region was closed for the run")
     (is (= 0 (sci/eval-string* p "@fin")) "its finalizer was skipped (the B3 exception)")
     (is (completes? w)))))

(deftest a-running-clause-with-an-open-inner-region-closes-in-order
  ;; the outer finally clause runs and opens an inner region (its `try` has
  ;; a non-suspending await, so it is CPS-lowered: no native finally); the
  ;; abort leaves both. The legal order is inner exit, inner leave, outer
  ;; leave; counts would emit a leave first, which the model refuses
  (checked
   (let [w (s/vworld)
         d (binding [v2/*world* w] (v2/deferred))
         reports (atom [])
         p (interpreter reports {'d d})
         t (ev w p "(def log (atom []))
                    (def done (task :ok))
                    (task (try (await d)
                               (finally (try (await done) (busy)
                                             (finally (swap! log conj :inner))))))")]
     (v2/deliver! d :go)
     (is (budget-error? (outcome t)))
     (is (s/wait-until #(= 1 (count @reports))))
     (let [rid (:run-id (first @reports))
           events (->> (verify/log w)
                       (map :item)
                       (filter #(and (#{:finally-enter :finally-exit :finally-leave} (first %)) (= rid (second %))))
                       (mapv first))]
       (is (= 2 (:regions (first @reports))))
       (is (= [:finally-enter :finally-exit :finally-enter :finally-exit :finally-leave :finally-leave] events)))
     (is (= [] (sci/eval-string* p "@log")))
     (is (completes? w)))))

(deftest a-creditor-catches-an-ordinary-error
  (checked
   (let [w (s/vworld)
         d (binding [v2/*world* w] (v2/deferred))
         p (interpreter (atom []) {'d d})
         a (ev w p "(def fin (atom 0)) (def a (task (await d) (busy))) a")
         b (ev w p "(task (try (await a)
                               (catch Exception e [:caught (:type (ex-data e)) (:hard (ex-data e)) (ex-cause e)])
                               (finally (swap! fin inc))))")]
     (v2/deliver! d :go)
     (is (= [:caught ::v2sci/budget-exceeded true nil] (v b)))
     (is (= 1 (sci/eval-string* p "@fin")) "the creditor's finalizer ran")
     (let [e (try (v2/value a 2000 ::timeout) (catch Exception e e))]
       (is (instance? clojure.lang.ExceptionInfo e))
       (is (not-any? #(contains? (ex-data %) :sci.impl/interrupt) (take-while some? (iterate ex-cause e)))
           "no SCI interrupt marker in the published error's cause chain"))
     (is (completes? w)))))

(deftest an-abort-in-a-cancellation-cleanup-stays-cancelled
  (checked
   (let [w (s/vworld)
         d (binding [v2/*world* w] (v2/deferred))
         reports (atom [])
         p (interpreter reports {'d d})
         t (ev w p "(def fin (atom [])) (task (try (await d) (finally (swap! fin conj :start) (busy) (swap! fin conj :end))))")]
     (v2/cancel-task! t)
     (is (v2/cancelled? (try (v2/value t 2000 ::timeout) (catch Exception e e))))
     (is (= [:start] (sci/eval-string* p "@fin")) "the cleanup was cut short")
     (is (s/wait-until #(= 1 (count @reports))))
     (is (= 0 (:regions (first @reports)))
         "the clause has no effect, so its leave is a native SCI finally, which SCI ran")
     (is (completes? w)))))

(deftest a-computation-stores-the-error-for-its-epoch
  (checked
   (let [w (s/vworld)
         p (interpreter (atom []) {})
         c (ev w p "(def runs (atom 0)) (spin (swap! runs inc) (busy))")]
     (is (budget-error? (outcome c)))
     (is (budget-error? (outcome c)) "a second read gets the same result")
     (is (= 1 (sci/eval-string* p "@runs")) "the body ran once")
     (is (completes? w)))))

(deftest a-nested-activation-has-its-own-clock
  ;; the task demands the computation on its stack (I10): the computation is
  ;; aborted, the task's clock stood still meanwhile, so its catch runs
  (checked
   (let [w (s/vworld)
         p (interpreter (atom []) {})
         t (ev w p "(def c (spin (busy))) (task (try (await c) (catch Exception e [:caught (:type (ex-data e))])))")]
     (is (= [:caught ::v2sci/budget-exceeded] (v t)))
     (is (completes? w)))))

(deftest two-savepoint-instances-keep-their-own-abort
  (checked
   (let [w (s/vworld)
         pubs (atom [])
         _ (v2/install-handlers! w {:choose (fn [p] (swap! pubs conj p))})
         reports (atom [])
         p (interpreter reports {})
         t (ev w p "(task (let [x (savepoint :choose nil)] (if (= x 1) (busy) [:done x])))")]
     (is (s/wait-until #(seq @pubs)))
     (let [pub (first @pubs)
           [i1 i2] (mapv (fn [x] (let [iw (v2/instantiate pub)] (v2/activate! iw x) iw)) [1 2])]
       (is (budget-error? (outcome (v2/in-world i1 t))))
       (is (= [:done 2] (v (v2/in-world i2 t))))
       (is (s/wait-until #(= 1 (count @reports))))
       (is (identical? i1 (:world (first @reports))))
       (v2/abandon! pub)
       (is (completes? i1))
       (is (completes? i2)))
     (is (completes? w)))))

(deftest no-sci-code-runs-after-the-abort
  (testing "a resumed continuation: the engine routes the failure to the error continuation"
    (checked
     (let [w (s/vworld)
           d (binding [v2/*world* w] (v2/deferred))
           p (interpreter (atom []) {'d d})
           t (ev w p "(def caught (atom 0))
                      (task (try (await d) (busy)
                                 (catch java.lang.Throwable e (swap! caught inc) :caught)))")]
       (v2/deliver! d :go)
       (is (budget-error? (outcome t)))
       (is (= 0 (sci/eval-string* p "@caught")) "the body's catch never saw it")
       (is (no-handoff-left?))
       (is (completes? w)))))
  (testing "a continuation resumed on the same stack (an await of a settled task)"
    (checked
     (let [w (s/vworld)
           p (interpreter (atom []) {})
           t (ev w p "(def caught (atom 0))
                      (def done (task :ok))
                      (task (try (let [x (await done)] (busy) x)
                                 (catch java.lang.Throwable e (swap! caught inc) :caught)))")]
       (is (budget-error? (outcome t)))
       (is (= 0 (sci/eval-string* p "@caught")))
       (is (no-handoff-left?))
       (is (completes? w))))))
