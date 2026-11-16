(ns org.replikativ.spindel.v2.await-op-test
  "C1 W5/R3: `await-op` runs a partial-cps op as a resource whose
   acknowledgement waits for its start to return, its committed cancel hooks
   to return and its result (or a cancellation before it started)."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [task await await-op]]))

(defn- wait-until [f]
  (loop [n 0] (cond (f) true (> n 400) false :else (do (Thread/sleep 5) (recur (inc n))))))

(defmacro in-world [[w & opts] & body]
  `(let [~w (v2/world ~@opts)]
     (binding [v2/*world* ~w] ~@body)))

(deftest values-errors-and-a-throwing-start
  (in-world [w]
            (is (= 42 (v2/value (task (await-op (fn [res _] (future (res 42))))) 2000 ::timeout)))
            (is (thrown-with-msg? Exception #"nope"
                                  (v2/value (task (await-op (fn [_ rej] (rej (ex-info "nope" {}))))) 2000 ::timeout)))
            (is (thrown-with-msg? Exception #"start blew up"
                                  (v2/value (task (await-op (fn [_ _] (throw (ex-info "start blew up" {}))))) 2000 ::timeout)))
            (testing "the op sees the originating world and the run's bindings"
              (is (= [true 7] (v2/value (task (binding [*print-length* 7]
                                                (await-op (fn [res _] (res [(identical? w v2/*world*) *print-length*])))))
                                        2000 ::timeout))))
            (v2/release-world! w)
            (is (true? (v2/await-complete w 2000 ::timeout)))))

(deftest cancel-runs-the-hook-and-the-join-waits-for-the-op
  (in-world [w]
            (let [stop (promise) hooks (atom 0) started (promise) settled (promise)
                  t (task (await-op (fn [res _]
                                      (v2/on-cancel! (fn [] (swap! hooks inc) (deliver stop true)))
                                      (deliver started true)
                                      (future (deref stop 5000 nil) (Thread/sleep 50) (deliver settled true) (res :late)))))]
              (deref started 2000 nil)
              (v2/cancel-task! t)
              (is (thrown? Exception (v2/value t 2000 ::timeout)) "settlement is prompt")
              (v2/release-world! w)
              (is (true? (v2/await-complete w 2000 ::timeout)))
              (is (realized? settled) "complete only after the op settled")
              (is (= 1 @hooks)))))

(deftest cancel-before-start-never-starts
  ;; an executor that holds the op's start until released
  (let [held (java.util.concurrent.LinkedBlockingQueue.)
        ex (reify java.util.concurrent.Executor (execute [_ r] (.add held r)))
        starts (atom 0)
        w (v2/world {:executor ex})]
    (binding [v2/*world* w]
      (let [t (task (await-op (fn [res _] (swap! starts inc) (res :ran))))]
        (v2/cancel-task! t)
        (loop [] (when-let [r (.poll held)] (.run ^Runnable r) (recur)))
        (is (zero? @starts))
        (v2/release-world! w)
        (loop [n 0] (when (< n 20) (loop [] (when-let [r (.poll held)] (.run ^Runnable r) (recur))) (Thread/sleep 5) (recur (inc n))))
        (is (v2/complete? w))))))

(deftest a-hook-registered-after-cancellation-runs-at-once
  (in-world [w]
            (let [gate (promise) hooked (atom 0) in-start (promise)
                  t (task (await-op (fn [res _]
                                      (deliver in-start true)
                                      (deref gate 5000 nil)           ; cancelled meanwhile
                                      (v2/on-cancel! (fn [] (swap! hooked inc)))
                                      (res :done))))]
              (deref in-start 2000 nil)
              (v2/cancel-task! t)
              (deliver gate true)
              (is (wait-until #(= 1 @hooked)))
              (v2/release-world! w)
              (is (true? (v2/await-complete w 2000 ::timeout))))))

(deftest detach-waives-the-join
  (in-world [w]
            (let [started (promise) never (promise)
                  t (task (await-op (fn [_ _] (deliver started true) (future (deref never))) {:detach true}))]
              (deref started 2000 nil)
              (v2/cancel-task! t)
              (v2/release-world! w)
              (is (true? (v2/await-complete w 2000 ::timeout)) "the op is left running, unowned"))))

(deftest a-result-before-start-returns
  ;; the run resumes with the result; the join waits for the start to return
  (in-world [w]
            (let [returned (promise)
                  t (task (await-op (fn [res _] (res :early) (Thread/sleep 150) (deliver returned true))))]
              (is (= :early (v2/value t 2000 ::timeout)))
              (v2/release-world! w)
              (is (true? (v2/await-complete w 2000 ::timeout)))
              (is (realized? returned)))))

(deftest a-queued-hook-delays-the-acknowledgement
  (in-world [w]
            (let [hook-done (promise) started (promise) resolve (promise)
                  t (task (await-op (fn [res _]
                                      (deliver resolve res)
                                      (v2/on-cancel! (fn [] (Thread/sleep 150) (deliver hook-done true)))
                                      (deliver started true))))]
              (deref started 2000 nil)
              (v2/cancel-task! t)
              ((deref resolve) :after-cancel)                    ; the op settles at once
              (v2/release-world! w)
              (is (true? (v2/await-complete w 2000 ::timeout)))
              (is (realized? hook-done) "the hook had returned before the world completed"))))

;; ---------------------------------------------------------------------------
;; Code review findings (c1-review-sol.md)

(deftest a-fired-op-is-still-cancelled
  ;; finding 3: the op resolved during its start, which waits for its stop
  ;; hook; cancellation (here: release) must still run the hook
  (in-world [w]
            (let [stop (promise) hooks (atom 0)
                  t (task (await-op (fn [res _]
                                      (v2/on-cancel! (fn [] (swap! hooks inc) (deliver stop true)))
                                      (res :early)
                                      (deref stop 5000 nil))))]
              (is (= :early (v2/value t 2000 ::timeout)))
              (v2/release-world! w)
              (is (true? (v2/await-complete w 2000 ::timeout)))
              (is (= 1 @hooks)))))

(deftest after-gate-actions-wait-for-an-enclosing-gate
  ;; finding 6: an op started from a nested entry (world b inside world a's
  ;; item) must not run while a's gate is held
  (let [inline (reify java.util.concurrent.Executor (execute [_ r] (.run ^Runnable r)))
        a (v2/world) b (v2/world {:executor inline})
        under-a (promise)]
    (v2/host-call! a (fn []
                       (v2/host! b (fn [] (binding [v2/*world* b]
                                            (task (await-op (fn [res _]
                                                              (deliver under-a (.isHeldByCurrentThread
                                                                                ^java.util.concurrent.locks.ReentrantLock
                                                                                (aget ^objects a 2)))
                                                              (res :ok)))))))
                       nil))
    (is (false? (deref under-a 2000 ::timeout)))))
