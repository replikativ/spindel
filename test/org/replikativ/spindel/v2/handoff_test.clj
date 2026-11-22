(ns org.replikativ.spindel.v2.handoff-test
  "H2 handoff: work already accepted makes progress when the world's
   executor refuses the drainer (Z#79)."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is]]
            [org.replikativ.spindel.v2.core :as v2 :refer [task await]]
            [org.replikativ.spindel.v2.host :as hs]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.verify :as verify]))

(def ^:dynamic *divergences* nil)

(defn- vworld
  ([] (vworld {}))
  ([opts]
   (v2/world (merge {:verify? true :hook (verify/checking-hook *divergences*)} opts))))

(defmacro ^:private checked [& body]
  `(binding [*divergences* (atom [])]
     ~@body
     (is (empty? @*divergences*) (str "Rule R divergences: " (vec (take 3 @*divergences*))))))

(defn- scheduled? [w] (.get ^java.util.concurrent.atomic.AtomicBoolean (aget ^objects w rw/W-SCHEDULED)))

(defn- rejecting-executor
  "Rejects the first `n` submissions (all with `n` nil), then runs on the
   default executor."
  [n]
  (let [left (atom (or n Long/MAX_VALUE))]
    (reify java.util.concurrent.Executor
      (execute [_ r]
        (if (neg? (swap! left dec))
          (.execute ^java.util.concurrent.Executor @hs/default-executor r)
          (throw (java.util.concurrent.RejectedExecutionException. "rejected")))))))

(deftest concurrent-enqueue-with-a-rejected-handoff
  (checked
   (let [w (vworld {:executor (rejecting-executor 1) :inline? false})
         s (binding [v2/*world* w] (v2/signal 0))
         start (promise)
         callers (mapv (fn [_] (future @start (dotimes [_ 50] (swap! s inc)) :done)) (range 4))]
     (deliver start true)
     (is (= [:done :done :done :done] (mapv #(deref % 10000 ::stuck) callers)) "no caller is stranded")
     (is (= 200 (v2/value s 2000 ::timeout)))
     (is (not (scheduled? w)) "no drainer is left marked scheduled")
     (v2/release-world! w)
     (is (true? (v2/await-complete w 5000 ::timeout))))))

(deftest permanent-rejection-still-drains
  (checked
   (let [w (vworld {:executor (rejecting-executor nil) :inline? false})
         [d s] (binding [v2/*world* w] [(v2/deferred) (v2/signal 0)])
         t (binding [v2/*world* w] (task (* 2 (await d))))]
     (is (= :sent (deref (future (v2/deliver! d 21) :sent) 2000 ::stuck)) "the caller gets no rejection")
     (is (= 42 (v2/value t 2000 ::timeout)))
     (is (= 3 (deref (future (swap! s + 3)) 2000 ::stuck)))
     (v2/release-world! w)
     (is (true? (v2/await-complete w 5000 ::timeout))))))

(deftest a-rejection-during-run-after-skips-no-handoff
  ;; two worlds receive items from inside a third world's gate (send-world!);
  ;; their handoffs run after that gate is left, the first one rejected
  (checked
   (let [p (vworld)
         c1 (vworld {:executor (rejecting-executor nil) :inline? false})
         c2 (vworld {:inline? false})
         got (atom #{})]
     (is (nil? (v2/host-call! p (fn [] (v2/send-world! c1 #(swap! got conj :c1))
                                  (v2/send-world! c2 #(swap! got conj :c2))
                                  nil)))
         "the caller sees no rejection")
     (is (true? (loop [n 0] (cond (= #{:c1 :c2} @got) true (> n 400) false :else (do (Thread/sleep 5) (recur (inc n)))))))
     (doseq [x [p c1 c2]] (v2/release-world! x))
     (doseq [x [p c1 c2]] (is (true? (v2/await-complete x 5000 ::timeout)))))))

(deftest an-executor-that-ran-the-drainer-and-then-threw
  ;; the executor runs the drainer in the caller, then throws. Meanwhile
  ;; another item was sent and its handoff (a later claim) is held by the
  ;; executor: the failed submission must not clear that claim
  (checked
   (let [log (atom [])
         held (atom nil)
         calls (atom 0)
         w-cell (promise)
         ex (reify java.util.concurrent.Executor
              (execute [_ r]
                (case (long (swap! calls inc))
                  1 (do (.run ^Runnable r)
                        (v2/send-world! @w-cell #(swap! log conj :second))
                        (throw (java.util.concurrent.RejectedExecutionException. "ran, then threw")))
                  2 (reset! held r)
                  (.execute ^java.util.concurrent.Executor @hs/default-executor r))))
         w (vworld {:executor ex :inline? false})]
     (deliver w-cell w)
     (is (= :first (v2/host-call! w (fn [] (swap! log conj :first) :first))))
     (Thread/sleep 50)
     (is (= [:first] @log) "the second item waits for its own drainer")
     (is (scheduled? w) "its claim survives the first submission's failure")
     (.run ^Runnable @held)
     (is (= [:first :second] @log))
     (is (not (scheduled? w)))
     (is (= :third (v2/host-call! w (fn [] :third))) "the world stays live")
     (v2/release-world! w)
     (is (true? (v2/await-complete w 5000 ::timeout))))))
