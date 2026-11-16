(ns org.replikativ.spindel.v2.completion-test
  "C1 world completion (c1-cancellation-joins-design.md W1-W2, R1-R2): a
   world is complete when it is released, every run has retired (also runs
   whose host work ignores interruption) and every world it owns is complete
   or was collected."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task await track]]
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
  (loop [n 0] (cond (f) true (> n 400) false :else (do (Thread/sleep 5) (recur (inc n))))))

(defn- stubborn
  "Host work that ignores interruption until `stop` is delivered."
  [stop started]
  (fn []
    (deliver started true)
    (loop [] (when-not (realized? stop) (try (Thread/sleep 5) (catch InterruptedException _)) (recur)))
    :stopped))

(deftest an-idle-world-completes-at-release
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (is (= 3 (v2/value (task (+ 1 2)) 2000 ::timeout))))
     (is (not (v2/complete? w)))
     (v2/release-world! w)
     (is (true? (v2/await-complete w 2000 ::timeout)))
     (is (v2/complete? w)))))

(deftest completion-waits-for-host-work-that-ignores-interruption
  (checked
   (let [w (vworld) stop (promise) started (promise)]
     (binding [v2/*world* w]
       (let [t (task (v2/offload (stubborn stop started)))]
         (deref started 2000 nil)
         (v2/release-world! w)
         (is (thrown? Exception (v2/value t 2000 ::timeout)) "settlement is prompt (::released)")
         (is (= ::timeout (v2/await-complete w 100 ::timeout)) "the offload still runs")
         (deliver stop true)
         (is (true? (v2/await-complete w 2000 ::timeout)) "complete once it has returned"))))))

(deftest a-root-computation-in-cleanup-keeps-the-world-incomplete
  ;; its run is not under the root scope's tasks (review 4A)
  (checked
   (let [w (vworld) stop (promise) started (promise)]
     (binding [v2/*world* w]
       (let [c (spin (v2/offload (stubborn stop started)))
             u (v2/observe! c (fn [_ _]))]
         (deref started 2000 nil)
         (v2/release-world! w)
         (is (= ::timeout (v2/await-complete w 100 ::timeout)))
         (deliver stop true)
         (is (true? (v2/await-complete w 2000 ::timeout))))))))

(deftest an-owner-completes-after-its-forks
  (checked
   (let [w (vworld) stop (promise) started (promise)]
     (binding [v2/*world* w]
       (let [s (v2/signal 0)
             child (v2/fork! w)]
         (binding [v2/*world* child] (task (v2/offload (stubborn stop started))))
         (deref started 2000 nil)
         (v2/release-world! w)           ; F2: releases the child (root-owned, weakly)
         (is (= ::timeout (v2/await-complete w 100 ::timeout)) "the child's offload still runs")
         (is (not (v2/complete? child)))
         (deliver stop true)
         (is (true? (v2/await-complete child 2000 ::timeout)))
         (is (true? (v2/await-complete w 2000 ::timeout)) "then the owner"))))))

(deftest a-fork-effect-child-is-an-obligation-of-its-owner
  (checked
   (let [w (vworld) stop (promise) started (promise) kid (promise)]
     (binding [v2/*world* w]
       (let [gate (v2/deferred)
             t (task (let [[side child] (v2/fork)]
                       (if (= side :child)
                         (v2/offload (stubborn stop started))
                         (do (deliver kid child) (await gate) :parent))))]
         (deref kid 2000 nil)
         (deref started 2000 nil)
         (v2/deliver! gate :go)
         (is (= :parent (v2/value t 2000 ::timeout)))   ; its run scope closes: the child is released
         (v2/release-world! w)
         (is (= ::timeout (v2/await-complete w 100 ::timeout)))
         (deliver stop true)
         (is (true? (v2/await-complete w 2000 ::timeout))))))))

(defn- stuck-fork!
  "A host fork with a run parked on a deferred nobody else can deliver (as in
   lifecycle-test)."
  [w]
  (let [c (v2/fork! w)
        d (v2/deferred c)]
    (binding [v2/*world* c] (task (await d)))
    c))

(deftest a-collected-child-ends-its-obligation
  ;; a weakly held host fork dropped by the host is collected without being
  ;; released (Z#58): that ends its owner's obligation (R2)
  (let [w (v2/world)
        probe (java.lang.ref.WeakReference. (stuck-fork! w))]
    ;; no local may hold the referent while collecting (an `and` on `.get` would)
    (is (loop [n 0] (cond (nil? (.get probe)) true (> n 40) false
                          :else (do (System/gc) (Thread/sleep 25) (recur (inc n)))))
        "the dropped stuck host fork is collected")
    (Thread/sleep 50)
    (v2/release-world! w)
    (is (true? (v2/await-complete w 2000 ::timeout)))))

(deftest an-unborn-instance-discarded-is-complete
  (let [w (v2/world) pubs (atom {})]
    (v2/install-handlers! w {:default (fn [p] (swap! pubs assoc (:payload p) p))})
    (binding [v2/*world* w]
      (task (v2/savepoint :choose :b))
      (is (wait-until #(get @pubs :b)))
      (let [i (v2/instantiate (get @pubs :b))]
        (v2/discard! i)
        (is (true? (v2/await-complete i 2000 ::timeout)) "nothing in it ever ran")
        (v2/abandon! (get @pubs :b))))
    (v2/release-world! w)
    (is (true? (v2/await-complete w 2000 ::timeout)))))

(deftest a-fork-discharges-an-inherited-cancelling-resource
  ;; R1: the parent's cancelled offload acknowledges only in the parent; the
  ;; child has no counterpart and must not wait for it
  (checked
   (let [w (vworld) stop (promise) started (promise)]
     (binding [v2/*world* w]
       (let [t (task (v2/offload (stubborn stop started)))]
         (deref started 2000 nil)
         (v2/cancel-task! t)               ; cancelling: waits for the physical return
         (let [child (v2/fork! w)]
           (v2/release-world! child)
           (is (true? (v2/await-complete child 2000 ::timeout)) "discharged in the child")
           (v2/release-world! w)
           (is (= ::timeout (v2/await-complete w 100 ::timeout)) "the parent still waits")
           (deliver stop true)
           (is (true? (v2/await-complete w 2000 ::timeout)))))))))

(deftest subscriptions
  (let [w (v2/world) calls (atom [])]
    (let [withdraw (v2/on-complete w #(swap! calls conj :withdrawn))]
      (v2/on-complete w #(swap! calls conj :a))
      (withdraw)
      (v2/release-world! w)
      (is (true? (v2/await-complete w 2000 ::timeout)))
      (is (wait-until #(= [:a] @calls)) "a withdrawn subscription never runs")
      (v2/on-complete w #(swap! calls conj :late))
      (is (wait-until #(= [:a :late] @calls)) "a subscription after completion runs at once"))))

(deftest a-fork-starts-with-its-own-ledger
  (checked
   (let [w (vworld) calls (atom 0)]
     (binding [v2/*world* w]
       (v2/on-complete w #(swap! calls inc))
       (v2/signal 0)
       (let [child (v2/fork! w)]
         (v2/release-world! child)
         (is (true? (v2/await-complete child 2000 ::timeout)))
         (Thread/sleep 50)
         (is (zero? @calls) "the parent's subscription is not inherited")
         (is (not (v2/complete? w)))
         (v2/release-world! w)
         (is (true? (v2/await-complete w 2000 ::timeout)))
         (is (wait-until #(= 1 @calls))))))))

(deftest cancellation-reaches-explicit-subscopes-at-once
  ;; R4: the parent's host work waits for a task inside its explicit scope to
  ;; stop; before, that task was cancelled only at the parent's retirement,
  ;; which waits for the host work (a cycle)
  (checked
   (let [w (vworld) child-done (promise) waiting (promise)]
     (binding [v2/*world* w]
       (let [t (task (v2/with-scope
                       (task (try (await (v2/deferred)) (finally (deliver child-done :stopped))))
                       (v2/offload (fn [] (deliver waiting true) (deref child-done 3000 :late)))))]
         (deref waiting 2000 nil)
         (v2/cancel-task! t)
         (is (= :stopped (deref child-done 1000 ::slow)) "the scoped child is cancelled with the request")
         (v2/release-world! w)
         (is (true? (v2/await-complete w 2000 ::timeout))))))))

(deftest finalizers-are-synchronous
  ;; W4: a suspending effect in a finally clause fails, on normal and on
  ;; cancellation entry; a settled await does not suspend and is allowed
  (checked
   (let [w (vworld) seen (atom [])]
     (binding [v2/*world* w]
       (let [d (v2/deferred)
             done (v2/deferred)
             _ (v2/deliver! done :ready)
             t1 (task (try :body
                           (finally (swap! seen conj [:settled (await done)])
                                    (try (await d)
                                         (catch Exception e (swap! seen conj [:normal (:spindel/invalid (ex-data e))]))))))
             _ (is (= :body (v2/value t1 2000 ::timeout)))
             started (promise)
             t2 (task (try (deliver started true) (await d)
                           (finally (try (v2/sleep 10)
                                         (catch Exception e (swap! seen conj [:cancel (:spindel/invalid (ex-data e))]))))))]
         (deref started 2000 nil)
         (v2/cancel-task! t2)
         (is (wait-until #(= 3 (count @seen))))
         (is (= #{[:settled :ready] [:normal :finalizer] [:cancel :finalizer]} (set @seen)))
         ;; the depth is restored: the body after a finally may suspend again
         (let [t3 (task (try 1 (finally nil)) (v2/sleep 1) :after)]
           (is (= :after (v2/value t3 2000 ::timeout))))))
     (v2/release-world! w))))
