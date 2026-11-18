(ns org.replikativ.spindel.v2.completion-test
  "C1 world completion (c1-cancellation-joins-design.md W1-W2, R1-R2): a
   world is complete when it is released, every run has retired (also runs
   whose host work ignores interruption) and every world it owns is complete
   or was collected."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task await track]]
            [org.replikativ.spindel.v2.verify :as verify]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.host :as hs]
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

(deftest idle-is-a-snapshot-not-completion
  (let [w (v2/world) stop (promise) started (promise)]
    (binding [v2/*world* w]
      (let [parked (task (await (v2/deferred)))]
        (is (wait-until #(v2/idle? w)) "a task parked on a deferred leaves the world idle")
        (let [t (task (v2/offload (stubborn stop started)))]
          (deref started 2000 nil)
          (is (not (v2/idle? w)) "an outstanding offload is not idle")
          (v2/cancel-task! t)
          (is (not (v2/idle? w)) "nor a cancelling one that ignores interruption")
          (deliver stop true)
          (is (wait-until #(v2/idle? w))))))
    (v2/release-world! w)
    (is (true? (v2/await-complete w 2000 ::timeout)))))

(deftest a-ready-await-in-a-cancellation-finalizer-is-refused-explicitly
  ;; review finding 4: never a silently dropped continuation
  (let [w (v2/world) seen (atom [])]
    (binding [v2/*world* w]
      (let [ready (v2/deferred) _ (v2/deliver! ready :r) started (promise)
            t (task (try (deliver started true) (await (v2/deferred))
                         (finally (swap! seen conj :entered)
                                  (try (await ready)
                                       (catch Exception e (swap! seen conj (:spindel/invalid (ex-data e)))))
                                  (swap! seen conj :rest))))]
        (deref started 2000 nil)
        (v2/cancel-task! t)
        (is (wait-until #(= [:entered :finalizer :rest] @seen)))))
    (v2/release-world! w)))

(deftest a-child-callback-may-wait-for-its-owner
  ;; review finding 5: the owner's acknowledgement precedes the child's
  ;; subscribers
  (let [w (v2/world) result (promise)]
    (binding [v2/*world* w] (v2/signal 0))
    (let [child (v2/fork! w)]
      (v2/on-complete child #(future (deliver result (v2/await-complete w 2000 ::timeout))))
      (v2/release-world! w)
      (is (true? (deref result 3000 ::slow))))))

(deftest a-child-completed-before-its-acceptance-is-acknowledged
  ;; review finding 2: ownership by another world queued behind its busy gate
  (let [src (v2/world) _ (binding [v2/*world* src] (v2/signal 0))
        owner (v2/fork! src) hold (promise) holding (promise)]
    (future (v2/host-call! owner (fn [] (deliver holding true) (deref hold 5000 nil) nil)))
    (deref holding 2000 nil)
    (let [child (v2/fork! src {:owner owner})]
      (v2/release-world! child)
      (is (true? (v2/await-complete child 2000 ::timeout)))
      (deliver hold true)
      (Thread/sleep 50)
      (v2/release-world! owner)
      (is (true? (v2/await-complete owner 2000 ::timeout))))))

(deftest a-cleanup-slice-after-release-adds-no-root
  ;; ansatz C1 stage B: a finalizer running after T21 may write, deliver,
  ;; post, release and close (Z#40), but an observe, pin or host wait from
  ;; there would be a new root, and the computation it demands could start
  ;; after the world completed
  (checked
   (let [w (vworld) seen (atom []) runs (atom 0)]
     (binding [v2/*world* w]
       (let [s (v2/signal 0)
             c2 (spin (swap! runs inc) (* 10 (iv/get-new (track s))))
             attempt (fn [label f] (try (f) [label :accepted]
                                        (catch Exception e [label (if (:spindel/released (ex-data e)) :released e)])))
             c (spin (try (await (v2/deferred))
                          (finally
                            (swap! seen conj (attempt :observe #(v2/observe! c2 (fn [_ _]))))
                            (swap! seen conj (attempt :pin #(v2/pin! c2)))
                            (v2/value-async c2 (fn [v err?] (swap! seen conj [:value-async (if err? (:spindel/released (ex-data v)) v)])))
                            (swap! seen conj (attempt :write #(v2/write! s 5))))))
             _ (v2/observe! c (fn [_ _]))]
         (v2/value (v2/signal 0) 200 nil)
         (v2/release-world! w)
         (is (true? (v2/await-complete w 2000 ::timeout)))
         (is (wait-until #(= 4 (count @seen))))
         (is (= #{[:observe :released] [:pin :released] [:value-async true] [:write :accepted]} (set @seen)))
         (is (zero? @runs) "the computation never ran"))))))

(deftest a-root-queued-before-release-is-revoked-not-thrown
  ;; Z#68: an observe or pin admitted before T21 but processed after it, in a
  ;; turn another thread drains, is revoked as T21 revokes roots (callback
  ;; ::released, pin dropped); the refusal never reaches the draining thread
  ;; (foerster SMC: release-world! threw an observer's refusal)
  (doseq [op [:observe :pin]]
    (checked
     (let [w (vworld)
           s (binding [v2/*world* w] (v2/signal 1))
           lk (aget ^objects w rw/W-LOCK)
           got (promise)]
       (hs/lock! lk)
       (let [queued (future (case op
                              :observe (v2/observe! s (fn [v err?] (deliver got [(:spindel/released (ex-data v)) err?])))
                              :pin (v2/pin! s)))]
         (is (wait-until #(not (hs/mpsc-empty? (aget ^objects w rw/W-INGRESS)))) "admitted and queued behind the gate")
         (#'v2/release-world* w)                  ; T21 first, under the held gate
         (hs/unlock! lk)
         (deref queued 2000 ::timeout)
         (is (nil? (try (#'v2/process! w) nil (catch Throwable t t))) (str op ": the drainer gets no refusal"))
         (when (= op :observe)
           (is (= [true true] (deref got 2000 ::timeout)) "the observer receives ::released"))
         (is (not-any? #(#{:observe :pin} (first (:item %))) (verify/log w)) "no root item")
         (is (true? (v2/await-complete w 2000 ::timeout))))))))
