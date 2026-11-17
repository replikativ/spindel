(ns org.replikativ.spindel.v2.owned-test
  "C1c stage B (spec Z#72): a fork made by the `(fork)` effect is counted on the
   forking run's scope (W-OWNED-N) until it completes or is collected; the
   count keeps the scope, so the task joins only after its forks. A fork,
   savepoint basis or instance inherits the parent's counts as W-NORMALIZE and
   drains them at its first turn (activation). A world completes only with no
   count and nothing to normalize."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [task await]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.host :as hs]
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

(defn- under-gate
  "`(f)` holding `w`'s gate without a turn (a host item would be a fork's first
   turn and drain it)."
  [^objects w f]
  (let [lk (aget w rw/W-LOCK)]
    (hs/lock! lk)
    (try (f) (finally (hs/unlock! lk) (#'v2/handoff! w)))))

(defn- counts [^objects w]
  (under-gate w (fn [] {:owned (into {} (map (fn [[sid [_ n]]] [sid n])) (aget w rw/W-OWNED-N))
                        :normalize (set (keys (aget w rw/W-NORMALIZE)))})))

(defn- items [w] (mapv :item (verify/log w)))

(defn- eventually [f]
  (loop [n 0] (cond (f) true (> n 200) false :else (do (Thread/sleep 10) (recur (inc n))))))

(defmacro ^:private forking-task
  "A task whose `(fork)` child runs `child-body`; the parent hands the child to
   `kid` as `(wrap child)`, awaits `pgate` and returns :parent."
  [kid wrap pgate child-body]
  `(task (let [[side# child#] (v2/fork)]
           (if (= side# :child)
             ~child-body
             (do (deliver ~kid (~wrap child#)) (await ~pgate) :parent)))))

(deftest a-counted-fork-keeps-its-owner-scope
  (checked
   (let [w (vworld) kid (promise) stop (promise) started (promise)]
     (binding [v2/*world* w]
       (let [pgate (v2/deferred)
             t (forking-task kid identity pgate (v2/offload (stubborn stop started)))
             child (deref kid 2000 nil)
             joined (promise)]
         (is (deref started 2000 false))
         (is (= 1 (count (:owned (counts w)))) "counted on the run's scope")
         (is (empty? (:normalize (counts child))) "the child does not inherit its own count")
         (v2/on-joined t #(deliver joined true))
         (v2/deliver! pgate :go)
         (is (= :parent (v2/value t 2000 ::timeout)))
         (Thread/sleep 50)
         (is (not (realized? joined)) "the task returned, but its fork still runs: not complete")
         (is (= 1 (count (:owned (counts w)))))
         (deliver stop true)
         (is (true? (deref joined 2000 ::timeout)) "the fork completed: [:owned-done], the task joins")
         (is (= {:owned {} :normalize #{}} (counts w)))
         (is (= 1 (count (filter #(= :owned-done (first %)) (items w)))))
         (v2/release-world! w)
         (is (true? (v2/await-complete w 2000 ::timeout))))))))

(deftest a-collected-counted-fork-ends-its-count
  ;; the child parks on an external operation that ignores cancellation and
  ;; whose complete! is dropped: once released, nothing holds it, it is
  ;; collected (C1 R2) and its owner runs [:owned-done]
  (checked
   (let [w (vworld) kid (promise) parked (promise)]
     (binding [v2/*world* w]
       (let [pgate (v2/deferred)
             t (forking-task kid (fn [c] (java.lang.ref.WeakReference. c)) pgate
                             (v2/external (fn [_complete!] (deliver parked true) nil)))
             ^java.lang.ref.WeakReference probe (deref kid 2000 nil)
             joined (promise)]
         (is (deref parked 2000 false))
         (v2/on-joined t #(deliver joined true))
         (v2/deliver! pgate :go)
         (is (= :parent (v2/value t 2000 ::timeout)))
         (Thread/sleep 50)
         (is (not (realized? joined)) "the released fork cannot finish")
         (is (loop [n 0] (cond (nil? (.get probe)) true (> n 80) false
                               :else (do (System/gc) (Thread/sleep 25) (recur (inc n)))))
             "the stuck fork is collected")
         (is (true? (deref joined 2000 ::timeout)) "its collection ends the count")
         (is (= {:owned {} :normalize #{}} (counts w))))))))

(deftest a-host-fork-inherits-and-drains-counts
  (checked
   (let [w (vworld) kid (promise) stop (promise) started (promise)]
     (binding [v2/*world* w]
       (let [pgate (v2/deferred)
             t (forking-task kid identity pgate (v2/offload (stubborn stop started)))
             _ (deref kid 2000 nil)
             _ (deref started 2000 nil)
             _ (v2/deliver! pgate :go)
             _ (v2/value t 2000 ::timeout)
             [sid] (keys (:owned (counts w)))
             touched (v2/fork! w)
             untouched (v2/fork! w)]
         (is (some? sid) "the closed run scope is kept by the count")
         (is (= #{sid} (:normalize (counts touched)) (:normalize (counts untouched))) "inherited")
         (is (= {} (:owned (counts touched))) "the counts are the parent's, not the fork's")
         (testing "a host item first: the first turn drains"
           (v2/call-in! touched (fn [] nil))
           (is (= #{} (:normalize (counts touched))))
           (is (= [[:normalize]] (items touched)))
           (is (true? (v2/await-joined (v2/in-world touched t) 2000 ::timeout)) "the fork's copy of the task joins"))
         (testing "released before its first turn (Q15): the release, then the drain, then completion"
           (v2/release-world! untouched)
           (is (true? (v2/await-complete untouched 2000 ::timeout)))
           (is (= [[:release-world] [:normalize]] (items untouched))))
         (is (= #{sid} (set (keys (:owned (counts w))))) "the parent's own count is untouched")
         (deliver stop true)
         (is (eventually #(empty? (:owned (counts w)))))
         (v2/release-world! touched)
         (v2/release-world! w)
         (is (true? (v2/await-complete w 2000 ::timeout))))))))

(deftest completion-waits-for-owned-done
  ;; Q16: the owner is released and its child completes (W-KIDS reaches 0)
  ;; while the owner's last run holds the gate; the run retires and the release
  ;; runs before [:owned-done], which alone may complete the world
  (checked
   (let [w (vworld) kid (promise) go (promise) spinning (promise)]
     (binding [v2/*world* w]
       (let [pg (v2/deferred)
             _t (task (let [[side child] (v2/fork)]
                        (if (= side :child)
                          (await (v2/deferred))
                          (do (deliver kid child)
                              (await pg)
                              (deliver spinning true)
                              (loop [] (when-not (realized? go) (Thread/sleep 5) (recur)))
                              :parent))))
             child (deref kid 2000 nil)
             done (promise)]
         (future (v2/deliver! pg 1))
         (is (deref spinning 2000 false))
         (v2/on-complete w #(deliver done (counts w)))
         (v2/release-world! w)
         (v2/release-world! child)
         (is (true? (v2/await-complete child 2000 ::timeout)))
         (is (eventually #(zero? (hs/kids-count (aget ^objects w rw/W-KIDS)))) "W-KIDS is 0 before the retirement")
         (deliver go true)
         (is (true? (v2/await-complete w 2000 ::timeout)))
         (is (= {:owned {} :normalize #{}} (deref done 2000 ::timeout)) "complete only with no count")
         (is (= [:complete :release-world :owned-done]
                (take-last 3 (map first (items w))))
             "the retirement and the release ran before [:owned-done]"))))))

(deftest an-instance-drains-at-activation
  (checked
   (let [w (vworld) kid (promise) stop (promise) started (promise) pubs (atom {})]
     (v2/install-handlers! w {:default (fn [p] (swap! pubs assoc (:payload p) p))})
     (binding [v2/*world* w]
       (let [pgate (v2/deferred)
             t (forking-task kid identity pgate (v2/offload (stubborn stop started)))
             _ (deref kid 2000 nil)
             _ (deref started 2000 nil)
             _ (v2/deliver! pgate :go)
             _ (v2/value t 2000 ::timeout)
             [sid] (keys (:owned (counts w)))
             b (task (inc (v2/savepoint :choose :b)))
             _ (eventually #(get @pubs :b))
             p (get @pubs :b)
             i (v2/instantiate p)]
         (is (= #{sid} (:normalize (counts i))) "the basis, and so the instance, inherits the count")
         (v2/activate! i 1)
         (is (= 2 (binding [v2/*world* i] (v2/value (v2/in-world i b) 2000 ::timeout))))
         (is (= #{} (:normalize (counts i))))
         (is (some #{[:normalize]} (items i)))
         (is (true? (v2/await-joined (v2/in-world i t) 2000 ::timeout)))
         (deliver stop true)
         (v2/abandon! p)
         (v2/release-world! i)
         (v2/release-world! w)
         (is (true? (v2/await-complete w 2000 ::timeout))))))))

(deftest host-forks-and-instances-are-not-counted
  ;; F2: they are owned weakly by the root scope, which is never removed
  (checked
   (let [w (vworld) pubs (atom {})]
     (v2/install-handlers! w {:default (fn [p] (swap! pubs assoc (:payload p) p))})
     (binding [v2/*world* w]
       (let [c (v2/fork! w)
             _ (task (v2/savepoint :choose :b))
             _ (eventually #(get @pubs :b))
             i (doto (v2/instantiate (get @pubs :b)) (v2/activate! 1))]
         (is (= {:owned {} :normalize #{}} (counts w)))
         (is (= {:owned {} :normalize #{}} (counts c) (counts i)))
         (v2/abandon! (get @pubs :b))
         (doseq [x [c i w]] (v2/release-world! x))
         (is (true? (v2/await-complete w 2000 ::timeout))))))))
