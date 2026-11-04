(ns org.replikativ.spindel.v2.resource-test
  "Resources (T15, T17, T18): offload and timers, and their join on cancel."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await offload sleep]]
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

(defn- census [w]
  (let [fr (v2/call-in! w #(frequencies (map (fn [r] (aget ^objects r rw/TYPE)) (vals (aget ^objects w rw/W-REG)))))]
    {:runs (get fr rw/T-RUN 0) :res (get fr rw/T-RES 0) :edges (get fr rw/T-EDGE 0)}))

(defn- wait-until [f]
  (loop [n 0] (cond (f) true (> n 500) false :else (do (Thread/sleep 5) (recur (inc n))))))

(deftest offload-returns
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [t (task (inc (offload #(+ 1 2))))]
         (is (= 4 (v2/value t 5000 ::timeout)))
         (is (wait-until #(zero? (:res (census w)))))
         (is (zero? (:runs (census w)))))))))

(deftest offload-error-propagates
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [t (task (offload #(throw (ex-info "boom" {:x 1}))))]
         (is (= {:x 1} (try (v2/value t 5000 ::timeout) (catch Exception e (ex-data e))))))))))

(deftest sleep-and-continue
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [t (task (sleep 20) :woke)]
         (is (= :woke (v2/value t 5000 ::timeout))))))))

(deftest cancel-waits-for-the-offload-to-join
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [started (promise)
             release (atom false)
              ;; ignores interrupts: the join must wait for the function
             t (task (offload #(do (deliver started true)
                                   (while (not @release) (Thread/onSpinWait))
                                   :late)))]
         (deref started 5000 nil)
         (v2/cancel-task! t)
         (is (v2/cancelled? (try (v2/value t 1000 ::timeout) (catch Exception e e))))
         (is (= 1 (:runs (census w))) "the run stays in cleanup until the resource joins")
         (reset! release true)
         (is (wait-until #(zero? (:runs (census w)))) "then it retires")
         (is (zero? (:res (census w)))))))))

(deftest cancel-interrupts-blocking-offload
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [started (promise)
             t (task (offload #(do (deliver started true) (Thread/sleep 60000))))]
         (deref started 5000 nil)
         (v2/cancel-task! t)
         (is (wait-until #(zero? (:runs (census w)))) "the interrupted function returned and joined"))))))

(deftest cancel-unschedules-a-timer
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [t (task (sleep 60000) :never)]
         (v2/cancel-task! t)
         (is (zero? (:runs (census w))))
         (is (zero? (:res (census w)))))))))

(deftest computation-offload
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [x (v2/signal 2)
             c (spin (let [v (iv/get-new (track x))] (offload #(* v v))))
             seen (atom [])
             u (v2/observe! c (fn [v _] (swap! seen conj v)))]
         (is (wait-until #(= [4] @seen)))
         (v2/write! x 3)
         (is (wait-until #(= [4 9] @seen)))
         (u))))))

(defn- reg-size [w] (count (aget ^objects w rw/W-REG)))

(deftest finalizers-act-after-release
  ;; Z#56: a cleanup slice of a released world may still deliver (Z#40)
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [d (v2/deferred) d2 (v2/deferred) ran (atom nil)
             _ (task (try (await d) (finally (v2/deliver! d2 :from-finally) (reset! ran :done))))]
         (v2/value (v2/signal 0) 100 nil)
         (let [left (v2/release-world! w)]
           (is (wait-until #(= :done @ran)) "the finalizer ran to its end")
           (is (wait-until #(zero? (left))))))))))

(deftest offload-joins-after-release
  ;; Z#56: an offload running at release completes into the released world,
  ;; joins, and its run retires
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [started (promise)
             _ (task (offload #(do (deliver started true)
                                   (try (Thread/sleep 300) (catch InterruptedException _ (Thread/sleep 50)))
                                   :done)))]
         (deref started 1000 nil)
         (let [left (v2/release-world! w)]
           (is (wait-until #(zero? (left))) "no rows left once the offload returned")
           (is (= 1 (reg-size w)) "only the root scope")))))))
