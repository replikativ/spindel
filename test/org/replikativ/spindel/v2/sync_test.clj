(ns org.replikativ.spindel.v2.sync-test
  "Mailboxes, semaphores and finalizers on cancellation."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await take! acquire!]]
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
  (let [fr (frequencies (map #(aget ^objects % rw/TYPE) (vals (aget ^objects w rw/W-REG))))]
    {:tasks (get fr rw/T-TASK 0) :runs (get fr rw/T-RUN 0) :edges (get fr rw/T-EDGE 0)
     :acts (get fr rw/T-ACT 0)}))

(defn- outcome [h]
  (try [:ok (v2/value h)] (catch Exception e [:err e])))

(deftest mailbox-fifo
  (checked
    (let [w (vworld)]
      (binding [v2/*world* w]
        (let [mb (v2/mailbox)
              got (atom [])
              a (task (swap! got conj [:a (take! mb)]))
              b (task (swap! got conj [:b (take! mb)]))]
          (v2/post! mb 1)
          (v2/post! mb 2)
          (v2/post! mb 3)
          (is (= [[:a 1] [:b 2]] @got) "waiters are served in order, one message each")
          (let [c (task (take! mb))]
            (is (= 3 (v2/value c)) "a queued message is taken at once"))
          (is (= 0 (:edges (census w)))))))))

(deftest cancelled-waiter-loses-its-place
  (checked
    (let [w (vworld)]
      (binding [v2/*world* w]
        (let [mb (v2/mailbox)
              a (task (take! mb))
              b (task (take! mb))]
          (v2/cancel-task! a)
          (v2/post! mb :m)
          (is (= :m (v2/value b)))
          (is (= :err (first (outcome a)))))))))

(deftest semaphore-permits
  (checked
    (let [w (vworld)]
      (binding [v2/*world* w]
        (let [s (v2/semaphore 1)
              log (atom [])
              t1 (task (acquire! s) (swap! log conj :t1) :t1)
              t2 (task (acquire! s) (swap! log conj :t2) :t2)]
          (is (= [:t1] @log))
          (v2/sem-release! s)
          (is (= [:t1 :t2] @log))
          (v2/sem-release! s)
          (is (= 1 (aget ^objects (v2/row-of s) rw/X-VALUE))))))))

(deftest finalizer-runs-on-cancel
  (checked
    (let [w (vworld)]
      (binding [v2/*world* w]
        (let [d (v2/deferred)
              s (v2/semaphore 0)
              log (atom [])
              t (task (try (await d)
                           (swap! log conj :body)
                           (finally (swap! log conj :finally)
                                    (v2/sem-release! s))))]
          (v2/cancel-task! t)
          (is (= [:finally] @log) "the finally region ran in a cleanup slice")
          (is (= 1 (aget ^objects (v2/row-of s) rw/X-VALUE)) "and could release a shared semaphore")
          (is (= :err (first (outcome t))))
          (is (= 0 (:runs (census w))) "the run retired after its finalizer"))))))

(deftest finalizer-runs-on-normal-exit
  (checked
    (let [w (vworld)]
      (binding [v2/*world* w]
        (let [d (v2/deferred)
              log (atom [])
              t (task (try (await d) (finally (swap! log conj :finally))))]
          (v2/deliver! d 7)
          (is (= 7 (v2/value t)))
          (is (= [:finally] @log))
          (is (= 0 (:runs (census w)))))))))

(deftest structured-cancel-runs-child-finalizers
  (checked
    (let [w (vworld)]
      (binding [v2/*world* w]
        (let [d (v2/deferred)
              log (atom [])
              t (task (let [child (task (try (await d) (finally (swap! log conj :child))))]
                        (await child)))]
          (v2/cancel-task! t)
          (is (= [:child] @log))
          (is (= 0 (:runs (census w)))))))))
