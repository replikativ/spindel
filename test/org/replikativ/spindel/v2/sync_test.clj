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
  (let [fr (v2/call-in! w #(frequencies (map (fn [r] (aget ^objects r rw/TYPE)) (vals (aget ^objects w rw/W-REG)))))]
    {:tasks (get fr rw/T-TASK 0) :runs (get fr rw/T-RUN 0) :edges (get fr rw/T-EDGE 0)
     :acts (get fr rw/T-ACT 0)}))

(defn- outcome [h]
  (try (let [v (v2/value h 100 ::pending)] (if (= ::pending v) [:pending] [:ok v]))
       (catch Exception e [:err e])))

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

(defmacro with-cleanup [log & body]
  `(try ~@body (finally (swap! ~log conj :macro-finally))))

(deftest macro-generated-finally-runs-on-cancel
  (checked
    (let [w (vworld)]
      (binding [v2/*world* w]
        (let [d (v2/deferred)
              log (atom [])
              t (task (with-cleanup log (await d)))]
          (v2/cancel-task! t)
          (is (= [:macro-finally] @log) "a finally region from a user macro is registered")
          (is (= 0 (:runs (census w)))))))))

(defn- waiter-on-closed [mk op]
  ;; the source is owned by k's run scope; cancelling k closes it (T16) while
  ;; a task and a computation wait on it
  (let [w (vworld)]
    (binding [v2/*world* w]
      (let [src (promise) gk (v2/deferred)
            k (task (deliver src (mk)) (await gk))
            x (deref src 1000 nil)
            t (case op
                :take (task (take! x))
                :acquire (task (acquire! x))
                :await (task (await x)))
            c (case op
                :take (spin (try (take! x) (catch Exception e [:caught (ex-data e)])))
                :acquire (spin (try (acquire! x) (catch Exception e [:caught (ex-data e)])))
                :await (spin (try (await x) (catch Exception e [:caught (ex-data e)]))))
            seen (atom [])]
        (v2/observe! c (fn [v _] (swap! seen conj v)))
        (v2/cancel-task! k)
        (v2/value (v2/signal 0) 100 nil)
        {:task (let [[tag v] (outcome t)] [tag (if (= :err tag) (ex-data v) v)])
         :comp @seen}))))

(deftest waiters-on-a-closed-source-get-an-error
  ;; Z#53: a closed source without a value wakes its waiters with err ::closed
  (checked
    (doseq [[mk op] [[v2/mailbox :take] [#(v2/semaphore 0) :acquire] [v2/deferred :await]]]
      (testing (name op)
        (let [{:keys [task comp]} (waiter-on-closed mk op)]
          (is (= [:err {:spindel/closed true}] task))
          (is (= [[:caught {:spindel/closed true}]] comp)))))))

(defn- invalid [t]
  (let [[tag v] (outcome t)] (when (= :err tag) (:spindel/invalid (ex-data v)))))

(deftest operations-by-source-kind
  ;; Z#54: await on a mailbox takes; track is for signals and cells; other
  ;; reads of a mailbox or semaphore are errors
  (checked
    (let [w (vworld)]
      (binding [v2/*world* w]
        (let [m (v2/mailbox) s (v2/semaphore 1) d (v2/deferred) x (v2/signal 1)]
          (testing "await on a mailbox takes, FIFO"
            (let [a (task (await m)) b (task (await m))]
              (v2/post! m :one)
              (v2/post! m :two)
              (is (= [[:ok :one] [:ok :two]] [(outcome a) (outcome b)]))))
          (testing "await on a semaphore is refused; acquire! still works"
            (is (= :await (invalid (task (await s)))))
            (is (= [:ok true] (outcome (task (acquire! s))))))
          (testing "group awaits with a consuming member are refused"
            (is (= :all (invalid (task (v2/await-all [d m])))))
            (is (= :any (invalid (task (v2/await-any [s d]))))))
          (testing "track on a non-signal is refused"
            (is (= :track (invalid (task (track m)))))
            (is (= :track (invalid (task (track d)))))
            (is (= [:ok 1] (outcome (task (iv/get-new (track x)))))))
          (testing "a host read of a mailbox or semaphore is refused"
            (is (thrown-with-msg? Exception #"Z#54" (v2/value m 100 nil)))
            (is (thrown-with-msg? Exception #"Z#54" (v2/value s 100 nil)))))))))
