(ns org.replikativ.spindel.v2.port.semaphore-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [task await acquire!]]
            [org.replikativ.spindel.v2.port.helpers :refer [checked-fixture outcome]]))

(use-fixtures :each checked-fixture)

(deftest test-semaphore-creation
  (let [s (v2/semaphore 5)] (is (= 5 (v2/permits s)))))

(deftest test-semaphore-deref
  (let [s (v2/semaphore 10)] (is (= 10 (v2/permits s)))))

(deftest test-acquire-immediate
  (let [s (v2/semaphore 3)]
    (is (= :acquired (v2/value (task (acquire! s)))))
    (is (= 2 (v2/permits s)))))

(deftest test-acquire-release
  (let [s (v2/semaphore 5)]
    (v2/value (task (acquire! s)))
    (is (= 4 (v2/permits s)))
    (v2/sem-release! s)
    (is (= 5 (v2/permits s)))))

(deftest test-multiple-acquires
  (let [s (v2/semaphore 10)]
    (v2/value (task (acquire! s) (acquire! s) (acquire! s)))
    (is (= 7 (v2/permits s)))))

(deftest test-acquire-waits-when-no-permits
  (let [s (v2/semaphore 1) seen (atom [])]
    (is (= :acquired (v2/value (task (acquire! s)))))
    (is (= 0 (v2/permits s)))
    (let [waiter (task (acquire! s) (swap! seen conj :acquired))]
      (is (empty? @seen))
      (v2/sem-release! s)
      (is (= [:ok [:acquired]] (outcome waiter)))
      (is (= [:acquired] @seen)))))

(deftest test-fifo-queueing
  (let [s (v2/semaphore 1) results (atom [])]
    (v2/value (task (acquire! s)))
    (let [waiters (mapv (fn [i] (task (acquire! s) (swap! results conj i) (v2/sem-release! s) i))
                        (range 3))]
      (is (empty? @results))
      (v2/sem-release! s)
      (doseq [[i t] (map-indexed vector waiters)] (is (= i (v2/value t))))
      (is (= 3 (count @results)))
      (is (= #{0 1 2} (set @results))))))

(deftest test-holding-success
  (let [s (v2/semaphore 2) gate (v2/deferred)
        t (task (acquire! s) (try (await gate) (finally (v2/sem-release! s))))]
    (is (= 1 (v2/permits s)) "one held during execution")
    (gate :done)
    (is (= :done (v2/value t)))
    (is (= 2 (v2/permits s)))))

(deftest test-holding-failure
  (let [s (v2/semaphore 3)
        t (task (acquire! s)
                (try (throw (ex-info "Test error" {})) (finally (v2/sem-release! s))))]
    (is (= :err (first (outcome t))))
    (is (= 3 (v2/permits s)))))

(deftest test-nested-holding
  (let [s (v2/semaphore 5) outer-gate (v2/deferred) inner-gate (v2/deferred)
        t (task (acquire! s)
                (try (await outer-gate)
                     (acquire! s)
                     (try (await inner-gate) (finally (v2/sem-release! s)))
                     (finally (v2/sem-release! s))))]
    (is (= 4 (v2/permits s)))
    (outer-gate :go)
    (is (= 3 (v2/permits s)))
    (inner-gate :done)
    (is (= :done (v2/value t)))
    (is (= 5 (v2/permits s)))))

(deftest test-concurrent-limit
  (let [s (v2/semaphore 2) active (atom 0) max-active (atom 0)
        tasks (mapv (fn [_]
                      (task (acquire! s)
                            (try (let [n (swap! active inc)]
                                   (swap! max-active max n)
                                   (v2/sleep 50)
                                   (swap! active dec))
                                 (finally (v2/sem-release! s))))) (range 10))]
    (doseq [t tasks] (is (= :ok (first (outcome t)))))
    (is (<= @max-active 2))
    (is (= 0 @active))
    (is (= 2 (v2/permits s)))))

(deftest test-over-release-error
  (let [s (v2/semaphore 2)]
    (is (= :over-release (:spindel/invalid (try (v2/sem-release! s) nil (catch Exception e (ex-data e))))))))

(deftest test-create-with-zero-permits
  ;; v2 refuses with ex-info (the old :pre raised AssertionError)
  (is (= :semaphore (:spindel/invalid (try (v2/semaphore 0) nil (catch Exception e (ex-data e))))))
  (is (= :semaphore (:spindel/invalid (try (v2/semaphore -1) nil (catch Exception e (ex-data e)))))))

(deftest test-semaphore-uses-dynamic-runtime
  (let [s (v2/semaphore 5)]
    (v2/value (task (acquire! s)))
    (is (= 4 (v2/permits s)))
    (binding [v2/*world* v2/*world*] (is (= 4 (v2/permits s))))))
