(ns org.replikativ.spindel.v2.port.spin-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin await track]]
            [org.replikativ.spindel.v2.port.support :refer [checking with-world outcome]]))

(use-fixtures :each checking)

(deftest test-basic-spin-execution
  (with-world [w]
    (is (= [:ok 3] (outcome (spin (+ 1 2)))))))

(deftest test-spin-with-binding
  (with-world [w]
    (let [x 10 y 20]
      (is (= [:ok 30] (outcome (spin (+ x y))))))))

(deftest test-spin-with-let-binding
  (with-world [w]
    (is (= [:ok 15]
           (outcome (spin (let [x 5 y (* x 2) z (+ x y)] z)))))))

(deftest test-spin-caching-basic
  (with-world [w]
    (let [executions (atom 0) c (spin (swap! executions inc) 42)]
      (is (= [:ok 42] (outcome c)))
      (is (= 1 @executions))
      (is (= [:ok 42] (outcome c)))
      (is (= 1 @executions) "A second host read uses the cache"))))

(deftest test-spin-caching-with-computation
  (with-world [w]
    (let [executions (atom 0)
          c (spin (swap! executions inc) (v2/sleep 10) (reduce + (range 1000)))
          start (System/nanoTime)]
      (is (= [:ok 499500] (outcome c)))
      (is (>= (/ (- (System/nanoTime) start) 1e6) 10))
      (is (= 1 @executions))
      (is (= [:ok 499500] (outcome c)))
      (is (= 1 @executions) "No second execution or timer"))))

(deftest test-spin-tracks-signal
  (with-world [w]
    (let [counter (v2/signal 42)]
      (is (= [:ok 84] (outcome (spin (* 2 (:new (track counter))))))))))

(deftest test-spin-tracks-multiple-signals
  (with-world [w]
    (let [x (v2/signal 10) y (v2/signal 20)]
      (is (= [:ok 30] (outcome (spin (+ (:new (track x)) (:new (track y))))))))))

(deftest test-signal-change-marks-spin-dirty
  (with-world [w]
    (let [counter (v2/signal 0) executions (atom 0)
          doubled (spin (let [{:keys [new]} (track counter)]
                          (swap! executions inc) (* 2 new)))]
      (is (= [:ok 0] (outcome doubled)))
      (is (= 1 @executions))
      (swap! counter inc)
      (is (= [:ok 2] (outcome doubled)))
      (is (= 2 @executions)))))

(deftest test-multiple-signal-updates
  (with-world [w]
    (let [counter (v2/signal 0) executions (atom 0)
          doubled (spin (let [{:keys [new]} (track counter)]
                          (swap! executions inc) (* 2 new)))]
      (is (= [:ok 0] (outcome doubled)))
      (is (= 1 @executions))
      (swap! counter inc)
      (is (= [:ok 2] (outcome doubled)))
      (is (= 2 @executions))
      (swap! counter inc)
      (is (= [:ok 4] (outcome doubled)))
      (is (= 3 @executions))
      (swap! counter + 3)
      (is (= [:ok 10] (outcome doubled)))
      (is (= 4 @executions)))))

(deftest test-multiple-signals-one-changes
  (with-world [w]
    (let [x (v2/signal 10) y (v2/signal 20) executions (atom 0)
          c (spin (let [a (:new (track x)) b (:new (track y))]
                    (swap! executions inc) (+ a b)))]
      (is (= [:ok 30] (outcome c)))
      (is (= 1 @executions))
      (swap! x + 5)
      (is (= [:ok 35] (outcome c)))
      (is (= 2 @executions))
      (swap! y + 10)
      (is (= [:ok 45] (outcome c)))
      (is (= 3 @executions)))))

(deftest test-spin-awaits-spin
  (with-world [w]
    (let [base (spin (+ 1 2)) dependent (spin (* 2 (await base)))]
      (is (= [:ok 6] (outcome dependent))))))

(deftest test-spin-chain
  (with-world [w]
    (let [a (spin (+ 1 2)) b (spin (* 2 (await a))) c (spin (dec (await b)))]
      (is (= [:ok 5] (outcome c))))))

(deftest test-spin-with-nil-result
  (with-world [w] (is (= [:ok nil] (outcome (spin nil))))))

(deftest test-spin-with-false-result
  (with-world [w] (is (= [:ok false] (outcome (spin false))))))

(deftest test-spin-with-vector-result
  (with-world [w] (is (= [:ok [1 2 3]] (outcome (spin [1 2 3]))))))

(deftest test-spin-with-map-result
  (with-world [w] (is (= [:ok {:a 1 :b 2}] (outcome (spin {:a 1 :b 2}))))))
