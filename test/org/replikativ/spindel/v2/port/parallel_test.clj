(ns org.replikativ.spindel.v2.port.parallel-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task await track]]
            [org.replikativ.spindel.v2.combinators :as comb]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.port.support2 :as h]))

(use-fixtures :each h/fixture)

(deftest test-parallel-two-immediate-spins
  (is (= [:a :b] (h/result (comb/parallel (spin :a) (spin :b))))))

(deftest test-parallel-three-spins-sum
  (is (= 6 (h/result (spin (apply + (await (comb/parallel (spin 1) (spin 2) (spin 3)))))))))

(deftest test-parallel-basic
  (is (= [:first :second :third]
         (h/result (comb/parallel (spin :first) (spin :second) (spin :third))))))

(deftest test-await-parallel-in-spin
  (is (= 60 (h/result (spin (let [a (spin 10) b (spin 20) c (spin 30)]
                              (apply + (await (comb/parallel a b c)))))))))

(deftest test-parallel-merge-maps
  (is (= {:a 1 :b 2}
         (h/result (spin (apply merge (await (comb/parallel (spin {:a 1}) (spin {:b 2})))))))))

(deftest test-nested-parallel
  (is (= [[1 2] [3 4]]
         (h/result (spin (await (comb/parallel (comb/parallel (spin 1) (spin 2))
                                               (comb/parallel (spin 3) (spin 4)))))))))

(deftest test-parallel-reactive-child-error-propagates
  (let [mode (v2/signal :ok)
        a (spin (if (= :fail (:new (track mode))) (throw (ex-info "child" {:boom true})) :a-value))
        parent (spin (await (comb/parallel a (spin :b-value))))
        seen (atom [])
        stop (v2/observe! parent #(swap! seen conj [%1 %2]))]
    (try
      (is (= [[[:a-value :b-value] false]] @seen))
      (reset! mode :fail)
      (is (= 2 (count @seen)))
      (is (true? (second (second @seen))))
      (is (= {:boom true} (ex-data (first (second @seen)))))
      (finally (stop)))))

(deftest test-parallel-with-deferreds
  (let [a (v2/deferred) b (v2/deferred) p (comb/parallel a b) seen (promise)]
    (v2/value-async p #(deliver seen [%1 %2]))
    (is (not (realized? seen)))
    (a :first)
    (is (not (realized? seen)))
    (b :second)
    (is (= [[:first :second] false] (deref seen 2000 ::timeout)))))

(deftest test-parallel-with-deferreds-three
  (let [a (v2/deferred) b (v2/deferred) c (v2/deferred)
        p (comb/parallel a b c) seen (promise)]
    (v2/value-async p #(deliver seen [%1 %2]))
    (c :third) (is (not (realized? seen)))
    (b :second) (is (not (realized? seen)))
    (a :first)
    (is (= [[:first :second :third] false] (deref seen 2000 ::timeout)))))

(deftest test-parallel-mixed-immediate-deferred
  (let [d (v2/deferred) p (comb/parallel (spin :immediate) d) seen (promise)]
    (v2/value-async p #(deliver seen [%1 %2]))
    (is (not (realized? seen)))
    (d :deferred)
    (is (= [[:immediate :deferred] false] (deref seen 2000 ::timeout)))))

(deftest test-parallel-first-error-fails
  (let [[tag e] (h/outcome (comb/parallel (spin :ok) (spin (throw (ex-info "test error" {:test true})))))]
    (is (= :err tag))
    (is (= "test error" (ex-message e)))
    (is (= {:test true} (ex-data e)))))

;; The model is still lazy at fork time. Every child evaluates its own copy;
;; physical operations arm there, rather than inheriting a running offload.
(defn- fork-results [make-model]
  (let [parent v2/*world*
        model (make-model)
        children (mapv (fn [_] (v2/fork! parent)) (range 3))]
    (mapv (fn [w]
            (comb/blocking #(v2/value (v2/in-world w model)))) children)))

(deftest test-parallel-with-forked-context
  (is (= [30 30 30] (h/result (apply comb/parallel (fork-results #(spin (* 5 6))))))))

(deftest test-parallel-with-forked-context-and-trampoline
  (is (= [56 56 56] (h/result (apply comb/parallel (fork-results #(spin (* 7 8))))))))

(deftest test-parallel-awaiting-same-shared-spin
  (let [shared (spin (+ 10 20))
        children (mapv (fn [_] (v2/fork! v2/*world*)) (range 3))]
    ;; H4: bridge independent worlds through offload; no cross-world wait in a slice.
    (is (= [30 30 30]
           (h/result (apply comb/parallel
                            (mapv (fn [w] (comb/blocking #(v2/value (v2/in-world w shared)))) children)))))))

(deftest test-parallel-with-model-like-spin
  (let [model #(spin (+ 100 (await (spin (* 2 3)))))]
    (is (= [106 106 106]
           (h/result (apply comb/parallel
                            (fork-results model)))))))

(deftest test-parallel-with-async-model
  (is (= [84 84 84]
         (h/result (apply comb/parallel
                          (fork-results #(spin (* 2 (v2/offload (fn [] 42))))))))))

(deftest test-parallel-with-multiple-async-in-model
  (is (= [30 30 30]
         (h/result (apply comb/parallel
                          (fork-results #(spin (+ (v2/offload (fn [] 10))
                                                  (v2/offload (fn [] 20))))))))))

(deftest test-parallel-model-created-outside-binding
  (let [w v2/*world*
        model (binding [v2/*world* w] (spin (await (spin (* 5 5)))))
        children (mapv (fn [_] (v2/fork! w)) (range 3))]
    (is (= [25 25 25]
           (h/result (apply comb/parallel
                            (mapv (fn [c] (comb/blocking #(v2/value (v2/in-world c model)))) children)))))))

(deftest test-parallel-reactive-fork-isolation
  (let [s (v2/signal 10) p (comb/parallel (spin (:new (track s))) (spin :static))]
    (is (= [10 :static] (h/result p)))
    (let [child (v2/fork! v2/*world*) cp (v2/in-world child p)]
      (reset! (v2/in-world child s) 99)
      (is (= [10 :static] (h/result p)))
      (is (= [99 :static] (h/result cp))))))
