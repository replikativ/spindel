(ns org.replikativ.spindel.v2.port.hof-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [org.replikativ.spindel.v2.core :refer [spin await]]
            [org.replikativ.spindel.v2.combinators :refer [parallel]]
            [org.replikativ.spindel.v2.port.support :refer [checking with-world outcome]]))

(use-fixtures :each checking)

(deftest pure-higher-order-calls-stay-lazy
  (with-world [w]
    (is (= [:ok ['(1 2 3) 3]]
           (outcome (spin [(take 3 (map inc (range)))
                           (count (map (fn [x] (spin x)) [1 2 3]))]))))))

(deftest core-doseq-supports-nested-bindings-and-modifiers
  (with-world [w]
    (let [seen (atom [])
          c (spin
             (doseq [x [0 1] y (range 5)
                     :let [v y] :when (even? v) :while (< v 3)]
               (swap! seen conj (await (spin [x y]))))
             :done)]
      (is (= [:ok :done] (outcome c)))
      (is (= [[0 0] [0 2] [1 0] [1 2]] @seen)))))

(defn- doubled-spin [x]
  (spin (await (spin (* 2 x)))))

(deftest named-callbacks-return-spins
  (with-world [w]
    (is (= [:ok [2 4 6]]
           (outcome (spin (await (apply parallel (mapv doubled-spin [1 2 3])))))))))

(deftest bare-suspension-in-higher-order-callbacks-is-rejected
  (binding [*ns* (the-ns 'org.replikativ.spindel.v2.port.hof-test)]
    (doseq [body ['(mapv (fn [x] (await (spin x))) [1])
                  '(map (fn [x] (await (spin x))) [1])
                  '(reduce (fn [a x] (+ a (await (spin x)))) 0 [1])
                  '(run! (fn [x] (await (spin x))) [1])]]
      (let [error (try (macroexpand-1 (list 'spin body)) nil
                       (catch Throwable e
                         (last (take-while some? (iterate ex-cause e)))))]
        (is (= :is.simm.partial-cps.ioc/unsupported-suspension
               (:type (ex-data error))) (str body))))))
