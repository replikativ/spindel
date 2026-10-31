(ns org.replikativ.spindel.spin.hof-test
  "Higher-order callbacks retain their own function scopes; native iteration
  macros remain resumable and pure collection calls retain their semantics."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.spin.combinators :refer [parallel]]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]])
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]])))

(deftest pure-higher-order-calls-stay-lazy
  (async done
         (with-ctx [_ctx]
           (run-spin! (spin [(take 3 (map inc (range)))
                             ;; a fn that only builds spins performs no effect
                             (count (map (fn [x] (spin x)) [1 2 3]))])
                      (fn [v] (is (= ['(1 2 3) 3] v)) (done))
                      (fn [e] (is false (str "rejected: " (ex-message e))) (done))))))

(deftest core-doseq-supports-nested-bindings-and-modifiers
  (async done
         (with-ctx [_ctx]
           (run-spin! (spin
                       (let [seen (atom [])]
                         (doseq [x [0 1] y (range 5)
                                 :let [v y] :when (even? v) :while (< v 3)]
                           (swap! seen conj (await (spin [x y]))))
                         @seen))
                      (fn [v]
                        (is (= [[0 0] [0 2] [1 0] [1 2]] v))
                        (done))
                      (fn [e] (is false (str e)) (done))))))

(defn- doubled-spin [x]
  (spin (await (spin (* 2 x)))))

(deftest named-callbacks-return-spins
  (async done
         (with-ctx [_ctx]
           (run-spin! (spin (await (apply parallel (mapv doubled-spin [1 2 3]))))
                      (fn [v] (is (= [2 4 6] v)) (done))
                      (fn [e] (is false (str e)) (done))))))

#?(:clj
   (deftest bare-suspension-in-higher-order-callbacks-is-rejected
     (binding [*ns* (the-ns 'org.replikativ.spindel.spin.hof-test)]
       (doseq [body ['(mapv (fn [x] (await (spin x))) [1])
                     '(map (fn [x] (await (spin x))) [1])
                     '(reduce (fn [a x] (+ a (await (spin x)))) 0 [1])
                     '(run! (fn [x] (await (spin x))) [1])]]
         (let [error (try (macroexpand-1 (list 'spin body)) nil
                          (catch Throwable e
                            (last (take-while some? (iterate ex-cause e)))))]
           (is (= :is.simm.partial-cps.ioc/unsupported-suspension
                  (:type (ex-data error))) (str body)))))))
