(ns org.replikativ.spindel.spin.hof-test
  "Higher-order calls over effectful fn literals inside a spin body become
  loops the CPS transformation sees through; pure ones keep their laziness."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]])
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]])))

(deftest effectful-higher-order-calls
  (async done
         (with-ctx [_ctx]
           (run-spin! (spin
                       {:mapv (mapv (fn [x] (await (spin (* 2 x)))) [1 2 3])
                        :map (map (fn [x] (await (spin (inc x)))) [1 2])
                        :reduce (reduce (fn [acc x] (+ acc (await (spin (* x x))))) 0 [1 2 3])
                        :filterv (filterv (fn [x] (odd? (await (spin x)))) (range 6))
                        :remove (remove (fn [x] (odd? (await (spin x)))) (range 6))
                        :keep (keep (fn [x] (when (even? x) (await (spin x)))) (range 5))
                        :doseq (let [a (atom [])]
                                 (doseq [x [1 2]] (swap! a conj (await (spin (inc x)))))
                                 @a)
                        :for (for [[k v] (sorted-map :a 1 :b 2)] [k (await (spin (* 10 v)))])
                        :run! (let [a (atom 0)]
                                (run! (fn [x] (swap! a + (await (spin x)))) [1 2 3])
                                @a)
                        :nested (mapv (fn [x] (mapv (fn [y] (await (spin (* x y)))) [1 2])) [1 2])})
                      (fn [v]
                        (is (= {:mapv [2 4 6] :map [2 3] :reduce 14 :filterv [1 3 5] :remove [0 2 4]
                                :keep [0 2 4] :doseq [2 3] :for [[:a 10] [:b 20]] :run! 6
                                :nested [[1 2] [2 4]]}
                               v))
                        (done))
                      (fn [e] (is false (str "rejected: " (ex-message e))) (done))))))

(deftest pure-higher-order-calls-stay-lazy
  (async done
         (with-ctx [_ctx]
           (run-spin! (spin [(take 3 (map inc (range)))
                             ;; a fn that only builds spins performs no effect
                             (count (map (fn [x] (spin x)) [1 2 3]))])
                      (fn [v] (is (= ['(1 2 3) 3] v)) (done))
                      (fn [e] (is false (str "rejected: " (ex-message e))) (done))))))
