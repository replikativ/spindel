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

(deftest rewritten-reduce-honors-reduced
  (async done
         (with-ctx [_ctx]
           (let [seen (atom [])]
             (run-spin! (spin (reduce (fn [acc x]
                                        (swap! seen conj x)
                                        (let [acc (+ acc (await (spin x)))]
                                          (if (= x 2) (reduced acc) acc)))
                                      0 [1 2 3 4]))
                        (fn [v]
                          (is (= 3 v))
                          (is (= [1 2] @seen) "no step runs after the reduced one")
                          (done))
                        (fn [e] (is false (str "rejected: " (ex-message e))) (done)))))))

(deftest locally-shadowed-names-are-not-rewritten
  (async done
         (with-ctx [_ctx]
           (run-spin! (spin
                       {:let (let [mapv (fn [_f _xs] :custom)]
                               (mapv (fn [x] (await x)) [1]))
                        :destructured (let [{:keys [run!]} {:run! (fn [_f _xs] :custom)}]
                                        (run! (fn [x] (await x)) [1]))
                        :loop (loop [filterv (fn [_f _xs] :custom)]
                                (filterv (fn [x] (await x)) [1]))
                        :when-let (when-let [keep (fn [_f _xs] :custom)]
                                    (keep (fn [x] (await x)) [1]))
                        :letfn (letfn [(map [_f _xs] :custom)]
                                 (map (fn [x] (await x)) [1]))
                        :fn-param (mapv (fn [reduce]
                                          [(await (spin 1)) (reduce (fn [a x] (await x)) 0 [1])])
                                        [(fn [_f _init _xs] :custom)])
                        :seq-let (vec (for [i [1] :let [remove (fn [_f _xs] [:custom i])]]
                                        (remove (fn [x] (await x)) [1])))
                        ;; the init sees only the bindings before it
                        :sequential (let [xs (mapv (fn [x] (await (spin x))) [1 2])
                                          mapv (fn [_f _xs] :custom)]
                                      [xs (mapv (fn [x] (await x)) [1])])})
                      (fn [v]
                        (is (= {:let :custom :destructured :custom :loop :custom :when-let :custom
                                :letfn :custom :fn-param [[1 :custom]] :seq-let [[:custom 1]]
                                :sequential [[1 2] :custom]}
                               v))
                        (done))
                      (fn [e] (is false (str "rejected: " (ex-message e))) (done))))))

(deftest inlined-fn-literals-keep-their-recur-target
  (async done
         (with-ctx [_ctx]
           (run-spin! (spin
                       {:mapv (mapv (fn [x] (let [y (await (spin x))]
                                              (if (pos? y) (recur (dec y)) [:done y])))
                                    [1 2])
                        :reduce (reduce (fn [acc x]
                                          (if (pos? x)
                                            (recur (+ acc (await (spin x))) (dec x))
                                            acc))
                                        0 [2 3])
                        :destructured (mapv (fn [[a b]] (if (< a b) (recur [(+ a (await (spin 1))) b]) a))
                                            [[0 2] [5 1]])
                        :named (mapv (fn named [x] (await (spin (inc x)))) [1 2])})
                      (fn [v]
                        (is (= {:mapv [[:done 0] [:done 0]] :reduce 9 :destructured [2 5] :named [2 3]} v))
                        (done))
                      (fn [e] (is false (str "rejected: " (ex-message e))) (done))))))

(defn- logged-seq
  "An unchunked lazy seq of [from, to) that logs each element's realization."
  [log from to]
  (lazy-seq
   (when (< from to)
     (swap! log conj [:realize from])
     (cons from (logged-seq log (inc from) to)))))

(deftest rewritten-loops-keep-evaluation-order
  (async done
         (with-ctx [_ctx]
           (let [run-log (atom []) for-log (atom []) reduce-log (atom [])]
             (run-spin! (spin
                         (run! (fn [x] (swap! run-log conj [:body (await (spin x))])) (logged-seq run-log 0 2))
                         (doall (for [x (logged-seq for-log 0 2)] (swap! for-log conj [:body (await (spin x))])))
                         (reduce (fn [acc x] (+ acc (await (spin x))))
                                 (do (swap! reduce-log conj :init) 0)
                                 (do (swap! reduce-log conj :coll) [1])))
                        (fn [v]
                          (is (= 1 v))
                          (is (= [[:realize 0] [:body 0] [:realize 1] [:body 1]] @run-log)
                              "an element's body runs before the walk realizes the next")
                          (is (= [[:realize 0] [:body 0] [:realize 1] [:body 1]] @for-log))
                          (is (= [:init :coll] @reduce-log) "init is evaluated before the collection")
                          (done))
                        (fn [e] (is false (str "rejected: " (ex-message e))) (done)))))))
