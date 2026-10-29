(ns org.replikativ.spindel.engine.kernel-runtime-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.kernel-runtime :as k #?@(:cljs [:include-macros true])]
            [org.replikativ.spindel.engine.kernel :as kernel]
            [org.replikativ.spindel.incremental.interval :as iv]))

(deftest track-reentry-preserves-the-executed-prefix
  (doseq [options [{} {:cells? true} {:cells? true :diagnostics? false}]]
    (let [rt (k/runtime options)
          source (k/signal rt :source 1)
          prefix (atom 0)
          s (k/kspin rt :spin
                     (swap! prefix inc)
                     (* 2 (iv/get-new (k/track source))))
          values (atom [])]
      (k/observe! rt s #(swap! values conj %) #(throw %))
      (k/set-signal! rt source 2)
      (k/set-signal! rt source 3)
      (is (= [2 4 6] @values))
      (is (= 1 @prefix)))))

(deftest signal-created-in-the-prefix-remains-owned
  (doseq [options [{} {:cells? true} {:cells? true :diagnostics? false}]]
    (let [rt (k/runtime options)
          source-holder (atom nil)
          s (k/kspin rt :spin
                     (let [source (k/signal rt :inner-source 1)]
                       (reset! source-holder source)
                       (iv/get-new (k/track source))))
          values (atom [])]
      (k/observe! rt s #(swap! values conj %) #(throw %))
      (k/set-signal! rt @source-holder 2)
      (k/set-signal! rt @source-holder 3)
      (is (= [1 2 3] @values)))))

(deftest diamond-coalesces-at-the-earliest-continuation
  (doseq [options [{} {:cells? true} {:cells? true :diagnostics? false}]]
    (let [rt (k/runtime options)
          source (k/signal rt :source 0)
          b (k/kspin rt :b (* 2 (iv/get-new (k/track source))))
          c (k/kspin rt :c (* 3 (iv/get-new (k/track source))))
          d (k/kspin rt :d (+ (k/await b) (k/await c)))
          e (k/kspin rt :e (* 2 (k/await d)))
          f (k/kspin rt :f (* 3 (k/await d)))
          g (k/kspin rt :g (+ (k/await e) (k/await f)))
          d-values (atom [])
          g-values (atom [])]
      (k/observe! rt d #(swap! d-values conj %) #(throw %))
      (k/observe! rt g #(swap! g-values conj %) #(throw %))
      (doseq [value (range 1 101)] (k/set-signal! rt source value))
      (is (= (mapv #(* 5 %) (range 101)) @d-values))
      (is (= (mapv #(* 25 %) (range 101)) @g-values))
      (let [world (get-in (kernel/snapshot (:kernel rt)) [:worlds [:w 0]])]
        (is (= 6 (count (:runs world))))
        (is (= 10 (count (:obligations world))))
        (is (empty? (:queue world)))))))

(deftest awaited-errors-reach-the-host
  (doseq [options [{} {:cells? true} {:cells? true :diagnostics? false}]]
    (let [rt (k/runtime options)
          failure (ex-info "body failed" {:test :body-error})
          child (k/kspin rt :child (throw failure))
          parent (k/kspin rt :parent (k/await child))
          errors (atom [])
          successes (atom [])]
      (k/observe! rt parent #(swap! successes conj %) #(swap! errors conj %))
      (is (empty? @successes))
      (is (= [failure] @errors)))))

(deftest executable-arena-follows-accepted-lifetimes
  (doseq [options [{} {:cells? true} {:cells? true :diagnostics? false}]]
    (let [rt (k/runtime options)
          unused (k/kspin rt :unused :unused)
          s (k/kspin rt :spin :first)
          values (atom [])]
      (is (empty? @(:bodies rt)))
      (k/observe! rt s #(swap! values conj %) #(throw %))
      (is (= #{[[:w 0] :spin]} (set (keys @(:bodies rt)))))
      (k/release-idle! rt)
      (is (empty? @(:bodies rt)))
      (is (empty? @(:callbacks rt)))
      (let [error (try (k/observe! rt s #(swap! values conj %) #(throw %)) nil
                       (catch #?(:clj Exception :cljs :default) e e))]
        (is (some? error)))
      (is (empty? @(:bodies rt)))
      (let [fresh (k/kspin rt :spin :second)]
        (k/observe! rt fresh #(swap! values conj %) #(throw %)))
      (k/observe! rt unused #(swap! values conj %) #(throw %))
      (is (= [:first :second :unused] @values))
      (k/release-idle! rt)
      (is (empty? @(:bodies rt))))))

#?(:clj
   (deftest concurrent-observers-publish-callbacks-before-delivery
     (let [rt (k/runtime {:cells? true :diagnostics? false})
           s (k/kspin rt :spin 42)
           values (atom [])
           subscriptions (atom [])
           jobs (doall (for [_ (range 8)]
                         (future
                           (dotimes [_ 50]
                             (swap! subscriptions conj
                                    (k/observe! rt s #(swap! values conj %) #(throw %)))))))]
       (doseq [job jobs] @job)
       (k/drain! rt)
       (is (= (vec (repeat 400 42)) @values))
       (doseq [unsubscribe @subscriptions] (unsubscribe))
       (is (empty? @(:callbacks rt))))))
