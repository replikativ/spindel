(ns org.replikativ.spindel.ygg-signal-test
  "A yggdrasil system living inside a spindel signal: `ygg-swap!` mutates it (sync
   path here — a JVM durable G-Set); the value is the system, read with its own
   ops. The async path (`swap-await!` for a cljs/konserve-backed value) is proven
   by signal-test's swap-await! tests + is the same dispatch."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.ygg-signal :as ys]
            [org.replikativ.spindel.test-helpers :refer [async with-ctx]]
            [yggdrasil.convergent.durable-gset :as g]))

(deftest ygg-signal-sync-swap
  (testing "a ygg-signal holds a yggdrasil system; ygg-swap! runs a yggdrasil op
            and commits the new system (sync dispatch for a JVM value)"
    (async done
           (with-ctx [_ctx]
             (let [gs  (g/durable-gset "kb" :store-config {:backend :memory :id (random-uuid)})
                   sig (ys/ygg-signal gs)]
               (is (false? (ys/async-system? gs)) "a JVM (:sync? true) system dispatches to swap!")
               (ys/ygg-swap! sig (fn [s] (g/add s :x)))
               (ys/ygg-swap! sig (fn [s] (g/add s :y)))
               (is (= #{:x :y} (g/elements @sig))
                   "ygg-swap! mutated the system held in the signal")
               (done))))))

(deftest ygg-merge-fn-joins
  (testing "ygg-merge-fn JOINs two convergent system values (for signal-sync)"
    (let [a (-> (g/durable-gset "a" :store-config {:backend :memory :id (random-uuid)}) (g/add :x))
          b (-> (g/durable-gset "b" :store-config {:backend :memory :id (random-uuid)}) (g/add :y))]
      (is (= #{:x :y} (g/elements (ys/ygg-merge-fn a b)))
          "convergent join, not LWW — both sides survive"))))
