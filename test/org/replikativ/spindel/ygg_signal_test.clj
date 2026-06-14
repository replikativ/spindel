(ns org.replikativ.spindel.ygg-signal-test
  "A yggdrasil system living inside a spindel signal: `ygg-swap!` mutates it (sync
   path here — a JVM durable G-Set); the value is the system, read with its own
   ops. The async path (`swap-await!` for a cljs/konserve-backed value) is proven
   by signal-test's swap-await! tests + is the same dispatch."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.ygg-signal :as ys]
            [org.replikativ.spindel.test-helpers :refer [async with-ctx]]
            [org.replikativ.spindel.distributed.signal-sync :as ss]
            [kabel.pubsub.protocol :as proto]
            [yggdrasil.convergent :as c]
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

(deftest convergent-join-no-op-is-identical
  (testing "issue-2 substrate: a -join that adds nothing returns the receiver
            IDENTICAL (observable lattice no-op), and a real join returns a new value"
    (let [a (-> (g/durable-gset "a" :store-config {:backend :memory :id (random-uuid)}) (g/add :x) (g/add :y))
          b (-> (g/durable-gset "b" :store-config {:backend :memory :id (random-uuid)}) (g/add :x))
          z (-> (g/durable-gset "z" :store-config {:backend :memory :id (random-uuid)}) (g/add :z))]
      (is (identical? a (c/-join a b)) "join with a subset is a no-op → SAME object")
      (is (not (identical? a (c/-join a z))) "join that adds :z → a new value")
      (is (= #{:x :y :z} (g/elements (c/-join a z)))))))

(deftest convergent-join-no-op-no-refire
  (testing "issue-2 runaway guard: through signal-sync, a no-op convergent join
            does NOT re-commit/re-publish — mutually-synced peers don't loop
            forever re-joining equal states; a real change fires exactly once"
    (let [g       (-> (g/durable-gset "kb" :store-config {:backend :memory :id (random-uuid)}) (g/add :x))
          sig     (atom g)
          changes (atom 0)
          _       (add-watch sig :c (fn [_ _ o n] (when (not= o n) (swap! changes inc))))
          strat   (ss/->SignalSyncStrategy sig nil (fn [cur incoming] (c/-join cur incoming)) nil)]
      ;; an incoming peer value that adds nothing (already contains :x)
      (let [g2 (-> (g/durable-gset "p2" :store-config {:backend :memory :id (random-uuid)}) (g/add :x))]
        (proto/-apply-publish strat {:value g2})
        (is (zero? @changes) "no-op join must NOT change the signal (no re-publish runaway)")
        (is (identical? g @sig) "the signal still holds the SAME object")
        (is (= #{:x} (g/elements @sig))))
      ;; an incoming peer value that adds :z — a real change fires exactly once
      (let [g3 (-> (g/durable-gset "p3" :store-config {:backend :memory :id (random-uuid)}) (g/add :z))]
        (proto/-apply-publish strat {:value g3})
        (is (= 1 @changes) "a real change fires exactly once")
        (is (= #{:x :z} (g/elements @sig)))))))
