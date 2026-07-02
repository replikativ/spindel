(ns org.replikativ.spindel.ygg-signal-test
  "A yggdrasil system living inside a spindel signal: mutate it with the ordinary
   signal primitives — `swap!` (sync, here — a JVM durable G-Set) / `swap-await!`
   (async, a cljs/konserve value, proven by signal-test's swap-await! tests). The
   value IS the system, read with its own ops."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.ygg-signal :as ys]
            [org.replikativ.spindel.test-helpers :refer [async with-ctx]]
            [org.replikativ.spindel.distributed.signal-sync :as ss]
            [kabel.pubsub.protocol :as proto]
            [superv.async :as sa]
            [yggdrasil.convergent :as c]
            [yggdrasil.convergent.gset :as g]))

(deftest ygg-signal-sync-swap
  (testing "a ygg-signal holds a yggdrasil system; a plain `swap!` runs a yggdrasil
            op and seats the new system (the sync path — a JVM value)"
    (async done
           (with-ctx [_ctx]
             (let [gs  (g/gset "kb" {:store-config {:backend :memory :id (random-uuid)}})
                   sig (ys/ygg-signal gs)]
               ;; a JVM system → plain `swap!` (its ops default to sync; a system
               ;; carries no mode — async-system?/sync-system? were removed).
               (swap! sig (fn [s] (g/conj s :x)))
               (swap! sig (fn [s] (g/conj s :y)))
               (is (= #{:x :y} (g/elements @sig))
                   "swap! mutated the system held in the signal")
               (done))))))

(deftest ygg-merge-fn-joins
  (testing "ygg-merge-fn JOINs two convergent system values (for signal-sync)"
    (let [a (-> (g/gset "a" {:store-config {:backend :memory :id (random-uuid)}}) (g/conj :x))
          b (-> (g/gset "b" {:store-config {:backend :memory :id (random-uuid)}}) (g/conj :y))]
      (is (= #{:x :y} (g/elements (ys/ygg-merge-fn a b)))
          "convergent join, not LWW — both sides survive"))))

(deftest convergent-join-no-op-is-identical
  (testing "issue-2 substrate: a -join that adds nothing returns the receiver
            IDENTICAL (observable lattice no-op), and a real join returns a new value"
    (let [a (-> (g/gset "a" {:store-config {:backend :memory :id (random-uuid)}}) (g/conj :x) (g/conj :y))
          b (-> (g/gset "b" {:store-config {:backend :memory :id (random-uuid)}}) (g/conj :x))
          z (-> (g/gset "z" {:store-config {:backend :memory :id (random-uuid)}}) (g/conj :z))]
      (is (identical? a (c/-join a b)) "join with a subset is a no-op → SAME object")
      (is (not (identical? a (c/-join a z))) "join that adds :z → a new value")
      (is (= #{:x :y :z} (g/elements (c/-join a z)))))))

(deftest convergent-join-no-op-no-refire
  (testing "issue-2 runaway guard: through signal-sync, a no-op convergent join
            does NOT re-commit/re-publish — mutually-synced peers don't loop
            forever re-joining equal states; a real change fires exactly once"
    (let [g       (-> (g/gset "kb" {:store-config {:backend :memory :id (random-uuid)}}) (g/conj :x))
          sig     (atom g)
          changes (atom 0)
          _       (add-watch sig :c (fn [_ _ o n] (when (not= o n) (swap! changes inc))))
          strat   (ss/->SignalSyncStrategy sig nil (fn [cur incoming] (c/-join cur incoming)) nil true nil)]
      ;; an incoming peer value that adds nothing (already contains :x)
      (let [g2 (-> (g/gset "p2" {:store-config {:backend :memory :id (random-uuid)}}) (g/conj :x))]
        (proto/-apply-publish strat {:value g2})
        (is (zero? @changes) "no-op join must NOT change the signal (no re-publish runaway)")
        (is (identical? g @sig) "the signal still holds the SAME object")
        (is (= #{:x} (g/elements @sig))))
      ;; an incoming peer value that adds :z — a real change fires exactly once
      (let [g3 (-> (g/gset "p3" {:store-config {:backend :memory :id (random-uuid)}}) (g/conj :z))]
        (proto/-apply-publish strat {:value g3})
        (is (= 1 @changes) "a real change fires exactly once")
        (is (= #{:x :z} (g/elements @sig)))))))

(deftest two-peer-op-based-sync
  (testing "OP-based peer sync (replikativ op-based, on a durable G-Set): peer A's
            local mutation ships JUST its δ; peer B applies the δ via apply-delta-fn
            and converges — WITHOUT A's full state crossing the wire, no diffing,
            and no echo of the remote op back into B's δ"
    (let [a (atom (-> (g/gset "A" {:store-config {:backend :memory :id (random-uuid)}}) (g/conj :x)))
          ;; B starts with :y already propagated (δ cleared) on its own store
          b (atom (c/clear-delta (-> (g/gset "B" {:store-config {:backend :memory :id (random-uuid)}}) (g/conj :y))))
          ;; B's subscriber strategy: OP-path apply-delta-fn (+ STATE-path merge-fn
          ;; for handshake); :sync? true (JVM durable G-Set — sync ops)
          b-strat (ss/->SignalSyncStrategy b nil ys/ygg-merge-fn ys/ygg-apply-delta-fn true nil)]
      ;; A applies a LOCAL op. The prior δ is already gone (export's :clear-delta-fn
      ;; clears each δ once shipped); modelled here by clearing inline before the op,
      ;; so the shipped δ is exactly this op.
      (swap! a (fn [v] (g/conj (c/clear-delta v) :z)))
      (let [a-op (ys/ygg-delta-fn @a)]
        (is (= #{:z} a-op) "A ships only the OP (#{:z}) — not its full state #{:x :z}")
        ;; the wire carries ONLY the δ, never A's value
        (proto/-apply-publish b-strat {:delta a-op})
        (is (= #{:y :z} (g/elements @b)) "B converged from the op alone: its :y + A's :z")
        (is (nil? (ys/ygg-delta-fn @b)) "A's op did NOT echo into B's δ (won't re-publish)")))))

(deftest export-clears-delta-after-send
  (testing "export-signal! with :clear-delta-fn drops each shipped δ, so the in-memory
            δ stays bounded (no unbounded accrual, no re-shipping the whole history);
            the `=`-preserving clear re-seat does NOT re-fire the watch"
    (let [peer (atom {:volatile {:supervisor sa/S}})  ; no subscribers ⇒ publish! sends nowhere; we test the send-side clear
          sig  (atom (g/gset "kb" {:store-config {:backend :memory :id (random-uuid)}}))]
      (ss/export-signal! peer :kb/topic sig
                         :delta-fn       ys/ygg-delta-fn
                         :clear-delta-fn ys/ygg-clear-delta-fn
                         :sync? true)
      ;; a local op accrues a δ; the watch ships it then clears it
      (swap! sig (fn [s] (g/conj s :x)))
      (is (nil? (ys/ygg-delta-fn @sig)) "δ cleared after the export shipped it")
      (is (= #{:x} (g/elements @sig)) "the value itself is intact")
      ;; a second op ships ONLY its own δ — the first did NOT accrue
      (swap! sig (fn [s] (g/conj s :y)))
      (is (nil? (ys/ygg-delta-fn @sig)) "δ cleared again — bounded across ops")
      (is (= #{:x :y} (g/elements @sig))))))
