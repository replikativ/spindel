(ns org.replikativ.spindel.signal-cas-test
  "compare-and-set-signal! soundness + swap-await! race-freedom: a concurrent local
   swap! landing DURING the await must not be lost (it is re-merged)."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]])
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]])))

(deftest test-compare-and-set-signal
  (testing "CAS installs only when the read value is still current (identity)"
    (async done
           (with-ctx [_ctx]
             (let [s   (sig/signal :a)
                   cur @s]
               (is (false? (sig/compare-and-set-signal! s :WRONG :z))
                   "mismatched expected ⇒ no-op")
               (is (= :a @s))
               (is (true? (sig/compare-and-set-signal! s cur :b))
                   "matching expected ⇒ set")
               (is (= :b @s))
               (is (false? (sig/compare-and-set-signal! s cur :c))
                   "stale expected (already moved on) ⇒ no-op")
               (is (= :b @s))
               (done))))))

(deftest test-swap-await-remerges-concurrent-write
  (testing "a local swap! during swap-await!'s await is re-merged, not clobbered"
    (async done
           (with-ctx [_ctx]
             (let [s    (sig/signal #{})
                   gate (atom nil)
                   ;; union-join as an ASYNC f: first invocation suspends (parks its
                   ;; resolve in `gate`); the retry invocation resolves synchronously.
                   join (fn [cur item]
                          (fn [resolve _reject]
                            (if @gate
                              (resolve (conj cur item))
                              (reset! gate #(resolve (conj cur item))))))]
               (run-spin!
                (spin (await (sig/swap-await! s join :a)))
                (fn [result]
                  ;; result is the deltaable-wrapped committed value; @s is the
                  ;; canonical unwrapped invariant — both writes survived.
                  (is (= #{:a :b} (into #{} (seq result))) "swap-await! returned the re-merged value")
                  (is (= #{:a :b} @s) "signal holds both — :b was not clobbered")
                  (done))
                (fn [e] (is false (str "swap-await! errored: " e)) (done)))
               ;; swap-await! has read cur=#{} and is parked in `gate`. Land a
               ;; concurrent local write, THEN release the await: the first commit's
               ;; CAS fails (value moved #{} -> #{:b}), so f re-runs against #{:b}.
               (swap! s conj :b)
               (@gate))))))

;; =============================================================================
;; SignalRef is now watchable (IRef/IWatchable), with fork-correct egress firing.
;; =============================================================================

(deftest test-signalref-watchable-and-fork-correct
  (testing "add-watch on a SignalRef fires at the commit site; a fork's own watcher
            fires for the fork's mutation and the parent's stays silent (no leak)"
    (async done
           (with-ctx [root]
             (let [s    (sig/signal 0)
                   rc   (clojure.core/atom [])
                   fc   (clojure.core/atom [])]
               (add-watch s :root (fn [_ _ o n] (clojure.core/swap! rc conj [o n])))
               (let [fork (ctx/fork-context root)]
                 (binding [ec/*execution-context* fork]
                   (add-watch s :fk (fn [_ _ o n] (clojure.core/swap! fc conj [o n])))
                   (swap! s inc))                 ; fork: 0 -> 1
                 (is (= [] @rc) "parent watcher silent on fork mutation (no egress leak)")
                 (is (= [[0 1]] @fc) "fork's own watcher fired"))
               (swap! s inc)                       ; root: 0 -> 1
               (is (= [[0 1]] @rc) "parent watcher fires on its own mutation")
               (done))))))
