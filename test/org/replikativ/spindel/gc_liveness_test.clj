(ns org.replikativ.spindel.gc-liveness-test
  "JVM Cleaner vs suspended spins — the awaiter-reap regression.

   Every reactive spin registers a `java.lang.ref.Cleaner` that full-cleans
   its engine node when the Spin JAVA OBJECT becomes unreachable
   (spin/core.cljc). The engine holds a suspended spin's continuations in
   context state, but nothing holds the Spin OBJECT itself — only the user's
   local binding does, and HotSpot liveness can drop that mid-`@deref`-park
   or after the last source-level use (fire-and-forget chains).

   `try-gc-cleanup-spin!` guards observers / signal-conts / EXTERNAL awaits,
   but historically exempted SPIN-awaits (`[:spin/complete _]`) — reasoning
   that `:awaited-spin` keeps the pair reachable. That keeps the CHILD
   reachable through the parent's cont; it does nothing for the PARENT.
   A parent suspended awaiting a still-running child could thus be reaped
   alive: node + conts + subscriptions deleted, the child's completion
   dispatched into `:parent-spin-ids nil`, silently dropped — the awaiter
   never resumed, no error. Manifested as the dvergr llm-agent ask hang
   (~50 % under organic GC, deterministic with forced GC mid-turn).

   Fixed by `has-live-spin-await?`: an await cont on a NOT-yet-completed
   child marks the spin live (orphan, don't full-clean); the generation
   sweep (`clear-all-await-continuations!`) reaps completed orphans."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest testing is]]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.effects.await :refer [await]]))

(defn- build-suspended-chain!
  "Construct parent→child→deferred awaiting chain and START it CPS-style,
   delivering into `result`. Runs in its own fn scope so that on return NO
   caller-reachable reference to either Spin object remains — the engine's
   context state is the only thing keeping the suspended chain alive, which
   is exactly the condition under which the Cleaner used to reap the parent."
  [result]
  (let [d      (sync/deferred)
        child  (spin (await d))
        parent (spin (inc (await child)))]
    ;; Fire-and-forget CPS start: parent suspends awaiting child, child
    ;; suspends awaiting the deferred.
    (parent (fn [v] (deliver result [:ok v]))
            (fn [e] (deliver result [:err e])))
    d))

(deftest test-gc-does-not-reap-suspended-spin-awaiter
  (testing "a parent suspended on a spin-await survives GC of its Spin object;
            the child's eventual completion still resumes it"
    (let [c (ctx/create-execution-context)]
      (try
        (binding [ec/*execution-context* c]
          (let [result (promise)
                d      (build-suspended-chain! result)]
            ;; The parent/child Spin objects are now unreachable from user
            ;; code. Force the Cleaner's hand.
            (dotimes [_ 3] (System/gc) (Thread/sleep 100))
            ;; Deliver the external resource — must propagate child→parent.
            (sync/deliver! d 41)
            (is (= [:ok 42] (deref result 10000 ::timeout))
                "the awaiter must resume after GC; ::timeout = it was reaped alive")))
        (finally
          (ctx/stop-context! c))))))
