(ns org.replikativ.spindel.engine.cont-cancellation-test
  "Regression test for the orphaned-callback double-execution bug
  (stage 4 of the experiment/unified-subscription-model branch).

  Scenario: a parent body has `(track A)` early, then `(await deferred)`.
  When signal A changes while the body is suspended on the deferred,
  `resume-single-observer!` truncates conts with `:order` greater than
  the track-cont — including the engine-side await cont. But the
  deferred's `:pending` list still holds the parent body's raw resolve
  closure. When the deferred is later delivered, that orphaned closure
  fires AND the new closure (registered by the parent's re-run body)
  fires. Both advance their body slices to outer-resolve, double-running
  any side effects.

  Stage 4 fix: every external-await (`await-deferred`, `await-mailbox`,
  the plain-fn awaitable path) wraps resolve/reject with a cancellation
  gate. The associated engine cont owns the gate via `:cancel!`. All
  cont-removal sites in the engine (`resume-single-observer!`,
  `re-execute-dirty-parent!`, `clear-all-await-continuations!`,
  `clear-deps!`, `full-cleanup-spin!`) call `:cancel!` on every removed
  cont before dissociating. The orphaned closure becomes a no-op."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.effects.await :refer [await]]))

(deftest no-double-side-effect-after-track-resume-mid-deferred-await
  (testing "When a parent body's track-cont is resumed mid `(await deferred)`,
            and the deferred is later delivered, the parent body's outer
            resolve fires EXACTLY ONCE, not twice. The orphaned resolve
            held in the deferred's :pending list is no-op'd by the
            cancellation gate."
    (let [ctx-root (ctx/create-execution-context)
          hold (atom [])]
      (try
        (binding [ec/*execution-context* ctx-root]
          (let [s (sig/signal :initial)
                gate (sync/deferred)
                ;; The side effect we want to verify fires exactly once.
                side-effect-count (atom 0)
                obs (spin
                      (let [{tracked :new} (track s)
                            _gate-val (await gate)]
                        (swap! side-effect-count inc)
                        tracked))
                _ (swap! hold conj obs)
                tid (spin-core/spin-id obs)]
            ;; First run: body suspends at (await gate).
            (obs identity identity)
            (is (zero? @side-effect-count)
                "body suspended before any external event")

            ;; Change signal mid-suspend. resume-single-observer
            ;; truncates the await cont (cancellation gate flips).
            (reset! s :changed)
            (simple/await-drain-complete! ctx-root :timeout-ms 2000)
            (is (zero? @side-effect-count)
                "body re-suspended at the new (await gate); no completion yet")

            ;; Deliver the gate. The deferred's :pending now holds TWO
            ;; resolve closures: the OLD one (orphaned, cancellation gate
            ;; @true) and the NEW one (cancellation gate @false). Only
            ;; the NEW one should advance the body to the swap! call.
            (sync/deliver! gate :gate-released)
            (simple/await-drain-complete! ctx-root :timeout-ms 2000)

            (is (= 1 @side-effect-count)
                "side effect fired EXACTLY ONCE despite two pending
                 resolve closures on the deferred")))
        (finally
          (reset! hold [])
          (ctx/close-context! ctx-root))))))
