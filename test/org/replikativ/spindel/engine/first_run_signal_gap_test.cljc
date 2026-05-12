(ns org.replikativ.spindel.engine.first-run-signal-gap-test
  "Documents the 'first-run signal-change gap' in spindel's reactive
  graph. This test PASSES on the current (buggy) behavior — it is a
  fingerprint of an open design bug we have characterized but not yet
  closed. Update the assertions when the bug is fixed.

  The gap: a spin's body has `(track A)` early then `(await
  some-deferred)` which suspends. The body has NOT yet called its outer
  resolve, so `record-deps!` has NOT yet committed. The track-cont for
  signal A exists in `:continuations` and `:subscriptions[[:signal sid]]`,
  but the spin is NOT yet in `:nodes[A]:observers`.

  `process-event!` for `:signal-change` reads `:nodes[sid]:observers`
  ONLY (via `ordered-observers`, graph.cljc:75) and then iterates that
  set in `observers-with-conts` (simple.cljc:495). A spin not in
  observers never has its cont consulted, so the signal change is
  effectively dropped for this spin's track cont.

  Symptom: when the await later resolves and the body completes, the
  spin's :result reflects the SIGNAL VALUE AT TRACK TIME, not the value
  at body-completion time. The spin's observer registration is now in
  place (record-deps! ran), so SUBSEQUENT signal changes propagate —
  but the change during the first suspend is silently lost.

  An earlier fix attempt (union :subscriptions into signal-change
  observers) revealed a separate Phase 2 deadlock: `process-event!`
  :signal-change blocks on `batch-take!` until every resumed observer
  produces a :spin-completion event. If a resumed observer's body
  suspends on a Deferred, no completion event arrives during the
  current drain — the subsequent :deferred-delivery sits in
  :engine/pending which Phase 2 doesn't poll, and the drain hangs.
  This is a latent issue for ANY observer (committed or not) that
  suspends on a Deferred during a signal-change resume, not just for
  first-run spins. Closing the gap will require addressing this too —
  candidate paths: (a) don't add subscription-only spins to
  resumed-observers so Phase 2 doesn't wait on them; (b) make Phase 2
  pump :engine/pending events while it waits; (c) abandon the
  subscriptions-union approach in favor of a body-completion
  generation-check (at record-deps!, if any tracked signal advanced
  since track time, re-enqueue :signal-change so the now-registered
  cont fires)."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.engine.nodes :as nodes]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.effects.await :refer [await]]))

(defn- signal-observers [signal-ref]
  (let [id (:id signal-ref)
        node (ec/get-state [:nodes id])]
    (or (when node (nodes/get-observers node)) #{})))

(deftest ^{:doc "Fingerprints the first-run signal-change gap. Asserts
                CURRENT (buggy) behavior, NOT desired behavior. When
                the gap is closed, change `:initial` to
                `:changed-during-suspend`."}
  first-run-signal-change-during-await-suspend
  (testing "Demonstrates that a signal change during a body's first-run
            suspend is silently dropped — body completes with stale
            tracked value."
    (let [ctx-root (ctx/create-execution-context)
          hold (atom [])]
      (try
        (binding [ec/*execution-context* ctx-root]
          (let [s (sig/signal :initial)
                gate (sync/deferred)
                seen (atom nil)
                obs (spin
                      (let [{tracked :new} (track s)
                            _gate-val (await gate)]
                        (reset! seen tracked)
                        tracked))
                _ (swap! hold conj obs)
                tid (spin-core/spin-id obs)]
            ;; Kick off the body — it tracks s, then suspends on gate.
            (obs identity identity)
            (is (nil? @seen) "body suspended before reset!")
            (is (not (contains? (signal-observers s) tid))
                "spin NOT in :observers yet — record-deps! has not fired")

            ;; Change the signal during the first-run suspend.
            (reset! s :changed-during-suspend)
            (simple/await-drain-complete! ctx-root :timeout-ms 2000)

            ;; Release the gate. Body should resume and complete.
            (sync/deliver! gate :gate-released)
            (simple/await-drain-complete! ctx-root :timeout-ms 2000)

            ;; CURRENT BEHAVIOR (the gap): body completes with the
            ;; signal value captured at track time, NOT the value the
            ;; signal has when the body resumes. Change to
            ;; `:changed-during-suspend` once the bug is fixed.
            (is (= :initial @seen)
                "GAP DEMO: body sees stale signal value because no fix
                yet for the first-run signal-change drop")

            ;; After body completion, the observer IS now registered,
            ;; so future changes propagate normally.
            (is (contains? (signal-observers s) tid)
                "spin is observer of s after first body completion")

            (reset! s :after-completion)
            (simple/await-drain-complete! ctx-root :timeout-ms 2000)
            (is (= :after-completion @seen)
                "post-completion changes propagate normally")))
        (finally
          (reset! hold [])
          (ctx/close-context! ctx-root))))))
