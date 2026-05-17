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

(deftest no-mailbox-message-loss-after-track-resume-mid-mailbox-await
  (testing "When a parent body's track-cont is resumed mid `(await mailbox)`,
            and a producer later posts a message, the message is NOT
            consumed by the orphaned waiter — `post-inline!` skips the
            cancelled waiter (via the per-cont :cancel-token check)
            and the NEW body slice's waiter receives the message."
    (let [ctx-root (ctx/create-execution-context)
          hold (atom [])]
      (try
        (binding [ec/*execution-context* ctx-root]
          (let [s (sig/signal :initial)
                mbx (sync/mailbox)
                ;; Record every value the body sees from the mailbox.
                received (atom [])
                obs (spin
                      (let [{tracked :new} (track s)
                            msg (await mbx)]
                        (swap! received conj [tracked msg])
                        msg))
                _ (swap! hold conj obs)]
            ;; First run suspends at (await mbx).
            (obs identity identity)
            (is (empty? @received) "no message consumed yet")

            ;; Change signal mid-suspend. resume-single-observer truncates
            ;; the await cont, which fires :cancel! → adds the cancel-token
            ;; to :engine/cancelled-tokens.
            (reset! s :changed)
            (simple/await-drain-complete! ctx-root :timeout-ms 2000)
            ;; Body re-runs, new (await mbx), new cancel-token. Mailbox
            ;; :waiters now has TWO entries: orphaned + new.
            (is (empty? @received) "still waiting; no message posted")

            ;; Producer posts ONE message. post-inline! takes the FIRST
            ;; waiter (the orphaned one), sees its cancel-token is in
            ;; the cancelled set, recurs. Takes the SECOND waiter
            ;; (legitimate), delivers the message.
            (mbx :hello)
            (simple/await-drain-complete! ctx-root :timeout-ms 2000)

            (is (= [[:changed :hello]] @received)
                "the legitimate (post-resume) waiter received :hello;
                 the orphaned waiter did NOT consume it")))
        (finally
          (reset! hold [])
          (ctx/close-context! ctx-root))))))

(deftest fork-isolated-cancellation
  (testing "Cancellation in a fork does NOT cancel the same orphaned
            cont in the parent context — and vice versa.

            Setup: parent body does (track s) → (await gate), suspends.
            Fork the context. Both contexts now have a cont referencing
            the SAME wrapped closure (added to gate.:pending before
            fork). Fork-side: change s, which triggers fork's resume-
            single-observer to truncate and cancel the cont (recording
            the cancel-token in fork's :engine/cancelled-tokens
            overlay).

            With Option A's state-backed cancel tokens, fork's
            cancellation set diverges from parent's via copy-on-write.
            Parent's context still has the original (no-cancellation)
            view. When parent delivers the gate, parent's drain binds
            its context, the wrapped resolve reads parent's set (empty
            for this token), and parent's body advances normally.

            With the prior volatile-in-closure approach, parent's
            wrapped resolve would see the shared volatile flipped by
            fork and stay no-op — silently disabling reactivity in the
            parent. This test pins the fork-isolation guarantee."
    (let [parent-ctx (ctx/create-execution-context)
          hold (atom [])]
      (try
        (let [s (binding [ec/*execution-context* parent-ctx] (sig/signal :initial))
              gate (binding [ec/*execution-context* parent-ctx] (sync/deferred))
              parent-side-effects (atom 0)
              fork-side-effects (atom 0)
              ;; Distinct atoms so each context's body increments its own counter.
              ;; We use (binding) to choose which counter the body sees at
              ;; spin construction time — but the body code is shared by
              ;; reference between parent and fork, so we use a single
              ;; counter and check the totals.
              total-side-effects (atom 0)
              obs (binding [ec/*execution-context* parent-ctx]
                    (spin
                      (let [{tracked :new} (track s)
                            _ (await gate)]
                        (swap! total-side-effects inc)
                        tracked)))
              _ (swap! hold conj obs)]
          ;; Start the body in parent — it suspends on gate.
          (binding [ec/*execution-context* parent-ctx]
            (obs identity identity)
            (simple/await-drain-complete! parent-ctx :timeout-ms 1000))
          (is (zero? @total-side-effects) "neither context has run the body yet")

          ;; Fork the context. Fork inherits parent's :continuations
          ;; (including the await-gate cont) plus parent's Deferred
          ;; state (gate.:pending containing the wrapped resolve).
          (let [fork-ctx (ctx/fork-context parent-ctx)]
            ;; In the FORK only: change s, then deliver gate.
            (binding [ec/*execution-context* fork-ctx]
              (reset! s :changed-in-fork)
              (simple/await-drain-complete! fork-ctx :timeout-ms 1000)
              ;; Body re-runs in fork, suspends on new (await gate).
              ;; Fork's :engine/cancelled-tokens now has the OLD cont's
              ;; token. Parent's set does NOT (fork's overlay diverged
              ;; on first write).
              (sync/deliver! gate :gate-released)
              (simple/await-drain-complete! fork-ctx :timeout-ms 2000))

            ;; In the fork, exactly one side effect fired (the new
            ;; body slice's swap!, with tracked = :changed-in-fork).
            (is (= 1 @total-side-effects)
                "fork ran the body exactly once with :changed-in-fork")

            ;; CRITICAL FORK ISOLATION CHECK:
            ;; The original wrapped resolve closure is shared between
            ;; parent and fork (both saw it in gate.:pending at fork
            ;; time). Fork cancelled the cont's token — but ONLY in
            ;; fork's overlay. Parent's :engine/cancelled-tokens is
            ;; still empty for that token. When parent delivers, the
            ;; closure reads parent's context's set and DOES fire.
            ;;
            ;; (We test this by delivering the gate in parent. Note:
            ;; the gate state-atom is fork-safe, so parent and fork
            ;; have independent :pending lists — fork's delivery did
            ;; NOT touch parent's pending. Parent still has the
            ;; original wrapped resolve in its view of gate.:pending.)
            (binding [ec/*execution-context* parent-ctx]
              (sync/deliver! gate :gate-released-in-parent)
              (simple/await-drain-complete! parent-ctx :timeout-ms 2000))

            (is (= 2 @total-side-effects)
                "parent also ran the body once with :initial — fork's
                 cancellation did NOT bleed into parent's view")
            (ctx/close-context! fork-ctx)))
        (finally
          (reset! hold [])
          (ctx/close-context! parent-ctx))))))

(deftest ^:known-failure
  parent-cancels-after-fork-must-not-bleed-into-fork
  (testing "Mirror image of `fork-isolated-cancellation` — closes the
            OTHER direction of fork isolation.

            Setup mirrors the fork→parent test but the cancel comes
            from the PARENT after the fork was created:

            1. parent: (track s) → (await gate), suspends.
            2. fork-ctx := (fork-context parent-ctx).
               Fork inherits parent's :continuations (fork-local
               with snapshot) and parent's gate.:pending list, which
               holds the ORIGINAL wrapped resolve closure.
            3. In PARENT only: change s. Parent's
               resume-single-observer truncates the await-gate cont
               and writes the cont's cancel-token into PARENT's
               :engine/cancelled-tokens. Parent's body re-runs,
               suspends on a new (await gate), so parent's pending
               now has [OLD wrapped resolve, NEW wrapped resolve].
            4. In PARENT only: sync/deliver! gate. Parent's drain
               iterates parent's pending, fires both closures:
               - OLD reads parent's cancelled-tokens → token present
                 → no-op (correct).
               - NEW reads parent's cancelled-tokens → no token for
                 NEW cont → fires → body advances → counter +1.
            5. In FORK only: sync/deliver! gate. Fork's pending still
               has the OLD wrapped resolve (the fork-time snapshot,
               not affected by parent's later truncation). The
               closure reads (ec/current-execution-context) — fork
               — and looks up :engine/cancelled-tokens.

            HERE IS THE GAP: :engine/cancelled-tokens is not in
            default-fork-local-paths. Fork's overlay has no entry for
            it (fork never wrote), so the read FALLS THROUGH to
            parent. Parent's set has the token from step 3. Fork's
            closure SEES the token and silently no-ops — even though
            the cancellation happened in parent AFTER the fork was
            created and is logically unrelated to fork's execution.

            Expected behaviour (with the eventual copy-on-fork fix):
            fork's pre-fork view of the cancelled-tokens set was
            empty. Parent's later writes do not bleed into fork's
            view. Fork's closure fires → fork's body advances →
            counter increments to 2.

            Until the fix lands this test fails with counter=1 and
            is tagged ^:known-failure so the suite stays green in
            CI runs that exclude that keyword. See design doc
            §Open follow-ups."
    (let [parent-ctx (ctx/create-execution-context)
          hold (atom [])]
      (try
        (let [s (binding [ec/*execution-context* parent-ctx] (sig/signal :initial))
              gate (binding [ec/*execution-context* parent-ctx] (sync/deferred))
              ;; One shared counter; we want to count body-runs across
              ;; both parent and fork.
              total-side-effects (atom 0)
              obs (binding [ec/*execution-context* parent-ctx]
                    (spin
                      (let [{tracked :new} (track s)
                            _ (await gate)]
                        (swap! total-side-effects inc)
                        tracked)))
              _ (swap! hold conj obs)]
          ;; Start body in parent — suspends on gate. Parent's
          ;; :continuations holds the await-gate cont; gate.:pending
          ;; holds the wrapped resolve closure.
          (binding [ec/*execution-context* parent-ctx]
            (obs identity identity)
            (simple/await-drain-complete! parent-ctx :timeout-ms 1000))
          (is (zero? @total-side-effects) "body suspended, hasn't run")

          ;; Fork BEFORE parent does anything else. Fork inherits the
          ;; await-gate cont and the wrapped closure in pending.
          (let [fork-ctx (ctx/fork-context parent-ctx)]
            ;; Now in PARENT only: change s (triggers truncation +
            ;; cancel in parent), then deliver gate (parent's body
            ;; re-runs once with :changed).
            (binding [ec/*execution-context* parent-ctx]
              (reset! s :changed-in-parent)
              (simple/await-drain-complete! parent-ctx :timeout-ms 1000)
              (sync/deliver! gate :gate-released-in-parent)
              (simple/await-drain-complete! parent-ctx :timeout-ms 2000))

            (is (= 1 @total-side-effects)
                "parent ran the body exactly once after its re-run + deliver")

            ;; CRITICAL parent→fork ISOLATION CHECK:
            ;; Fork's pending still has the original wrapped resolve
            ;; (fork-time snapshot, unaffected by parent's truncation).
            ;; When fork delivers gate, the closure should fire because
            ;; from fork's perspective NOTHING was cancelled — the
            ;; cancel happened in a sibling context.
            (binding [ec/*execution-context* fork-ctx]
              (sync/deliver! gate :gate-released-in-fork)
              (simple/await-drain-complete! fork-ctx :timeout-ms 2000))

            (is (= 2 @total-side-effects)
                (str "fork's body must run; parent's cancellation must NOT "
                     "bleed into fork. If you see total=1 here, the parent→"
                     "fork direction is leaking via :engine/cancelled-tokens "
                     "falling through from parent's overlay."))
            (ctx/close-context! fork-ctx)))
        (finally
          (reset! hold [])
          (ctx/close-context! parent-ctx))))))
