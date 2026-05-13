(ns org.replikativ.spindel.engine.eager-spin-observer-test
  "Symmetric to first-run-signal-gap-test: verifies that the parent of an
  awaited child is registered as a child.observers entry IMMEDIATELY at
  `(await child)`, not at parent body completion. This is the spin-side
  half of the unified-subscription design (stage 3 of the
  experiment/unified-subscription-model branch).

  Under the old two-stage design, child.observers got the parent
  registered only when `record-deps!` ran at the parent's body resolve.
  Until then, a child completion would mark observers dirty via
  `cache-result!`'s observer-iteration — and miss in-flight parents
  whose body had reached `(await child)` but not yet resolved."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.engine.nodes :as nodes]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.effects.await :refer [await]]))

(defn- spin-observers [tid]
  (let [node (ec/get-state [:nodes tid])]
    (or (when node (nodes/get-observers node)) #{})))

(deftest parent-registers-as-child-observer-at-await
  (testing "When a parent body hits `(await child)`, the parent is
            immediately listed in `child.observers` — before the
            parent's body resolves."
    (let [ctx-root (ctx/create-execution-context)
          hold (atom [])]
      (try
        (binding [ec/*execution-context* ctx-root]
          (let [gate (sync/deferred)
                child (spin (await gate))         ; child awaits the gate
                parent (spin (await child))       ; parent awaits the child
                child-id (spin-core/spin-id child)
                parent-id (spin-core/spin-id parent)]
            (swap! hold conj child)
            (swap! hold conj parent)

            ;; Kick off parent — its body reaches (await child), which
            ;; in turn invokes child whose body reaches (await gate).
            (parent identity identity)

            ;; Drain so any sync execution settles. The chain is now
            ;; parent → child → gate(undelivered). Neither parent nor
            ;; child has completed yet — gate hasn't been delivered.
            (simple/await-drain-complete! ctx-root :timeout-ms 1000)

            (is (contains? (spin-observers child-id) parent-id)
                "parent IS in child.observers immediately at (await child),
                 even though parent body hasn't resolved yet")

            ;; Release the gate. Cascade: child completes, parent
            ;; resumes and completes.
            (sync/deliver! gate :gate-released)
            (simple/await-drain-complete! ctx-root :timeout-ms 2000)

            (is (contains? (spin-observers child-id) parent-id)
                "parent stays in child.observers after both complete
                 (committed via record-deps!)")))
        (finally
          (reset! hold [])
          (ctx/close-context! ctx-root))))))
