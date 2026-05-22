(ns org.replikativ.spindel.engine.generation-staleness-test
  "Verifies §2.7 of docs/engine-formalism.md — the conjectured
  'generation staleness on truncate-re-tracked continuations'.

  A track continuation captures its signal's :generation at creation time
  as :consumed-generation. get-track-value-if-newer delivers real deltas
  only when the signal's *current* generation exceeds that captured value;
  otherwise it delivers a no-delta interval (the change was already seen).

  Scenario under test: a spin tracks signal A, then signal B. When B
  changes, the body resumes from B's continuation; truncate-stale-conts!
  KEEPS A's continuation (it has a lower :order) and re-tracks its signal
  dependency — but does NOT refresh A's :consumed-generation.

  The conjecture (engine-formalism §2.7): A's kept continuation could
  therefore carry a stale :consumed-generation.

  This test pins the actual behavior. The expectation: a kept continuation
  is only ever kept *un-replaced* while its own signal is unchanged — and
  :consumed-generation equals the signal's generation at capture — so the
  capture is still accurate, and A's next change is delivered correctly.
  A failure here would CONFIRM §2.7 as a real bug."
  (:require #?(:clj [clojure.test :refer [deftest is testing]])
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.effects.track :refer [track]]))

#?(:clj
   (defn- track-cont-for
     "The track continuation registered on spin `tid` for `signal-ref`."
     [tid signal-ref]
     (->> (vals (ec/get-state [:track-subscriptions tid]))
          (filter #(= (:signal-id %) (:id signal-ref)))
          first)))

#?(:clj
   (defn- signal-generation [signal-ref]
     (:generation (ec/get-state [:nodes (:id signal-ref)]))))

#?(:clj
   (deftest kept-cont-consumed-generation-stays-consistent
     (testing "a track continuation kept + re-tracked by truncate-stale-conts!
              (because an unrelated signal resumed the body) retains a
              :consumed-generation consistent with its own — unchanged —
              signal, and that signal's next change is delivered correctly"
       (let [ctx-root (ctx/create-execution-context)
             hold (atom nil)]
         (try
           (binding [ec/*execution-context* ctx-root]
             (let [s-a (sig/signal 0)
                   s-b (sig/signal 0)
                   obs (spin
                        (let [{a :new} (track s-a)
                              {b :new} (track s-b)]
                          [a b]))
                   _   (reset! hold obs)
                   tid (spin-core/spin-id obs)]
               (is (= [0 0] @obs) "initial value")
               (simple/await-drain-complete! ctx-root :timeout-ms 2000)

               ;; A's continuation captures A's generation at creation.
               (is (= (signal-generation s-a)
                      (:consumed-generation (track-cont-for tid s-a)))
                   "A cont's :consumed-generation matches A's generation initially")

               ;; Change B. The resume runs from B's continuation;
               ;; truncate-stale-conts! keeps A's continuation (lower :order)
               ;; and re-tracks it — this is the §2.7 path.
               (reset! s-b 1)
               (simple/await-drain-complete! ctx-root :timeout-ms 2000)

               ;; §2.7: the kept A continuation must still carry a
               ;; :consumed-generation consistent with A's (unchanged)
               ;; generation — otherwise A's deltas would be mis-gated.
               (is (some? (track-cont-for tid s-a))
                   "A continuation survives the B-change resume")
               (is (= (signal-generation s-a)
                      (:consumed-generation (track-cont-for tid s-a)))
                   "A cont's :consumed-generation is NOT stale after the B resume")

               ;; A's next change must be delivered through the kept cont.
               (reset! s-a 10)
               (simple/await-drain-complete! ctx-root :timeout-ms 2000)
               (is (= [10 1] @obs)
                   "an A change after the B resume is delivered")

               ;; And the kept-then-fired continuation keeps working.
               (reset! s-a 20)
               (simple/await-drain-complete! ctx-root :timeout-ms 2000)
               (is (= [20 1] @obs)
                   "subsequent A changes keep working")
               (is (some? @hold))))
           (finally
             (reset! hold nil)
             (ctx/close-context! ctx-root)))))))
