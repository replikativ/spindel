(ns org.replikativ.spindel.engine.await-supersession-test
  "Regression: the await slow path must run the full body re-entry
  prologue (mark-running! / clear-created-spins! / clear-prior-body-conts!
  / seed-body-chain-head!) — parity with `Spin`'s `-invoke` Case 2.

  Before the fix it only seeded the chain-head. Because track conts have
  no deterministic id (they gensym), every slow-path re-run APPENDED a new
  generation of track conts on top of the prior body's. Dispatch resumes
  the earliest cont by :order — always the STALE one — which then
  truncates the live body's conts and re-runs with its frozen lexical
  bindings ('zombie repaint'). Discovered in simmis: opening a tab (parent
  re-run with changed captures → child re-run via await slow path) and
  then firing ANY signal the column tracked reverted the column DOM to its
  pre-tab-open state while the layout signal held the new state.

  Scenario: parent tracks P and awaits a child whose body captures P's
  value lexically BEFORE tracking T. Changing P supersedes the child body
  (changed captures → dirty → await slow path). Firing T afterwards must
  resume the NEW body (fresh capture), and the child must hold exactly ONE
  track cont for T — no accumulation."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]])
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]))

#?(:clj
   (defn- track-conts-for
     "All track conts registered on spin `tid` for `signal-ref`."
     [tid signal-ref]
     (->> (vals (ec/get-state [:track-subscriptions tid]))
          (filterv #(= (:signal-id %) (:id signal-ref))))))

#?(:clj
   (deftest superseded-await-child-does-not-zombie
     (testing "after a parent re-run supersedes an awaited child (changed
              captures → await slow path), firing the child's tracked
              signal resumes the NEW body, not the stale one"
       (let [ctx-root (ctx/create-execution-context)
             hold (atom nil)]
         (try
           (binding [ec/*execution-context* ctx-root]
             (let [s-p (sig/signal :old)      ; parent-owned capture source
                   s-t (sig/signal 0)         ; child-tracked signal
                   runs (atom [])             ; [label t] per child body slice
                   child-id (atom nil)
                   parent (spin
                           (let [{p :new} (track s-p)
                                 c (spin
                                    (let [{t :new} (track s-t)]
                                      ;; `p` is captured lexically BEFORE the
                                      ;; track point — the zombie's frozen value
                                      (swap! runs conj [p t])
                                      [p t]))]
                             (reset! child-id (spin-core/spin-id c))
                             (await c)))
                   _ (reset! hold parent)]
               (is (= [:old 0] @parent) "initial value")
               (simple/await-drain-complete! ctx-root :timeout-ms 2000)

               ;; Supersede: P changes → parent re-runs → child re-created
               ;; with changed captures → re-run via the await SLOW path.
               (reset! s-p :new)
               (simple/await-drain-complete! ctx-root :timeout-ms 2000)
               (is (= [:new 0] @parent) "supersession delivered")

               ;; The child must hold exactly ONE track cont for T. Before
               ;; the fix the stale body's cont survived alongside the new
               ;; one (2 conts), and being earlier by :order it won dispatch.
               (is (= 1 (count (track-conts-for @child-id s-t)))
                   "no track-cont accumulation across slow-path re-runs")

               ;; Fire the child's tracked signal: the NEW body must resume.
               (reset! s-t 1)
               (simple/await-drain-complete! ctx-root :timeout-ms 2000)
               (is (= [:new 1] @parent)
                   "post-supersession T change resumes the NEW body")
               (is (not-any? #(= % [:old 1]) @runs)
                   "the stale body (frozen :old capture) never re-ran")

               ;; And the lineage keeps working.
               (reset! s-t 2)
               (simple/await-drain-complete! ctx-root :timeout-ms 2000)
               (is (= [:new 2] @parent) "subsequent T changes keep working")
               (is (some? @hold))))
           (finally
             (reset! hold nil)
             (ctx/close-context! ctx-root)))))))
