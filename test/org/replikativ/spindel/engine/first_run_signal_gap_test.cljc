(ns org.replikativ.spindel.engine.first-run-signal-gap-test
  "Regression test for the FIRST-RUN SIGNAL-CHANGE GAP.

  Scenario: a spin's body has `(track A)` early then `(await some-deferred)`
  which suspends. The body has NOT yet called its outer resolve, so under
  the old (two-stage) design, `record-deps!` would NOT have committed and
  the spin was NOT yet in `:nodes[A]:observers`. The signal-change
  handler reads observers, so the change was silently dropped — when the
  await later resolved and the body completed, the body would see the
  signal value at TRACK time, not the value at body-completion time.

  Under the UNIFIED-SUBSCRIPTION design (this experiment branch),
  observer registration is EAGER: `track-signal-dep!` adds the spin to
  `signal.observers` at the moment of the `(track ...)` call. The gap
  closes: a signal change during a first-run suspend resumes the cont
  and the body completes with the FRESH value.

  This test asserts the post-fix behavior. If you ever revert eager
  observer registration, these assertions will catch it."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.nodes :as nodes]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.test-helpers :refer [async with-ctx await-engine-idle!]]
            #?(:clj [org.replikativ.spindel.spin.cps :refer [spin]]))
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]]
                            [org.replikativ.spindel.test-helpers :refer [async with-ctx]])))

(defn- signal-observers [signal-ref]
  (let [id (:id signal-ref)
        node (ec/get-state [:nodes id])]
    (or (when node (nodes/get-observers node)) #{})))

(deftest first-run-signal-change-during-await-suspend
  (testing "Signal change during a body's first-run suspend reaches
            the spin via eager observer registration; body completes
            with the fresh signal value."
    (async done
           (with-ctx [ctx-root]
             (let [s (sig/signal :initial)
                   gate (sync/deferred)
                   seen (atom nil)
                   obs (spin
                        (let [{tracked :new} (track s)
                              _gate-val (await gate)]
                          (reset! seen tracked)
                          tracked))
                   tid (spin-core/spin-id obs)]
          ;; Kick off the body — it tracks s, then suspends on gate.
               (obs identity identity)
               (await-engine-idle! ctx-root
                                   (fn []
              ;; Body suspended on gate. Tracked-but-not-yet-completed.
                                     (is (nil? @seen) "body suspended before any external change")
              ;; UNIFIED-SUBSCRIPTION: spin is in observers immediately.
                                     (is (contains? (signal-observers s) tid)
                                         "spin IS in :observers after (track s) — eager registration")

              ;; Change the signal during the first-run suspend.
                                     (reset! s :changed-during-suspend)
                                     (await-engine-idle! ctx-root
                                                         (fn []
                  ;; Release the gate. Body should resume and complete with
                  ;; the FRESH signal value (gap closed).
                                                           (sync/deliver! gate :gate-released)
                                                           (await-engine-idle! ctx-root
                                                                               (fn []
                                                                                 (is (= :changed-during-suspend @seen)
                                                                                     "body sees FRESH signal value — gap closed")
                                                                                 (is (contains? (signal-observers s) tid)
                                                                                     "spin remains observer of s after first body completion")
                      ;; Post-completion: subsequent changes propagate normally.
                                                                                 (reset! s :after-completion)
                                                                                 (await-engine-idle! ctx-root
                                                                                                     (fn []
                                                                                                       (is (= :after-completion @seen)
                                                                                                           "post-completion changes propagate normally")
                                                                                                       (done))))))))))))))
