(ns org.replikativ.spindel.engine.multi-track-observer-test
  "Regression test for the multi-track signal-observer-drop bug.

  Scenario: a spin body has N sequential `(track ...)` calls. When the K-th
  signal changes, the engine resumes from cont K. The pre-fix code captured
  cont K's tracking snapshot (`:slice-state :tracking`) BEFORE adding signal
  K to the spin's transient tracking — so on resume, the restored snap was
  missing signal K. The body slice continued from AFTER `(track signal-K)`,
  so the body never re-tracked signal K. `record-deps!` then committed deps
  without signal K, leaving the signal with no observer. Future changes of
  signal K were silently dropped.

  User-visible symptom: a tracked signal loses reactivity after the first
  re-render — downstream consumers see no further updates until a full
  re-render is forced.

  The fix in `effects/track.cljc` constructs the tracking snapshot by
  explicitly conj-ing the current signal-id onto the base snapshot,
  regardless of when the underlying `deps-track-signal!` write becomes
  visible."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.engine.nodes :as nodes]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.effects.await :refer [await]]))

(defn- signal-observer-count [signal-ref]
  (let [id (:id signal-ref)
        node (ec/get-state [:nodes id])]
    (count (or (when node (nodes/get-observers node)) #{}))))

(defn- signal-observers [signal-ref]
  (let [id (:id signal-ref)
        node (ec/get-state [:nodes id])]
    (or (when node (nodes/get-observers node)) #{})))

#?(:clj
   (deftest middle-track-signal-keeps-observer-after-resume
     (testing "When a middle-of-body tracked signal changes, the signal's
            observer registration survives the resume cycle — the spin must
            remain a listed observer of the signal."
       (let [ctx-root (ctx/create-execution-context)
             hold (atom nil)]
         (try
           (binding [ec/*execution-context* ctx-root]
             (let [s-a (sig/signal :a0)
                   s-b (sig/signal :b0)
                   s-c (sig/signal :c0)
                   obs (spin
                        (let [{a :new} (track s-a)
                              {b :new} (track s-b)
                              {c :new} (track s-c)]
                          [a b c]))
                   _   (reset! hold obs)
                   tid (spin-core/spin-id obs)]
               @obs
               (simple/await-drain-complete! ctx-root :timeout-ms 2000)

               (is (contains? (signal-observers s-a) tid) "spin observes A initially")
               (is (contains? (signal-observers s-b) tid) "spin observes B initially")
               (is (contains? (signal-observers s-c) tid) "spin observes C initially")

            ;; Change B (the middle track) - this triggers the bug path
               (reset! s-b :b1)
               (simple/await-drain-complete! ctx-root :timeout-ms 2000)

               (is (contains? (signal-observers s-a) tid)
                   "A observer survives B-change resume")
               (is (contains? (signal-observers s-b) tid)
                   "B observer survives B-change resume (this is the bug)")
               (is (contains? (signal-observers s-c) tid)
                   "C observer survives B-change resume")

            ;; Trigger B again to verify reactivity actually still works
               (reset! s-b :b2)
               (simple/await-drain-complete! ctx-root :timeout-ms 2000)

               (let [result-after (ec/spin-current-result tid)]
                 (is (some? result-after)
                     "spin has a result after second B-change"))
               (is (some? @hold))))
           (finally
             (reset! hold nil)
             (ctx/close-context! ctx-root)))))))

#?(:clj
   (deftest first-track-signal-keeps-observer-after-resume
     (testing "Resume from the FIRST track cont must not lose any observer."
       (let [ctx-root (ctx/create-execution-context)
             hold (atom nil)]
         (try
           (binding [ec/*execution-context* ctx-root]
             (let [s-a (sig/signal :a0)
                   s-b (sig/signal :b0)
                   s-c (sig/signal :c0)
                   obs (spin
                        (let [{a :new} (track s-a)
                              {b :new} (track s-b)
                              {c :new} (track s-c)]
                          [a b c]))
                   _   (reset! hold obs)
                   tid (spin-core/spin-id obs)]
               @obs
               (simple/await-drain-complete! ctx-root :timeout-ms 2000)

               (reset! s-a :a1)
               (simple/await-drain-complete! ctx-root :timeout-ms 2000)

               (is (contains? (signal-observers s-a) tid) "A keeps observer")
               (is (contains? (signal-observers s-b) tid) "B keeps observer")
               (is (contains? (signal-observers s-c) tid) "C keeps observer")
               (is (some? @hold))))
           (finally
             (reset! hold nil)
             (ctx/close-context! ctx-root)))))))

#?(:clj
   (deftest last-track-signal-keeps-observer-after-resume
     (testing "Resume from the LAST track cont must not lose any observer."
       (let [ctx-root (ctx/create-execution-context)
             hold (atom nil)]
         (try
           (binding [ec/*execution-context* ctx-root]
             (let [s-a (sig/signal :a0)
                   s-b (sig/signal :b0)
                   s-c (sig/signal :c0)
                   obs (spin
                        (let [{a :new} (track s-a)
                              {b :new} (track s-b)
                              {c :new} (track s-c)]
                          [a b c]))
                   _   (reset! hold obs)
                   tid (spin-core/spin-id obs)]
               @obs
               (simple/await-drain-complete! ctx-root :timeout-ms 2000)

               (reset! s-c :c1)
               (simple/await-drain-complete! ctx-root :timeout-ms 2000)

               (is (contains? (signal-observers s-a) tid) "A keeps observer")
               (is (contains? (signal-observers s-b) tid) "B keeps observer")
               (is (contains? (signal-observers s-c) tid) "C keeps observer")
               (is (some? @hold))))
           (finally
             (reset! hold nil)
             (ctx/close-context! ctx-root)))))))
