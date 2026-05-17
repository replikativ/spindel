(ns org.replikativ.spindel.inference.inference-failure-test
  "Regression test: a particle's spin failure must resolve the inference
  (re-throwing the failure to the caller) — NOT hang forever waiting for
  the coordinator to see all particles complete.

  The bug this guards against: `start-particle!`'s reject-fn used to
  just log :smc/task-failed and (throw error), never notifying the
  coordinator. KernelCoordinator gates completion on
  `barrier-count == total-particles`, incremented only by
  notify-complete!. A failed particle never reported in →
  `(:on-complete coordinator)` was never delivered → kernel-infer's
  `(await (await-completion …))` waited forever, blocking the calling
  thread AND keeping every particle context (its daemon drain thread)
  reachable. Observed in production as 14k leaked `Thread-N` and 6/8
  core.async dispatch threads parked on un-timed CountDownLatch.await.

  Fix: notify-failed! on the InferenceCoordinator protocol. The
  KernelCoordinator marks the particle :failed and delivers an
  InferenceFailure marker to on-complete (deliver-once). kernel-infer
  re-throws on the marker."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.inference.inference :as infer]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.engine.core :as rtc]
            [org.replikativ.spindel.test-helpers :refer [with-ctx]]))

(defn clean-context-fixture [f]
  (binding [rtc/*execution-context* nil]
    (f)))

(use-fixtures :each clean-context-fixture)

(deftest test-particle-failure-resolves-not-hangs
  (testing "When every particle's spin throws, smc-infer must propagate
            the failure to the caller within a bounded time — not hang
            forever waiting for completion notifications that will
            never arrive."
    (with-ctx [_ctx]
      (let [;; A model whose spin body throws — every particle fails
            ;; identically. This mirrors the production failure mode
            ;; (a broken model where `sample` runs outside spin context
            ;; and throws on every particle).
            failing-model (spin
                            (throw (ex-info "model went boom"
                                            {:reason :regression-test})))

            outer (spin
                    (try
                      (let [m (await (infer/smc-infer failing-model 3))]
                        ;; Should never reach here — the inference must
                        ;; throw the InferenceFailure rather than return
                        ;; a measure when every particle errored.
                        {:status :unexpected-success :measure m})
                      (catch Throwable t
                        {:status :threw
                         :message (ex-message t)
                         :cause-message (some-> t ex-cause ex-message)})))]

        ;; Bounded wall-clock: a regression that re-introduces the hang
        ;; would block on the inference forever. 5s is generous — the
        ;; expected path is "fail fast, the moment any particle throws"
        ;; (well under 1s with 3 particles).
        (let [result (deref outer 5000 ::timed-out)]
          (is (not= ::timed-out result)
              "smc-infer must NOT hang when particles fail")
          (when (not= ::timed-out result)
            (is (= :threw (:status result))
                (str "outer spin must propagate the inference failure, got: "
                     (pr-str result)))
            (is (re-find #"Inference failed" (str (:message result)))
                "thrown error message identifies it as an inference failure")
            (is (re-find #"boom" (str (:cause-message result)))
                "the original model error is preserved as the cause")))))))
