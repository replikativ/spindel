(ns org.replikativ.spindel.engine.finalization-state-test
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.atom :as ratom]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.effects.await :refer [await await-finalization]]
            [org.replikativ.spindel.spin.core :as sc]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin! await-engine-idle!]]
            [is.simm.partial-cps.async :as cps]))

(defn exercise-finalization [cancel-body? await-child? done]
  (with-ctx [ctx]
    (let [blocker (sync/deferred)
          trace (atom []) observed (atom []) callback (atom nil) fresh-result (atom nil)
          s (spin
             (let [cell (ratom/atom 41)]
               (try
                 (if cancel-body? (await blocker) :normal-result)
                 (finally
                   (swap! trace conj [:before @cell])
                   (await-finalization (fn [resolve _reject] (reset! callback resolve)))
                   (swap! cell inc)
                   (swap! trace conj [:after @cell
                                      (ec/same-world? ctx (ec/current-execution-context))])))))
          driver (if await-child? (spin (await s)) s)]
      ;; The original invocation may finish its rejection path after cleanup.
      ;; A fresh observer must see cancellation while that path is still parked.
      (run-spin! driver #(swap! observed conj [:success %])
                 #(swap! observed conj [:error (:type (ex-data %))]))
      (await-engine-idle!
       ctx
       (fn []
         (when cancel-body? (sc/cancel-spin! s))
         (await-engine-idle!
          ctx
          (fn []
            (is (= [[:before 41]] @trace))
            (is (fn? @callback))
            (when-not cancel-body? (sc/cancel-spin! s))
            (sc/cancel-spin! s)
            (is (sc/spin-cancelled? s))
            (run-spin! s #(reset! fresh-result [:success %])
                       #(reset! fresh-result [:error (:type (ex-data %))]))
            (await-engine-idle!
             ctx
             (fn []
               (is (= [:error ::sc/spin-cancelled] @fresh-result))
               (is (= [[:before 41]] @trace)
                   "repeated cancellation did not truncate or restart finalization")
               (if-let [resume @callback]
                 (do
                   (binding [cps/*in-trampoline* false]
                     (resume :cleanup-finished))
                   (await-engine-idle!
                    ctx
                    (fn []
                      (is (= [[:before 41] [:after 42 true]] @trace))
                      (is (sc/spin-cancelled? s) "cleanup cannot replace cached cancellation")
                      (is (= [[:error ::sc/spin-cancelled]] @observed)
                          "the original invocation rejects once with the authoritative cancellation")
                      (done))))
                 (done)))))))))))

(deftest cancellation-retains-owned-state-through-asynchronous-finally
  (async done (exercise-finalization true false done)))

(deftest cancellation-preserves-finalization-already-started-on-success-path
  (async done (exercise-finalization false false done)))

(deftest direct-await-slow-path-preserves-cancellation-during-success-finalization
  (async done (exercise-finalization false true done)))

(deftest cancellation-fencing-ends-only-at-a-fresh-generation
  (with-ctx [ctx]
    (let [s (spin :unused) sid (sc/spin-id s)
          run (simple/mark-running! ctx sid)
          cancellation (sc/error (ex-info "cancelled" {:type ::sc/spin-cancelled}))
          proposal (sc/ok :must-not-publish)]
      (simple/cancel-result! ctx sid cancellation)
      (is (identical? cancellation (simple/commit-result! ctx sid proposal run)))
      (is (identical? cancellation (simple/commit-result! ctx sid proposal)))
      (is (identical? cancellation (ec/spin-current-result sid)))
      (let [fresh (simple/mark-running! ctx sid) result (sc/ok :fresh)]
        (is (not= run fresh))
        (is (nil? (simple/commit-result! ctx sid proposal run)))
        (is (identical? result (simple/commit-result! ctx sid result fresh)))
        (is (identical? result (ec/spin-current-result sid)))))))

(deftest propagated-cancellation-does-not-fence-reactive-cache-recovery
  (with-ctx [ctx]
    (let [s (spin :unused) sid (sc/spin-id s)
          run (simple/mark-running! ctx sid)
          child-cancel (sc/error (ex-info "child cancelled" {:type ::sc/spin-cancelled :spin-id :child}))
          recovered (sc/ok :recovered)]
      (is (ec/spin-cache-result! sid child-cancel))
      (is (identical? recovered (simple/commit-result! ctx sid recovered)))
      (is (identical? recovered (ec/spin-current-result sid)))
      (is (identical? recovered (simple/commit-result! ctx sid recovered run))))))
