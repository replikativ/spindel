(ns org.replikativ.spindel.inference.world-particles-test
  "Canonical Yggdrasil worlds for effectful inference particles."
  (:refer-clojure :exclude [await])
  (:require [anglican.runtime :as ar]
            [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.executor :as executor]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.state-backend :as backend]
            [org.replikativ.spindel.inference.coordinator :as coordinator]
            [org.replikativ.spindel.inference.effects :refer [observe]]
            [org.replikativ.spindel.inference.inference :as inference]
            [org.replikativ.spindel.inference.kernel :as kernel]
            [org.replikativ.spindel.inference.measure :as measure]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.yggdrasil :as ygg]
            [yggdrasil.convergent.gset :as g]))

(defn- mem-gset [id]
  (g/gset id {:store-config {:backend :memory :id (random-uuid)}}
          {:sync? true}))

(defn- observed-model []
  (spin
   (observe (ar/normal 0.0 1.0) 0.0 :id :evidence)
   :done))

(defn- await-cps [operation]
  (let [result (promise)]
    (operation #(deliver result [:ok %])
               #(deliver result [:error %]))
    (deref result 5000 ::timed-out)))

(deftest smc-resamples-independent-worlds-and-discards-the-tree
  (let [root (context/create-execution-context)
        manager* (atom nil)
        create-manager coordinator/create-world-manager]
    (try
      (binding [ec/*execution-context* root]
        (let [knowledge
              (ygg/register! (-> (mem-gset "particle-kb")
                                 (g/conj :root {:sync? true})))
              model
              (spin
               (let [particle-id
                     (rtp/get-state ec/*execution-context*
                                    [:inference :particle-id])
                     _ (reset! (ygg/system-signal "particle-kb")
                               (g/conj @knowledge particle-id {:sync? true}))
                     _ (observe (ar/normal 0.0 1.0) 0.0 :id :evidence)]
                 (g/elements @knowledge {:sync? true})))
              posterior
              (with-redefs
               [coordinator/create-world-manager
                (fn [opts]
                  (let [manager (create-manager opts)]
                    (reset! manager* manager)
                    manager))]
                @(spin
                  (await
                   (inference/smc-infer
                    model 4
                    {:world-policy :fork
                     ;; Force a resampling generation even with equal weights.
                     :resample-threshold 2.0}))))
              results
              (mapv #(rtp/get-state % [:inference :result])
                    (measure/get-contexts posterior))]
          (testing "each resampled particle sees only its selected ancestry"
            (is (= 4 (count results)))
            (is (every? #(and (= 2 (count %))
                              (contains? % :root))
                        results)))
          (testing "particle writes never contaminate the ambient world"
            (is (= #{:root} (g/elements @knowledge {:sync? true}))))
          (testing "the complete speculative tree is consumed after projection"
            (is (= :discarded (:status @@manager*)))
            (is (= 8 (count (:descriptors @@manager*)))
                "four initial worlds plus four resampled worlds")
            (is (empty? (:handles @@manager*))
                "settled generations no longer pin live contexts")
            (is (every? #(= :discarded (:fork/status %))
                        (:descriptors @@manager*)))
            (is (every? nil? (map :parent-ctx
                                  (measure/get-contexts posterior)))
                "posterior projections do not retain resampling ancestry")
            (is (every? #(= :immutable
                            (backend/backend-type (:backend %)))
                        (measure/get-contexts posterior)))
            (is (every? map?
                        (map #(rtp/get-state
                               % [:inference :world-descriptor])
                             (measure/get-contexts posterior)))))))
      (finally
        (context/stop-context! root)))))

(deftest resampling-retires-source-worlds-before-running-children
  (let [root (context/create-execution-context
              {:executor (executor/thread-pool-executor 4)})
        source-count 3
        finalized (atom [])
        child-finally-counts (atom [])]
    (try
      (binding [ec/*execution-context* root]
        (let [model
              (spin
               (try
                 (observe (ar/normal 0.0 1.0) 0.0 :id :evidence)
                 ;; Only replacement children resume through the successful
                 ;; side of the barrier. Every source `finally` must already
                 ;; have run before any child is admitted here.
                 (swap! child-finally-counts conj (count @finalized))
                 :done
                 (finally
                   (swap! finalized conj
                          (rtp/get-state ec/*execution-context*
                                         [:inference :particle-id])))))
              result
              (deref
               (spin
                (try
                  (await
                   (inference/smc-infer
                    model source-count
                    {:world-policy :fork
                     :executor (:executor root)
                     :resample-threshold 2.0}))
                  (catch Throwable error error)))
               5000 ::timed-out)]
          (is (not= ::timed-out result))
          (is (not (instance? Throwable result))
              "expected source retirement is not a global inference failure")
          (is (= source-count (count (measure/get-contexts result))))
          (is (= source-count (count @child-finally-counts)))
          (is (every? #(>= % source-count) @child-finally-counts)
              "all superseded sources unwind before replacement children run")
          (is (= (* 2 source-count) (count @finalized))
              "both source and replacement generations execute finally")
          (is (= (* 2 source-count) (count (distinct @finalized)))
              "each retired or completed particle reaches one terminal path")))
      (finally
        (context/close-context! root)))))

(deftest cancellation-during-source-retirement-never-admits-children
  (let [root (context/create-execution-context
              {:executor (executor/thread-pool-executor 4)})
        manager* (atom nil)
        retirement-entered (promise)
        release-retirement (promise)
        child-entered (atom 0)
        create-manager coordinator/create-world-manager]
    (try
      (binding [ec/*execution-context* root]
        (let [model
              (spin
               (try
                 (observe (ar/normal 0.0 1.0) 0.0 :id :evidence)
                 (swap! child-entered inc)
                 (await (fn [_resolve _reject] nil))
                 (finally
                   (deliver retirement-entered true)
                   @release-retirement)))
              outcome
              (future
                (with-redefs
                 [coordinator/create-world-manager
                  (fn [opts]
                    (let [manager (create-manager opts)]
                      (reset! manager* manager)
                      manager))]
                  (binding [ec/*execution-context* root]
                    (try
                      @(inference/smc-infer
                        model 1
                        {:world-policy :fork
                         :executor (:executor root)
                         :resample-threshold 2.0})
                      (catch Throwable error error)))))]
          (is (= true (deref retirement-entered 5000 ::timed-out)))
          (is (= :retiring (:generation-phase @@manager*)))
          (let [cancelled (promise)
                operation (coordinator/cancel-particle-worlds! @manager*)]
            (operation #(deliver cancelled [:ok %])
                       #(deliver cancelled [:error %]))
            (deliver release-retirement true)
            (is (= [:ok nil] (deref cancelled 5000 ::timed-out)))
            (is (instance? Throwable (deref outcome 5000 ::timed-out)))
            (is (zero? @child-entered)
                "replacement children never run after cancellation wins")
            (is (= :discarded (:status @@manager*)))
            (is (empty? (:handles @@manager*))))))
      (finally
        (deliver release-retirement true)
        (context/close-context! root)))))

(deftest cancellation-during-resampling-fork-construction-gates-settlement
  (let [root (context/create-execution-context
              {:executor (executor/thread-pool-executor 4)})
        manager* (atom nil)
        fork-count (atom 0)
        child-fork-entered (promise)
        release-child-fork (promise)
        source-finalizer-entered (promise)
        release-source-finalizer (promise)
        child-entered (atom 0)
        create-manager coordinator/create-world-manager
        fork-world coordinator/fork-particle-world!]
    (try
      (binding [ec/*execution-context* root]
        (let [model
              (spin
               (try
                 (observe (ar/normal 0.0 1.0) 0.0 :id :evidence)
                 (swap! child-entered inc)
                 (await (fn [_resolve _reject] nil))
                 (finally
                   (deliver source-finalizer-entered true)
                   @release-source-finalizer)))
              outcome
              (future
                (with-redefs
                 [coordinator/create-world-manager
                  (fn [opts]
                    (let [manager (create-manager opts)]
                      (reset! manager* manager)
                      manager))
                  coordinator/fork-particle-world!
                  (fn [manager source resolve reject]
                    (if (= 2 (swap! fork-count inc))
                      (do
                        (deliver child-fork-entered true)
                        (future
                          @release-child-fork
                          (fork-world manager source resolve reject)))
                      (fork-world manager source resolve reject)))]
                  (binding [ec/*execution-context* root]
                    (try
                      @(inference/smc-infer
                        model 1
                        {:world-policy :fork
                         :executor (:executor root)
                         :resample-threshold 2.0})
                      (catch Throwable error error)))))]
          (is (= true (deref child-fork-entered 5000 ::timed-out)))
          (is (= :forking (:generation-phase @@manager*)))
          (let [cancelled (promise)
                operation (coordinator/cancel-particle-worlds! @manager*)]
            (operation #(deliver cancelled [:ok %])
                       #(deliver cancelled [:error %]))
            (is (= true (deref source-finalizer-entered 5000 ::timed-out)))
            (is (= :open (:status @@manager*))
                "settlement waits for the outstanding fork callback")
            (deliver release-child-fork true)
            (is (= ::still-waiting
                   (deref cancelled 100 ::still-waiting))
                "the late fork callback cannot erase an unwinding source")
            (is (= 1 (count (:active-contexts @@manager*))))
            (deliver release-source-finalizer true)
            (is (= [:ok nil] (deref cancelled 5000 ::timed-out)))
            (is (instance? Throwable (deref outcome 5000 ::timed-out)))
            (is (zero? @child-entered))
            (is (= :discarded (:status @@manager*)))
            (is (= 2 (count (:descriptors @@manager*)))
                "the late child handle remains inside affine cleanup")
            (is (empty? (:handles @@manager*))))))
      (finally
        (deliver release-child-fork true)
        (deliver release-source-finalizer true)
        (context/close-context! root)))))

(deftest cancellation-during-initial-fork-construction-joins-late-world
  (let [root (context/create-execution-context
              {:executor (executor/thread-pool-executor 2)})
        manager* (atom nil)
        task* (atom nil)
        fork-entered (promise)
        release-fork (promise)
        create-manager coordinator/create-world-manager
        fork-world ygg/fork!]
    (try
      (let [outcome
            (future
              (with-redefs
               [coordinator/create-world-manager
                (fn [opts]
                  (let [manager (create-manager opts)]
                    (reset! manager* manager)
                    manager))
                ygg/fork!
                (fn [opts]
                  (let [operation (fork-world opts)]
                    (fn [resolve reject]
                      (operation
                       (fn [handle]
                         (deliver fork-entered true)
                         (future @release-fork (resolve handle)))
                       reject))))]
                (binding [ec/*execution-context* root]
                  (let [task (inference/smc-infer
                              (spin :done) 1
                              {:world-policy :fork
                               :executor (:executor root)})]
                    (reset! task* task)
                    (try @task (catch Throwable error error))))))]
        (is (= true (deref fork-entered 5000 ::timed-out)))
        (binding [ec/*execution-context* root]
          (spin-core/cancel-spin! @task*))
        (is (= ::still-waiting (deref outcome 100 ::still-waiting))
            "public cancellation waits for the outstanding affine fork")
        (is (= 1 (:pending-forks @@manager*)))
        (is (= :open (:status @@manager*)))
        (deliver release-fork true)
        (let [result (deref outcome 5000 ::timed-out)]
          (is (instance? Throwable result))
          (is (= spin-core/spin-cancelled (:type (ex-data result))))
          (is (= :discarded (:status @@manager*)))
          (is (= 1 (count (:descriptors @@manager*))))
          (is (empty? (:handles @@manager*)))))
      (finally
        (deliver release-fork true)
        (context/close-context! root)))))

(deftest cancelling-public-inference-spin-cancels-and-joins-worlds
  (let [root (context/create-execution-context
              {:executor (executor/thread-pool-executor 4)})
        manager* (atom nil)
        task* (atom nil)
        model-entered (promise)
        model-cleaned? (atom false)
        discard-entered (promise)
        release-discard (promise)
        create-manager coordinator/create-world-manager
        discard-world ygg/discard-fork!]
    (try
      (let [outcome
            (future
              (with-redefs
               [coordinator/create-world-manager
                (fn [opts]
                  (let [manager (create-manager opts)]
                    (reset! manager* manager)
                    manager))
                ygg/discard-fork!
                (fn [handle opts]
                  (let [operation (discard-world handle opts)]
                    (fn [resolve reject]
                      (deliver discard-entered true)
                      (future
                        @release-discard
                        (operation resolve reject)))))]
                (binding [ec/*execution-context* root]
                  (let [task
                        (inference/smc-infer
                         (spin
                          (try
                            (deliver model-entered true)
                            (await (fn [_resolve _reject] nil))
                            (finally (reset! model-cleaned? true))))
                         1
                         {:world-policy :fork
                          :executor (:executor root)})]
                    (reset! task* task)
                    (try @task (catch Throwable error error))))))]
        (is (= true (deref model-entered 5000 ::timed-out)))
        (binding [ec/*execution-context* root]
          (spin-core/cancel-spin! @task*))
        (is (= true (deref discard-entered 5000 ::timed-out)))
        (is (= ::still-waiting (deref outcome 100 ::still-waiting))
            "public cancellation stays pending through asynchronous discard")
        (is (= :discarding (:status @@manager*)))
        (deliver release-discard true)
        (let [result (deref outcome 5000 ::timed-out)]
          (is (instance? Throwable result))
          (is (= spin-core/spin-cancelled (:type (ex-data result))))
          (is @model-cleaned?)
          (is (= :discarded (:status @@manager*))
              "the public Spin rejects only after manager settlement")
          (is (empty? (:handles @@manager*)))))
      (finally
        (deliver release-discard true)
        (context/close-context! root)))))

(deftest canonical-worlds-reject-unsafe-pgas-scoring
  (let [root (context/create-execution-context)]
    (try
      (binding [ec/*execution-context* root]
        (let [result
              @(spin
                (try
                  (await
                   (inference/smc-infer
                    (spin :done) 2
                    {:world-policy :fork
                     :pgas-ancestor-sampling? true}))
                  :unexpected-success
                  (catch Throwable error error)))]
          (is (instance? Throwable result))
          (is (= ::inference/world-pgas-unsupported
                 (:type (ex-data result))))))
      (finally
        (context/stop-context! root)))))

(deftest public-pgas-rejects-worlds-before-starting-the-model
  (let [root (context/create-execution-context)
        invocations (atom 0)]
    (try
      (binding [ec/*execution-context* root]
        (let [result
              @(spin
                (try
                  (await
                   (inference/pgas-infer
                    (spin (swap! invocations inc) :done)
                    2 1 {:world-policy :fork}))
                  :unexpected-success
                  (catch Throwable error error)))]
          (is (instance? Throwable result))
          (is (= ::inference/world-pgas-unsupported
                 (:type (ex-data result))))
          (is (zero? @invocations)
              "the public wrapper rejects before its initial SMC sweep")))
      (finally
        (context/stop-context! root)))))

(deftest world-policy-is-explicit
  (let [root (context/create-execution-context)]
    (try
      (binding [ec/*execution-context* root]
        (let [result
              @(spin
                (try
                  (await (inference/smc-infer
                          (spin :done) 1 {:world-policy :unknown}))
                  :unexpected-success
                  (catch Throwable error error)))]
          (is (instance? Throwable result))
          (is (= ::inference/invalid-world-policy
                 (:type (ex-data result))))))
      (finally
        (context/stop-context! root)))))

(deftest partial-initialization-failure-consumes-created-worlds
  (let [root (context/create-execution-context)
        manager* (atom nil)
        fork-count (atom 0)
        create-manager coordinator/create-world-manager
        fork-world coordinator/fork-particle-world!]
    (try
      (binding [ec/*execution-context* root]
        (let [result
              (with-redefs
               [coordinator/create-world-manager
                (fn [opts]
                  (let [manager (create-manager opts)]
                    (reset! manager* manager)
                    manager))
                coordinator/fork-particle-world!
                (fn [manager source resolve reject]
                  (if (= 3 (swap! fork-count inc))
                    (reject (ex-info "synthetic fork failure" {:stage :initial}))
                    (fork-world manager source resolve reject)))]
                @(spin
                  (try
                    (await (inference/smc-infer
                            (spin :done) 4 {:world-policy :fork}))
                    :unexpected-success
                    (catch Throwable error error))))]
          (is (instance? Throwable result))
          (is (= :discarded (:status @@manager*)))
          (is (= 2 (count (:descriptors @@manager*))))
          (is (empty? (:handles @@manager*)))))
      (finally
        (context/stop-context! root)))))

(deftest read-only-cleanup-failure-can-be-retried
  (let [root (context/create-execution-context)
        manager (coordinator/create-world-manager {})
        discard ygg/discard-fork!
        attempts (atom 0)]
    (try
      (binding [ec/*execution-context* root]
        (is (= :ok
               (first
                (await-cps
                 (fn [resolve reject]
                   (coordinator/fork-particle-world!
                    manager root resolve reject))))))
        (let [first-result
              (with-redefs
               [ygg/discard-fork!
                (fn [handle opts]
                  (if (= 1 (swap! attempts inc))
                    (fn [_resolve reject]
                      (reject (ex-info "synthetic preflight failure" {})))
                    (discard handle opts)))]
                (let [failed (await-cps
                              (coordinator/discard-particle-worlds! manager))
                      retried (await-cps
                               (coordinator/discard-particle-worlds! manager))]
                  [failed retried]))]
          (is (= :error (ffirst first-result)))
          (is (= [:ok nil] (second first-result)))
          (is (= :discarded (:status @manager)))
          (is (empty? (:handles @manager)))))
      (finally
        (context/stop-context! root)))))

(deftest resampling-fork-failure-consumes-the-suspended-tree
  (let [root (context/create-execution-context
              {:executor (executor/thread-pool-executor 4)})
        manager* (atom nil)
        fork-count (atom 0)
        schedules (atom 0)
        root-executor (:executor root)
        rejecting-cancel-executor
        (reify executor/PExecutor
          (execute! [_ task]
            (if (> (swap! schedules inc) 4)
              (throw (ex-info "synthetic cancellation scheduling rejection"
                              {}))
              (executor/execute! root-executor task)))
          (execute-after! [_ delay-ms task]
            (executor/execute-after! root-executor delay-ms task)))
        create-manager coordinator/create-world-manager
        fork-world coordinator/fork-particle-world!]
    (try
      (binding [ec/*execution-context* root]
        (let [result
              (with-redefs
               [coordinator/create-world-manager
                (fn [opts]
                  (let [manager (create-manager opts)]
                    (reset! manager* manager)
                    manager))
                coordinator/fork-particle-world!
                (fn [manager source resolve reject]
                  (if (= 6 (swap! fork-count inc))
                    (reject (ex-info "synthetic fork failure" {:stage :resampling}))
                    (fork-world manager source resolve reject)))]
                (deref
                 (spin
                  (try
                    (await (inference/smc-infer
                            (observed-model) 4
                            {:world-policy :fork
                             :executor rejecting-cancel-executor
                             :resample-threshold 2.0}))
                    :unexpected-success
                    (catch Throwable error error)))
                 5000 ::timed-out))]
          (is (not= ::timed-out result))
          (is (instance? Throwable result))
          (let [recovery (:world/recovery (ex-data result))]
            (is (map? recovery))
            (is (= [:ok nil] (await-cps (:await-quiescent recovery))))
            (is (= [:ok nil] (await-cps ((:discard! recovery))))))
          (is (= :discarded (:status @@manager*)))
          (is (= 5 (count (:descriptors @@manager*))))
          (is (empty? (:handles @@manager*)))))
      (finally
        (context/close-context! root)))))

(deftest partial-particle-start-failure-is-cancelled-and-recoverable
  (let [root (context/create-execution-context
              {:executor (executor/thread-pool-executor 4)})
        manager* (atom nil)
        schedules (atom 0)
        root-executor (:executor root)
        rejecting-executor
        (reify executor/PExecutor
          (execute! [_ task]
            (if (= 2 (swap! schedules inc))
              (throw (ex-info "synthetic executor rejection" {}))
              (executor/execute! root-executor task)))
          (execute-after! [_ delay-ms task]
            (executor/execute-after! root-executor delay-ms task)))
        create-manager coordinator/create-world-manager]
    (try
      (binding [ec/*execution-context* root]
        (let [result
              (with-redefs
               [coordinator/create-world-manager
                (fn [opts]
                  (let [manager (create-manager opts)]
                    (reset! manager* manager)
                    manager))]
                @(spin
                  (try
                    (await
                     (inference/smc-infer
                      (spin (await (fn [_resolve _reject] nil)))
                      3 {:world-policy :fork
                         :executor rejecting-executor}))
                    :unexpected-success
                    (catch Throwable error error))))
              recovery (:world/recovery (ex-data result))]
          (is (instance? Throwable result))
          (is (= ::inference/particle-start-failed
                 (:type (ex-data result))))
          (is (= 1 (:started (ex-data result))))
          (is (= [:ok nil] (await-cps (:await-quiescent recovery))))
          (is (= [:ok nil] (await-cps ((:discard! recovery)))))
          (is (= :discarded (:status @@manager*)))
          (is (= 3 (count (:descriptors @@manager*))))
          (is (empty? (:handles @@manager*)))))
      (finally
        (context/close-context! root)))))

(deftest iterative-particles-remain-live-until-their-final-completion
  (let [root (context/create-execution-context
              {:executor (executor/thread-pool-executor 4)})
        manager* (atom nil)
        second-pass (promise)
        arrivals (atom 0)
        create-manager coordinator/create-world-manager
        iterative-kernel
        (reify kernel/PInferenceKernel
          (kernel-id [_] :world-lifecycle-regression)
          (step [_ _ checkpoint _]
            {:action :assign
             :value (or (get-in checkpoint [:options :observe]) 0.0)})
          (on-complete [_ particle _trace _result]
            (rtp/swap-state! particle [:test :iterate?] (constantly true))
            {:action :iterate :updates {}}))]
    (try
      (binding [ec/*execution-context* root]
        (with-redefs
         [coordinator/create-world-manager
          (fn [opts]
            (let [manager (create-manager opts)]
              (reset! manager* manager)
              manager))]
          (let [model
                (spin
                 (observe (ar/normal 0.0 1.0) 0.0 :id :evidence)
                 (when (rtp/get-state ec/*execution-context*
                                      [:test :iterate?])
                   (when (= 2 (swap! arrivals inc))
                     (deliver second-pass true))
                   (await (fn [_resolve _reject] nil)))
                 :done)
                task (inference/kernel-infer
                      model iterative-kernel 2
                      {:world-policy :fork :barrier-policy :none})
                result (future
                         (try
                           (deref task 5000 ::timed-out)
                           (catch Throwable error error)))]
            (is (= true (deref second-pass 5000 ::timed-out)))
            (is (= 2 (count (:active-contexts @@manager*)))
                "an :iterate completion is not a terminal world callback")
            (is (= [:ok nil]
                   (await-cps
                    (coordinator/cancel-particle-worlds! @manager*))))
            (is (not= ::timed-out (deref result 5000 ::timed-out)))
            (is (= [:ok nil]
                   (await-cps
                    (coordinator/discard-particle-worlds-when-quiescent!
                     @manager*))))
            (is (= :discarded (:status @@manager*))))))
      (finally
        (context/close-context! root)))))

(deftest model-failure-exposes-portable-world-recovery
  (let [root (context/create-execution-context)]
    (try
      (binding [ec/*execution-context* root]
        (let [task
              (spin
               (try
                 (await
                  (inference/smc-infer
                   (spin (throw (ex-info "model failed" {:stage :model})))
                   3
                   {:world-policy :fork}))
                 :unexpected-success
                 (catch Throwable error error)))
              result (deref task 5000 ::timed-out)
              recovery (:world/recovery (ex-data result))]
          (is (not= ::timed-out result))
          (is (instance? Throwable result))
          (is (contains? #{:open :discarding :discarded} (:status recovery)))
          (is (= 3 (count (:descriptors recovery))))
          (is (every? #(and (map? %)
                            (keyword? (:fork/id %))
                            (= :particle (:fork/purpose %)))
                      (:descriptors recovery)))
          (is (instance? clojure.lang.IAtom (:manager recovery))
              "the live recovery capability stays process-local")
          (is (= [:ok nil] (await-cps (:await-quiescent recovery))))
          (is (= [:ok nil] (await-cps ((:discard! recovery)))))
          (is (= :discarded (:status @(:manager recovery))))
          (is (empty? (:handles @(:manager recovery))))))
      (finally
        (context/stop-context! root)))))
