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
            [org.replikativ.spindel.world.scope :as world-scope]
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

(defn- coordinator-private [symbol]
  (ns-resolve 'org.replikativ.spindel.inference.coordinator symbol))

(deftest generation-retirement-claim-uses-the-committed-state
  (let [manager (coordinator/create-world-manager {})
        claim! (coordinator-private 'claim-particle-generation-retirement!)
        real-swap-vals! swap-vals!]
    (coordinator/begin-particle-generation-transition! manager)
    (let [claimed?
          (with-redefs
           [clojure.core/swap-vals!
            (fn [target f & args]
              (when (identical? target manager)
                ;; Evaluate and abandon this contender's transition, then let
                ;; a competing retirement claim commit before its retry.
                (apply f @target args)
                (swap! target assoc
                       :generation-phase :retiring
                       :retiring-context-ids #{:competitor}))
              (apply real-swap-vals! target f args))]
            (claim! manager))]
      (is (false? claimed?)
          "observing :forking before a lost transition does not grant ownership")
      (is (= #{:competitor} (:retiring-context-ids @manager))))
    (coordinator/complete-particle-generation-transition! manager [])))

(deftest retirement-callback-claim-uses-the-committed-prior-state
  (let [retiring (atom {:source {:finish! identity}})
        client {:retiring-contexts retiring}
        context {:fork-id :source}
        take! (coordinator-private 'take-retirement!)
        real-swap-vals! swap-vals!
        claimed
        (with-redefs
         [clojure.core/swap-vals!
          (fn [target f & args]
            (when (identical? target retiring)
              ;; Evaluate and abandon this take, then let another terminal
              ;; callback remove the entry before the retry commits.
              (apply f @target args)
              (swap! target dissoc :source))
            (apply real-swap-vals! target f args))]
          (take! client context))]
    (is (nil? claimed)
        "only the callback that removed the entry owns its finish function")))

(deftest checkpoint-cancellation-claim-uses-the-committed-prior-state
  (let [rejected (atom 0)
        particles (atom {:particle
                         {:context
                          {:fork-id :particle
                           :executor (executor/synchronous-executor)}
                          :checkpoint
                          {:reject (fn [_error] (swap! rejected inc))}
                          :status :checkpoint}})
        client {:particles particles}
        cancel! (coordinator-private 'cancel-kernel-checkpoints!)
        real-swap-vals! swap-vals!]
    (with-redefs
     [clojure.core/swap-vals!
      (fn [target f & args]
        (when (identical? target particles)
          ;; Evaluate and abandon this checkpoint claim, then let a competing
          ;; cancellation take ownership before the retry commits.
          (apply f @target args)
          (swap! target assoc-in [:particle :status] :cancelling))
        (apply real-swap-vals! target f args))]
      (cancel! client #{}))
    (is (zero? @rejected)
        "a checkpoint seen only by an abandoned attempt is not rejected twice")
    (is (= :cancelling (get-in @particles [:particle :status])))))

(deftest cancellation-does-not-claim-a-retiring-generation-checkpoint
  (let [source-id :retiring-source
        rejected (atom 0)
        source-context {:fork-id source-id
                        :executor (executor/synchronous-executor)}
        particles (atom {:source {:context source-context
                                  :checkpoint
                                  {:reject (fn [_error] (swap! rejected inc))}
                                  :status :checkpoint}})
        client {:particles particles}
        manager (coordinator/create-world-manager {})]
    ;; This is the intentional hand-off interval: the manager has published
    ;; retirement ownership, while the coordinator has not yet changed the
    ;; source particle's status from :checkpoint to :retiring.
    (swap! manager assoc
           :client client
           :generation-phase :retiring
           :retiring-context-ids #{source-id}
           :activities {source-id {:kind :particle-context
                                   :value source-context}})
    (coordinator/cancel-particle-worlds! manager)
    (is (zero? @rejected)
        "manager cancellation must not reject retirement-owned CPS slices")
    (is (= :checkpoint (get-in @particles [:source :status])))
    (is (:cancel-requested? @manager))))

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
            (is (= 2 (count (world-scope/activity-values
                             @manager* :particle-context)))
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

(deftest pure-inference-has-no-world-descriptors
  (let [root (context/create-execution-context)]
    (try
      (binding [ec/*execution-context* root]
        (let [posterior @(spin (await (inference/smc-infer (spin 7) 2 {:world-policy :fresh})))]
          (is (= [7 7] (mapv measure/get-value (measure/get-contexts posterior))))
          (is (= [] (measure/world-descriptors posterior)))))
      (finally
        (context/stop-context! root)))))

;; -----------------------------------------------------------------------------
;; Canonical worlds on savepoint SMC
;; -----------------------------------------------------------------------------

(defmacro ^:private capturing-scopes
  "Run `body` with every world scope created meanwhile collected in `scopes`."
  [[scopes] & body]
  `(let [~scopes (atom [])
         create# world-scope/create]
     (with-redefs [world-scope/create (fn [opts#]
                                        (let [s# (create# opts#)]
                                          (swap! ~scopes conj s#)
                                          s#))]
       ~@body)))

(defn- settled? [scopes]
  (every? #(and (= :discarded (:status @%)) (empty? (:handles @%))) scopes))

(defn- slot-name []
  (keyword (str "p" (rtp/get-state ec/*execution-context* [:inference :slot]))))

(deftest smc-resamples-independent-worlds-and-discards-the-tree
  (let [root (context/create-execution-context)]
    (try
      (binding [ec/*execution-context* root]
        (let [knowledge (ygg/register! (-> (mem-gset "particle-kb")
                                           (g/conj :root {:sync? true})))
              model (spin
                     (observe (ar/normal 0.0 1.0) 0.0 :id :evidence)
                     (reset! (ygg/system-signal "particle-kb")
                             (g/conj @knowledge (slot-name) {:sync? true}))
                     (g/elements @knowledge {:sync? true}))]
          (capturing-scopes [scopes]
                            (let [posterior @(spin (await (inference/smc-infer
                                                           model 4
                                                           {:world-policy :fork
                                            ;; resample even with equal weights
                                                            :resample-threshold 2.0})))
                                  results (mapv measure/get-value (measure/get-contexts posterior))
                                  descriptors (measure/world-descriptors posterior)]
                              (testing "each particle sees the caller's state and its own write"
                                (is (= #{#{:root :p0} #{:root :p1} #{:root :p2} #{:root :p3}} (set results))))
                              (testing "particle writes never reach the caller's world"
                                (is (= #{:root} (g/elements @knowledge {:sync? true}))))
                              (testing "the posterior names its worlds, settled"
                                (is (= 4 (count descriptors)))
                                (is (every? #(and (= :particle (:fork/purpose %))
                                                  (= :discarded (:fork/status %)))
                                            descriptors))
                                (is (every? #(instance? org.replikativ.spindel.inference.measure.Sample %)
                                            (measure/get-contexts posterior))
                                    "no execution context is retained"))
                              (testing "every world is discarded before the posterior is delivered"
                                (is (= 2 (count @scopes)) "the root's scope and the session's")
                                (is (settled? @scopes)))))))
      (finally
        (context/stop-context! root)))))

(deftest every-superseded-world-unwinds
  (let [root (context/create-execution-context
              {:executor (executor/thread-pool-executor 4)})
        finalized (atom [])
        n 3]
    (try
      (binding [ec/*execution-context* root]
        (let [model (spin
                     (try
                       (observe (ar/normal 0.0 1.0) 0.0 :id :evidence)
                       :done
                       (finally
                         (swap! finalized conj (:fork-id ec/*execution-context*)))))
              result (deref (spin (await (inference/smc-infer
                                          model n {:world-policy :fork
                                                   :executor (:executor root)
                                                   :resample-threshold 2.0})))
                            5000 ::timed-out)]
          (is (= (repeat n :done) (mapv measure/get-value (measure/get-contexts result))))
          ;; the resampled sources and their children; the root does not run
          ;; the model
          (is (= (* 2 n) (count @finalized)))
          (is (apply distinct? @finalized) "each world reaches one terminal path")))
      (finally
        (context/close-context! root)))))

(deftest every-particle-runs-the-whole-model
  ;; A canonical model's effects may be random without a sample site (a
  ;; model call): each particle makes its own, none shares another's prefix.
  (let [root (context/create-execution-context)
        calls (atom 0)]
    (try
      (binding [ec/*execution-context* root]
        (let [posterior @(spin (await (inference/smc-infer
                                       (spin
                                        (let [answer (swap! calls inc)]
                                          (observe (ar/normal 0.0 1.0) 0.0 :id :evidence)
                                          answer))
                                       4 {:world-policy :fork})))]
          (is (= 4 @calls))
          (is (= #{1 2 3 4} (set (map measure/get-value (measure/get-contexts posterior)))))))
      (finally
        (context/stop-context! root)))))

(deftest cancelling-public-inference-spin-cancels-and-joins-worlds
  (let [root (context/create-execution-context
              {:executor (executor/thread-pool-executor 4)})
        task* (atom nil)
        model-entered (promise)
        model-cleaned? (atom false)
        discard-entered (promise)
        release-discard (promise)
        discard-world ygg/discard-fork!]
    (try
      (capturing-scopes [scopes]
                        (let [outcome
                              (future
                                (with-redefs
                                 [ygg/discard-fork!
                                  (fn [handle opts]
                                    (let [operation (discard-world handle opts)]
                                      (fn [resolve reject]
                                        (deliver discard-entered true)
                                        (future
                                          @release-discard
                                          (if (fn? operation) (operation resolve reject) (resolve operation))))))]
                                  (binding [ec/*execution-context* root]
                                    (let [task (inference/smc-infer
                                                (spin
                                                 (observe (ar/normal 0.0 1.0) 0.0 :id :evidence)
                                                 (try
                                                   (deliver model-entered true)
                                                   (await (fn [_resolve _reject] nil))
                                                   (finally (reset! model-cleaned? true))))
                                                2
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
                          (deliver release-discard true)
                          (let [result (deref outcome 5000 ::timed-out)]
                            (is (instance? Throwable result))
                            (is (= spin-core/spin-cancelled (:type (ex-data result))))
                            (is @model-cleaned?)
                            (is (settled? @scopes)
                                "the public Spin rejects only after every world is discarded"))))
      (finally
        (deliver release-discard true)
        (context/close-context! root)))))

(deftest cancellation-during-the-root-fork-joins-the-late-world
  (let [root (context/create-execution-context
              {:executor (executor/thread-pool-executor 2)})
        task* (atom nil)
        fork-entered (promise)
        release-fork (promise)
        model-ran? (atom false)
        fork-world ygg/fork!]
    (try
      (capturing-scopes [scopes]
                        (let [outcome
                              (future
                                (with-redefs
                                 [ygg/fork!
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
                                                (spin (reset! model-ran? true) :done) 1
                                                {:world-policy :fork
                                                 :executor (:executor root)})]
                                      (reset! task* task)
                                      (try @task (catch Throwable error error))))))]
                          (is (= true (deref fork-entered 5000 ::timed-out)))
                          (binding [ec/*execution-context* root]
                            (spin-core/cancel-spin! @task*))
                          (is (= ::still-waiting (deref outcome 100 ::still-waiting))
                              "cancellation waits for the fork in flight")
                          (deliver release-fork true)
                          (let [result (deref outcome 5000 ::timed-out)]
                            (is (= spin-core/spin-cancelled (:type (ex-data result))))
                            (is (not @model-ran?))
                            (is (= 1 (count @scopes)))
                            (is (settled? @scopes) "the late root is discarded")
                            (is (= 1 (count (world-scope/descriptors (first @scopes))))))))
      (finally
        (deliver release-fork true)
        (context/close-context! root)))))

(deftest a-fork-failure-fails-inference-and-leaves-no-world
  (doseq [failing [3 6]] ; a first particle, a resampled one
    (let [root (context/create-execution-context)
          forks (atom 0)
          fork-world world-scope/fork!]
      (try
        (binding [ec/*execution-context* root]
          (capturing-scopes [scopes]
                            (let [result
                                  (with-redefs
                                   [world-scope/fork!
                                    (fn fork*
                                      ([scope source resolve reject] (fork* scope source nil resolve reject))
                                      ([scope source opts resolve reject]
                                       (if (= failing (swap! forks inc))
                                         (reject (ex-info "synthetic fork failure" {:fork failing}))
                                         (fork-world scope source opts resolve reject))))]
                                    (deref (spin (try
                                                   (await (inference/smc-infer
                                                           (observed-model) 4
                                                           {:world-policy :fork :resample-threshold 2.0}))
                                                   (catch Throwable error error)))
                                           5000 ::timed-out))
                                  recovery (:world/recovery (ex-data result))]
                              (is (= ::inference/inference-failed (:type (ex-data result))) (str "fork " failing))
                              (is (= {:fork failing} (ex-data (ex-cause result))))
                              (is (map? recovery))
                              (is (= [:ok nil] (await-cps ((:discard! recovery)))) "cleanup is idempotent")
                              (is (settled? @scopes)))))
        (finally
          (context/stop-context! root))))))

(deftest model-failure-exposes-portable-world-recovery
  (let [root (context/create-execution-context)]
    (try
      (binding [ec/*execution-context* root]
        (let [result (deref (spin
                             (try
                               (await
                                (inference/smc-infer
                                 (spin
                                  (observe (ar/normal 0.0 1.0) 0.0 :id :evidence)
                                  (throw (ex-info "model failed" {:stage :model})))
                                 3
                                 {:world-policy :fork}))
                               :unexpected-success
                               (catch Throwable error error)))
                            5000 ::timed-out)
              recovery (:world/recovery (ex-data result))]
          (is (= ::inference/inference-failed (:type (ex-data result))))
          (is (= {:stage :model} (ex-data (ex-cause result))))
          (is (= [:inference :particle :particle :particle]
                 (mapv :fork/purpose (:descriptors recovery)))
              "the root, then the particles")
          (is (every? #(keyword? (:fork/id %)) (:descriptors recovery)))
          (is (instance? clojure.lang.IAtom (:manager recovery))
              "the live recovery capability stays process-local")
          (is (= [:ok nil] (await-cps (:await-quiescent recovery))))
          (is (= [:ok nil] (await-cps ((:discard! recovery)))))
          (is (= :discarded (:status @(:manager recovery))))))
      (finally
        (context/stop-context! root)))))
