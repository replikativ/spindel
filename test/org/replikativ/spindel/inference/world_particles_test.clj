(ns org.replikativ.spindel.inference.world-particles-test
  "Canonical Yggdrasil worlds for effectful inference particles."
  (:refer-clojure :exclude [await])
  (:require [anglican.runtime :as ar]
            [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.inference.coordinator :as coordinator]
            [org.replikativ.spindel.inference.effects :refer [observe]]
            [org.replikativ.spindel.inference.inference :as inference]
            [org.replikativ.spindel.inference.measure :as measure]
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
            (is (every? nil?
                        (map #(rtp/get-state
                               % [:inference :inference-coordinator])
                             (measure/get-contexts posterior))))
            (is (every? map?
                        (map #(rtp/get-state
                               % [:inference :world-descriptor])
                             (measure/get-contexts posterior)))))))
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

(deftest resampling-fork-failure-consumes-the-suspended-tree
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
                  (if (= 6 (swap! fork-count inc))
                    (reject (ex-info "synthetic fork failure" {:stage :resampling}))
                    (fork-world manager source resolve reject)))]
                (deref
                 (spin
                  (try
                    (await (inference/smc-infer
                            (observed-model) 4
                            {:world-policy :fork
                             :resample-threshold 2.0}))
                    :unexpected-success
                    (catch Throwable error error)))
                 5000 ::timed-out))]
          (is (not= ::timed-out result))
          (is (instance? Throwable result))
          (is (= :discarded (:status @@manager*)))
          (is (= 5 (count (:descriptors @@manager*))))
          (is (empty? (:handles @@manager*)))))
      (finally
        (context/stop-context! root)))))

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
          (is (= :open (:status recovery))
              "fail-fast cannot consume worlds while sibling particles may run")
          (is (= 3 (count (:descriptors recovery))))
          (is (every? #(and (map? %)
                            (keyword? (:fork/id %))
                            (= :particle (:fork/purpose %)))
                      (:descriptors recovery)))
          (is (instance? clojure.lang.IAtom (:manager recovery))
              "the live recovery capability stays process-local")))
      (finally
        (context/stop-context! root)))))
