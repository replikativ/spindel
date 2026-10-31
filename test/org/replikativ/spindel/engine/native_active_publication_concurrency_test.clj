(ns org.replikativ.spindel.engine.native-active-publication-concurrency-test
  (:require [clojure.test :refer [deftest is]]
            [org.replikativ.spindel.engine.impl.owned :as c]
            [org.replikativ.spindel.engine.lifetime :as lifetime]
            [org.replikativ.spindel.engine.lifecycle :as lifecycle]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.owned-runtime-test :refer [verify-boundaries!]])
  (:import [java.lang.ref Reference]
           [java.util.concurrent CountDownLatch TimeUnit]))

(deftest host-thread-cannot-borrow-an-executing-source-activation
  (let [rt (c/runtime {:audit? true :cps-exit? true}) root (lifetime/root-scope rt)
        entered (CountDownLatch. 1) continue (CountDownLatch. 1)
        published (atom nil) effects (atom []) errors (atom []) values (atom [])
        task (c/cspin rt :concurrent-requester
                      (swap! effects conj :before)
                      (.countDown entered)
                      ;; The test deliberately holds a real ordinary body, not
                      ;; the mutation gate or a fabricated activation frame.
                      (when-not (.await continue 10 TimeUnit/SECONDS)
                        (throw (ex-info "Source actor gate timed out" {:test :source-gate})))
                      (reset! published (rtp/fork-owned-world! rt {:world-id [:w 1] :owner root}))
                      (swap! effects conj :after)
                      (c/park (c/ticket :source-suffix)))
        runner (future (c/observe! rt task #(swap! values conj %) #(swap! errors conj %)))
        timed-out (Object.)]
    (try
      (is (.await entered 5 TimeUnit/SECONDS) "Actual source body must enter")
      (let [before (c/snapshot-family rt)
            source (get before c/w)
            refused (try
                      (rtp/fork-owned-world! rt {:world-id [:w 1] :owner root})
                      nil
                      (catch clojure.lang.ExceptionInfo error error))]
        (is (= :running (get-in source [:runs [:concurrent-requester 1] :status])))
        (is (true? (get-in source [:threads :engine :executing?])))
        (is (= [:concurrent-requester 1] (get-in source [:threads :engine :run])))
        (is (= :fork-activation (:operation (ex-data refused))))
        (is (= :unsupported-operation (:error (ex-data refused))))
        (is (= before (c/snapshot-family rt)) "Refusal must publish no row or cursor change")
        (is (= [:before] @effects))
        (is (nil? @published))
        (verify-boundaries! rt))
      (.countDown continue)
      (is (not (identical? timed-out (deref runner 5000 timed-out)))
          "Source actor must publish and return to the parked boundary")
      (is (future-done? runner))
      (is (= [:before :after] @effects))
      (is (empty? @values))
      (is (empty? @errors))
      (let [child (:context @published)]
        (is (some? child))
        (is (= :parked (get-in (c/snapshot rt) [:runs [:concurrent-requester 1] :status])))
        (when child
          (is (empty? (:runs (c/snapshot child))))
          (is (not (contains? (:entities (c/snapshot child)) :concurrent-requester)))
          (is (empty? (:native (c/snapshot child)))))
        (verify-boundaries! rt)
        (let [released (atom []) release-errors (atom [])]
          (lifecycle/observe! (rtp/request-world-release! rt :finished)
                              #(swap! released conj %) #(swap! release-errors conj %))
          (is (= [nil] @released))
          (is (empty? @release-errors))
          (is (= [:finished] @errors))
          (when child (is (= :released (:status (c/snapshot child)))))
          (is (= :released (:status (c/snapshot rt))))
          (is (= [:before :after] @effects))
          (verify-boundaries! rt)))
      (finally
        ;; Every failure path releases the actual source thread before cleanup.
        (.countDown continue)
        (when (identical? timed-out (deref runner 5000 timed-out))
          (future-cancel runner))
        (rtp/request-world-release! rt :finished)
        (Reference/reachabilityFence task)))))
