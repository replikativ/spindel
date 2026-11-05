(ns org.replikativ.spindel.v2.port.gc-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task await track]]
            [org.replikativ.spindel.v2.combinators :as comb]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.v2.port.support2 :as h]))

(use-fixtures :each h/fixture)

(defn- reactive-parent-case [delayed?]
  (let [source (v2/signal 1) gate (v2/deferred) seen (atom [])
        outer (spin (await (comb/parallel
                            (spin (let [v (:new (track source))] (when delayed? (await gate)) v))
                            (spin :other))))
        stop (v2/observe! outer (fn [v err?] (swap! seen conj [v err?])))]
    (try
      (is (= (if delayed? [] [[[1 :other] false]]) @seen))
      ;; Simulate the handle's Cleaner while the explicit observation remains.
      (v2/release! outer)
      (when delayed? (gate :ready))
      (is (= [[[1 :other] false]] @seen))
      (reset! source 2)
      (is (= [[[1 :other] false] [[2 :other] false]] @seen))
      (finally (stop)))))

(deftest transitive-reactivity-survives-parent-gc (reactive-parent-case false))
(deftest suspended-orphan-retains-transitive-reactivity-after-completion (reactive-parent-case true))

(deftest test-try-gc-cleanup-preserves-live-external-await
  (let [d (v2/deferred) result (promise) s (spin (await d))]
    (v2/value-async s #(deliver result [%1 %2]))
    (v2/release! s)
    (d :delivered)
    (is (= [:delivered false] (deref result 2000 ::timeout)))))

(deftest test-spawn-registers-and-releases-keep-alive
  (let [d (v2/deferred) callbacks (atom []) s (spin (await d))]
    (comb/spawn! s {:on-success #(swap! callbacks conj %)})
    (v2/release! s)
    (is (empty? @callbacks))
    (d :delivered)
    (is (= [:delivered] @callbacks))))

(deftest test-spawn-terminal-callback-runs-once-for-reactive-spin
  (let [s (v2/signal 0) callbacks (atom []) c (spin (:new (track s)))
        stop (v2/observe! c (fn [_ _]))]
    (try
      (comb/spawn! c {:on-success #(swap! callbacks conj %)})
      (is (= [0] @callbacks))
      (reset! s 1)
      (is (= 1 (h/result c)))
      (is (= [0] @callbacks))
      (finally (stop)))))

(deftest test-spawn-terminal-callbacks-release-on-reject-and-pre-start-cancel
  (testing "rejection preserves the original exception, once"
    (let [failure (ex-info "spawn rejected" {:test true}) ok (atom []) bad (atom [])
          s (spin (throw failure))]
      (comb/spawn! s {:on-success #(swap! ok conj %) :on-error #(swap! bad conj %)})
      (is (empty? @ok)) (is (= [failure] @bad))))
  (testing "cancellation before the work starts never runs that work"
    (let [gate (v2/deferred) runs (atom 0) ok (atom []) bad (atom [])
          t (task (await gate) (swap! runs inc) :unexpected)]
      (v2/cancel-task! t)
      (comb/spawn! t {:on-success #(swap! ok conj %) :on-error #(swap! bad conj %)})
      (gate :late)
      (is (zero? @runs)) (is (empty? @ok))
      (is (= 1 (count @bad))) (is (v2/cancelled? (first @bad)))))
  (testing "in-flight cancellation rejects once"
    (let [gate (v2/deferred) ok (atom []) bad (atom []) t (task (await gate))]
      (comb/spawn! t {:on-success #(swap! ok conj %) :on-error #(swap! bad conj %)})
      (v2/cancel-task! t) (gate :late)
      (is (empty? @ok)) (is (= 1 (count @bad))) (is (v2/cancelled? (first @bad)))))
  (testing "throwing host callbacks cannot reclassify results"
    (let [ok (atom []) bad (atom []) s (spin :value) failure (ex-info "body failed" {:body true})
          f (spin (throw failure))]
      (binding [*err* (java.io.StringWriter.)]
        (comb/spawn! s {:on-success (fn [v] (swap! ok conj v) (throw (ex-info "callback" {})))
                        :on-error #(swap! bad conj %)})
        (is (= [:value] @ok)) (is (empty? @bad)) (is (= :value (h/result s)))
        (comb/spawn! f {:on-error (fn [e] (swap! bad conj e) (throw (ex-info "callback" {})))})
        (is (= [failure] @bad)) (is (= [:err failure] (h/outcome f)))))))

(deftest test-spawn-survives-gc-mid-await-jvm
  (let [d (v2/deferred) result (promise)]
    (comb/spawn! (spin (deliver result (await d))))
    (dotimes [_ 3] (System/gc) (Thread/sleep 30))
    (d :delivered)
    (is (= :delivered (deref result 2000 ::timeout)))))
