(ns org.replikativ.spindel.blocking-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.blocking :as blocking]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.spin.combinators :as comb]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.test-helpers :refer [with-ctx]]))

(def ^:dynamic *conveyed* nil)

(deftest the-value-of-f-on-a-worker-thread
  (with-ctx [_]
    (let [thread (promise)
          s (spin (inc (await (blocking/blocking (fn [] (deliver thread (Thread/currentThread)) 41)))))]
      (is (= 42 (deref s 5000 ::timeout)))
      (is (not (re-find #"spindel-drain" (.getName ^Thread @thread))) "not the drain thread")
      (when (.isVirtual ^Thread @thread)
        (is true "a virtual thread")))))

(deftest a-throw-rejects
  (with-ctx [_]
    (let [s (spin (try (await (blocking/blocking #(throw (ex-info "boom" {:code 7}))))
                       (catch Exception e (:code (ex-data e)))))]
      (is (= 7 (deref s 5000 ::timeout))))))

(deftest every-call-is-fresh-work
  (with-ctx [_]
    (let [n (atom 0)
          f #(swap! n inc)
          s (spin [(await (blocking/blocking f)) (await (blocking/blocking f))])]
      (is (= [1 2] (deref s 5000 ::timeout)) "two calls of the same f run twice"))))

(deftest the-callers-bindings-are-conveyed
  (with-ctx [_]
    (let [b (binding [*conveyed* :yes] (blocking/blocking (fn [] *conveyed*)))
          s (spin (await b))]
      (is (= :yes (deref s 5000 ::timeout))))))

(deftest losing-a-timeout-interrupts-the-worker
  (with-ctx [_]
    (let [interrupted (promise)
          s (comb/timeout (blocking/blocking
                           (fn []
                             (try (Thread/sleep 30000) :slept
                                  (catch InterruptedException _
                                    (deliver interrupted true)
                                    :interrupted))))
                          100 ::fallback)]
      (is (= ::fallback (deref s 5000 ::timeout)))
      (is (true? (deref interrupted 5000 false)) "the worker was interrupted"))))

(deftest cancelling-interrupts-the-worker
  (with-ctx [_]
    (let [started (promise)
          interrupted (promise)
          b (blocking/blocking (fn []
                                 (deliver started true)
                                 (try (Thread/sleep 30000)
                                      (catch InterruptedException _ (deliver interrupted true)))))
          s (spin (await b))]
      (future (try @s (catch Throwable _ nil)))
      (is (true? (deref started 5000 false)))
      (spin-core/cancel-spin! b)
      (is (true? (deref interrupted 5000 false))))))

(deftest blocking-work-does-not-hold-the-drain
  ;; the point of the primitive: a Spin waiting on slow I/O leaves the
  ;; context's other Spins running
  (with-ctx [_]
    (let [release (promise)
          slow (spin (await (blocking/blocking #(deref release 10000 :never))))
          fast (spin (+ 1 (await (comb/sleep 10 1))))]
      (future (try @slow (catch Throwable _ nil)))
      (is (= 2 (deref fast 2000 ::stuck)) "another Spin of the context completes meanwhile")
      (deliver release :done)
      (is (= :done (deref slow 5000 ::timeout))))))

(deftest many-at-once
  (with-ctx [_]
    (let [n 200
          s (apply comb/parallel (vec (for [i (range n)]
                                  (blocking/blocking (fn [] (Thread/sleep 50) i)))))
          t0 (System/currentTimeMillis)
          r (deref s 10000 ::timeout)]
      (is (= (vec (range n)) r))
      (is (< (- (System/currentTimeMillis) t0) 5000) "they block concurrently, not one by one"))))
