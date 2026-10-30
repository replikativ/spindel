(ns org.replikativ.spindel.engine.trampoline-scope-test
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.addressing :as addr]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.signal :as signal]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin! await-engine-idle!]]))

(deftest context-scope-survives-initial-inline-loop-bounces
  (async done
         (with-ctx [ctx]
           (let [source (signal/signal 0) seen (atom [])
                 s (spin
                    (addr/with-key :inside
                      (loop [i 0]
                        (when (< i 3)
                          (track source)
                          (swap! seen conj [(addr/current-key ec/*execution-context*)
                                            (ec/same-world? ctx ec/*execution-context*)])
                          (recur (inc i)))))
                    (addr/current-key ec/*execution-context*))]
             (run-spin! s
                        (fn [value] (is (nil? value)) (is (= [[:inside true] [:inside true] [:inside true]] @seen)) (done))
                        (fn [error] (is false (str error)) (done)))))))

(deftest repeated-context-scope-entry-and-exit-is-stack-safe
  (async done
         (with-ctx [_ctx]
           (let [source (signal/signal 0) wrong (atom []) depths (atom [])
                 s (spin
                    (loop [i 0]
                      (if (< i 3000)
                        (do
                          (addr/with-key :inside
                            (track source)
                            (when-not (= :inside (addr/current-key ec/*execution-context*))
                              (swap! wrong conj [:inside i])))
                          (when (addr/current-key ec/*execution-context*) (swap! wrong conj [:outside i]))
                          #?(:clj (when (zero? (mod i 500))
                                    (swap! depths conj (count (.getStackTrace (Thread/currentThread))))))
                          (recur (inc i)))
                        :done)))]
             (run-spin! s
                        (fn [value]
                          (is (= :done value)) (is (empty? @wrong))
                          #?(:clj (is (< (- (apply max @depths) (apply min @depths)) 20)))
                          (done))
                        (fn [error] (is false (str error)) (done)))))))

(deftest parked-context-scope-survives-later-inline-bounces
  (async done
         (with-ctx [ctx]
           (let [blocker (sync/deferred) source (signal/signal 0) seen (atom [])
                 s (spin
                    (addr/with-key :inside
                      (swap! seen conj :park)
                      (await blocker)
                      (loop [i 0]
                        (when (< i 3)
                          (track source)
                          (swap! seen conj (addr/current-key ec/*execution-context*))
                          (recur (inc i)))))
                    (addr/current-key ec/*execution-context*))]
             (run-spin! s
                        (fn [value] (is (nil? value)) (is (= [:park :inside :inside :inside] @seen)) (done))
                        (fn [error] (is false (str error)) (done)))
             (await-engine-idle! ctx (fn [] (sync/deliver! blocker :ready)))))))

(deftest scope-follows-an-operation-resumed-in-a-fork
  (async done
         (with-ctx [parent]
           (let [fork (context/fork-context parent :mode :frozen)
                 seen (atom [])
                 settle (fn [r _] (binding [ec/*execution-context* fork] (r nil)) nil)
                 s (spin
                    (addr/with-key :inside
                      (loop [i 0]
                        (when (< i 3)
                          (await settle)
                          (swap! seen conj [(addr/current-key ec/*execution-context*)
                                            (ec/same-world? fork ec/*execution-context*)])
                          (recur (inc i)))))
                    [(addr/current-key ec/*execution-context*) (ec/same-world? fork ec/*execution-context*)])]
             (binding [ec/*callback-egress-policy* :causal-follow]
               (run-spin! s
                          (fn [value]
                            (is (= [nil true] value))
                            (is (= [[:inside true] [:inside true] [:inside true]] @seen))
                            (context/stop-context! fork) (done))
                          (fn [error] (is false (str error)) (context/stop-context! fork) (done))))))))
