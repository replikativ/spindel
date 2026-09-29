(ns org.replikativ.spindel.effect-adapter-test
  "An effect registered with its adapter function dispatches in both
  runtimes: in ClojureScript an adapter symbol cannot be resolved."
  #?(:clj
     (:require [clojure.test :refer [deftest is]]
               [org.replikativ.spindel.engine.effects :as eff]
               [org.replikativ.spindel.spin.cps :refer [spin]]
               [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]])
     :cljs
     (:require [cljs.test :refer-macros [deftest is]]
               [org.replikativ.spindel.engine.effects :as eff]
               [org.replikativ.spindel.spin.cps :refer [spin]]
               [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]]))
  ;; the spin macro sees `twice` registered once this namespace has loaded on
  ;; the JVM, where ClojureScript's macros expand
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]]
                            [org.replikativ.spindel.effect-adapter-test])))

(defn twice
  "(twice x): an effect resolving 2x. Must be called inside a spin."
  [& _]
  (throw (ex-info "twice called outside of spin context" {})))

(defn- twice-adapter [[x]] {:x x})

(eff/register-effect-by-symbol!
 'org.replikativ.spindel.effect-adapter-test/twice
 (eff/sync-effect (fn [_context {:keys [x]}] (* 2 x)))
 twice-adapter)

(deftest an-effect-with-an-adapter-function-dispatches
  (async done
         (with-ctx [_ctx]
           (run-spin! (spin (+ 1 (twice 20)))
                      (fn [v] (is (= 41 v)) (done))
                      (fn [e] (is false (str e)) (done))))))
