(ns org.replikativ.spindel.sci.trampoline-test
  "Sandbox code cannot touch which trampoline runs on its thread: it can start
   balanced activations of its own, nothing else."
  (:require [clojure.test :refer [deftest is testing]]
            [is.simm.partial-cps.async :as async]
            [is.simm.partial-cps.runtime :as runtime]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.sci.macro :as macro]
            [sci.core :as sci]))

(defn- interpreter []
  (let [rt (ctx/create-execution-context)
        sci-ctx (macro/create-spin-macro-context {:runtime rt})]
    (fn [source] (binding [ec/*execution-context* rt] (sci/eval-string* sci-ctx source)))))

(deftest the-runtime-it-sees-is-pinned
  ;; a new runtime public is reviewed before sandbox code reaches it
  (is (= '#{->Thunk ->thunk thunk? force-thunk owns-trampoline? call-in-trampoline bound-fn}
         (set (keys ((interpreter) "(ns-publics 'is.simm.partial-cps.runtime)"))))))

(deftest activations-cannot-be-entered-or-left-by-hand
  (let [ev (interpreter)]
    (doseq [source ["(is.simm.partial-cps.runtime/enter-trampoline!)"
                    "(is.simm.partial-cps.runtime/leave-trampoline! nil)"]]
      (is (thrown-with-msg? Exception #"resolve" (ev source)) source))))

(deftest a-stale-token-cannot-be-forged
  ;; A continuation that still carries the token of an activation that has
  ;; ended (conveyed bindings) must start a trampoline of its own. Sandbox code
  ;; that set the thread to that token made it return its Thunk to no one.
  (let [ev (interpreter)
        stale (async/with-trampoline async/*in-trampoline*)
        ;; refused when it is read: the fns are not there
        forge (try (ev "(fn [t] (let [[_ previous] (is.simm.partial-cps.runtime/enter-trampoline!)]
                                  (is.simm.partial-cps.runtime/leave-trampoline! t)))")
                   (catch Exception _ nil))]
    (try
      (when forge (forge stale))
      (is (= :forced (binding [async/*in-trampoline* stale]
                       (async/invoke-continuation (fn [] (runtime/->thunk (fn [] :forced)))))))
      (finally (runtime/leave-trampoline! nil)))))

(deftest sandbox-spins-still-trampoline
  ;; loop/recur across awaits bounces through the interpreted with-trampoline
  (is (= 45 ((interpreter)
             "(require '[org.replikativ.spindel.spin.cps :refer [spin]]
                       '[org.replikativ.spindel.effects.await :refer [await]])
              @(spin (loop [i 0 acc 0]
                       (if (< i 10) (recur (inc i) (+ acc (await (spin i)))) acc)))"))))
