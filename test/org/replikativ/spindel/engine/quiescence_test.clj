(ns org.replikativ.spindel.engine.quiescence-test
  "A world is quiescent when nothing it started is left to run: the
  `on-quiescent` callback must not fire while any consequence of a change is
  still in flight, and must fire once it has all happened."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.executor :as executor]
            [org.replikativ.spindel.engine.quiescence :as q]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.combinators :refer [parallel]]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.keyed :refer [keyed children rerun!]]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]))

(defn- when-quiescent
  "Block until `world` reports quiescence; returns what `observe` saw then."
  [world observe]
  (let [p (promise)]
    (q/on-quiescent world #(deliver p (observe)))
    (deref p 10000 ::timeout)))

(defn- busy [ms] (Thread/sleep (long ms)))

(deftest quiescence-waits-for-every-parallel-child
  (let [exec (executor/default-executor)]
    (dotimes [round 30]
      (let [world (ctx/create-execution-context :executor exec)
            done (atom 0)
            result (atom nil)
            n 12]
        (try
          (binding [ec/*execution-context* world]
            (let [outer (spin (let [vs (await (apply parallel
                                                     (for [i (range n)]
                                                       (spin (busy (rand-int 4)) (swap! done inc) i))))]
                                (reset! result (reduce + vs))
                                vs))]
              (outer (fn [_]) (fn [_]))
              (is (= [n (reduce + (range n))]
                     (when-quiescent world (fn [] [@done @result])))
                  (str "round " round))))
          (finally (ctx/stop-context! world)))))))

(deftest quiescence-follows-a-signal-change
  (let [exec (executor/default-executor)
        world (ctx/create-execution-context :executor exec)]
    (try
      (binding [ec/*execution-context* world]
        (let [s (sig/signal 1)
              seen (atom nil)
              outer (spin (let [vs (await (parallel (spin (let [v (:new (track s))] (busy 3) (* 10 v)))
                                                    (spin (busy 2) :other)))]
                            (reset! seen vs)
                            vs))]
          (outer (fn [_]) (fn [_]))
          (is (= [10 :other] (when-quiescent world #(deref seen))))
          (dotimes [i 20]
            (reset! s (+ 2 i))
            (is (= [(* 10 (+ 2 i)) :other] (when-quiescent world #(deref seen)))
                (str "change " i)))))
      (finally (ctx/stop-context! world)))))

(deftest a-busy-sibling-does-not-hold-up-a-fork
  (let [exec (executor/default-executor)
        world (ctx/create-execution-context :executor exec)]
    (try
      (binding [ec/*execution-context* world]
        @(spin :ready)
        (let [a (ctx/fork-context world :mode :frozen)
              b (ctx/fork-context world :mode :frozen)
              release (promise)]
          ;; the blocking work runs as a parallel child, on the executor (a
          ;; spin invoked directly runs on the caller's thread)
          (binding [ec/*execution-context* a]
            ((spin (await (parallel (spin (deref release 5000 nil) :a)))) (fn [_]) (fn [_])))
          (is (= :b-quiet (when-quiescent b (constantly :b-quiet))))
          (is (pos? (q/in-flight a)) "the sibling is still busy")
          (deliver release true)
          (is (= :a-quiet (when-quiescent a (constantly :a-quiet))))))
      (finally (ctx/stop-context! world)))))

(deftest quiescence-after-rerunning-one-key-in-a-fork
  (let [exec (executor/default-executor)
        world (ctx/create-execution-context :executor exec)
        knob (atom {})
        result (atom nil)]
    (try
      (binding [ec/*execution-context* world]
        (let [p (atom nil)
              outer (spin (let [k (keyed :items (range 50)
                                         (fn [i] (spin (busy 1) (+ i (get @knob i 0)))))]
                            (reset! p k)
                            (reset! result (reduce + (await k)))))]
          (outer (fn [_]) (fn [_]))
          (is (= (reduce + (range 50)) (when-quiescent world #(deref result))))
          (dotimes [i 10]
            (let [fork (ctx/fork-context world :mode :frozen)
                  kid (get (children (spin-core/spin-id @p)) i)]
              (swap! knob assoc i 100)
              (binding [ec/*execution-context* fork]
                ((rerun! kid) (fn [_]) (fn [_])))
              ;; each fork is of the original world: only key i moved
              (is (= (+ (reduce + (range 50)) 100)
                     (when-quiescent fork #(deref result)))
                  (str "re-run " i))))))
      (finally (ctx/stop-context! world)))))

(deftest a-refused-task-releases-its-count
  (let [world (ctx/create-execution-context)]
    (try
      (let [t (q/task world (fn [] :ran))]
        (is (= 1 (q/in-flight world)))
        (is (thrown? Exception (q/submit! (fn [_] (throw (ex-info "refused" {}))) t)))
        (is (= 0 (q/in-flight world)) "released when the executor refused it")
        (t)
        (is (= 0 (q/in-flight world)) "running it later releases nothing twice"))
      (finally (ctx/stop-context! world)))))
