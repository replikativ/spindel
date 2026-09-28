(ns org.replikativ.spindel.world.what-if-test
  "Live what-ifs (law 11 of the world algebra): the view is the parent now
  under the overrides, the overrides survive the parent's changes, the view
  never mixes moments, and only the signals a watch read move it."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.world.what-if :as wi]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.signal :refer [signal]]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.effects.await :refer [await]]))

(defn- in [c f] (binding [ec/*execution-context* c] (f)))

(defn- eventually
  "Poll `f` until it returns `expected` or 3 s pass; returns the last value."
  [expected f]
  (loop [waited 0]
    (let [v (f)]
      (if (or (= expected v) (>= waited 3000))
        v
        (do (Thread/sleep 20) (recur (+ waited 20)))))))

(defn- quiet
  "Let the engine run for a moment, for assertions that something did NOT
  happen."
  []
  (Thread/sleep 300))

(defmacro ^:private with-parent [[p] & body]
  `(let [~p (ctx/create-execution-context)]
     (try ~@body (finally (ctx/stop-context! ~p)))))

(deftest the-view-follows-the-parent-under-the-overrides
  (with-parent [p]
    (let [a (in p #(signal 1))
          b (in p #(signal 10))
          w (wi/what-if p {a 5})
          seen (atom [])
          stop (wi/watch! w #(spin (+ (:new (track a)) (:new (track b))))
                          #(swap! seen conj %))]
      (is (= [15] (eventually [15] #(deref seen))))
      (testing "a change the watch read reaches the view"
        (in p #(reset! b 20))
        (is (= [15 25] (eventually [15 25] #(deref seen)))))
      (testing "an overridden signal keeps its override"
        (in p #(reset! a 7))
        (quiet)
        (is (= [15 25] @seen))
        (is (= 7 (in p #(deref a))) "the parent has its own value"))
      (stop)
      (wi/stop! w))))

(deftest a-view-is-one-moment-of-the-parent
  ;; A following fork that tracked b could read a derived spin the parent has
  ;; since recomputed from a newer b. A what-if's view cannot.
  (with-parent [p]
    (let [b (in p #(signal 1))
          doubled (in p #(spin (* 2 (:new (track b)))))
          _ (is (= 2 (in p #(deref doubled))))
          w (wi/what-if p {})
          seen (atom [])]
      (wi/watch! w #(spin [(:new (track b)) (await doubled)]) #(swap! seen conj %))
      (is (= [[1 2]] (eventually [[1 2]] #(deref seen))))
      (in p #(reset! b 3))
      (is (= [[1 2] [3 6]] (eventually [[1 2] [3 6]] #(deref seen))))
      (is (every? (fn [[x y]] (= y (* 2 x))) @seen))
      (wi/stop! w))))

(deftest only-what-a-watch-read-moves-it
  (with-parent [p]
    (let [a (in p #(signal 1))
          c (in p #(signal :unrelated))
          w (wi/what-if p {})
          runs (atom 0)]
      (wi/watch! w #(spin (swap! runs inc) (:new (track a))) (fn [_]))
      (is (= 1 (eventually 1 #(deref runs))))
      (in p #(reset! c :changed))
      (quiet)
      (is (= 1 @runs) "a signal nobody read does not re-derive")
      (in p #(reset! a 2))
      (is (= 2 (eventually 2 #(deref runs))))
      (wi/stop! w)
      (in p #(reset! a 3))
      (quiet)
      (is (= 2 @runs) "a stopped what-if does not follow"))))

(deftest a-frozen-copy-keeps-its-moment
  (with-parent [p]
    (let [a (in p #(signal 1))
          b (in p #(signal 10))
          w (wi/what-if p {a 5})
          copy (wi/freeze w)]
      (in p #(reset! b 20))
      (is (= [5 10] (in copy #(deref (spin [(:new (track a)) (:new (track b))])))))
      (is (= [5 10] (in (wi/view w) #(deref (spin [(:new (track a)) (:new (track b))]))))
          "nothing watched b, so the view is still the old moment")
      (wi/stop! w))))
