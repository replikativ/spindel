(ns org.replikativ.spindel.v2.binding-cljc-test
  "B10 on both platforms: a body keeps the bindings it makes across effects
   and starts from its creator's (CLJS: declared vars only, via `convey`);
   the resuming side's bindings do not reach it and its own do not leak."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is]]
            [org.replikativ.spindel.v2.core :as v2 :refer [task await spin track]]
            [org.replikativ.spindel.incremental.interval :as iv]))

(def ^:dynamic *x* :root)
(def ^:dynamic *y* :root)

(v2/convey *y*)

(defn- now
  "The settled outcome of `h`. CLJS inline worlds settle synchronously."
  [h]
  #?(:clj (try (v2/value h 2000 ::timeout) (catch Exception e [:err (ex-message e)]))
     :cljs (let [a (atom ::pending)]
             (v2/value-async h (fn [v err?] (reset! a (if err? [:err (ex-message v)] v))))
             @a)))

(defn- in-world [f]
  (let [w (v2/world)]
    (try (binding [v2/*world* w] (f)) (finally (v2/release-world! w)))))

(deftest a-body-binding-spans-an-effect
  (in-world
   #(let [d (v2/deferred)
          t (task (binding [*x* :inner] (let [a *x*] (await d) [a *x*])))]
      (is (= :root *x*) "the parked body's binding does not leak out")
      (binding [*x* :deliverer] (v2/deliver! d :go))
      (is (= [:inner :inner] (now t)) "the deliverer's binding does not leak in")
      (is (= :root *x*)))))

(deftest a-binding-exits-to-the-outer-value
  (in-world
   #(let [d (v2/deferred)
          t (task (let [a (binding [*x* :inner] (await d) *x*)] [a *x*]))]
      (v2/deliver! d :go)
      (is (= [:inner :root] (now t))))))

(deftest nested-bindings-of-one-var
  (in-world
   #(let [d (v2/deferred) e (v2/deferred)
          t (task (binding [*x* :outer]
                    (let [a (binding [*x* :inner] (await d) *x*)
                          _ (await e)]
                      [a *x*])))]
      (v2/deliver! d 1)
      (v2/deliver! e 2)
      (is (= [:inner :outer] (now t))))))

(deftest a-set-inside-a-body-binding-persists-across-an-effect
  (in-world
   #(let [d (v2/deferred)
          t (task (binding [*x* :inner] (set! *x* :changed) (await d) *x*))]
      (v2/deliver! d :go)
      (is (= :changed (now t)))
      (is (= :root *x*)))))

(deftest a-child-task-starts-from-the-live-binding
  (in-world
   #(let [d (v2/deferred)
          t (task (let [c (binding [*x* :inner] (task (await d) *x*))] (await c)))]
      (v2/deliver! d :go)
      (is (= :inner (now t))))))

(deftest a-declared-host-binding-reaches-the-body
  (in-world
   #(let [d (v2/deferred)
          t (binding [*y* :creator] (task (let [a *y*] (await d) [a *y*])))]
      (binding [*y* :deliverer] (v2/deliver! d :go))
      (is (= [:creator :creator] (now t))))))

(deftest a-computation-reruns-with-its-creators-declared-binding
  (in-world
   #(let [x (v2/signal 1)
          seen (atom [])
          c (binding [*y* :creator] (spin [(iv/get-new (track x)) *y*]))
          unobserve (v2/observe! c (fn [v _] (swap! seen conj v)))]
      (binding [*y* :writer] (v2/write! x 2))
      (is (= [[1 :creator] [2 :creator]] @seen))
      (unobserve))))

(deftest cancelling-inside-a-body-binding-unwinds-with-its-value
  (in-world
   #(let [d (v2/deferred)
          cleaned (atom nil)
          t (task (binding [*x* :inner]
                    (try (await d) (finally (reset! cleaned *x*)))))]
      (binding [*x* :canceller] (v2/cancel-task! t))
      (is (= :inner @cleaned))
      (is (= :root *x*)))))
