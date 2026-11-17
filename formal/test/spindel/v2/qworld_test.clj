(ns spindel.v2.qworld-test
  (:require [clojure.test :refer [deftest is]]
            [ansatz.core :as a]
            [spindel.v2.state :as s]
            [spindel.v2.engine :as en]
            [spindel.v2.quiet :as q]
            [spindel.v2.qworld :as qw]
            [spindel.v2.engine-test :as et]))

(def theorems '[step-gc step-gc-rest gc-empty step-qinv qinv-empty quiet-rows raw0-quiet quiet-refused quiet-step quiet-stays])

(deftest theorems-kernel-checked
  (doseq [t theorems]
    (is (some? (.lookup ^ansatz.kernel.Env @a/ansatz-env (ansatz.kernel.Name/fromString (str t)))) (str t))))

;; the Q5 trace (engine_test c1-no-roots-after-release): after the cleanup slice exits the world is
;; quiet, K, gc and I3 hold, it holds only scopes, and items of every kind are refused
(deftest quiet-world-runtime
  (let [w0 s/empty-world
        c (:next-id w0)
        w (:world (en/world-step w0 (et/create-comp-top et/root c 1 1)))
        w (:world (en/world-step w (et/observe c 1 (:next-id w))))
        w (:world (en/world-step w (et/start c (:next-id w))))
        r (:run (et/find-row w :comps c))
        w (:world (en/world-step w (et/schedule r)))
        w (:world (en/world-step w (et/release-world)))
        w (:world (en/world-step w (et/slice-exit r)))]
    (is (true? (en/world-quiet w)))
    (is (true? (q/gk-rest w)) "K")
    (is (true? (qw/gc-rest w)) "every cleanup entry has its run")
    (is (true? (qw/i3 w)) "I3")
    (is (every? empty? ((juxt :comps :tasks :runs :sources :edges :acts :res :cleanup :pubs :forks) w)) "only scopes")
    (doseq [it [(et/start c (:next-id w)) (et/handle-new c) (et/close-scope et/root) (et/append* 3 1 0)
                (et/create-comp-top et/root (:next-id w) 1 1) (et/schedule r) (et/release-world) (et/write 3 1)]]
      (is (= {:accepted false :world w} (into {} (en/world-step w it))) (pr-str it)))))
