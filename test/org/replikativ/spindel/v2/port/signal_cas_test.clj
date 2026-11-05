(ns org.replikativ.spindel.v2.port.signal-cas-test
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task await]]
            [org.replikativ.spindel.v2.port.helpers :refer [checked-fixture api]]))

(use-fixtures :each checked-fixture)

(deftest test-compare-and-set-signal
  (let [s (v2/signal :a) cur @s]
    (is (false? (compare-and-set! s :WRONG :z))) (is (= :a @s))
    (is (true? (compare-and-set! s cur :b))) (is (= :b @s))
    (is (false? (compare-and-set! s cur :c))) (is (= :b @s))))

(deftest ^:gap test-swap-await-remerges-concurrent-write
  (when-let [swap-await! (api 'swap-await!)]
    (let [s (v2/signal #{}) gate (v2/deferred) calls (atom 0)
          join (fn [cur item] (let [n (swap! calls inc)]
                                (spin (when (= n 1) (await gate)) (conj cur item))))
          t (task (await (swap-await! s join :a)))]
      (swap! s conj :b)
      (gate :go)
      (is (= #{:a :b} (v2/value t)))
      (is (= #{:a :b} @s)))))

(deftest ^:gap test-signalref-watchable-and-fork-correct
  (let [s (v2/signal 0) rc (atom []) fc (atom [])]
    (add-watch s :root (fn [_ _ o n] (swap! rc conj [o n])))
    (let [child (v2/fork! v2/*world*) cs (v2/in-world child s)]
      (try
        (add-watch cs :fork (fn [_ _ o n] (swap! fc conj [o n])))
        (swap! cs inc)
        (is (= [] @rc)) (is (= [[0 1]] @fc))
        (swap! s inc) (is (= [[0 1]] @rc))
        (finally (v2/release-world! child))))))
