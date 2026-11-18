(ns spindel.v2.z61-test
  "Z#61 (spec T6): an `all` activation resumes at its first err slot, and its unfilled member tasks
  are cancelled as an `any`'s losers; the group-await fast path stops at the resolving fill (engine
  `await-group!`). Model level (`act-fill`, `fill-slot`, `cancel-losers`) and against the engine
  probes oracle/log-probe-z61-*.edn (generator oracle/gen/probe-z61.clj)."
  (:require [clojure.test :refer [deftest is testing]]
            [spindel.v2.state :as s]
            [spindel.v2.step :as st]
            [spindel.v2.engine :as en]
            [spindel.v2.oracle :as o]))

(def dir "test/spindel/v2/oracle/")
(defn- probe [n] (o/read-log (str dir "log-probe-z61-" n ".edn")))
(defn- row [w t id] (some #(when (= id (:id %)) %) (get w t)))

(def ok (s/->RunResult s/res-ok 7))
(def err (s/->RunResult s/res-err 9))
(defn- act [mode] (s/->ActRow 10 5 mode [(s/->Member 11 0) (s/->Member 12 1) (s/->Member 13 2)]
                              (vec (repeat 3 (s/->RunResult s/res-none 0))) 3 0 []))

(deftest act-fill-fail-fast
  (testing "an err fill of an `all` leaves nothing to wait for"
    (let [a (st/act-fill 11 err (act s/am-all))]
      (is (= 0 (:remaining a)))
      (is (true? (st/act-ready a)))
      (is (= [12 13] (map :edge (:members a))))
      (is (= err (first (:slots a))))))
  (testing "an ok fill of an `all` counts down"
    (let [a (st/act-fill 11 ok (act s/am-all))]
      (is (= 2 (:remaining a)))
      (is (false? (st/act-ready a)))))
  (testing "`one` and `any` are unchanged"
    (is (true? (st/act-ready (st/act-fill 11 ok (act s/am-any)))))
    (is (true? (st/act-ready (st/act-fill 11 err (act s/am-any)))))
    (let [a (st/act-fill 11 err (s/->ActRow 10 5 s/am-one [(s/->Member 11 0)] [(s/->RunResult s/res-none 0)] 1 0 []))]
      (is (= 0 (:remaining a))))))

(deftest loser-modes
  (is (true? (en/group-mode s/am-any)))
  (is (true? (en/group-mode s/am-all)))
  (is (false? (en/group-mode s/am-one))))

(deftest engine-probes-replay
  (doseq [n [1 2 3 4]]
    (let [l (probe n) res (o/replay l :worlds? true)]
      (is (= [(count l) 0 0] ((juxt :checked :n-divergences :resyncs) res)) (str "probe " n)))))

(deftest any-fast-path-stops-at-the-winner
  ;; probe 1: (await-any [s1 s2]) in a computation; s1 fills, s2's dep edge stays armed and the
  ;; computation is not invalidated
  (let [l (probe 1) ws (:worlds (o/replay l :worlds? true))
        w (nth ws 6)]                                   ; `:worlds` = the world after each item
    (is (= [:await 7 [3 4] :any 8 9 []] (:item (nth l 6))))
    (is (= 1 (:epoch (row w :comps 5))))
    (is (= s/ph-armed (:phase (some #(when (= 4 (:debtor %)) %) (:edges w)))))))

(deftest all-fails-fast-and-cancels-the-loser
  ;; probe 2: task 5 awaits all over task 8 (fails on a deferred) and task 11 (parked on another
  ;; deferred); task 8's completion with an error resumes run 6 and cancels task 11's run 12
  (let [l (probe 2) ws (:worlds (o/replay l :worlds? true))
        i (.indexOf ^java.util.List (mapv :item l) [:complete 9 2 12])
        before (nth ws (dec i)) after (nth ws i)]
    (is (pos? i))
    (is (some? (row before :acts 14)) "the `all` activation waits for both")
    (is (nil? (row after :acts 14)) "the first err slot resumes it")
    (is (= s/act-active (:act (row after :runs 6))))
    (is (not= s/res-none (:tag (:result (row after :tasks 11)))) "the loser is cancelled")))
