(ns ^:ansatz/lean spindel.v2.inv.members.base
  "The chain link chain-to-edge-kinds = chain-to-marks-waiting && alive-run-latest && edge-kinds: the AR (spindel.v2.inv.alive-runs) and edge-kind (spindel.v2.inv.members.cascade)
   invariants attached to chain-to-marks-waiting, with `step-chain-to-edge-kinds`. It is the premise world of the current-members (h-mem2) stages
   spindel.v2.inv.members.* from react on (README order), up to spindel.v2.inv.members.step, where chain = chain-to-edge-kinds && current-members [] and `step-chain` close P11."
  (:require [ansatz.core :as a]
            [spindel.v2.state :refer :all]
            [spindel.v2.engine :refer :all]
            [spindel.v2.inv.base :refer :all]
            [spindel.v2.inv.comp-facts :refer :all]
            [spindel.v2.inv.i14 :refer :all]
            [spindel.v2.inv.marks-step :refer :all]
            [spindel.v2.inv.alive-runs :refer :all]
            [spindel.v2.inv.members.cascade :refer :all]))

(a/defn chain-to-edge-kinds [w :- World] Bool
  (Bool.and (chain-to-marks-waiting w) (Bool.and (alive-run-latest w) (edge-kinds w))))

(a/theorem chain-to-edge-kinds-parts [w :- World]
  (=> (= (chain-to-edge-kinds w) true)
      (And (= (chain-to-marks-waiting w) true) (And (= (alive-run-latest w) true) (= (edge-kinds w) true))))
  (intro h) (simp only [chain-to-edge-kinds Bool.and_eq_true] at h) (exact h))
(a/theorem chain-to-edge-kinds-prev [w :- World]
  (=> (= (chain-to-edge-kinds w) true) (= (chain-to-marks-waiting w) true))
  (intro h) (exact (And.left (chain-to-edge-kinds-parts w h))))
(a/theorem chain-to-edge-kinds-alive-run-latest [w :- World]
  (=> (= (chain-to-edge-kinds w) true) (= (alive-run-latest w) true))
  (intro h) (exact (And.left (And.right (chain-to-edge-kinds-parts w h)))))
(a/theorem chain-to-edge-kinds-edge-kinds [w :- World]
  (=> (= (chain-to-edge-kinds w) true) (= (edge-kinds w) true))
  (intro h) (exact (And.right (And.right (chain-to-edge-kinds-parts w h)))))

(a/theorem chain-to-edge-kinds-implies-chain-to-i8-closed [w :- World]
  (=> (= (chain-to-edge-kinds w) true) (= (chain-to-i8-closed w) true))
  (intro h)
  (have pk := (chain-to-marks-waiting-parts w (chain-to-edge-kinds-prev w h)))
  (have pj := (chain-to-i14-ordered-parts w (And.left pk)))
  (exact (And.left (chain-to-comp-facts-parts w (And.left pj)))))
(a/theorem chain-to-edge-kinds-implies-chain-start [w :- World]
  (=> (= (chain-to-edge-kinds w) true) (= (chain-start w) true))
  (intro h) (exact (And.left (chain-to-i8-closed-ctx w (chain-to-edge-kinds-implies-chain-to-i8-closed w h)))))
(a/theorem chain-to-edge-kinds-i7-idle [w :- World]
  (=> (= (chain-to-edge-kinds w) true) (= (i7-idle w) true))
  (intro h) (exact (chain-to-i8-closed-i7-idle w (chain-to-edge-kinds-implies-chain-to-i8-closed w h))))
(a/theorem chain-to-edge-kinds-acts-parked [w :- World]
  (=> (= (chain-to-edge-kinds w) true) (= (acts-parked w) true))
  (intro h) (exact (And.left (chain-start-parts w (chain-to-edge-kinds-implies-chain-start w h)))))

(a/theorem chain-to-edge-kinds-empty [] (= (chain-to-edge-kinds empty-world) true)
  (simp only [chain-to-edge-kinds chain-to-marks-waiting-empty alive-run-latest-empty edge-kinds-empty Bool.and_self]))
(a/theorem step-chain-to-edge-kinds [w :- World, it :- Item]
  (=> (= (chain-to-edge-kinds w) true) (= (chain-to-edge-kinds (:world (world-step w it))) true))
  (intro h)
  (have hs := (step-rule-r-safe w it (chain-to-edge-kinds-implies-chain-start w h)))
  (have hp := (step-chain-to-marks-waiting w it (chain-to-edge-kinds-prev w h)))
  (have ha := (step-alive-run-latest w it (chain-to-edge-kinds-i7-idle w h) (chain-to-edge-kinds-acts-parked w h) (chain-to-edge-kinds-alive-run-latest w h) hs))
  (have he := (step-edge-kinds w it (chain-to-edge-kinds-edge-kinds w h) hs))
  (simp only [chain-to-edge-kinds hp ha he Bool.and_self]))
