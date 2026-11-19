(ns spindel.v2.top
  "Headline statements of the model, in one place (correctness stage 1; the namespace's final home
  is decided by the restructure). Layer 1:

    inv w := p3m w && svb w && inv-i9 w && inv-i10-slice w && i3 w        (the single top invariant)
      p3m            the bundle chain p3b ⊂ … ⊂ p3m (hm18): activations, I12 ranks, I10, I11a and the
                     fork markers, I1, I5 dep-final, I8, the L5 computation facts, I14, h-mark, the
                     alive runs and edge kinds, h-mem2
      svb            I5 observe (`seen` never ahead of the debtor's version)          (inv/base.clj)
      inv-i9         I9 (no activation of an unwinding run outside its cleanup)        (inv.clj)
      inv-i10-slice  I10, D0 half (one slice holder)                                    (inv.clj)
      i3             I3 (every row live, storage, in a cleanup entry or admitted)      (completion/quiet_world.clj)

    inv-empty   inv empty-world
    inv-step    inv w -> inv (world-step w it)            (every item, accepted or refused; `step-inv`
                is the older inv-sample statement of engine.clj)
    Reach1      the worlds reachable from the empty world by steps
    reach-inv   Reach1 w -> inv w"
  (:require [ansatz.core :as a]
            [spindel.v2.state :refer :all]
            [spindel.v2.step :refer :all]
            [spindel.v2.engine :refer :all]
            [spindel.v2.inv.base :refer [svb]]
            [spindel.v2.inv :refer [inv-i9 inv-i10-slice]]
            [spindel.v2.inv.marks-step :refer [p3l]]
            [spindel.v2.inv.members.step :refer [p3m]]
            [spindel.v2.completion.quiet-world :refer [i3]]))

;; ===========================================================================
;; Layer 1: one world
;; ===========================================================================

(a/defn inv [w :- World] Bool
  (Bool.and (p3m w) (Bool.and (svb w) (Bool.and (inv-i9 w) (Bool.and (inv-i10-slice w) (i3 w))))))

(a/theorem inv-top-parts [w :- World]
  (=> (= (inv w) true)
      (And (= (p3m w) true) (And (= (svb w) true) (And (= (inv-i9 w) true) (And (= (inv-i10-slice w) true) (= (i3 w) true))))))
  (intro h) (simp only [inv Bool.and_eq_true] at h) (exact h))

(a/theorem inv-p3m [w :- World] (=> (= (inv w) true) (= (p3m w) true))
  (intro h) (exact (And.left (inv-top-parts w h))))
(a/theorem inv-p3l [w :- World] (=> (= (inv w) true) (= (p3l w) true))
  (intro h) (exact (p3la-p3l w (And.left (p3m-parts w (inv-p3m w h))))))

;; Theorem: the empty world satisfies inv
(a/theorem inv-empty [] (= (inv empty-world) true) (rfl))

;; Theorem: every step (every item, accepted or refused) keeps inv
(a/theorem inv-step [w :- World, it :- Item] (=> (= (inv w) true) (= (inv (:world (world-step w it))) true))
  (intro h)
  (have p := (inv-top-parts w h))
  (have hm := (And.left p))
  (have hv := (And.left (And.right p)))
  (have h9 := (And.left (And.right (And.right p))))
  (have h10 := (And.left (And.right (And.right (And.right p)))))
  (have hi3 := (And.right (And.right (And.right (And.right p)))))
  (have la := (And.left (p3m-parts w hm)))
  (have pb := (p3la-p3b w la))
  (have hs := (p3l-sample w (p3la-p3l w la)))
  (have a1 := (step-p3m w it hm))
  (have a2 := (step-svb-total w it pb hv))
  (have a3 := (step-i9 w it hs h9))
  (have a4 := (step-i10-slice w it h10))
  (have a5 := (step-i3-inv w it hi3))
  (simp only [inv a1 a2 a3 a4 a5 Bool.and_self]))

;; the worlds reachable from the empty world by steps (every item; a refused one changes nothing)
(a/inductive Reach1 [] :in Prop :indices [w World]
  (start [w World] [e (= w empty-world)] :where [w])
  (step [w World] [it Item] [r (Reach1 w)] :where [(:world (world-step w it))]))

;; Theorem: every reachable world satisfies inv
(a/theorem reach-inv [w :- World] (=> (Reach1 w) (= (inv w) true))
  (intro hr)
  (induction hr)
  (case [start w1 e] (exact (Eq.trans (congrArg inv e) inv-empty)))
  (case [step w1 it r ih] (exact (inv-step w1 it ih))))
