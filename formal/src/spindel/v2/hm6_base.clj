(ns spindel.v2.hm6-base
  "Reachable-state premises for the next P11 proof stage. This conjunction
   attaches the already proved AR and edge-kind invariants to p3l; it does
   not assert arbitrary-step h3 preservation or extend the layer-1 model."
  (:require [ansatz.core :as a]
            [spindel.v2.state :refer :all]
            [spindel.v2.engine :refer :all]
            [spindel.v2.p3 :refer :all]
            [spindel.v2.hm :refer :all]
            [spindel.v2.i14 :refer :all]
            [spindel.v2.hmk2 :refer :all]
            [spindel.v2.ar :refer :all]
            [spindel.v2.hm6 :refer :all]))

(a/defn p3la [w :- World] Bool
  (Bool.and (p3l w) (Bool.and (ar w) (ekb w))))

(a/theorem p3la-parts [w :- World]
  (=> (= (p3la w) true)
      (And (= (p3l w) true) (And (= (ar w) true) (= (ekb w) true))))
  (intro h) (simp only [p3la Bool.and_eq_true] at h) (exact h))
(a/theorem p3la-p3l [w :- World]
  (=> (= (p3la w) true) (= (p3l w) true))
  (intro h) (exact (And.left (p3la-parts w h))))
(a/theorem p3la-ar [w :- World]
  (=> (= (p3la w) true) (= (ar w) true))
  (intro h) (exact (And.left (And.right (p3la-parts w h)))))
(a/theorem p3la-ekb [w :- World]
  (=> (= (p3la w) true) (= (ekb w) true))
  (intro h) (exact (And.right (And.right (p3la-parts w h)))))

(a/theorem p3la-p3i [w :- World]
  (=> (= (p3la w) true) (= (p3i w) true))
  (intro h)
  (have pk := (p3l-parts w (p3la-p3l w h)))
  (have pj := (p3k-parts w (And.left pk)))
  (exact (And.left (p3j-parts w (And.left pj)))))
(a/theorem p3la-p3b [w :- World]
  (=> (= (p3la w) true) (= (p3b w) true))
  (intro h) (exact (And.left (p3i-ctx w (p3la-p3i w h)))))
(a/theorem p3la-g7 [w :- World]
  (=> (= (p3la w) true) (= (g7 w) true))
  (intro h) (exact (p3i-g7 w (p3la-p3i w h))))
(a/theorem p3la-ga [w :- World]
  (=> (= (p3la w) true) (= (ga w) true))
  (intro h) (exact (And.left (p3b-parts w (p3la-p3b w h)))))

(a/theorem p3la-empty [] (= (p3la empty-world) true)
  (simp only [p3la p3l-empty ar-empty ekb-empty Bool.and_self]))
(a/theorem step-p3la [w :- World, it :- Item]
  (=> (= (p3la w) true) (= (p3la (:world (world-step w it))) true))
  (intro h)
  (have hs := (step-rule-r-safe w it (p3la-p3b w h)))
  (have hp := (step-p3l w it (p3la-p3l w h)))
  (have ha := (step-ar w it (p3la-g7 w h) (p3la-ga w h) (p3la-ar w h) hs))
  (have he := (step-ekb w it (p3la-ekb w h) hs))
  (simp only [p3la hp ha he Bool.and_self]))
