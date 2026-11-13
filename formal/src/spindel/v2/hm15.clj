(ns spindel.v2.hm15
  "h-mem2 bundle h3 through raw (P11): the lifts from raw0 to raw0g and raw, T22 host await, T8 observe."
  (:require [ansatz.core :as a]
            [spindel.v2.state :refer :all]
            [spindel.v2.edits :refer :all]
            [spindel.v2.reach :refer :all]
            [spindel.v2.retain :refer :all]
            [spindel.v2.step :refer :all]
            [spindel.v2.rule :refer :all]
            [spindel.v2.engine :refer :all]
            [spindel.v2.rank :refer :all]
            [spindel.v2.rank-step :refer :all]
            [spindel.v2.casc :refer :all]
            [spindel.v2.acts :refer :all]
            [spindel.v2.inv :refer :all]
            [spindel.v2.lit :refer :all]
            [spindel.v2.idle :refer :all]
            [spindel.v2.p3 :refer :all]
            [spindel.v2.hm :refer :all]
            [spindel.v2.i10 :refer :all]
            [spindel.v2.ar :refer :all]
            [spindel.v2.hmk2 :refer :all]
            [spindel.v2.hmk :refer :all]
            [spindel.v2.hm3 :refer :all]
            [spindel.v2.hm5 :refer :all]
            [spindel.v2.hm6 :refer :all]
            [spindel.v2.hm6-base :refer :all]
            [spindel.v2.hm7 :refer :all]
            [spindel.v2.hm8 :refer :all]
            [spindel.v2.i5 :refer :all]
            [spindel.v2.i8 :refer :all]
            [spindel.v2.i1r :refer :all]
            [spindel.v2.hm4 :refer :all]
            [spindel.v2.hm9 :refer :all]
            [spindel.v2.l5 :refer :all]
            [spindel.v2.hm10 :refer :all]
            [spindel.v2.hm11 :refer :all]
            [spindel.v2.hm12 :refer :all]
            [spindel.v2.hm13 :refer :all]
            [spindel.v2.hm14 :refer :all]))


;; ---- from raw0 to raw0g (a released world refuses the host's admissions) and to raw (post: the any-losers)

(a/theorem h15-raw0g-lift [xm :- (List Nat), w :- World, it :- Item]
  (=> (= (h3 xm w) true) (= (h3 xm (:world (raw0 w it))) true) (= (h3 xm (:world (raw0g w it))) true))
  (intros h h0)
  (cases hs (host-shut w it))
  (case [true] (simp only [raw0g hs refuse]) (exact h))
  (case [false] (simp only [raw0g hs]) (exact h0)))

(a/theorem h15-raw-lift [xm :- (List Nat), w :- World, it :- Item]
  (=> (= (p3la w) true) (= (h3 xm (:world (raw0g w it))) true) (= (h3 xm (:world (raw w it))) true))
  (intros hp before)
  (have support := (h13-raw0g-support w it hp))
  (simp only [raw])
  (exact (h13-post-h3 xm w (raw0g w it) (And.left support) (And.left (And.right support)) (And.right (And.right support)) before)))

;; ---- T22 host await: a fresh host wait edge (no activation's member), the demand, the fast fire

(a/theorem h15-host-await-raw-h3 [xm :- (List Nat), w :- World, d :- Nat]
  (=> (= (p3la w) true) (= (h3 xm w) true) (= (h3 xm (host-await-raw w d)) true))
  (intros hp h)
  (have h1 (= (h3 xm (host-await-dem w d)) true))
  (exact (h3-demand-reactive xm _ d
           (g7-insert-edge-checked w (host-wait-edge d) (Eq.refl true) (p3la-g7 w hp))
           (aha-insert-edge-checked w (host-wait-edge d) (p3la-aha w hp))
           (hm3-insert-edge-checked xm w (host-wait-edge d) h)))
  (cases hr (fast-ready (host-await-dem w d) d))
  (case [false] (simp only [host-await-raw hr]) (exact h1))
  (case [true] (simp only [host-await-raw hr]) (exact (h3-fire-edge xm _ _ (:next-id w) h1))))

(a/theorem h15-raw0-host-await-h3 [xm :- (List Nat), w :- World, d :- Nat, fresh :- Nat]
  (=> (= (p3la w) true) (= (h3 xm w) true) (= (h3 xm (:world (raw0 w (Item.host-await d fresh)))) true))
  (intros hp h)
  (cases hc (deb-consuming w d))
  (case [true] (simp only [raw0 hc refuse]) (exact h))
  (case [false]
    (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (deb-exists w d)))
    (case [false] (simp only [raw0 hc t22-host-await hg refuse]) (exact h))
    (case [true] (simp only [raw0 hc t22-host-await hg accept]) (exact (h15-host-await-raw-h3 xm w d hp h)))))

;; ---- T8 observe: a fresh observe edge, the demand, the fire on a ready debtor

(a/theorem h15-t8-full-h3 [xm :- (List Nat), w :- World, d :- Nat, cb :- Nat, fresh :- Nat]
  (=> (= (p3la w) true) (= (h3 xm w) true) (= (h3 xm (:world (t8-full w d cb fresh))) true))
  (intros hp h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (edge-ok-in w (observe-edge w d cb))))
  (case [false] (simp only [t8-full hg refuse]) (exact h))
  (case [true]
    (have he (= (edge-ok-in w (observe-edge w d cb)) true))
    (have hg2 := hg) (simp only [Bool.and_eq_true] at hg2) (exact (And.right hg2))
    (have h1 := (h3-demand-reactive xm _ d
                  (g7-insert-edge-fresh w (observe-edge w d cb) (Eq.refl true) he (p3la-g7 w hp))
                  (insert-edge-fresh-aha w (observe-edge w d cb) he (p3la-aha w hp))
                  (insert-edge-fresh-h3 xm w (observe-edge w d cb) he h)))
    (simp only [t8-full hg accept observe-raw])
    (cases hr (deb-ready (demand-reactive (insert-edge-fresh w (observe-edge w d cb)) d) d))
    (case [false] (simp only [hr]) (exact h1))
    (case [true] (simp only [hr]) (exact (h3-fire-edge xm _ _ (:next-id w) h1)))))
