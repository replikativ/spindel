(ns spindel.v2.hm13
  "Raw await H3 through post/cancel-losers, before finish/Rule R."
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
            [spindel.v2.hm12 :refer :all]))


;; Exactly five reviewed THMs; no new kernel helpers/DEFs or copier requests.

(a/theorem
 h13-raw0g-support
 [w :- World it :- Item]
 (=>
  (= (p3la w) true)
  (And
   (= (hmk (List.nil Nat) (:world (raw0g w it))) true)
   (And
    (= (g10 (List.nil Nat) (List.nil Nat) (:world (raw0g w it))) true)
    (= (ekb (:world (raw0g w it))) true))))
 (intro hp)
 (have
  hk
  :=
  (raw0g-hmk
   (List.nil Nat)
   w
   it
   (p3la-gd w hp)
   (p3la-g7 w hp)
   (p3la-ga w hp)
   (p3la-g10r w hp)
   (p3la-hmk w hp)))
 (have hg := (raw0g-g10r w it (p3la-g10r w hp)))
 (simp only [g10r] at hg)
 (have he := (raw0g-ekb w it (p3la-ekb w hp)))
 (exact (And.intro hk (And.intro hg he))))


(a/theorem
 h13-post-h3
 [xm :- (List Nat) w :- World o :- Outcome]
 (=>
  (= (hmk (List.nil Nat) (:world o)) true)
  (= (g10 (List.nil Nat) (List.nil Nat) (:world o)) true)
  (= (ekb (:world o)) true)
  (= (h3 xm (:world o)) true)
  (= (h3 xm (:world (post w o))) true))
 (intros hk hg he h)
 (cases ha (:accepted o))
 (case [false] (simp only [post ha]) (exact h))
 (case
  [true]
  (simp only [post ha accept])
  (exact
   (h3-cancel-losers
    xm
    (List.nil Nat)
    (List.nil Nat)
    (List.nil Nat)
    w
    (:world o)
    hk
    hg
    he
    h))))


(a/theorem
 h13-raw0g-await-outcome
 [xm
  :-
  (List Nat)
  w
  :-
  World
  st
  :-
  Nat
  ds
  :-
  (List Nat)
  mode
  :-
  Nat
  k
  :-
  Nat
  fresh
  :-
  Nat
  mine
  :-
  (List Nat)]
 (=>
  (= (p3la w) true)
  (= (h3 xm w) true)
  (And
   (=
    (h3 xm (:world (raw0g w (Item.await st ds mode k fresh mine))))
    true)
   (=>
    (=
     (:accepted (raw0g w (Item.await st ds mode k fresh mine)))
     false)
    (= (:world (raw0g w (Item.await st ds mode k fresh mine))) w))))
 (intros hp h)
 (have
  non-host
  (= (host-item (Item.await st ds mode k fresh mine)) false))
 (rfl)
 (have
  same
  :=
  (raw0g-of w (Item.await st ds mode k fresh mine) non-host))
 (apply And.intro)
 (rw [same])
 (exact
  (And.left
   (h12-raw0-await-outcome xm w st ds mode k fresh mine hp h)))
 (exact (raw0g-refuse w (Item.await st ds mode k fresh mine))))


(a/theorem
 h13-raw-await-accepted
 [w
  :-
  World
  st
  :-
  Nat
  ds
  :-
  (List Nat)
  mode
  :-
  Nat
  k
  :-
  Nat
  fresh
  :-
  Nat
  mine
  :-
  (List Nat)]
 (And
  (=
   (:accepted (raw w (Item.await st ds mode k fresh mine)))
   (:accepted (raw0 w (Item.await st ds mode k fresh mine))))
  (=>
   (= (:accepted (raw0 w (Item.await st ds mode k fresh mine))) true)
   (=
    (raw w (Item.await st ds mode k fresh mine))
    (accept
     (cancel-losers
      w
      (:world (raw0 w (Item.await st ds mode k fresh mine))))))))
 (have
  non-host
  (= (host-item (Item.await st ds mode k fresh mine)) false))
 (rfl)
 (have
  same
  :=
  (raw0g-of w (Item.await st ds mode k fresh mine) non-host))
 (apply And.intro)
 (cases ha (:accepted (raw0 w (Item.await st ds mode k fresh mine))))
 (case [false] (simp only [raw same post ha]))
 (case [true] (simp only [raw same post ha accept]))
 (intro accepted)
 (simp only [raw same post accepted]))


(a/theorem
 h13-raw-await-outcome
 [xm
  :-
  (List Nat)
  w
  :-
  World
  st
  :-
  Nat
  ds
  :-
  (List Nat)
  mode
  :-
  Nat
  k
  :-
  Nat
  fresh
  :-
  Nat
  mine
  :-
  (List Nat)]
 (=>
  (= (p3la w) true)
  (= (h3 xm w) true)
  (And
   (=
    (h3 xm (:world (raw w (Item.await st ds mode k fresh mine))))
    true)
   (=>
    (= (:accepted (raw w (Item.await st ds mode k fresh mine))) false)
    (= (:world (raw w (Item.await st ds mode k fresh mine))) w))))
 (intros hp h)
 (have
  support
  :=
  (h13-raw0g-support w (Item.await st ds mode k fresh mine) hp))
 (have
  before
  :=
  (And.left
   (h13-raw0g-await-outcome xm w st ds mode k fresh mine hp h)))
 (apply And.intro)
 (simp only [raw])
 (exact
  (h13-post-h3
   xm
   w
   (raw0g w (Item.await st ds mode k fresh mine))
   (And.left support)
   (And.left (And.right support))
   (And.right (And.right support))
   before))
 (exact (raw-refuse w (Item.await st ds mode k fresh mine))))
