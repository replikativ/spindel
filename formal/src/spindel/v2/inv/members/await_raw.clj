(ns ^:ansatz/lean spindel.v2.inv.members.await-raw
  "Raw await H3 through post/cancel-losers, before finish/Rule R."
  (:require [ansatz.core :as a]
            [spindel.v2.state :refer :all]
            [spindel.v2.edits :refer :all]
            [spindel.v2.reach :refer :all]
            [spindel.v2.retain :refer :all]
            [spindel.v2.step :refer :all]
            [spindel.v2.rule :refer :all]
            [spindel.v2.engine :refer :all]
            [spindel.v2.inv.rank :refer :all]
            [spindel.v2.inv.rank-step :refer :all]
            [spindel.v2.progress.casc :refer :all]
            [spindel.v2.inv.acts :refer :all]
            [spindel.v2.inv :refer :all]
            [spindel.v2.inv.copier :refer :all]
            [spindel.v2.inv.idle :refer :all]
            [spindel.v2.inv.base :refer :all]
            [spindel.v2.inv.comp-facts :refer :all]
            [spindel.v2.inv.i10 :refer :all]
            [spindel.v2.inv.alive-runs :refer :all]
            [spindel.v2.inv.marks-step :refer :all]
            [spindel.v2.inv.marks :refer :all]
            [spindel.v2.inv.members.bundle :refer :all]
            [spindel.v2.inv.members.track-take :refer :all]
            [spindel.v2.inv.members.cascade :refer :all]
            [spindel.v2.inv.members.base :refer :all]
            [spindel.v2.inv.members.react :refer :all]
            [spindel.v2.inv.members.await-prep :refer :all]
            [spindel.v2.inv.i5 :refer :all]
            [spindel.v2.inv.i8 :refer :all]
            [spindel.v2.inv.i1-runs :refer :all]
            [spindel.v2.inv.members.fires :refer :all]
            [spindel.v2.inv.members.await-wire :refer :all]
            [spindel.v2.progress.l5 :refer :all]
            [spindel.v2.inv.members.await-fill :refer :all]
            [spindel.v2.inv.members.await-post :refer :all]
            [spindel.v2.inv.members.await-guard :refer :all]))


;; Exactly five reviewed THMs; no new kernel helpers/DEFs or copier requests.

(a/theorem
 current-members-host-guarded-transition-support
 [w :- World it :- Item]
 (=>
  (= (chain-to-edge-kinds w) true)
  (And
   (= (marks-waiting (List.nil Nat) (:world (host-guarded-transition w it))) true)
   (And
    (= (i10-current-exempt (List.nil Nat) (List.nil Nat) (:world (host-guarded-transition w it))) true)
    (= (edge-kinds (:world (host-guarded-transition w it))) true))))
 (intro hp)
 (have
  hk
  :=
  (marks-waiting-host-guarded-transition
   (List.nil Nat)
   w
   it
   (chain-to-edge-kinds-comp-facts w hp)
   (chain-to-edge-kinds-i7-idle w hp)
   (chain-to-edge-kinds-acts-parked w hp)
   (chain-to-edge-kinds-i10-current w hp)
   (chain-to-edge-kinds-marks-waiting w hp)))
 (have hg := (i10-current-host-guarded-transition w it (chain-to-edge-kinds-i10-current w hp)))
 (simp only [i10-current] at hg)
 (have he := (edge-kinds-host-guarded-transition w it (chain-to-edge-kinds-edge-kinds w hp)))
 (exact (And.intro hk (And.intro hg he))))


(a/theorem
 current-members-then-cancel-losers
 [xm :- (List Nat) w :- World o :- Outcome]
 (=>
  (= (marks-waiting (List.nil Nat) (:world o)) true)
  (= (i10-current-exempt (List.nil Nat) (List.nil Nat) (:world o)) true)
  (= (edge-kinds (:world o)) true)
  (= (current-members xm (:world o)) true)
  (= (current-members xm (:world (then-cancel-losers w o))) true))
 (intros hk hg he h)
 (cases ha (:accepted o))
 (case [false] (simp only [then-cancel-losers ha]) (exact h))
 (case
  [true]
  (simp only [then-cancel-losers ha accept])
  (exact
   (current-members-cancel-losers
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
 current-members-host-guarded-transition-await-outcome
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
  (= (chain-to-edge-kinds w) true)
  (= (current-members xm w) true)
  (And
   (=
    (current-members xm (:world (host-guarded-transition w (Item.await st ds mode k fresh mine))))
    true)
   (=>
    (=
     (:accepted (host-guarded-transition w (Item.await st ds mode k fresh mine)))
     false)
    (= (:world (host-guarded-transition w (Item.await st ds mode k fresh mine))) w))))
 (intros hp h)
 (have
  non-host
  (= (host-item (Item.await st ds mode k fresh mine)) false))
 (rfl)
 (have
  same
  :=
  (host-guarded-transition-non-host w (Item.await st ds mode k fresh mine) non-host))
 (apply And.intro)
 (rw [same])
 (exact
  (And.left
   (current-members-transition-await-outcome xm w st ds mode k fresh mine hp h)))
 (exact (host-guarded-transition-refuse w (Item.await st ds mode k fresh mine))))


(a/theorem
 current-members-raw-await-accepted
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
   (:accepted (transition w (Item.await st ds mode k fresh mine))))
  (=>
   (= (:accepted (transition w (Item.await st ds mode k fresh mine))) true)
   (=
    (raw w (Item.await st ds mode k fresh mine))
    (accept
     (cancel-losers
      w
      (:world (transition w (Item.await st ds mode k fresh mine))))))))
 (have
  non-host
  (= (host-item (Item.await st ds mode k fresh mine)) false))
 (rfl)
 (have
  same
  :=
  (host-guarded-transition-non-host w (Item.await st ds mode k fresh mine) non-host))
 (apply And.intro)
 (cases ha (:accepted (transition w (Item.await st ds mode k fresh mine))))
 (case [false] (simp only [raw same then-cancel-losers ha]))
 (case [true] (simp only [raw same then-cancel-losers ha accept]))
 (intro accepted)
 (simp only [raw same then-cancel-losers accepted]))


(a/theorem
 current-members-raw-await-outcome
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
  (= (chain-to-edge-kinds w) true)
  (= (current-members xm w) true)
  (And
   (=
    (current-members xm (:world (raw w (Item.await st ds mode k fresh mine))))
    true)
   (=>
    (= (:accepted (raw w (Item.await st ds mode k fresh mine))) false)
    (= (:world (raw w (Item.await st ds mode k fresh mine))) w))))
 (intros hp h)
 (have
  support
  :=
  (current-members-host-guarded-transition-support w (Item.await st ds mode k fresh mine) hp))
 (have
  before
  :=
  (And.left
   (current-members-host-guarded-transition-await-outcome xm w st ds mode k fresh mine hp h)))
 (apply And.intro)
 (simp only [raw])
 (exact
  (current-members-then-cancel-losers
   xm
   w
   (host-guarded-transition w (Item.await st ds mode k fresh mine))
   (And.left support)
   (And.left (And.right support))
   (And.right (And.right support))
   before))
 (exact (raw-refuse w (Item.await st ds mode k fresh mine))))
