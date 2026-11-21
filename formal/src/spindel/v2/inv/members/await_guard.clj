(ns spindel.v2.inv.members.await-guard
  "Guarded T6 and transition await H3, before post/cancel-losers and Rule R."
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
            [spindel.v2.inv.members.await-post :refer :all]))

;; No helper, copier override, new predicate or transition is introduced.

(a/theorem current-members-await-raw [xm :- (List Nat) w :- World r :- RunRow ds :- (List Nat) mode :- Nat k :- Nat mine :- (List Nat) st :- Nat fresh :- Nat]
  (=> (current-members-entry xm w r ds mode st fresh) (= (current-members xm (await-raw w r ds mode k mine)) true))
  (intro ent)
  (exact (current-members-await-post xm w r ds mode k mine st fresh ent))
)

(a/theorem current-members-t6-await-accepted [xm :- (List Nat) w :- World r :- RunRow st :- Nat ds :- (List Nat) mode :- Nat k :- Nat fresh :- Nat mine :- (List Nat)]
  (=>
    (= (chain-to-edge-kinds w) true)
    (= (current-members xm w) true)
    (= (tok-run w st) (Option.some RunRow r))
    (= (:accepted (t6-await w st ds mode k fresh mine)) true)
    (And
      (= (t6-await w st ds mode k fresh mine) (accept (await-raw w r ds mode k mine)))
      (= (current-members xm (:world (t6-await w st ds mode k fresh mine))) true)))
  (intros hp h ht accepted)
  (cases guard (Bool.and (await-ok w r ds mode fresh) (:ok (await-acc w r ds mode k mine))))
  (case [false] (simp [t6-await ht guard refuse] at accepted))
  (case
    [true]
    (have facts := guard)
    (simp only [Bool.and_eq_true] at facts)
    (have ent (current-members-entry xm w r ds mode st fresh))
    (exact (And.intro hp (And.intro h (And.intro ht (And.left facts)))))
    (have out (= (t6-await w st ds mode k fresh mine) (accept (await-raw w r ds mode k mine))))
    (simp only [t6-await ht guard])
    (have preserved (= (current-members xm (:world (t6-await w st ds mode k fresh mine))) true))
    (rw [out])
    (exact (current-members-await-raw xm w r ds mode k mine st fresh ent))
    (exact (And.intro out preserved)))
)

(a/theorem current-members-t6-await-outcome [xm :- (List Nat) w :- World st :- Nat ds :- (List Nat) mode :- Nat k :- Nat fresh :- Nat mine :- (List Nat)]
  (=>
    (= (chain-to-edge-kinds w) true)
    (= (current-members xm w) true)
    (And
      (= (current-members xm (:world (t6-await w st ds mode k fresh mine))) true)
      (=>
        (= (:accepted (t6-await w st ds mode k fresh mine)) false)
        (= (:world (t6-await w st ds mode k fresh mine)) w))))
  (intros hp h)
  (apply And.intro)
  (cases ht (tok-run w st))
  (case [none] (simp only [t6-await ht refuse]) (exact h))
  (case
    [some r]
    (cases guard (Bool.and (await-ok w r ds mode fresh) (:ok (await-acc w r ds mode k mine))))
    (case [false] (simp only [t6-await ht guard refuse]) (exact h))
    (case
      [true]
      (have accepted (= (:accepted (t6-await w st ds mode k fresh mine)) true))
      (simp only [t6-await ht guard accept])
      (exact (And.right (current-members-t6-await-accepted xm w r st ds mode k fresh mine hp h ht accepted)))))
  (exact (t6-await-refuse w st ds mode k fresh mine))
)

(a/theorem current-members-transition-await-outcome [xm :- (List Nat) w :- World st :- Nat ds :- (List Nat) mode :- Nat k :- Nat fresh :- Nat mine :- (List Nat)]
  (=>
    (= (chain-to-edge-kinds w) true)
    (= (current-members xm w) true)
    (And
      (= (current-members xm (:world (transition w (Item.await st ds mode k fresh mine)))) true)
      (=>
        (= (:accepted (transition w (Item.await st ds mode k fresh mine))) false)
        (= (:world (transition w (Item.await st ds mode k fresh mine))) w))))
  (intros hp h)
  (apply And.intro)
  (cases hd (await-refused w st ds mode))
  (case [true] (simp only [transition hd refuse]) (exact h))
  (case [false] (simp only [transition hd]) (exact (And.left (current-members-t6-await-outcome xm w st ds mode k fresh mine hp h))))
  (exact (transition-refuse w (Item.await st ds mode k fresh mine)))
)

