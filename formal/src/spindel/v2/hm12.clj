(ns spindel.v2.hm12
  "Guarded T6 and raw0 await H3, before post/cancel-losers and Rule R."
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
            [spindel.v2.hm11 :refer :all]))

;; No helper, copier override, new predicate or transition is introduced.

(a/theorem h12-await-raw-h3 [xm :- (List Nat) w :- World r :- RunRow ds :- (List Nat) mode :- Nat k :- Nat mine :- (List Nat) st :- Nat fresh :- Nat]
  (=> (h9-entry xm w r ds mode st fresh) (= (h3 xm (await-raw w r ds mode k mine)) true))
  (intro ent)
  (exact (h11-await-post-h3 xm w r ds mode k mine st fresh ent))
)

(a/theorem h12-t6-accepted [xm :- (List Nat) w :- World r :- RunRow st :- Nat ds :- (List Nat) mode :- Nat k :- Nat fresh :- Nat mine :- (List Nat)]
  (=>
    (= (p3la w) true)
    (= (h3 xm w) true)
    (= (tok-run w st) (Option.some RunRow r))
    (= (:accepted (t6-await w st ds mode k fresh mine)) true)
    (And
      (= (t6-await w st ds mode k fresh mine) (accept (await-raw w r ds mode k mine)))
      (= (h3 xm (:world (t6-await w st ds mode k fresh mine))) true)))
  (intros hp h ht accepted)
  (cases guard (Bool.and (await-ok w r ds mode fresh) (:ok (await-acc w r ds mode k mine))))
  (case [false] (simp [t6-await ht guard refuse] at accepted))
  (case
    [true]
    (have facts := guard)
    (simp only [Bool.and_eq_true] at facts)
    (have ent (h9-entry xm w r ds mode st fresh))
    (exact (And.intro hp (And.intro h (And.intro ht (And.left facts)))))
    (have out (= (t6-await w st ds mode k fresh mine) (accept (await-raw w r ds mode k mine))))
    (simp only [t6-await ht guard])
    (have preserved (= (h3 xm (:world (t6-await w st ds mode k fresh mine))) true))
    (rw [out])
    (exact (h12-await-raw-h3 xm w r ds mode k mine st fresh ent))
    (exact (And.intro out preserved)))
)

(a/theorem h12-t6-outcome [xm :- (List Nat) w :- World st :- Nat ds :- (List Nat) mode :- Nat k :- Nat fresh :- Nat mine :- (List Nat)]
  (=>
    (= (p3la w) true)
    (= (h3 xm w) true)
    (And
      (= (h3 xm (:world (t6-await w st ds mode k fresh mine))) true)
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
      (exact (And.right (h12-t6-accepted xm w r st ds mode k fresh mine hp h ht accepted)))))
  (exact (t6-refuse w st ds mode k fresh mine))
)

(a/theorem h12-raw0-await-outcome [xm :- (List Nat) w :- World st :- Nat ds :- (List Nat) mode :- Nat k :- Nat fresh :- Nat mine :- (List Nat)]
  (=>
    (= (p3la w) true)
    (= (h3 xm w) true)
    (And
      (= (h3 xm (:world (raw0 w (Item.await st ds mode k fresh mine)))) true)
      (=>
        (= (:accepted (raw0 w (Item.await st ds mode k fresh mine))) false)
        (= (:world (raw0 w (Item.await st ds mode k fresh mine))) w))))
  (intros hp h)
  (apply And.intro)
  (cases hd (await-kind-bad w ds))
  (case [true] (simp only [raw0 hd refuse]) (exact h))
  (case [false] (simp only [raw0 hd]) (exact (And.left (h12-t6-outcome xm w st ds mode k fresh mine hp h))))
  (exact (raw0-refuse w (Item.await st ds mode k fresh mine)))
)

