(ns ^:ansatz/lean spindel.v2.inv.members.raw-lifts
  "h-mem2 bundle current-members through raw (P11): the lifts from transition to host-guarded-transition and raw, T22 host await, T8 observe."
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
            [spindel.v2.inv.members.await-guard :refer :all]
            [spindel.v2.inv.members.await-raw :refer :all]
            [spindel.v2.inv.members.dispatch :refer :all]))


;; ---- from transition to host-guarded-transition (a released world refuses the host's admissions) and to raw (post: the any-losers)

(a/theorem current-members-host-guarded-transition-lift [xm :- (List Nat), w :- World, it :- Item]
  (=> (= (current-members xm w) true) (= (current-members xm (:world (transition w it))) true) (= (current-members xm (:world (host-guarded-transition w it))) true))
  (intros h h0)
  (cases hs (host-item-refused w it))
  (case [true] (simp only [host-guarded-transition hs refuse]) (exact h))
  (case [false] (simp only [host-guarded-transition hs]) (exact h0)))

(a/theorem current-members-raw-lift [xm :- (List Nat), w :- World, it :- Item]
  (=> (= (chain-to-edge-kinds w) true) (= (current-members xm (:world (host-guarded-transition w it))) true) (= (current-members xm (:world (raw w it))) true))
  (intros hp before)
  (have support := (current-members-host-guarded-transition-support w it hp))
  (simp only [raw])
  (exact (current-members-then-cancel-losers xm w (host-guarded-transition w it) (And.left support) (And.left (And.right support)) (And.right (And.right support)) before)))

;; ---- T22 host await: a fresh host wait edge (no activation's member), the demand, the fast fire

(a/theorem current-members-host-await-raw [xm :- (List Nat), w :- World, d :- Nat]
  (=> (= (chain-to-edge-kinds w) true) (= (current-members xm w) true) (= (current-members xm (host-await-raw w d)) true))
  (intros hp h)
  (have h1 (= (current-members xm (host-await-dem w d)) true))
  (exact (current-members-demand-reactive xm _ d
           (i7-idle-insert-edge-checked w (host-wait-edge d) (Eq.refl true) (chain-to-edge-kinds-i7-idle w hp))
           (act-runs-alive-insert-edge-checked w (host-wait-edge d) (chain-to-edge-kinds-act-runs-alive w hp))
           (current-members-insert-edge-checked xm w (host-wait-edge d) h)))
  (cases hr (fast-ready (host-await-dem w d) d))
  (case [false] (simp only [host-await-raw hr]) (exact h1))
  (case [true] (simp only [host-await-raw hr]) (exact (current-members-fire-edge xm _ _ (:next-id w) h1))))

(a/theorem current-members-transition-host-await [xm :- (List Nat), w :- World, d :- Nat, fresh :- Nat]
  (=> (= (chain-to-edge-kinds w) true) (= (current-members xm w) true) (= (current-members xm (:world (transition w (Item.host-await d fresh)))) true))
  (intros hp h)
  (cases hc (host-await-refused w d))
  (case [true] (simp only [transition hc refuse]) (exact h))
  (case [false]
    (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (deb-exists w d)))
    (case [false] (simp only [transition hc t22-host-await hg refuse]) (exact h))
    (case [true] (simp only [transition hc t22-host-await hg accept]) (exact (current-members-host-await-raw xm w d hp h)))))

;; ---- T8 observe: a fresh observe edge, the demand, the fire on a ready debtor

(a/theorem current-members-t8-observe-any-kind [xm :- (List Nat), w :- World, d :- Nat, cb :- Nat, fresh :- Nat]
  (=> (= (chain-to-edge-kinds w) true) (= (current-members xm w) true) (= (current-members xm (:world (t8-observe-any-kind w d cb fresh))) true))
  (intros hp h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (edge-ok-in w (observe-edge w d cb))))
  (case [false] (simp only [t8-observe-any-kind hg refuse]) (exact h))
  (case [true]
    (have he (= (edge-ok-in w (observe-edge w d cb)) true))
    (have hg2 := hg) (simp only [Bool.and_eq_true] at hg2) (exact (And.right hg2))
    (have h1 := (current-members-demand-reactive xm _ d
                  (i7-idle-insert-edge-fresh w (observe-edge w d cb) (Eq.refl true) he (chain-to-edge-kinds-i7-idle w hp))
                  (act-runs-alive-insert-edge-fresh w (observe-edge w d cb) he (chain-to-edge-kinds-act-runs-alive w hp))
                  (current-members-insert-edge-fresh xm w (observe-edge w d cb) he h)))
    (simp only [t8-observe-any-kind hg accept observe-raw])
    (cases hr (deb-ready (demand-reactive (insert-edge-fresh w (observe-edge w d cb)) d) d))
    (case [false] (simp only [hr]) (exact h1))
    (case [true] (simp only [hr]) (exact (current-members-fire-edge xm _ _ (:next-id w) h1)))))
