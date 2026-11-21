(ns spindel.v2.layer2.top
  "Headline statement of layer 2 (correctness stage 1; the namespace's final home is decided by the
  restructure; layer 1's is spindel.v2.top, which spindel.v2.layer2.sys builds on):

    sysinv cells pubs := sinv cells && pinv pubs && cinv cells && qsinv cells && qpinv pubs && jinv cells
      sinv / pinv    every live world / live publication basis satisfies the top invariant `inv`
      cinv           completion soundness: a live complete cell is ready
      qsinv / qpinv  every live world / basis is quiet-compatible (unborn-released or quiet-world-inv)
      jinv           the host joins are well formed
    SysReach        the systems reachable from an initial one by the 28 operations of spindel.v2.layer2.sys,
                    each with the premises (guards) its preservation theorems take
    sys-reach-inv   SysReach cells pubs -> sysinv cells pubs"
  (:require [ansatz.core :as a]
            [spindel.v2.state :refer :all]
            [spindel.v2.step :refer :all]
            [spindel.v2.engine :refer :all]
            [spindel.v2.top :refer [inv]]
            [spindel.v2.layer2.sys :refer :all]))

;; ===========================================================================
;; Layer 2: a system of worlds (spindel.v2.layer2.sys)
;; ===========================================================================

;; the system invariant: every live world and every live publication's basis satisfies inv; completion
;; soundness; every live world quiet-compatible (and every live basis); host joins well formed
(a/defn sysinv [cells :- (=> Nat Cell), pubs :- (=> Nat Pub)] Prop
  (And (sinv cells) (And (pinv pubs) (And (cinv cells) (And (qsinv cells) (And (qpinv pubs) (jinv cells)))))))
(a/theorem sysinv-mk [cells :- (=> Nat Cell), pubs :- (=> Nat Pub)]
  (=> (sinv cells) (pinv pubs) (cinv cells) (qsinv cells) (qpinv pubs) (jinv cells) (sysinv cells pubs))
  (intros a b c d e f) (simp only [sysinv]) (exact (And.intro a (And.intro b (And.intro c (And.intro d (And.intro e f)))))))
(a/theorem sysinv-s [cells :- (=> Nat Cell), pubs :- (=> Nat Pub)] (=> (sysinv cells pubs) (sinv cells))
  (intro h) (simp only [sysinv] at h) (exact (And.left h)))
(a/theorem sysinv-p [cells :- (=> Nat Cell), pubs :- (=> Nat Pub)] (=> (sysinv cells pubs) (pinv pubs))
  (intro h) (simp only [sysinv] at h) (exact (And.left (And.right h))))
(a/theorem sysinv-c [cells :- (=> Nat Cell), pubs :- (=> Nat Pub)] (=> (sysinv cells pubs) (cinv cells))
  (intro h) (simp only [sysinv] at h) (exact (And.left (And.right (And.right h)))))
(a/theorem sysinv-q [cells :- (=> Nat Cell), pubs :- (=> Nat Pub)] (=> (sysinv cells pubs) (qsinv cells))
  (intro h) (simp only [sysinv] at h) (exact (And.left (And.right (And.right (And.right h))))))
(a/theorem sysinv-qp [cells :- (=> Nat Cell), pubs :- (=> Nat Pub)] (=> (sysinv cells pubs) (qpinv pubs))
  (intro h) (simp only [sysinv] at h) (exact (And.left (And.right (And.right (And.right (And.right h)))))))
(a/theorem sysinv-j [cells :- (=> Nat Cell), pubs :- (=> Nat Pub)] (=> (sysinv cells pubs) (jinv cells))
  (intro h) (simp only [sysinv] at h) (exact (And.right (And.right (And.right (And.right (And.right h)))))))
(a/theorem pinv-none [pubs :- (=> Nat Pub)] (=> (forall [p :- Nat] (= (:live (pubs p)) false)) (pinv pubs))
  (intro h) (simp only [pinv]) (intros p hl) (rw [(h p)] at hl) (cases hl))

;; the systems reachable from an initial one (live cells hold the empty world, none complete, no join, no
;; live publication) by the operations of spindel.v2.layer2.sys, each with the premises its theorems take: a fork,
;; fork effect or instance takes an id no cell has accepted, from a live cell (a live publication); a
;; publication is made from a live cell; a disown is of a cell that is not complete
(a/inductive SysReach [] :in Prop :indices [cells (=> Nat Cell) pubs (=> Nat Pub)]
  (init [cells (=> Nat Cell)] [pubs (=> Nat Pub)]
        [h0 (forall [k :- Nat] (=> (= (:live (cells k)) true) (= (:world (cells k)) empty-world)))]
        [hc (forall [k :- Nat] (= (:complete (cells k)) false))]
        [hj (forall [k :- Nat] (=> (= (:live (cells k)) true) (= (:joins (cells k)) (List.nil Join))))]
        [hp (forall [p :- Nat] (= (:live (pubs p)) false))]
        [hr0 (forall [k :- Nat] (= (:rpend (cells k)) false))]
        :where [cells pubs])
  (step [cells (=> Nat Cell)] [pubs (=> Nat Pub)] [k Nat] [it Item] [r (SysReach cells pubs)] [hr0 (= (:rpend (cells k)) false)] :where [(sys-step cells k it) pubs])
  (fork [cells (=> Nat Cell)] [pubs (=> Nat Pub)] [k Nat] [m Nat] [owner Nat] [r (SysReach cells pubs)] [hl (= (:live (cells k)) true)] [hf (forall [j :- Nat] (= (tbl-all (nat-ne m) (:kids (cells j))) true))] [hr0 (= (:rpend (cells k)) false)] :where [(sys-fork cells k m owner) pubs])
  (wake [cells (=> Nat Cell)] [pubs (=> Nat Pub)] [k Nat] [r (SysReach cells pubs)] [hr0 (= (:rpend (cells k)) false)] :where [(sys-wake cells k) pubs])
  (accept [cells (=> Nat Cell)] [pubs (=> Nat Pub)] [k Nat] [m Nat] [r (SysReach cells pubs)]  :where [(sys-accept cells k m) pubs])
  (complete [cells (=> Nat Cell)] [pubs (=> Nat Pub)] [k Nat] [r (SysReach cells pubs)]  :where [(sys-complete cells k) pubs])
  (drop [cells (=> Nat Cell)] [pubs (=> Nat Pub)] [k Nat] [r (SysReach cells pubs)]  :where [(sys-drop cells k) pubs])
  (fork-effect [cells (=> Nat Cell)] [pubs (=> Nat Pub)] [k Nat] [m Nat] [owner Nat] [st Nat] [kont Nat] [v Nat] [r (SysReach cells pubs)] [hl (= (:live (cells k)) true)] [hf (forall [j :- Nat] (= (tbl-all (nat-ne m) (:kids (cells j))) true))] [hr0 (= (:rpend (cells k)) false)] :where [(sys-fork-effect-g cells k m owner st kont v) pubs])
  (publish [cells (=> Nat Cell)] [pubs (=> Nat Pub)] [k Nat] [p Nat] [st Nat] [kont Nat] [fresh Nat] [r (SysReach cells pubs)] [hl (= (:live (cells k)) true)] [hr0 (= (:rpend (cells k)) false)] :where [(sys-publish cells k st kont fresh) (pubs-publish cells pubs k p st kont fresh)])
  (resume [cells (=> Nat Cell)] [pubs (=> Nat Pub)] [p Nat] [v Nat] [r (SysReach cells pubs)] [hr0 (= (:rpend (cells (:cell (pubs p)))) false)] :where [(sys-resume cells pubs p v) pubs])
  (instantiate [cells (=> Nat Cell)] [pubs (=> Nat Pub)] [p Nat] [m Nat] [owner Nat] [r (SysReach cells pubs)] [hlp (= (:live (pubs p)) true)] [hf (forall [j :- Nat] (= (tbl-all (nat-ne m) (:kids (cells j))) true))] :where [(sys-instantiate-g cells pubs p m owner) pubs])
  (activate [cells (=> Nat Cell)] [pubs (=> Nat Pub)] [m Nat] [v Nat] [r (SysReach cells pubs)] [hr0 (= (:rpend (cells m)) false)] :where [(sys-activate cells m v) pubs])
  (abandon [cells (=> Nat Cell)] [pubs (=> Nat Pub)] [p Nat] [r (SysReach cells pubs)] [hr0 (= (:rpend (cells (:cell (pubs p)))) false)] :where [(sys-abandon cells pubs p) (pubs-abandon pubs p)])
  (merge [cells (=> Nat Cell)] [pubs (=> Nat Pub)] [k Nat] [m Nat] [b World] [rv (=> Nat Nat Nat Nat (Option Nat))] [r (SysReach cells pubs)] [hr0 (= (:rpend (cells k)) false)] [hr1 (= (:rpend (cells m)) false)] :where [(sys-merge cells k m b rv) pubs])
  (merge-release [cells (=> Nat Cell)] [pubs (=> Nat Pub)] [k Nat] [m Nat] [b World] [rv (=> Nat Nat Nat Nat (Option Nat))] [r (SysReach cells pubs)] [hr0 (= (:rpend (cells k)) false)] [hr1 (= (:rpend (cells m)) false)] :where [(sys-merge-release cells k m b rv) pubs])
  (seal [cells (=> Nat Cell)] [pubs (=> Nat Pub)] [k Nat] [r (SysReach cells pubs)] [hr0 (= (:rpend (cells k)) false)] :where [(sys-seal cells k) pubs])
  (idle-release [cells (=> Nat Cell)] [pubs (=> Nat Pub)] [m Nat] [r (SysReach cells pubs)]  :where [(sys-idle-release cells m) pubs])
  (release-unborn [cells (=> Nat Cell)] [pubs (=> Nat Pub)] [k Nat] [r (SysReach cells pubs)] [hr0 (= (:rpend (cells k)) false)] :where [(sys-release-unborn cells k) pubs])
  (join [cells (=> Nat Cell)] [pubs (=> Nat Pub)] [k Nat] [t Nat] [r (SysReach cells pubs)]  :where [(sys-join cells k t) pubs])
  (deliver [cells (=> Nat Cell)] [pubs (=> Nat Pub)] [k Nat] [r (SysReach cells pubs)]  :where [(sys-deliver cells k) pubs])
  (withdraw [cells (=> Nat Cell)] [pubs (=> Nat Pub)] [k Nat] [x Nat] [r (SysReach cells pubs)]  :where [(sys-withdraw cells k x) pubs])
  (reown [cells (=> Nat Cell)] [pubs (=> Nat Pub)] [m Nat] [k Nat] [r (SysReach cells pubs)]  :where [(sys-reown cells m k) pubs])
  (xfer-reserve [cells (=> Nat Cell)] [pubs (=> Nat Pub)] [m Nat] [k2 Nat] [n (List Nat)] [r (SysReach cells pubs)]  :where [(sys-xfer-reserve cells m k2 n) pubs])
  (unseal [cells (=> Nat Cell)] [pubs (=> Nat Pub)] [k Nat] [r (SysReach cells pubs)] [hr0 (= (:rpend (cells k)) false)] :where [(sys-unseal cells k) pubs])
  (own [cells (=> Nat Cell)] [pubs (=> Nat Pub)] [k Nat] [s Nat] [m Nat] [r (SysReach cells pubs)] [hr0 (= (:rpend (cells k)) false)] :where [(sys-own cells k s m) pubs])
  (owned-done [cells (=> Nat Cell)] [pubs (=> Nat Pub)] [k Nat] [s Nat] [c Nat] [r (SysReach cells pubs)] [hr0 (= (:rpend (cells k)) false)] :where [(sys-owned-done cells k s c) pubs])
  (drain [cells (=> Nat Cell)] [pubs (=> Nat Pub)] [k Nat] [r (SysReach cells pubs)] [hr0 (= (:rpend (cells k)) false)] :where [(sys-drain cells k) pubs])
  (disown [cells (=> Nat Cell)] [pubs (=> Nat Pub)] [k Nat] [m Nat] [r (SysReach cells pubs)] [hk (= (:complete (cells k)) false)] :where [(sys-disown cells k m) pubs])
  (xfer-move [cells (=> Nat Cell)] [pubs (=> Nat Pub)] [m Nat] [k2 Nat] [r (SysReach cells pubs)]  :where [(sys-xfer-move cells m k2) pubs])
  (retire [cells (=> Nat Cell)] [pubs (=> Nat Pub)] [k Nat] [v Nat] [r (SysReach cells pubs)]  :where [(sys-retire cells k v) pubs]))

;; Theorem (layer 2): every reachable system satisfies the system invariant
(a/theorem sys-reach-inv [cells :- (=> Nat Cell), pubs :- (=> Nat Pub)] (=> (SysReach cells pubs) (sysinv cells pubs))
  (intro hr)
  (induction hr)
  (case [init cells pubs h0 hc hj hp hr0]
    (exact (sysinv-mk cells pubs (sinv-init cells h0) (pinv-none pubs hp) (cinv-none cells hc) (qsinv-init cells h0)
             (qpinv-none pubs hp) (jinv-init cells hj))))
  (case [step cells pubs k it r hr0 ih]
    (have S := (sysinv-s _ _ ih)) (have Pp := (sysinv-p _ _ ih)) (have Cc := (sysinv-c _ _ ih))
    (have Q := (sysinv-q _ _ ih)) (have QP := (sysinv-qp _ _ ih)) (have J := (sysinv-j _ _ ih))
    (exact (sysinv-mk _ _ (sinv-step cells k it S) Pp (cinv-step-q cells k it S Q Cc) (qsinv-step cells k it S Q) QP (jinv-step cells k it J))))
  (case [fork cells pubs k m owner r hl hf hr0 ih]
    (have S := (sysinv-s _ _ ih)) (have Pp := (sysinv-p _ _ ih)) (have Cc := (sysinv-c _ _ ih))
    (have Q := (sysinv-q _ _ ih)) (have QP := (sysinv-qp _ _ ih)) (have J := (sysinv-j _ _ ih))
    (exact (sysinv-mk _ _ (sinv-fork cells k m owner S hl) Pp (cinv-fork cells k m owner Cc hf) (qsinv-fork cells k m owner Q hl) QP (jinv-fork cells k m owner J))))
  (case [wake cells pubs k r hr0 ih]
    (have S := (sysinv-s _ _ ih)) (have Pp := (sysinv-p _ _ ih)) (have Cc := (sysinv-c _ _ ih))
    (have Q := (sysinv-q _ _ ih)) (have QP := (sysinv-qp _ _ ih)) (have J := (sysinv-j _ _ ih))
    (exact (sysinv-mk _ _ (sinv-wake cells k S) Pp (cinv-wake-q cells k S Q Cc) (qsinv-wake cells k S Q) QP (jinv-wake cells k J))))
  (case [accept cells pubs k m r ih]
    (have S := (sysinv-s _ _ ih)) (have Pp := (sysinv-p _ _ ih)) (have Cc := (sysinv-c _ _ ih))
    (have Q := (sysinv-q _ _ ih)) (have QP := (sysinv-qp _ _ ih)) (have J := (sysinv-j _ _ ih))
    (exact (sysinv-mk _ _ (sinv-accept cells k m S) Pp (cinv-accept cells k m Cc) (qsinv-accept cells k m Q) QP (jinv-accept cells k m J))))
  (case [complete cells pubs k r ih]
    (have S := (sysinv-s _ _ ih)) (have Pp := (sysinv-p _ _ ih)) (have Cc := (sysinv-c _ _ ih))
    (have Q := (sysinv-q _ _ ih)) (have QP := (sysinv-qp _ _ ih)) (have J := (sysinv-j _ _ ih))
    (exact (sysinv-mk _ _ (sinv-complete cells k S) Pp (cinv-complete cells k Cc) (qsinv-complete cells k Q) QP (jinv-complete cells k J))))
  (case [drop cells pubs k r ih]
    (have S := (sysinv-s _ _ ih)) (have Pp := (sysinv-p _ _ ih)) (have Cc := (sysinv-c _ _ ih))
    (have Q := (sysinv-q _ _ ih)) (have QP := (sysinv-qp _ _ ih)) (have J := (sysinv-j _ _ ih))
    (exact (sysinv-mk _ _ (sinv-drop cells k S) Pp (cinv-drop cells k Cc) (qsinv-drop cells k Q) QP (jinv-drop cells k J))))
  (case [fork-effect cells pubs k m owner st kont v r hl hf hr0 ih]
    (have S := (sysinv-s _ _ ih)) (have Pp := (sysinv-p _ _ ih)) (have Cc := (sysinv-c _ _ ih))
    (have Q := (sysinv-q _ _ ih)) (have QP := (sysinv-qp _ _ ih)) (have J := (sysinv-j _ _ ih))
    (exact (sysinv-mk _ _ (sinv-fork-effect-g cells k m owner st kont v S hl) Pp (cinv-fork-effect-g cells k m owner st kont v Cc hf) (qsinv-fork-effect-g cells k m owner st kont v Q hl) QP (jinv-fork-effect-g cells k m owner st kont v J))))
  (case [publish cells pubs k p st kont fresh r hl hr0 ih]
    (have S := (sysinv-s _ _ ih)) (have Pp := (sysinv-p _ _ ih)) (have Cc := (sysinv-c _ _ ih))
    (have Q := (sysinv-q _ _ ih)) (have QP := (sysinv-qp _ _ ih)) (have J := (sysinv-j _ _ ih))
    (exact (sysinv-mk _ _ (sinv-step cells k (publish-item st kont fresh) S) (pinv-publish cells pubs k p st kont fresh S hl Pp) (cinv-publish-q cells k st kont fresh S Q Cc) (qsinv-publish cells k st kont fresh S Q) (qpinv-publish cells pubs k p st kont fresh S Q hl QP) (jinv-publish cells k st kont fresh J))))
  (case [resume cells pubs p v r hr0 ih]
    (have S := (sysinv-s _ _ ih)) (have Pp := (sysinv-p _ _ ih)) (have Cc := (sysinv-c _ _ ih))
    (have Q := (sysinv-q _ _ ih)) (have QP := (sysinv-qp _ _ ih)) (have J := (sysinv-j _ _ ih))
    (exact (sysinv-mk _ _ (sinv-resume cells pubs p v S) Pp (cinv-resume-q cells pubs p v S Q Cc) (qsinv-resume cells pubs p v S Q) QP (jinv-resume cells pubs p v J))))
  (case [instantiate cells pubs p m owner r hlp hf ih]
    (have S := (sysinv-s _ _ ih)) (have Pp := (sysinv-p _ _ ih)) (have Cc := (sysinv-c _ _ ih))
    (have Q := (sysinv-q _ _ ih)) (have QP := (sysinv-qp _ _ ih)) (have J := (sysinv-j _ _ ih))
    (exact (sysinv-mk _ _ (sinv-instantiate-g cells pubs p m owner S Pp hlp) Pp (cinv-instantiate-g cells pubs p m owner Cc hf) (qsinv-instantiate-g cells pubs p m owner Q QP hlp) QP (jinv-instantiate-g cells pubs p m owner J))))
  (case [activate cells pubs m v r hr0 ih]
    (have S := (sysinv-s _ _ ih)) (have Pp := (sysinv-p _ _ ih)) (have Cc := (sysinv-c _ _ ih))
    (have Q := (sysinv-q _ _ ih)) (have QP := (sysinv-qp _ _ ih)) (have J := (sysinv-j _ _ ih))
    (exact (sysinv-mk _ _ (sinv-activate cells m v S) Pp (cinv-activate cells m v Cc) (qsinv-activate cells m v Q) QP (jinv-activate cells m v J))))
  (case [abandon cells pubs p r hr0 ih]
    (have S := (sysinv-s _ _ ih)) (have Pp := (sysinv-p _ _ ih)) (have Cc := (sysinv-c _ _ ih))
    (have Q := (sysinv-q _ _ ih)) (have QP := (sysinv-qp _ _ ih)) (have J := (sysinv-j _ _ ih))
    (exact (sysinv-mk _ _ (sinv-step cells (:cell (pubs p)) (Item.cancel (:run (pubs p))) S) (pinv-abandon pubs p Pp) (cinv-abandon-q cells pubs p S Q Cc) (qsinv-abandon cells pubs p S Q) (qpinv-abandon pubs p QP) (jinv-abandon cells pubs p J))))
  (case [merge cells pubs k m b rv r hr0 hr1 ih]
    (have S := (sysinv-s _ _ ih)) (have Pp := (sysinv-p _ _ ih)) (have Cc := (sysinv-c _ _ ih))
    (have Q := (sysinv-q _ _ ih)) (have QP := (sysinv-qp _ _ ih)) (have J := (sysinv-j _ _ ih))
    (exact (sysinv-mk _ _ (sinv-merge cells k m b rv S) Pp (cinv-merge-q cells k m b rv S Q Cc) (qsinv-merge cells k m b rv S Q) QP (jinv-merge cells k m b rv J))))
  (case [merge-release cells pubs k m b rv r hr0 hr1 ih]
    (have S := (sysinv-s _ _ ih)) (have Pp := (sysinv-p _ _ ih)) (have Cc := (sysinv-c _ _ ih))
    (have Q := (sysinv-q _ _ ih)) (have QP := (sysinv-qp _ _ ih)) (have J := (sysinv-j _ _ ih))
    (exact (sysinv-mk _ _ (sinv-merge-release cells k m b rv S) Pp (cinv-merge-release-q cells k m b rv S Q Cc) (qsinv-merge-release cells k m b rv S Q) QP (jinv-merge-release cells k m b rv J))))
  (case [seal cells pubs k r hr0 ih]
    (have S := (sysinv-s _ _ ih)) (have Pp := (sysinv-p _ _ ih)) (have Cc := (sysinv-c _ _ ih))
    (have Q := (sysinv-q _ _ ih)) (have QP := (sysinv-qp _ _ ih)) (have J := (sysinv-j _ _ ih))
    (exact (sysinv-mk _ _ (sinv-seal cells k S) Pp (cinv-seal cells k Cc) (qsinv-seal cells k Q) QP (jinv-seal cells k J))))
  (case [idle-release cells pubs m r ih]
    (have S := (sysinv-s _ _ ih)) (have Pp := (sysinv-p _ _ ih)) (have Cc := (sysinv-c _ _ ih))
    (have Q := (sysinv-q _ _ ih)) (have QP := (sysinv-qp _ _ ih)) (have J := (sysinv-j _ _ ih))
    (exact (sysinv-mk _ _ (sinv-idle-release cells m S) Pp (cinv-idle-release cells m Cc) (qsinv-idle-release cells m Q) QP (jinv-idle-release cells m J))))
  (case [release-unborn cells pubs k r hr0 ih]
    (have S := (sysinv-s _ _ ih)) (have Pp := (sysinv-p _ _ ih)) (have Cc := (sysinv-c _ _ ih))
    (have Q := (sysinv-q _ _ ih)) (have QP := (sysinv-qp _ _ ih)) (have J := (sysinv-j _ _ ih))
    (exact (sysinv-mk _ _ (sinv-release-unborn cells k S) Pp (cinv-release-unborn cells k Cc) (qsinv-release-unborn cells k Q) QP (jinv-release-unborn cells k J))))
  (case [join cells pubs k t r ih]
    (have S := (sysinv-s _ _ ih)) (have Pp := (sysinv-p _ _ ih)) (have Cc := (sysinv-c _ _ ih))
    (have Q := (sysinv-q _ _ ih)) (have QP := (sysinv-qp _ _ ih)) (have J := (sysinv-j _ _ ih))
    (exact (sysinv-mk _ _ (sinv-join cells k t S) Pp (cinv-join cells k t Cc) (qsinv-join cells k t Q) QP (jinv-join cells k t J))))
  (case [deliver cells pubs k r ih]
    (have S := (sysinv-s _ _ ih)) (have Pp := (sysinv-p _ _ ih)) (have Cc := (sysinv-c _ _ ih))
    (have Q := (sysinv-q _ _ ih)) (have QP := (sysinv-qp _ _ ih)) (have J := (sysinv-j _ _ ih))
    (exact (sysinv-mk _ _ (sinv-deliver cells k S) Pp (cinv-deliver cells k Cc) (qsinv-deliver cells k Q) QP (jinv-deliver cells k J))))
  (case [withdraw cells pubs k x r ih]
    (have S := (sysinv-s _ _ ih)) (have Pp := (sysinv-p _ _ ih)) (have Cc := (sysinv-c _ _ ih))
    (have Q := (sysinv-q _ _ ih)) (have QP := (sysinv-qp _ _ ih)) (have J := (sysinv-j _ _ ih))
    (exact (sysinv-mk _ _ (sinv-withdraw cells k x S) Pp (cinv-withdraw cells k x Cc) (qsinv-withdraw cells k x Q) QP (jinv-withdraw cells k x J))))
  (case [reown cells pubs m k r ih]
    (have S := (sysinv-s _ _ ih)) (have Pp := (sysinv-p _ _ ih)) (have Cc := (sysinv-c _ _ ih))
    (have Q := (sysinv-q _ _ ih)) (have QP := (sysinv-qp _ _ ih)) (have J := (sysinv-j _ _ ih))
    (exact (sysinv-mk _ _ (sinv-reown cells m k S) Pp (cinv-reown cells m k Cc) (qsinv-reown cells m k Q) QP (jinv-reown cells m k J))))
  (case [xfer-reserve cells pubs m k2 n r ih]
    (have S := (sysinv-s _ _ ih)) (have Pp := (sysinv-p _ _ ih)) (have Cc := (sysinv-c _ _ ih))
    (have Q := (sysinv-q _ _ ih)) (have QP := (sysinv-qp _ _ ih)) (have J := (sysinv-j _ _ ih))
    (exact (sysinv-mk _ _ (sinv-xfer-reserve cells m k2 n S) Pp (cinv-xfer-reserve cells m k2 n Cc) (qsinv-xfer-reserve cells m k2 n Q) QP (jinv-xfer-reserve cells m k2 n J))))
  (case [unseal cells pubs k r hr0 ih]
    (have S := (sysinv-s _ _ ih)) (have Pp := (sysinv-p _ _ ih)) (have Cc := (sysinv-c _ _ ih))
    (have Q := (sysinv-q _ _ ih)) (have QP := (sysinv-qp _ _ ih)) (have J := (sysinv-j _ _ ih))
    (exact (sysinv-mk _ _ (sinv-unseal cells k S) Pp (cinv-unseal cells k Cc) (qsinv-unseal cells k Q) QP (jinv-unseal cells k J))))
  (case [own cells pubs k s m r hr0 ih]
    (have S := (sysinv-s _ _ ih)) (have Pp := (sysinv-p _ _ ih)) (have Cc := (sysinv-c _ _ ih))
    (have Q := (sysinv-q _ _ ih)) (have QP := (sysinv-qp _ _ ih)) (have J := (sysinv-j _ _ ih))
    (exact (sysinv-mk _ _ (sinv-own cells k s m S) Pp (cinv-own cells k s m Cc) (qsinv-own cells k s m S Q) QP (jinv-own cells k s m J))))
  (case [owned-done cells pubs k s c r hr0 ih]
    (have S := (sysinv-s _ _ ih)) (have Pp := (sysinv-p _ _ ih)) (have Cc := (sysinv-c _ _ ih))
    (have Q := (sysinv-q _ _ ih)) (have QP := (sysinv-qp _ _ ih)) (have J := (sysinv-j _ _ ih))
    (exact (sysinv-mk _ _ (sinv-owned-done cells k s c S) Pp (cinv-owned-done cells k s c S Cc) (qsinv-owned-done cells k s c S Q) QP (jinv-owned-done cells k s c J))))
  (case [drain cells pubs k r hr0 ih]
    (have S := (sysinv-s _ _ ih)) (have Pp := (sysinv-p _ _ ih)) (have Cc := (sysinv-c _ _ ih))
    (have Q := (sysinv-q _ _ ih)) (have QP := (sysinv-qp _ _ ih)) (have J := (sysinv-j _ _ ih))
    (exact (sysinv-mk _ _ (sinv-drain cells k S) Pp (cinv-drain cells k S Cc) (qsinv-drain cells k S Q) QP (jinv-drain cells k J))))
  (case [disown cells pubs k m r hk ih]
    (have S := (sysinv-s _ _ ih)) (have Pp := (sysinv-p _ _ ih)) (have Cc := (sysinv-c _ _ ih))
    (have Q := (sysinv-q _ _ ih)) (have QP := (sysinv-qp _ _ ih)) (have J := (sysinv-j _ _ ih))
    (exact (sysinv-mk _ _ (sinv-disown cells k m S) Pp (cinv-disown cells k m Cc hk) (qsinv-disown cells k m Q) QP (jinv-disown cells k m J))))
  (case [xfer-move cells pubs m k2 r ih]
    (have S := (sysinv-s _ _ ih)) (have Pp := (sysinv-p _ _ ih)) (have Cc := (sysinv-c _ _ ih))
    (have Q := (sysinv-q _ _ ih)) (have QP := (sysinv-qp _ _ ih)) (have J := (sysinv-j _ _ ih))
    (exact (sysinv-mk _ _ (sinv-xfer-move cells m k2 S) Pp (cinv-xfer-move cells m k2 S Cc) (qsinv-xfer-move cells m k2 S Q) QP (jinv-xfer-move cells m k2 J))))
  (case [retire cells pubs k v r ih]
    (have S := (sysinv-s _ _ ih)) (have Pp := (sysinv-p _ _ ih)) (have Cc := (sysinv-c _ _ ih))
    (have Q := (sysinv-q _ _ ih)) (have QP := (sysinv-qp _ _ ih)) (have J := (sysinv-j _ _ ih))
    (exact (sysinv-mk _ _ (sinv-retire cells k v S) Pp (cinv-retire-q cells k v S Q Cc) (qsinv-retire cells k v S Q) QP (jinv-retire cells k v J)))))

;; Theorem (Z#77, LOC3 / retire-precedes): in every reachable system, a cell whose fork-local retirement is pending
;; still holds the world it was made with: no item, wake, activation, merge or release reached it before
;; `[:retire-local]` (`sys-retire`), which runs at its first entry
(a/theorem sys-reach-rinv [cells :- (=> Nat Cell), pubs :- (=> Nat Pub)] (=> (SysReach cells pubs) (rinv cells))
  (intro hr)
  (induction hr)
  (case [init cells pubs h0 hc hj hp hr0] (exact (rinv-init cells hr0)))
  (case [step cells pubs k it r hr0 ih] (exact (rinv-step cells k it ih hr0)))
  (case [fork cells pubs k m owner r hl hf hr0 ih] (exact (rinv-fork cells k m owner ih)))
  (case [wake cells pubs k r hr0 ih] (exact (rinv-wake cells k ih hr0)))
  (case [accept cells pubs k m r ih] (exact (rinv-accept cells k m ih)))
  (case [complete cells pubs k r ih] (exact (rinv-complete cells k ih)))
  (case [drop cells pubs k r ih] (exact (rinv-drop cells k ih)))
  (case [fork-effect cells pubs k m owner st kont v r hl hf hr0 ih] (exact (rinv-fork-effect-g cells k m owner st kont v ih)))
  (case [publish cells pubs k p st kont fresh r hl hr0 ih] (simp only [sys-publish]) (exact (rinv-step cells k _ ih hr0)))
  (case [resume cells pubs p v r hr0 ih] (exact (rinv-resume cells pubs p v ih hr0)))
  (case [instantiate cells pubs p m owner r hlp hf ih] (exact (rinv-instantiate-g cells pubs p m owner ih)))
  (case [activate cells pubs m v r hr0 ih] (exact (rinv-activate cells m v ih hr0)))
  (case [abandon cells pubs p r hr0 ih] (simp only [sys-abandon]) (exact (rinv-step cells _ _ ih hr0)))
  (case [merge cells pubs k m b rv r hr0 hr1 ih] (exact (rinv-merge cells k m b rv ih hr0)))
  (case [merge-release cells pubs k m b rv r hr0 hr1 ih] (exact (rinv-merge-release cells k m b rv ih hr0 hr1)))
  (case [seal cells pubs k r hr0 ih] (exact (rinv-seal cells k ih)))
  (case [idle-release cells pubs m r ih] (exact (rinv-idle-release cells m ih)))
  (case [release-unborn cells pubs k r hr0 ih] (exact (rinv-release-unborn cells k ih hr0)))
  (case [join cells pubs k t r ih] (exact (rinv-join cells k t ih)))
  (case [deliver cells pubs k r ih] (exact (rinv-deliver cells k ih)))
  (case [withdraw cells pubs k x r ih] (exact (rinv-withdraw cells k x ih)))
  (case [reown cells pubs m k r ih] (exact (rinv-reown cells m k ih)))
  (case [xfer-reserve cells pubs m k2 n r ih] (exact (rinv-xfer-reserve cells m k2 n ih)))
  (case [unseal cells pubs k r hr0 ih] (exact (rinv-unseal cells k ih)))
  (case [own cells pubs k s m r hr0 ih] (exact (rinv-own cells k s m ih hr0)))
  (case [owned-done cells pubs k s c r hr0 ih] (exact (rinv-owned-done cells k s c ih hr0)))
  (case [drain cells pubs k r hr0 ih] (exact (rinv-drain cells k ih hr0)))
  (case [disown cells pubs k m r hk ih] (exact (rinv-disown cells k m ih)))
  (case [xfer-move cells pubs m k2 r ih] (exact (rinv-xfer-move cells m k2 ih)))
  (case [retire cells pubs k v r ih] (exact (rinv-retire cells k v ih))))
