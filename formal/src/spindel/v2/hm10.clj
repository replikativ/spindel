(ns spindel.v2.hm10
  "Bounded H3 restoration through member installation, fast fills and park.
   Stops before fin-if-final in await-post."
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
            [spindel.v2.l5 :refer :all]))

(a/defn h10-install [a :- Nat, ds :- (List Nat), acc :- AwAcc] World
  (act-upd (:world acc) a
    (act-set-members (mk-members (:pairs acc) 0 ds))))

(a/defn h10-fill-prefix [a :- Nat, ds :- (List Nat), acc :- AwAcc,
                       pre :- (List Nat)] World
  (nat-fold (fast-fill (:pairs acc)) (h10-install a ds acc) pre))

(a/defn h10-pending-exempt [ps :- (List DE), tail :- (List Nat),
                          xm :- (List Nat)] (List Nat)
  (match tail
    [nil xm]
    [(cons d t) (List.cons Nat (pair-edge d ps)
                         (h10-pending-exempt ps t xm))]))


;; Materialize actual support closures before any use, without placeholder overrides.
(doseq [root '[inv-react-edges inv-react-loop inv-demand-reactive nat-fold-inv inv-await-wire]]
  (lcopy! AWO root))
(lcopy! H3 'inv-fast-fill)
(lcopy! H3 'nat-fold-inv)
(doseq [B [GD GL AWO], root '[inv-fast-fill nat-fold-inv]] (lcopy! B root))

(a/theorem h10-fast-not-ready-waiting [w :- World, d :- Nat]
  (=> (= (gd w) true) (= (awake (:comps w) d) true) (= (fast-ready w d) false)
      (= (tbl-all (hk-wif d) (:comps w)) true))
  (intros hg ha hn)
  (cases hf (comp-find w d))
  (case [none] (exact (hk-wif-none w d hf)))
  (case [some c]
    (have nl (= (comp-live c) false))
    (simp only [fast-ready hf Bool.or_eq_false_iff] at hn)
    (exact (And.left hn))
    (have nr (= (ready-id w d) false))
    (simp only [ready-id hf opt-test settle-ready nl Bool.false_and])
    (exact (hk-wif-nready w d hg ha nr))))

(a/theorem h10-react-one-awake [w :- World, c :- CompRow]
  (=> (= (inv-sample w) true) (= (awake (:comps (react-one w c)) (:id c)) true))
  (intro hs)
  (have base := (inv-comp-upd w (:id c) comp-react-row comp-react-row-id comp-react-row-pending hs))
  (have awakened (= (awake (:comps (comp-upd w (:id c) comp-react-row)) (:id c)) true))
  (exact (awake-wake (:id c) comp-react-row comp-react-row-id (fn [q :- CompRow] (Eq.refl false)) (:comps w)))
  (have support := (awo-zero (:id c) _ base awakened))
  (exact (awo-awake (:id c) 0 _ (awo-react-edges (:id c) 0 (:validity c) _ (:id c) support))))

(a/theorem h10-demand-awake [w :- World, d :- Nat]
  (=> (= (inv-sample w) true) (= (awake (:comps (demand-reactive w d)) d) true))
  (intro hs)
  (cases hf (comp-find w d))
  (case [none]
    (simp only [demand-reactive hf])
    (exact (awake-absent (:comps w) d (tbl-find-none-has CompRow comp-id d (:comps w) hf))))
  (case [some c]
    (have id (= (:id c) d)) (exact (tbl-find-id CompRow comp-id d c (:comps w) hf))
    (cases hi (:idle c))
    (case [false] (simp only [demand-reactive hf hi]) (exact (find-awake w d c hs hf hi)))
    (case [true]
      (cases hv (valid-idle w c))
      (case [false]
        (simp only [demand-reactive hf hi hv comp-upd set-comps])
        (exact (awake-wake d comp-demand-row comp-demand-row-id (fn [q :- CompRow] (Eq.refl false)) (:comps w))))
      (case [true]
        (have aw := (h10-react-one-awake w c hs))
        (rw [id] at aw)
        (have support := (awo-zero d (react-one w c) (inv-react-one w c hs) aw))
        (simp only [demand-reactive hf hi hv react-fuel react-loop hf hi List.append])
        (exact (awo-awake d 0 _
                 (awo-react-loop d 0
                   (List.cons Nat 0 (tbl-gather (fn [q :- CompRow] true) (fn [q :- CompRow] (valid-debtors (:validity q))) (:comps w)))
                   (react-one w c) (valid-debtors (:validity c)) support)))))))

(a/theorem h10-demand-fold-awake [xs :- (List Nat)]
  (forall [w :- World, d :- Nat]
    (=> (= (inv-sample w) true) (= (nat-mem d xs) true)
        (= (awake (:comps (nat-fold demand-reactive w xs)) d) true)))
  (induction xs)
  (case [nil] (intros w d hs hm) (simp only [nat-mem] at hm) (cases hm))
  (case [cons x t ih]
    (intros w d hs hm)
    (have next := (inv-demand-reactive w x hs))
    (cases eq (Nat.beq x d))
    (case [true]
      (have dx := (Nat.eq_of_beq_eq_true eq))
      (have aw := (h10-demand-awake w x hs))
      (have awd (= (awake (:comps (demand-reactive w x)) d) true))
      (rw [← dx]) (exact aw)
      (have support := (awo-zero d (demand-reactive w x) next awd))
      (simp only [nat-fold])
      (exact (awo-awake d 0 _ (nat-fold-awo d 0 demand-reactive (awo-demand-reactive d 0) t _ support))))
    (case [false]
      (simp only [nat-mem eq Bool.false_or] at hm)
      (simp only [nat-fold])
      (exact (ih (demand-reactive w x) d next hm)))))

(a/theorem h10-await-debtor-awake [xm :- (List Nat), w :- World, r :- RunRow,
         ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat),
         st :- Nat, fresh :- Nat, d :- Nat]
  (=> (h9-entry xm w r ds mode st fresh) (= (nat-mem d ds) true)
      (= (awake (:comps (:world (await-acc w r ds mode k mine))) d) true))
  (intros ent md)
  (have hp := (And.left ent))
  (have hs := (g7-sample w (p3la-g7 w hp)))
  (have ticked := (inv-run-upd w (:id r) run-tick run-tick-run-id hs))
  (have allocated := (inv-act-ins-fresh (run-upd w (:id r) run-tick) (h9-act w r ds mode k mine) (rfl) ticked))
  (have distinct := (h9-distinct-complete ds d md))
  (have aw := (h10-demand-fold-awake (nat-distinct ds)
                (bump (act-ins (run-upd w (:id r) run-tick) (h9-act w r ds mode k mine))) d allocated distinct))
  (have support := (awo-zero d (await-pre w r ds mode k mine) (inv-await-pre w r ds mode k mine hs) aw))
  (exact (awo-awake d 0 _
           (awo-await-wire d 0 r (:next-id w) mode k (nat-distinct ds)
             (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) support))))

(a/theorem h10-pending-weakens [ps :- (List DE), tail :- (List Nat)]
  (forall [xm :- (List Nat), w :- World]
    (=> (= (h3 xm w) true) (= (h3 (h10-pending-exempt ps tail xm) w) true)))
  (induction tail)
  (case [nil] (intros xm w h) (simp only [h10-pending-exempt]) (exact h))
  (case [cons d t ih] (intros xm w h) (simp only [h10-pending-exempt])
    (exact (h3-xm-cons (h10-pending-exempt ps t xm) (pair-edge d ps) w (ih xm w h)))))

(a/theorem h10-pending-member [ps :- (List DE), tail :- (List Nat)]
  (forall [xm :- (List Nat), d :- Nat]
    (=> (= (nat-mem d tail) true) (= (reach-mem (pair-edge d ps) (h10-pending-exempt ps tail xm)) true)))
  (induction tail)
  (case [nil] (intros xm d h) (simp only [nat-mem] at h) (cases h))
  (case [cons x t ih]
    (intros xm d h) (cases eq (Nat.beq x d))
    (case [true] (have xd := (Nat.eq_of_beq_eq_true eq)) (rw [xd])
      (simp only [h10-pending-exempt reach-mem-cons Nat.beq_refl Bool.true_or]))
    (case [false] (simp only [nat-mem eq] at h)
      (simp only [h10-pending-exempt reach-mem-cons (ih xm d h) Bool.or_true]))))

(a/theorem h10-members-exempt [ps :- (List DE), ds :- (List Nat)]
  (forall [ex :- (List Nat), i :- Nat]
    (=> (forall [d :- Nat] (=> (= (nat-mem d ds) true) (= (reach-mem (pair-edge d ps) ex) true)))
        (forall [y :- Nat] (=> (= (mem-has y (mk-members ps i ds)) true) (= (reach-mem y ex) true)))))
  (induction ds)
  (case [nil] (intros ex i all y h) (simp only [mk-members mem-has] at h) (cases h))
  (case [cons d t ih]
    (intros ex i all y h)
    (have first-member (= (nat-mem d (List.cons Nat d t)) true))
    (simp only [nat-mem Nat.beq_refl])
    (have hd := (all d first-member))
    (have rest (forall [x :- Nat] (=> (= (nat-mem x t) true) (= (reach-mem (pair-edge x ps) ex) true))))
    (intros x hx) (exact (all x (nat-mem-cons-of x d t hx)))
    (cases first (Nat.beq (pair-edge d ps) y))
    (case [true] (have ey := (Nat.eq_of_beq_eq_true first)) (rw [← ey]) (exact hd))
    (case [false] (simp only [mk-members mem-has first] at h) (exact (ih ex (+ i 1) rest y h)))))

;; Replacing a row's member list by entirely exempt members retains its own
;; bounds, epoch and current-not-completed facts. No H3 installation hole is used.
(a/theorem h10-a-exempt [xm :- (List Nat), w :- World, b :- ActRow, b2 :- ActRow, as2 :- (List ActRow)]
  (=> (= (:run b2) (:run b))
      (forall [y :- Nat] (=> (= (mem-has y (:members b2)) true) (= (reach-mem y xm) true)))
      (= (h3-a xm w b) true) (= (h3-a xm (set-acts w as2) b2) true))
  (intros run members h)
  (simp only [h3-a Bool.and_eq_true] at h)
  (simp only [h3-a set-acts run Bool.and_eq_true])
  (apply And.intro) (exact (And.left h))
  (apply (tbl-all-mem-mono RunRow _ _ (:runs w) _ (And.right h)))
  (intros r mr hr)
  (simp only [h3-rr h3-r Bool.or_eq_true Bool.and_eq_true] at hr)
  (simp only [h3-rr h3-r set-acts run Bool.or_eq_true Bool.and_eq_true])
  (cases hr)
  (case [inl no] (exact (Or.inl no)))
  (case [inr yes]
    (apply Or.inr) (apply And.intro) (exact (And.left yes))
    (apply And.intro) (exact (And.left (And.right yes)))
    (have old := (And.right (And.right yes)))
    (simp only [h3-ob Bool.or_eq_true Bool.and_eq_true] at old)
    (simp only [h3-ob set-acts Bool.or_eq_true Bool.and_eq_true])
    (cases old)
    (case [inl owner] (exact (Or.inl owner)))
    (case [inr current]
      (apply Or.inr) (cases current)
      (case [inl stale] (exact (Or.inl stale)))
      (case [inr obliged]
        (apply Or.inr) (apply And.intro) (exact (And.left obliged))
        (apply all-of-mem) (intros y my)
        (have mh (= (mem-has y (:members b2)) true))
        (exact (Eq.trans (Eq.symm (h3-rm-members y (:members b2))) (Iff.mpr (reach-mem-iff y (act-contrib b2)) my)))
        (simp only [h3-x (members y mh) Bool.true_or])))))

(a/theorem h10-install-all-exempt [xm :- (List Nat), w :- World, b :- ActRow, tail :- (List ActRow), ms :- (List Member)]
  (=> (= (:acts w) (List.cons ActRow b tail))
      (forall [y :- Nat] (=> (= (mem-has y ms) true) (= (reach-mem y xm) true)))
      (= (h3 xm w) true)
      (= (h3 xm (act-upd w (:id b) (act-set-members ms))) true))
  (intros acts members h)
  (have hs := (h3-sample xm w h))
  (have nd := (h3-acts-nodup w hs)) (rw [acts] at nd)
  (have absent (= (tbl-has act-id (:id b) tail) false))
  (have parsed := nd)
  (simp only [tbl-ids nat-nodup Bool.and_eq_true] at parsed)
  (exact (Eq.trans (Eq.symm (nat-mem-ids ActRow act-id (:id b) tail)) (bnot-true _ (And.left parsed))))
  (have removed (= (:acts (act-del w (:id b))) tail))
  (simp only [act-del set-acts acts tbl-del act-id Nat.beq_refl (tbl-del-absent ActRow act-id (:id b) tail absent)])
  (have changed (= (act-upd w (:id b) (act-set-members ms))
                   (act-ins (act-del w (:id b)) (act-set-members ms b))))
  (simp only [act-upd act-ins act-del set-acts acts
               (h9-update-head b tail (act-set-members ms) nd) tbl-ins tbl-del act-id Nat.beq_refl
               (tbl-del-absent ActRow act-id (:id b) tail absent)])
  (have hb (= (h3-a xm w b) true))
  (have rest := (h3-rest-of xm w h)) (simp only [h3-rest acts tbl-all Bool.and_eq_true] at rest)
  (exact (And.left rest))
  (have own := (h10-a-exempt xm w b (act-set-members ms b)
                 (List.cons ActRow (act-set-members ms b) tail) (rfl) members hb))
  (have tail-rest := (h3r-act-del xm w (:id b) (h3-rest-of xm w h)))
  (have own2 (= (h3-a xm (act-ins (act-del w (:id b)) (act-set-members ms b)) (act-set-members ms b)) true))
  (simp only [act-ins set-acts tbl-ins removed]) (exact own)
  (have allowed
    (forall [y :- Nat]
      (=> (= (mem-has y (:members (act-set-members ms b))) true)
          (Or (= (reach-mem y xm) true) (= (tbl-has edge-id y (:edges (act-del w (:id b)))) false)))))
  (intros y hy) (apply Or.inl) (exact (members y hy))
  (have rest := (h3r-act-ins xm (act-del w (:id b)) (act-set-members ms b) allowed own2 tail-rest))
  (have installed-rest (= (h3-rest xm (act-upd w (:id b) (act-set-members ms))) true))
  (rw [changed]) (exact rest)
  (exact (h3-intro xm _ (inv-act-upd w (:id b) (act-set-members ms) (act-set-members-id ms) hs) installed-rest)))

(a/theorem h10-install-h3-exempt [xm :- (List Nat), w :- World, r :- RunRow,
         ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat]
  (=> (h9-entry xm w r ds mode st fresh)
      (let [C (await-acc w r ds mode k mine)]
        (= (h3 (h10-pending-exempt (:pairs C) (nat-distinct ds) xm)
               (h10-install (:next-id w) ds C)) true)))
  (intro ent)
  (have split := (h9-app-nil (nat-distinct ds)))
  (have support := (h9-prefix-support xm w r ds mode k mine st fresh (nat-distinct ds) (List.nil Nat) ent split))
  (have shape := (h9-prefix-shape xm w r ds mode k mine st fresh (nat-distinct ds) (List.nil Nat) ent split))
  (have weakened := (h10-pending-weakens (:pairs (await-acc w r ds mode k mine)) (nat-distinct ds)
                       xm (:world (await-acc w r ds mode k mine)) (And.left support)))
  (have members
    (forall [y :- Nat]
      (=> (= (mem-has y (mk-members (:pairs (await-acc w r ds mode k mine)) 0 ds)) true)
          (= (reach-mem y (h10-pending-exempt (:pairs (await-acc w r ds mode k mine)) (nat-distinct ds) xm)) true))))
  (apply (h10-members-exempt (:pairs (await-acc w r ds mode k mine)) ds
            (h10-pending-exempt (:pairs (await-acc w r ds mode k mine)) (nat-distinct ds) xm) 0))
  (intros d md)
  (exact (h10-pending-member (:pairs (await-acc w r ds mode k mine)) (nat-distinct ds) xm d (h9-distinct-complete ds d md)))
  (exact (h10-install-all-exempt
           (h10-pending-exempt (:pairs (await-acc w r ds mode k mine)) (nat-distinct ds) xm)
           (:world (await-acc w r ds mode k mine)) (h9-act w r ds mode k mine) (:acts w)
           (mk-members (:pairs (await-acc w r ds mode k mine)) 0 ds) (And.left shape) members weakened)))

(a/theorem h10-x-widen [xm :- (List Nat), ym :- (List Nat), w :- World, b :- ActRow, key :- RK3, x :- Nat]
  (=> (forall [y :- Nat] (=> (= (reach-mem y xm) true) (= (reach-mem y ym) true)))
      (= (h3-x xm w b key x) true) (= (h3-x ym w b key x) true))
  (intros wider h)
  (simp only [h3-x Bool.or_eq_true Bool.and_eq_true] at h)
  (simp only [h3-x Bool.or_eq_true Bool.and_eq_true])
  (cases h)
  (case [inl exempt] (exact (Or.inl (wider x exempt))))
  (case [inr obliged]
    (apply Or.inr) (apply And.intro) (exact (And.left obliged))
    (apply (tbl-all-mono EdgeRow _ _ _ (:edges w) (And.right obliged)))
    (intros e good)
    (simp only [h3-eok Bool.or_eq_true Bool.and_eq_true] at good)
    (simp only [h3-eok Bool.or_eq_true Bool.and_eq_true])
    (cases good)
    (case [inl different] (exact (Or.inl different)))
    (case [inr same]
      (apply Or.inr) (apply And.intro) (exact (And.left same))
      (have alternatives := (And.right same))
      (cases alternatives)
      (case [inl debtor-exempt] (exact (Or.inl (wider (:debtor e) debtor-exempt))))
      (case [inr waiting] (exact (Or.inr waiting))))))

(a/theorem h10-pending-includes [ps :- (List DE), tail :- (List Nat)]
  (forall [xm :- (List Nat), x :- Nat]
    (=> (= (reach-mem x xm) true) (= (reach-mem x (h10-pending-exempt ps tail xm)) true)))
  (induction tail)
  (case [nil] (intros xm x h) (simp only [h10-pending-exempt]) (exact h))
  (case [cons d t ih] (intros xm x h)
    (simp only [h10-pending-exempt reach-mem-cons (ih xm x h) Bool.or_true])))

(a/theorem h10-undo-pending-fixed [ps :- (List DE), tail :- (List Nat)]
  (forall [xm :- (List Nat), w :- World]
    (=> (forall [d :- Nat] (=> (= (nat-mem d tail) true) (= (tbl-has comp-id (pair-edge d ps) (:comps w)) false)))
        (forall [d :- Nat, e :- EdgeRow]
          (=> (= (nat-mem d tail) true) (List.Mem e (:edges w)) (= (Nat.beq (:debtor e) (pair-edge d ps)) false)))
        (forall [d :- Nat, b :- ActRow, r :- RunRow]
          (=> (= (nat-mem d tail) true) (List.Mem b (:acts w)) (List.Mem r (:runs w)) (= (:id r) (:run b))
              (= (reach-mem (:of r) xm) false) (= (tbl-any (h3-cur (rk3 r)) (:comps w)) true)
              (= (reach-mem (pair-edge d ps) (act-contrib b)) true) (= (reach-mem (pair-edge d ps) xm) false)
              (= (h3-x xm w b (rk3 r) (pair-edge d ps)) true)))
        (= (h3 (h10-pending-exempt ps tail xm) w) true) (= (h3 xm w) true)))
  (induction tail)
  (case [nil] (intros xm w no-comp no-deb good h) (simp only [h10-pending-exempt] at h) (exact h))
  (case [cons d t ih]
    (intros xm w no-comp no-deb good h)
    (have md (= (nat-mem d (List.cons Nat d t)) true)) (simp only [nat-mem Nat.beq_refl])
    (have target-good
      (forall [b :- ActRow, r :- RunRow]
        (=> (List.Mem b (:acts w)) (List.Mem r (:runs w)) (= (:id r) (:run b))
            (= (reach-mem (:of r) (h10-pending-exempt ps t xm)) false)
            (= (tbl-any (h3-cur (rk3 r)) (:comps w)) true)
            (= (reach-mem (pair-edge d ps) (act-contrib b)) true)
            (= (reach-mem (pair-edge d ps) (h10-pending-exempt ps t xm)) false)
            (= (h3-x (h10-pending-exempt ps t xm) w b (rk3 r) (pair-edge d ps)) true))))
    (intros b r mb mr id owner current member nonexempt)
    (have old-owner (= (reach-mem (:of r) xm) false))
    (cases ho (reach-mem (:of r) xm))
    (case [false] (rfl))
    (case [true] (have contra := (h10-pending-includes ps t xm (:of r) ho)) (rw [owner] at contra) (cases contra))
    (have old-exempt (= (reach-mem (pair-edge d ps) xm) false))
    (cases hx (reach-mem (pair-edge d ps) xm))
    (case [false] (rfl))
    (case [true] (have contra := (h10-pending-includes ps t xm (pair-edge d ps) hx)) (rw [nonexempt] at contra) (cases contra))
    (exact (h10-x-widen xm (h10-pending-exempt ps t xm) w b (rk3 r) (pair-edge d ps)
             (h10-pending-includes ps t xm) (good d b r md mb mr id old-owner current member old-exempt)))
    (have no-edge-debtor
      (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (= (Nat.beq (:debtor e) (pair-edge d ps)) false))))
    (intros e me) (exact (no-deb d e md me))
    (have dropped := (h3-undo-g (h10-pending-exempt ps t xm) w (pair-edge d ps)
                       (no-comp d md) no-edge-debtor target-good (h3-rest-of _ w h)))
    (have after (= (h3 (h10-pending-exempt ps t xm) w) true))
    (exact (h3-intro _ w (h3-sample _ w h) dropped))
    (apply (ih xm w _ _ _ after))
    (intros x mx) (exact (no-comp x (nat-mem-cons-of x d t mx)))
    (intros x e mx me) (exact (no-deb x e (nat-mem-cons-of x d t mx) me))
    (intros x b r mx mb mr id owner current member nonexempt)
    (exact (good x b r (nat-mem-cons-of x d t mx) mb mr id owner current member nonexempt))))

(a/theorem h10-not-in-smaller [xs :- (List Nat), ys :- (List Nat), x :- Nat]
  (=> (forall [y :- Nat] (=> (= (reach-mem y xs) true) (= (reach-mem y ys) true)))
      (= (reach-mem x ys) false) (= (reach-mem x xs) false))
  (intros include no)
  (cases yes (reach-mem x xs))
  (case [false] (rfl))
  (case [true] (have contra := (include x yes)) (rw [no] at contra) (cases contra)))

(a/theorem h10-head-holder-good [xm :- (List Nat), ex :- (List Nat), acc :- AwAcc,
                                b :- ActRow, tail :- (List ActRow), stored :- RunRow, ds :- (List Nat)]
  (=> (= (h3 xm (:world acc)) true)
      (= (:acts (:world acc)) (List.cons ActRow b tail))
      (List.Mem stored (:runs (:world acc))) (= (:run b) (:id stored))
      (forall [d :- Nat] (=> (= (nat-mem d ds) true) (= (h3-free xm (:world acc) (pair-edge d (:pairs acc))) true)))
      (forall [d :- Nat] (=> (= (nat-mem d ds) true)
        (Exists (fn [e :- EdgeRow]
          (And (= (edge-find (:world acc) (pair-edge d (:pairs acc))) (Option.some EdgeRow e))
           (And (= (:debtor e) d)
                (= (h3-s (:acts (h10-install (:id b) ds acc))
                         (act-set-members (mk-members (:pairs acc) 0 ds) b) (rk3 stored) e) true)))))))
      (forall [y :- Nat] (=> (= (reach-mem y xm) true) (= (reach-mem y ex) true)))
      (forall [d :- Nat] (=> (= (nat-mem d ds) true) (= (reach-mem d ex) true)))
      (forall [d :- Nat, a :- ActRow, q :- RunRow]
        (=> (= (nat-mem d ds) true)
            (List.Mem a (:acts (h10-install (:id b) ds acc)))
            (List.Mem q (:runs (h10-install (:id b) ds acc))) (= (:id q) (:run a))
            (= (reach-mem (:of q) ex) false)
            (= (tbl-any (h3-cur (rk3 q)) (:comps (h10-install (:id b) ds acc))) true)
            (= (reach-mem (pair-edge d (:pairs acc)) (act-contrib a)) true)
            (= (reach-mem (pair-edge d (:pairs acc)) ex) false)
            (= (h3-x ex (h10-install (:id b) ds acc) a (rk3 q) (pair-edge d (:pairs acc))) true))))
  (intros h acts member run free fields include debtors d a q md ma mq iq owner current contributes nonexempt)
  (have hs := (h3-sample xm _ h))
  (have nd := (h3-acts-nodup (:world acc) hs)) (rw [acts] at nd)
  (have changed (= (:acts (h10-install (:id b) ds acc))
                   (List.cons ActRow (act-set-members (mk-members (:pairs acc) 0 ds) b) tail)))
  (simp only [h10-install act-upd set-acts acts])
  (exact (h9-update-head b tail (act-set-members (mk-members (:pairs acc) 0 ds)) nd))
  (rw [changed] at ma)
  (cases ma)
  (case [head]
    (have same (= q stored))
    (apply (h3-run-uniq (:world acc) stored q hs member mq))
    (have keys (= (:id q) (:id stored))) (simp only [act-set-members] at iq) (exact (Eq.trans iq run))
    (rw [keys]) (exact (Nat.beq_refl _))
    (rw [same])
    (have picked := (fields d md))
    (cases picked)
    (case [intro e picked]
      (have found := (And.left picked))
      (have debtor := (And.left (And.right picked)))
      (have structure := (And.right (And.right picked)))
      (have me := (tbl-find-mem EdgeRow edge-id _ e (:edges (:world acc)) found))
      (have id (= (:id e) (pair-edge d (:pairs acc))))
      (exact (tbl-find-id EdgeRow edge-id _ e (:edges (:world acc)) found))
      (simp only [h3-x Bool.or_eq_true Bool.and_eq_true])
      (apply Or.inr) (apply And.intro)
      (exact (tbl-find-has EdgeRow edge-id _ e (:edges (:world acc)) found))
      (apply all-of-mem) (intros e2 me2)
      (cases equal (Nat.beq (:id e2) (pair-edge d (:pairs acc))))
      (case [false] (simp only [h3-eok equal Bool.not_false Bool.true_or]))
      (case [true]
        (have same-edge (= e2 e))
        (exact (h9-row-uniq EdgeRow edge-id e2 e (:edges (:world acc)) (edges-nodup _ hs)
                 me2 me (Eq.trans (Nat.eq_of_beq_eq_true equal) (Eq.symm id))))
        (rw [same-edge])
        (simp only [h3-eok id Nat.beq_refl Bool.not_true Bool.false_or structure debtor (debtors d md) Bool.true_or Bool.and_self]))))
  (case [tail old]
    (have before (List.Mem a (:acts (:world acc)))) (rw [acts]) (exact (List.Mem.tail b old))
    (have original-owner := (h10-not-in-smaller xm ex (:of q) include owner))
    (have original-exempt := (h10-not-in-smaller xm ex (pair-edge d (:pairs acc)) include nonexempt))
    (exact (False.elim (h3-free-use xm (:world acc) (pair-edge d (:pairs acc)) a q
                         (free d md) before mq iq original-owner current contributes original-exempt)))))

(a/theorem h10-wired-stored [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat,
                            k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat]
  (=> (h9-entry xm w r ds mode st fresh)
      (List.Mem (run-tick r) (:runs (:world (await-acc w r ds mode k mine)))))
  (intro ent)
  (have ht := (And.left (And.right (And.right ent))))
  (have mr := (And.left (tok-facts w st r ht)))
  (have hs := (h3-sample xm w (And.left (And.right ent))))
  (have before := (find-self RunRow run-id r (:runs w) (lit-runs-nodup w hs) mr))
  (have after := (hk-find-upd RunRow run-id (:id r) run-tick run-tick-run-id (:runs w) r before))
  (have shape := (h9-prefix-shape xm w r ds mode k mine st fresh (nat-distinct ds) (List.nil Nat) ent (h9-app-nil _)))
  (rw [(And.left (And.right shape))])
  (exact (tbl-find-mem RunRow run-id (:id r) (run-tick r) (:runs (run-upd w (:id r) run-tick)) after)))

(a/theorem h10-wired-pair-free [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat,
                               k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, d :- Nat]
  (=> (h9-entry xm w r ds mode st fresh) (= (nat-mem d ds) true)
      (= (h3-free xm (:world (await-acc w r ds mode k mine)) (pair-edge d (:pairs (await-acc w r ds mode k mine)))) true))
  (intros ent md)
  (have distinct := (h9-distinct-complete ds d md))
  (have has (= (de-has d (:pairs (await-acc w r ds mode k mine))) true))
  (exact (Eq.trans (h9-prefix-has w r ds mode k mine (nat-distinct ds) d) distinct))
  (have chosen := (h9-pair-picked (:pairs (await-acc w r ds mode k mine)) d has))
  (cases chosen)
  (case [intro p chosen]
    (have fr := (h9-prefix-pair-free xm w r ds mode k mine st fresh (nat-distinct ds) (List.nil Nat) p ent (h9-app-nil _) (And.left chosen)))
    (rw [(And.right (And.right chosen))] at fr) (exact fr)))

(a/theorem h10-installed-pair-fields [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat,
                                     k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, d :- Nat]
  (=> (h9-entry xm w r ds mode st fresh) (= (nat-mem d ds) true)
      (Exists (fn [e :- EdgeRow]
        (And (= (edge-find (:world (await-acc w r ds mode k mine)) (pair-edge d (:pairs (await-acc w r ds mode k mine)))) (Option.some EdgeRow e))
         (And (= (:debtor e) d)
              (= (h3-s (:acts (h10-install (:next-id w) ds (await-acc w r ds mode k mine)))
                       (act-set-members (mk-members (:pairs (await-acc w r ds mode k mine)) 0 ds) (h9-act w r ds mode k mine)) (rk3 (run-tick r)) e) true))))))
  (intros ent md)
  (have installed := (h9-installed-first-holder xm w r ds mode k mine st fresh d ent md))
  (have fields := (h9-prefix-pair-edge xm w r ds mode k mine st fresh (nat-distinct ds) (List.nil Nat) d ent (h9-app-nil _) (h9-distinct-complete ds d md)))
  (cases installed)
  (case [intro e installed]
    (cases fields)
    (case [intro e2 fields]
      (have same (= e2 e)) (exact (Option.some.inj (Eq.trans (Eq.symm (And.left fields)) (And.left installed))))
      (have actual := (And.left (And.right (And.right fields)))) (rw [same] at actual)
      (apply (Exists.intro e)) (apply And.intro) (exact (And.left installed))
      (apply And.intro) (exact (And.left actual))
      (exact (And.right (And.right (And.right installed)))))))

(a/theorem h10-installed-shadow [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat,
                               k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat]
  (=> (h9-entry xm w r ds mode st fresh)
      (= (h3 (List.append Nat ds xm) (h10-install (:next-id w) ds (await-acc w r ds mode k mine))) true))
  (intro ent)
  (have include (forall [y :- Nat] (=> (= (reach-mem y xm) true) (= (reach-mem y (List.append Nat ds xm)) true))))
  (intros y hy) (simp only [reach-mem-append hy Bool.or_true])
  (have debtors (forall [d :- Nat] (=> (= (nat-mem d ds) true) (= (reach-mem d (List.append Nat ds xm)) true))))
  (intros d md) (simp only [reach-mem-append (reach-mem-nat-mem d ds) md Bool.true_or])
  (have hs := (h3-sample xm w (And.left (And.right ent))))
  (have hshadow := (h3-intro (List.append Nat ds xm) w hs
                     (h3-rest-xm xm (List.append Nat ds xm) w include (h3-rest-of xm w (And.left (And.right ent))))))
  (have shadow-ent (h9-entry (List.append Nat ds xm) w r ds mode st fresh))
  (exact (And.intro (And.left ent) (And.intro hshadow (And.right (And.right ent)))))
  (have initial := (h10-install-h3-exempt (List.append Nat ds xm) w r ds mode k mine st fresh shadow-ent))
  (have support := (h9-prefix-support xm w r ds mode k mine st fresh (nat-distinct ds) (List.nil Nat) ent (h9-app-nil _)))
  (have shape := (h9-prefix-shape xm w r ds mode k mine st fresh (nat-distinct ds) (List.nil Nat) ent (h9-app-nil _)))
  (have input := (And.left support))
  (have allocated := (inv-act-upd (:world (await-acc w r ds mode k mine)) (:next-id w)
                      (act-set-members (mk-members (:pairs (await-acc w r ds mode k mine)) 0 ds))
                      (act-set-members-id _) (h3-sample xm _ input)))
  (have good := (h10-head-holder-good xm (List.append Nat ds xm) (await-acc w r ds mode k mine)
                  (h9-act w r ds mode k mine) (:acts w) (run-tick r) ds input (And.left shape)
                  (h10-wired-stored xm w r ds mode k mine st fresh ent) (rfl)
                  (fn [d :- Nat, md :- (= (nat-mem d ds) true)] (h10-wired-pair-free xm w r ds mode k mine st fresh d ent md))
                  (fn [d :- Nat, md :- (= (nat-mem d ds) true)] (h10-installed-pair-fields xm w r ds mode k mine st fresh d ent md)) include debtors))
  (apply (h10-undo-pending-fixed (:pairs (await-acc w r ds mode k mine)) (nat-distinct ds)
            (List.append Nat ds xm) (h10-install (:next-id w) ds (await-acc w r ds mode k mine)) _ _ _ initial))
  (intros d md)
  (have found := (h9-installed-first-holder xm w r ds mode k mine st fresh d ent (h9-distinct-source ds d md)))
  (cases found)
  (case [intro e found]
    (exact (h3-edge-not-comp _ _ allocated (tbl-find-has EdgeRow edge-id _ e _ (And.left (And.right found))))))
  (intros d e md me)
  (have found := (h9-installed-first-holder xm w r ds mode k mine st fresh d ent (h9-distinct-source ds d md)))
  (cases found)
  (case [intro row found]
    (have not-debtor := (h3-edge-not-debtor _ _ allocated (tbl-find-has EdgeRow edge-id _ row _ (And.left (And.right found)))))
    (have fact := (tbl-all-mem EdgeRow _ e _ not-debtor me))
    (exact (bnot-true _ fact)))
  (intros d b q md mb mq id owner current contributes nonexempt)
  (exact (good d b q (h9-distinct-source ds d md) mb mq id owner current contributes nonexempt)))

(a/theorem h10-fm-fast-fill [ps :- (List DE), w :- World, d :- Nat]
  (h3-fm w (fast-fill ps w d))
  (cases ready (fast-ready w d))
  (case [false] (simp only [fast-fill ready]) (exact (fm-refl w)))
  (case [true] (simp only [fast-fill ready]) (exact (fm-fire-edge (deb-result w d) w (pair-edge d ps)))))

(a/theorem h10-fm-prefix [a :- Nat, ds :- (List Nat), acc :- AwAcc, pre :- (List Nat)]
  (h3-fm (h10-install a ds acc) (h10-fill-prefix a ds acc pre))
  (exact (fm-nat-fold (fast-fill (:pairs acc)) (h10-fm-fast-fill (:pairs acc)) pre (h10-install a ds acc))))

(a/theorem h10-prefix-shadow [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat,
                            k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, pre :- (List Nat)]
  (=> (h9-entry xm w r ds mode st fresh)
      (= (h3 (List.append Nat ds xm) (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre)) true))
  (intro ent)
  (exact (nat-fold-h3 (List.append Nat ds xm) (fast-fill (:pairs (await-acc w r ds mode k mine)))
           (hm3-fast-fill (List.append Nat ds xm) (:pairs (await-acc w r ds mode k mine))) pre
           (h10-install (:next-id w) ds (await-acc w r ds mode k mine))
           (h10-installed-shadow xm w r ds mode k mine st fresh ent))))

(a/theorem h10-prefix-gd [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat,
                        k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, pre :- (List Nat)]
  (=> (h9-entry xm w r ds mode st fresh)
      (= (gd (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre)) true))
  (intro ent)
  (have support := (h9-prefix-support xm w r ds mode k mine st fresh (nat-distinct ds) (List.nil Nat) ent (h9-app-nil _)))
  (have gd := (And.left (And.right (And.right (And.right support)))))
  (have installed := (gd-act-upd (:world (await-acc w r ds mode k mine)) (:next-id w)
                       (act-set-members (mk-members (:pairs (await-acc w r ds mode k mine)) 0 ds)) (act-set-members-id _) gd))
  (exact (nat-fold-gd (fast-fill (:pairs (await-acc w r ds mode k mine)))
           (gd-fast-fill (:pairs (await-acc w r ds mode k mine))) pre
           (h10-install (:next-id w) ds (await-acc w r ds mode k mine)) installed)))

(a/theorem h10-prefix-gl [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat,
                        k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, pre :- (List Nat)]
  (=> (h9-entry xm w r ds mode st fresh)
      (= (gl (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre)) true))
  (intro ent)
  (have support := (h9-prefix-support xm w r ds mode k mine st fresh (nat-distinct ds) (List.nil Nat) ent (h9-app-nil _)))
  (have gl := (And.left (And.right (And.right (And.right (And.right (And.right (And.right (And.right support)))))))))
  (have installed := (gl-act-upd (:world (await-acc w r ds mode k mine)) (:next-id w)
                       (act-set-members (mk-members (:pairs (await-acc w r ds mode k mine)) 0 ds)) (act-set-members-id _) gl))
  (exact (nat-fold-gl (fast-fill (:pairs (await-acc w r ds mode k mine)))
           (gl-fast-fill (:pairs (await-acc w r ds mode k mine))) pre
           (h10-install (:next-id w) ds (await-acc w r ds mode k mine)) installed)))

(a/theorem h10-prefix-awake [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat,
                           k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, pre :- (List Nat), d :- Nat]
  (=> (h9-entry xm w r ds mode st fresh) (= (nat-mem d ds) true)
      (= (awake (:comps (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre)) d) true))
  (intros ent md)
  (have support := (h9-prefix-support xm w r ds mode k mine st fresh (nat-distinct ds) (List.nil Nat) ent (h9-app-nil _)))
  (have awake := (h10-await-debtor-awake xm w r ds mode k mine st fresh d ent md))
  (have aw0 := (awo-zero d (:world (await-acc w r ds mode k mine)) (h3-sample xm _ (And.left support)) awake))
  (have installed := (awo-act-upd d 0 (:world (await-acc w r ds mode k mine)) (:next-id w)
                       (act-set-members (mk-members (:pairs (await-acc w r ds mode k mine)) 0 ds)) (act-set-members-id _) aw0))
  (exact (awo-awake d 0 _
           (nat-fold-awo d 0 (fast-fill (:pairs (await-acc w r ds mode k mine)))
             (awo-fast-fill d 0 (:pairs (await-acc w r ds mode k mine))) pre
             (h10-install (:next-id w) ds (await-acc w r ds mode k mine)) installed))))

;; The Entry guard excludes the selected computation from its original debtor
;; list. Use the actual bounded cycle worklist, rather than assume convergence.
(a/theorem h10-count-absent [xs :- (List Nat), x :- Nat]
  (=> (= (nat-mem x xs) false) (= (tbl-count (fn [y :- Nat] (Nat.beq y x)) xs) 0))
  (induction xs)
  (case [nil] (intro h) (simp only [tbl-count]))
  (case [cons y t ih]
    (intro h) (cases eq (Nat.beq y x))
    (case [true] (simp only [nat-mem eq] at h) (cases h))
    (case [false] (simp only [nat-mem eq] at h) (simp only [tbl-count eq]) (exact (ih h)))))

(a/theorem h10-count-unique [xs :- (List Nat)]
  (forall [x :- Nat] (=> (= (nat-nodup xs) true) (<= (tbl-count (fn [y :- Nat] (Nat.beq y x)) xs) 1)))
  (induction xs)
  (case [nil] (intros x h) (simp only [tbl-count]) (omega))
  (case [cons y t ih]
    (intros x h) (simp only [nat-nodup Bool.and_eq_true] at h)
    (cases eq (Nat.beq y x))
    (case [false] (simp only [tbl-count eq]) (exact (ih x (And.right h))))
    (case [true]
      (have yx := (Nat.eq_of_beq_eq_true eq))
      (have no := (bnot-true _ (And.left h))) (rw [yx] at no)
      (simp only [tbl-count eq (h10-count-absent t x no)]) (omega))))

(a/theorem h10-dep-cost-zero [us :- (List Nat)]
  (= (unseen-cost (dep-debtors (List.nil EdgeRow)) (List.nil Nat) us) 0)
  (induction us)
  (case [nil] (simp only [unseen-cost]))
  (case [cons x t ih] (simp only [unseen-cost dep-debtors List.length ih Nat.add_zero])))

(a/theorem h10-dep-cost-cons [us :- (List Nat), e :- EdgeRow, es :- (List EdgeRow)]
  (= (unseen-cost (dep-debtors (List.cons EdgeRow e es)) (List.nil Nat) us)
     (+ (if (Nat.beq (:kind e) ek-dep) (tbl-count (fn [x :- Nat] (Nat.beq x (:creditor e))) us) 0)
        (unseen-cost (dep-debtors es) (List.nil Nat) us)))
  (induction us)
  (case [nil] (simp only [unseen-cost tbl-count]))
  (case [cons x t ih]
    (cases kind (Nat.beq (:kind e) ek-dep))
    (case [false]
      (simp only [unseen-cost reach-mem dep-debtors dep-of kind Bool.and_false tbl-count List.length ih]) (all_goals (omega)))
    (case [true]
      (cases creditor (Nat.beq (:creditor e) x))
      (case [false]
        (have inverse (= (Nat.beq x (:creditor e)) false)) (rw [beq-comm]) (exact creditor)
        (simp only [unseen-cost reach-mem dep-debtors dep-of kind creditor inverse Bool.false_and Bool.true_and tbl-count List.length ih]) (all_goals (omega)))
      (case [true]
        (have inverse (= (Nat.beq x (:creditor e)) true)) (rw [beq-comm]) (exact creditor)
        (simp only [unseen-cost reach-mem dep-debtors dep-of kind creditor inverse Bool.false_and Bool.true_and tbl-count List.length ih]) (all_goals (omega))))))

(a/theorem h10-dep-cost-bound [es :- (List EdgeRow)]
  (forall [us :- (List Nat)]
    (=> (= (nat-nodup us) true)
        (<= (unseen-cost (dep-debtors es) (List.nil Nat) us) (List.length es))))
  (induction es)
  (case [nil] (intros us nd) (rw [h10-dep-cost-zero]) (simp only [List.length]) (omega))
  (case [cons e t ih]
    (intros us nd) (have bound := (ih us nd)) (have count := (h10-count-unique us (:creditor e) nd))
    (rw [h10-dep-cost-cons])
    (cases kind (Nat.beq (:kind e) ek-dep))
    (all_goals (simp only [kind List.length]))
    (all_goals (omega))))

(a/theorem h10-dep-absent [es :- (List EdgeRow), cs :- (List CompRow), x :- Nat]
  (=> (forall [e :- EdgeRow]
        (=> (List.Mem e es) (= (Nat.beq (:kind e) ek-dep) true) (= (tbl-has comp-id (:creditor e) cs) true)))
      (= (tbl-has comp-id x cs) false) (= (dep-debtors es x) (List.nil Nat)))
  (induction es)
  (case [nil] (intros valid no) (simp only [dep-debtors]))
  (case [cons e t ih]
    (intros valid no)
    (have rest (forall [q :- EdgeRow] (=> (List.Mem q t) (= (Nat.beq (:kind q) ek-dep) true) (= (tbl-has comp-id (:creditor q) cs) true))))
    (intros q mq kind) (exact (valid q (List.Mem.tail e mq) kind))
    (cases dep (Bool.and (Nat.beq (:creditor e) x) (Nat.beq (:kind e) ek-dep)))
    (case [false] (simp only [dep-debtors dep]) (exact (ih rest no)))
    (case [true]
      (simp only [Bool.and_eq_true] at dep)
      (have exists := (valid e (List.Mem.head t) (And.right dep)))
      (rw [(Nat.eq_of_beq_eq_true (And.left dep)) no] at exists) (cases exists))))

(a/theorem h10-cycle-converged [w :- World, ds :- (List Nat)]
  (=> (= (inv-sample w) true)
      (= (:converged (reach-run-l (cycle-fuel w ds) (dep-debtors (:edges w)) ds)) true))
  (intro hs)
  (have valid
    (forall [e :- EdgeRow]
      (=> (List.Mem e (:edges w)) (= (Nat.beq (:kind e) ek-dep) true)
          (= (tbl-has comp-id (:creditor e) (:comps w)) true))))
  (intros e me kind)
  (have integrity := (tbl-all-mem EdgeRow _ e (:edges w) (And.left (And.right (inv-parts w hs))) me))
  (simp only [edges-ref-ok-in edge-ok Bool.and_eq_true] at integrity)
  (have creditor := (And.left integrity)) (simp only [cred-ok kind] at creditor) (exact creditor)
  (apply (reach-run-l-conv (cycle-fuel w ds) (dep-debtors (:edges w)) ds (tbl-ids comp-id (:comps w))))
  (intros x no)
  (have absent (= (tbl-has comp-id x (:comps w)) false))
  (rw [← nat-mem-ids ← reach-mem-nat-mem]) (exact no)
  (exact (h10-dep-absent (:edges w) (:comps w) x valid absent))
  (have bound := (h10-dep-cost-bound (:edges w) (tbl-ids comp-id (:comps w)) (comps-nodup w hs)))
  (simp only [cycle-fuel List.length list-length-append ids-len]) (omega))

(a/theorem h10-entry-not-self [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, st :- Nat, fresh :- Nat]
  (=> (h9-entry xm w r ds mode st fresh) (= (comp-has w (:of r)) true)
      (= (reach-mem (:of r) ds) false))
  (intros ent comp)
  (have hs := (h3-sample xm w (And.left (And.right ent))))
  (have ok := (And.right (And.right (And.right ent))))
  (simp only [await-ok Bool.and_eq_true] at ok)
  (have no := (bnot-true _ (And.right (And.right (And.right (And.right ok))))))
  (cases member (reach-mem (:of r) ds))
  (case [false] (rfl))
  (case [true]
    (have conv := (h10-cycle-converged w ds hs))
    (rw [reach-run-l-eq] at conv)
    (have visited := (reach-run-roots (List.length (cycle-fuel w ds)) (dep-debtors (:edges w)) ds (:of r) conv member))
    (have cyclic (= (await-cycle w r ds) true))
    (simp only [await-cycle in-comp comp Bool.true_and reach-run-l-eq]) (exact visited)
    (rw [cyclic] at no) (cases no)))

(a/theorem h10-holder-key [xm :- (List Nat), acc :- AwAcc, b :- ActRow, tail :- (List ActRow),
                         stored :- RunRow, ds :- (List Nat), V :- World, d :- Nat, a :- ActRow, q :- RunRow]
  (=> (= (h3 xm (:world acc)) true) (= (:acts (:world acc)) (List.cons ActRow b tail))
      (List.Mem stored (:runs (:world acc))) (= (:run b) (:id stored))
      (= (h3-free xm (:world acc) (pair-edge d (:pairs acc))) true)
      (h3-fm (h10-install (:id b) ds acc) V)
      (List.Mem a (:acts V)) (List.Mem q (:runs V)) (= (:id q) (:run a))
      (= (reach-mem (:of q) xm) false) (= (tbl-any (h3-cur (rk3 q)) (:comps V)) true)
      (= (reach-mem (pair-edge d (:pairs acc)) (act-contrib a)) true)
      (= (reach-mem (pair-edge d (:pairs acc)) xm) false)
      (= (rk3 q) (rk3 stored)))
  (intros h acts stored-member run free relation ma mq id owner current contributes nonexempt)
  (have hs := (h3-sample xm _ h))
  (have nd := (h3-acts-nodup (:world acc) hs)) (rw [acts] at nd)
  (have changed (= (:acts (h10-install (:id b) ds acc))
                   (List.cons ActRow (act-set-members (mk-members (:pairs acc) 0 ds) b) tail)))
  (simp only [h10-install act-upd set-acts acts])
  (exact (h9-update-head b tail (act-set-members (mk-members (:pairs acc) 0 ds)) nd))
  (have old-act := (tbl-all-mem ActRow _ a _ (fm-acts-of _ V relation) ma))
  (simp only [fm-aa] at old-act)
  (apply (any-elim ActRow (fm-ab a) _ (:acts (h10-install (:id b) ds acc)) old-act))
  (intros a0 ma0 act-key)
  (have old-run := (tbl-all-mem RunRow _ q _ (fm-runs-of _ V relation) mq))
  (simp only [fm-rr] at old-run)
  (apply (any-elim RunRow (h3-rkq q) _ (:runs (h10-install (:id b) ds acc)) old-run))
  (intros q0 mq0 run-key)
  (have key := (h3-rk3-eq q0 q run-key))
  (have qid (= (:id q0) (:id q))) (exact (congrArg (fn [k :- RK3] (:id k)) key))
  (have qof (= (:of q0) (:of q))) (exact (congrArg (fn [k :- RK3] (:of k)) key))
  (simp only [fm-ab Bool.and_eq_true] at act-key)
  (have arun := (Nat.eq_of_beq_eq_true (And.left act-key)))
  (have old-id (= (:id q0) (:run a0))) (rw [qid id ← arun])
  (have old-contributes := (tbl-all-mem Nat _ (pair-edge d (:pairs acc)) _ (And.right act-key)
                             (Iff.mp (reach-mem-iff _ (act-contrib a)) contributes)))
  (simp only [fm-in] at old-contributes)
  (have old-current (= (tbl-any (h3-cur (rk3 q0)) (:comps (:world acc))) true))
  (rw [key]) (exact (fm-cur-of _ V (rk3 q) relation current))
  (rw [changed] at ma0)
  (cases ma0)
  (case [head]
    (have equal (= q0 stored))
    (apply (h3-run-uniq (:world acc) stored q0 hs stored-member mq0))
    (have ids (= (:id q0) (:id stored))) (simp only [act-set-members] at old-id) (exact (Eq.trans old-id run))
    (rw [ids]) (exact (Nat.beq_refl _))
    (rw [← key equal]))
  (case [tail before]
    (have original-member (List.Mem a0 (:acts (:world acc)))) (rw [acts]) (exact (List.Mem.tail b before))
    (have original-owner (= (reach-mem (:of q0) xm) false)) (rw [qof]) (exact owner)
    (exact (False.elim (h3-free-use xm (:world acc) (pair-edge d (:pairs acc)) a0 q0 free
                         original-member mq0 old-id original-owner old-current old-contributes nonexempt)))))

(a/theorem h10-prefix-holder-key [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat,
                                k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, pre :- (List Nat),
                                d :- Nat, b :- ActRow, q :- RunRow]
  (=> (h9-entry xm w r ds mode st fresh) (= (nat-mem d ds) true)
      (List.Mem b (:acts (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre)))
      (List.Mem q (:runs (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre))) (= (:id q) (:run b))
      (= (reach-mem (:of q) xm) false)
      (= (tbl-any (h3-cur (rk3 q)) (:comps (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre))) true)
      (= (reach-mem (pair-edge d (:pairs (await-acc w r ds mode k mine))) (act-contrib b)) true)
      (= (reach-mem (pair-edge d (:pairs (await-acc w r ds mode k mine))) xm) false)
      (= (rk3 q) (rk3 r)))
  (intros ent md mb mq id owner current contributes nonexempt)
  (have support := (h9-prefix-support xm w r ds mode k mine st fresh (nat-distinct ds) (List.nil Nat) ent (h9-app-nil _)))
  (have shape := (h9-prefix-shape xm w r ds mode k mine st fresh (nat-distinct ds) (List.nil Nat) ent (h9-app-nil _)))
  (exact (h10-holder-key xm (await-acc w r ds mode k mine) (h9-act w r ds mode k mine) (:acts w) (run-tick r) ds
           (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre) d b q
           (And.left support) (And.left shape) (h10-wired-stored xm w r ds mode k mine st fresh ent) (rfl)
           (h10-wired-pair-free xm w r ds mode k mine st fresh d ent md)
           (h10-fm-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre)
           mb mq id owner current contributes nonexempt)))

(a/theorem h10-cur-has [w :- World, key :- RK3]
  (=> (= (tbl-any (h3-cur key) (:comps w)) true) (= (comp-has w (:of key)) true))
  (intro current)
  (apply (any-elim CompRow (h3-cur key) _ (:comps w) current))
  (intros c mc hc)
  (simp only [h3-cur Bool.and_eq_true] at hc)
  (have exists := (has-of-mem CompRow comp-id c (:comps w) mc))
  (have id (= (comp-id c) (:of key))) (exact (Nat.eq_of_beq_eq_true (And.left hc)))
  (rw [id] at exists) (exact exists))

(a/theorem h10-fm-not-comp [w :- World, V :- World, x :- Nat]
  (=> (h3-fm w V) (= (comp-has w x) false) (= (comp-has V x) false))
  (intros relation absent)
  (cases found (comp-find V x))
  (case [none] (exact (tbl-find-none-has CompRow comp-id x (:comps V) found)))
  (case [some c]
    (have mc := (tbl-find-mem CompRow comp-id x c (:comps V) found))
    (have id (= (:id c) x)) (exact (tbl-find-id CompRow comp-id x c (:comps V) found))
    (have current (= (tbl-any (h3-cur (RK3.mk 0 x (:epoch c))) (:comps V)) true))
    (apply (any-elim-of CompRow (h3-cur (RK3.mk 0 x (:epoch c))) c (:comps V) mc))
    (simp only [h3-cur id Nat.beq_refl gd-ble-refl Bool.and_self])
    (have old := (h10-cur-has w (RK3.mk 0 x (:epoch c)) (fm-cur-of w V _ relation current)))
    (rw [absent] at old) (cases old)))

(a/theorem h10-prefix-owner-not-shadow [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat,
                                      k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, pre :- (List Nat),
                                      d :- Nat, b :- ActRow, q :- RunRow]
  (=> (h9-entry xm w r ds mode st fresh) (= (nat-mem d ds) true)
      (List.Mem b (:acts (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre)))
      (List.Mem q (:runs (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre))) (= (:id q) (:run b))
      (= (reach-mem (:of q) xm) false)
      (= (tbl-any (h3-cur (rk3 q)) (:comps (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre))) true)
      (= (reach-mem (pair-edge d (:pairs (await-acc w r ds mode k mine))) (act-contrib b)) true)
      (= (reach-mem (pair-edge d (:pairs (await-acc w r ds mode k mine))) xm) false)
      (= (reach-mem (:of q) (List.append Nat ds xm)) false))
  (intros ent md mb mq id owner current contributes nonexempt)
  (have key := (h10-prefix-holder-key xm w r ds mode k mine st fresh pre d b q ent md mb mq id owner current contributes nonexempt))
  (have qof (= (:of q) (:of r))) (exact (congrArg (fn [k :- RK3] (:of k)) key))
  (have shape := (h9-prefix-shape xm w r ds mode k mine st fresh (nat-distinct ds) (List.nil Nat) ent (h9-app-nil _)))
  (have relation := (h10-fm-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre))
  (have old-current := (fm-cur-of (h10-install (:next-id w) ds (await-acc w r ds mode k mine))
                         (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre) (rk3 q) relation current))
  (have wired-has := (h10-cur-has (:world (await-acc w r ds mode k mine)) (rk3 q) old-current))
  (have original-has (= (comp-has w (:of r)) true))
  (have frame := ((And.right (And.right (And.right (And.right (And.right shape))))) (:of r)))
  (have wh (= (comp-has (:world (await-acc w r ds mode k mine)) (:of r)) true)) (rw [← qof]) (exact wired-has)
  (exact (Eq.trans (Eq.symm frame) wh))
  (have not-self := (h10-entry-not-self xm w r ds mode st fresh ent original-has))
  (have no-debtor (= (reach-mem (:of q) ds) false)) (rw [qof]) (exact not-self)
  (simp only [reach-mem-append no-debtor owner Bool.false_or]))

(a/theorem h10-edge-not-entity [w :- World, x :- Nat]
  (=> (= (inv-sample w) true) (= (tbl-has edge-id x (:edges w)) true) (= (deb-exists w x) false))
  (intros hs edge)
  (simp only [deb-exists comp-has task-has source-has resource-has
               (h3-edge-not-comp w x hs edge) (h3-edge-not-task w x hs edge)
               (h3-edge-not-source w x hs edge) (h3-edge-not-res w x hs edge) Bool.false_or]))

(a/theorem h10-pair-not-ds [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat,
                         k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, d :- Nat]
  (=> (h9-entry xm w r ds mode st fresh) (= (nat-mem d ds) true)
      (= (reach-mem (pair-edge d (:pairs (await-acc w r ds mode k mine))) ds) false))
  (intros ent md)
  (have support := (h9-prefix-support xm w r ds mode k mine st fresh (nat-distinct ds) (List.nil Nat) ent (h9-app-nil _)))
  (have shape := (h9-prefix-shape xm w r ds mode k mine st fresh (nat-distinct ds) (List.nil Nat) ent (h9-app-nil _)))
  (have found := (h9-prefix-pair-edge xm w r ds mode k mine st fresh (nat-distinct ds) (List.nil Nat) d ent (h9-app-nil _) (h9-distinct-complete ds d md)))
  (cases found)
  (case [intro e found]
    (have absent := (h10-edge-not-entity (:world (await-acc w r ds mode k mine)) (pair-edge d (:pairs (await-acc w r ds mode k mine)))
                      (h3-sample xm _ (And.left support)) (tbl-find-has EdgeRow edge-id _ e _ (And.left found))))
    (have ok := (And.right (And.right (And.right ent))))
    (simp only [await-ok Bool.and_eq_true] at ok)
    (have debtors := (And.left (And.right (And.right (And.right ok)))))
    (cases member (reach-mem (pair-edge d (:pairs (await-acc w r ds mode k mine))) ds))
    (case [false] (rfl))
    (case [true]
      (have exists := (tbl-all-mem Nat (deb-exists w) (pair-edge d (:pairs (await-acc w r ds mode k mine))) ds debtors (Iff.mp (reach-mem-iff _ ds) member)))
      (have still := (h9-deb-shape w r ds mode k mine (:world (await-acc w r ds mode k mine)) _ shape exists))
      (rw [absent] at still) (cases still))))

;; Any edge-row property preserved by the actual phase/rearm/seen edits is
;; preserved for surviving rows. Filters and consumption only remove rows.
(a/theorem h10-es-upd [P :- (=> EdgeRow Bool), f :- (=> EdgeRow EdgeRow),
                     keep :- (forall [e :- EdgeRow] (=> (= (P e) true) (= (P (f e)) true))),
                     x :- Nat, es :- (List EdgeRow)]
  (=> (= (tbl-all P es) true) (= (tbl-all P (tbl-upd edge-id x f es)) true))
  (intro h)
  (exact (tbl-all-upd EdgeRow edge-id x f P P
           (fn [e :- EdgeRow, he :- (= (P e) true), hx :- (= (Nat.beq (edge-id e) x) true)] (keep e he))
           (fn [e :- EdgeRow, he :- (= (P e) true), hx :- (= (Nat.beq (edge-id e) x) false)] he) es h)))

(a/theorem h10-es-remove [P :- (=> EdgeRow Bool), w :- World, x :- Nat]
  (=> (= (tbl-all P (:edges w)) true) (= (tbl-all P (:edges (remove-edge w x))) true))
  (intro h)
  (cases found (edge-find w x))
  (case [none] (simp only [remove-edge found]) (exact h))
  (case [some e]
    (have removed := (tbl-all-del EdgeRow edge-id x P P
                       (fn [q :- EdgeRow, hq :- (= (P q) true), hx :- (= (Nat.beq (edge-id q) x) false)] hq) (:edges w) h))
    (cases marked (:marked e))
    (all_goals (simp only [remove-edge found marked comp-upd edge-del set-comps set-edges]))
    (all_goals (exact removed))))

(a/theorem h10-es-dep-consumed [P :- (=> EdgeRow Bool),
                              rearm :- (forall [v :- Nat, ver :- Nat, e :- EdgeRow]
                                (=> (= (P e) true) (= (P (edge-rearm v ver e)) true))), w :- World, e :- EdgeRow]
  (=> (= (tbl-all P (:edges w)) true) (= (tbl-all P (:edges (dep-consumed w e))) true))
  (intro h)
  (cases final (deb-final w (:debtor e)))
  (case [true] (simp only [dep-consumed final]) (exact (h10-es-remove P w (:id e) h)))
  (case [false]
    (simp only [dep-consumed final edge-upd set-edges])
    (exact (h10-es-upd P (edge-rearm (deb-value w (:debtor e)) (deb-version w (:debtor e)))
             (rearm (deb-value w (:debtor e)) (deb-version w (:debtor e))) (:id e) (:edges w) h))))

(a/theorem h10-es-fire-dep [P :- (=> EdgeRow Bool),
                          phase :- (forall [p :- Nat, e :- EdgeRow]
                            (=> (= (P e) true) (= (P (edge-set-phase p e)) true))),
                          rearm :- (forall [v :- Nat, ver :- Nat, e :- EdgeRow]
                            (=> (= (P e) true) (= (P (edge-rearm v ver e)) true))), w :- World, e :- EdgeRow]
  (=> (= (tbl-all P (:edges w)) true) (= (tbl-all P (:edges (fire-dep w e))) true))
  (intro h)
  (have invalidated (= (tbl-all P (:edges (invalidate w e))) true))
  (exact (h10-es-upd P (edge-set-phase ph-fired) (phase ph-fired) (:id e) (:edges w) h))
  (cases holder (act-with-member (:id e) (:acts w)))
  (case [none] (simp only [fire-dep holder]) (exact invalidated))
  (case [some a]
    (cases deliver (Bool.and (run-current-of w (:run a) (:creditor e)) (deb-avail w (:debtor e))))
    (case [false] (simp only [fire-dep holder deliver]) (exact invalidated))
    (case [true]
      (simp only [fire-dep holder deliver deliver-dep])
      (exact (h3-fill-edges P (dep-consumed w e) a (:id e) (deb-result w (:debtor e)) (h10-es-dep-consumed P rearm w e h))))))

(a/theorem h10-es-fire-wait-act [P :- (=> EdgeRow Bool),
                               phase :- (forall [p :- Nat, e :- EdgeRow]
                                 (=> (= (P e) true) (= (P (edge-set-phase p e)) true))),
                               res :- RunResult, w :- World, e :- EdgeRow]
  (=> (= (tbl-all P (:edges w)) true) (= (tbl-all P (:edges (fire-wait-act res w e))) true))
  (intro h)
  (have phased := (h10-es-upd P (edge-set-phase ph-fired) (phase ph-fired) (:id e) (:edges w) h))
  (cases found (act-find w (:creditor e)))
  (case [none] (simp only [fire-wait-act found]) (exact phased))
  (case [some a]
    (cases current (run-current w (:run a)))
    (case [false] (simp only [fire-wait-act found current]) (exact phased))
    (case [true] (simp only [fire-wait-act found current])
      (exact (h3-fill-edges P (edge-upd w (:id e) (edge-set-phase ph-fired)) a (:id e) res phased)))))

(a/theorem h10-es-fire-edge [P :- (=> EdgeRow Bool),
                           phase :- (forall [p :- Nat, e :- EdgeRow]
                             (=> (= (P e) true) (= (P (edge-set-phase p e)) true))),
                           rearm :- (forall [v :- Nat, ver :- Nat, e :- EdgeRow]
                             (=> (= (P e) true) (= (P (edge-rearm v ver e)) true))),
                           seen :- (forall [ver :- Nat, e :- EdgeRow]
                             (=> (= (P e) true) (= (P (edge-set-seen ver e)) true))),
                           res :- RunResult, w :- World, x :- Nat]
  (=> (= (tbl-all P (:edges w)) true) (= (tbl-all P (:edges (fire-edge res w x))) true))
  (intro h)
  (cases found (edge-find w x))
  (case [none] (simp only [fire-edge found]) (exact h))
  (case [some e]
    (cases armed (Nat.beq (:phase e) ph-armed))
    (case [false] (simp only [fire-edge found armed]) (exact h))
    (case [true]
      (cases dep (Nat.beq (:kind e) ek-dep))
      (case [true] (simp only [fire-edge found armed dep]) (exact (h10-es-fire-dep P phase rearm w e h)))
      (case [false]
        (cases wait (Nat.beq (:kind e) ek-wait))
        (case [true]
          (simp only [fire-edge found armed dep wait])
          (cases host (Nat.beq (:creditor e) 0))
          (case [true] (simp only [fire-wait host]) (exact (h10-es-remove P w (:id e) h)))
          (case [false] (simp only [fire-wait host]) (exact (h10-es-fire-wait-act P phase res w e h))))
        (case [false]
          (cases observe (Nat.beq (:kind e) ek-observe))
          (case [false] (simp only [fire-edge found armed dep wait observe fire-savepoint-todo]) (exact h))
          (case [true]
            (cases fresh (observe-new e (deb-version w (:debtor e))))
            (case [false] (simp only [fire-edge found armed dep wait observe fire-observe fresh]) (exact h))
            (case [true] (simp only [fire-edge found armed dep wait observe fire-observe fresh edge-upd set-edges])
              (exact (h10-es-upd P (edge-set-seen (deb-version w (:debtor e))) (seen (deb-version w (:debtor e))) (:id e) (:edges w) h)))))))))

(a/theorem h10-es-fast-fill [P :- (=> EdgeRow Bool),
                           phase :- (forall [p :- Nat, e :- EdgeRow]
                             (=> (= (P e) true) (= (P (edge-set-phase p e)) true))),
                           rearm :- (forall [v :- Nat, ver :- Nat, e :- EdgeRow]
                             (=> (= (P e) true) (= (P (edge-rearm v ver e)) true))),
                           seen :- (forall [ver :- Nat, e :- EdgeRow]
                             (=> (= (P e) true) (= (P (edge-set-seen ver e)) true))),
                           ps :- (List DE), w :- World, d :- Nat]
  (=> (= (tbl-all P (:edges w)) true) (= (tbl-all P (:edges (fast-fill ps w d))) true))
  (intro h)
  (cases ready (fast-ready w d))
  (case [false] (simp only [fast-fill ready]) (exact h))
  (case [true] (simp only [fast-fill ready]) (exact (h10-es-fire-edge P phase rearm seen (deb-result w d) w (pair-edge d ps) h))))

(a/theorem h10-es-fold [P :- (=> EdgeRow Bool),
                      phase :- (forall [p :- Nat, e :- EdgeRow]
                        (=> (= (P e) true) (= (P (edge-set-phase p e)) true))),
                      rearm :- (forall [v :- Nat, ver :- Nat, e :- EdgeRow]
                        (=> (= (P e) true) (= (P (edge-rearm v ver e)) true))),
                      seen :- (forall [ver :- Nat, e :- EdgeRow]
                        (=> (= (P e) true) (= (P (edge-set-seen ver e)) true))),
                      ps :- (List DE), pre :- (List Nat)]
  (forall [w :- World]
    (=> (= (tbl-all P (:edges w)) true) (= (tbl-all P (:edges (nat-fold (fast-fill ps) w pre))) true)))
  (induction pre)
  (case [nil] (intros w h) (simp only [nat-fold]) (exact h))
  (case [cons d t ih] (intros w h) (simp only [nat-fold]) (exact (ih _ (h10-es-fast-fill P phase rearm seen ps w d h)))))

(a/theorem h10-pair-row-frame [a :- Nat, ds :- (List Nat), acc :- AwAcc, pre :- (List Nat), x :- Nat, d :- Nat, kind :- Nat]
  (=> (forall [e :- EdgeRow]
        (=> (List.Mem e (:edges (:world acc))) (= (:id e) x) (And (= (:debtor e) d) (= (:kind e) kind))))
      (forall [e :- EdgeRow]
        (=> (List.Mem e (:edges (h10-fill-prefix a ds acc pre))) (= (:id e) x)
            (And (= (:debtor e) d) (= (:kind e) kind)))))
  (intro fields)
  (have initial
    (= (tbl-all (fn [e :- EdgeRow]
          (Bool.or (Bool.not (Nat.beq (:id e) x))
                   (Bool.and (Nat.beq (:debtor e) d) (Nat.beq (:kind e) kind)))) (:edges (:world acc))) true))
  (apply all-of-mem) (intros e me)
  (cases id (Nat.beq (:id e) x))
  (case [false] (simp only [id Bool.not_false Bool.true_or]))
  (case [true]
    (have actual := (fields e me (Nat.eq_of_beq_eq_true id)))
    (simp only [id Bool.not_true Bool.false_or (And.left actual) (And.right actual) Nat.beq_refl Bool.and_self]))
  (have after := (h10-es-fold
    (fn [e :- EdgeRow] (Bool.or (Bool.not (Nat.beq (:id e) x)) (Bool.and (Nat.beq (:debtor e) d) (Nat.beq (:kind e) kind))))
    (fn [p :- Nat, e :- EdgeRow, h :- (= (Bool.or (Bool.not (Nat.beq (:id e) x)) (Bool.and (Nat.beq (:debtor e) d) (Nat.beq (:kind e) kind))) true)] h)
    (fn [v :- Nat, ver :- Nat, e :- EdgeRow, h :- (= (Bool.or (Bool.not (Nat.beq (:id e) x)) (Bool.and (Nat.beq (:debtor e) d) (Nat.beq (:kind e) kind))) true)] h)
    (fn [ver :- Nat, e :- EdgeRow, h :- (= (Bool.or (Bool.not (Nat.beq (:id e) x)) (Bool.and (Nat.beq (:debtor e) d) (Nat.beq (:kind e) kind))) true)] h)
    (:pairs acc) pre (h10-install a ds acc) initial))
  (intros e me id)
  (have fact := (tbl-all-mem EdgeRow _ e _ after me))
  (simp only [id Nat.beq_refl Bool.not_true Bool.false_or Bool.and_eq_true] at fact)
  (exact (And.intro (Nat.eq_of_beq_eq_true (And.left fact)) (Nat.eq_of_beq_eq_true (And.right fact)))))

(a/theorem h10-ndx-prefix [a :- Nat, ds :- (List Nat), acc :- AwAcc, pre :- (List Nat), x :- Nat]
  (=> (= (tbl-all (h3-ndx x) (:edges (:world acc))) true)
      (= (tbl-all (h3-ndx x) (:edges (h10-fill-prefix a ds acc pre))) true))
  (intro h)
  (exact (h10-es-fold (h3-ndx x)
           (fn [p :- Nat, e :- EdgeRow, h :- (= (h3-ndx x e) true)] h)
           (fn [v :- Nat, ver :- Nat, e :- EdgeRow, h :- (= (h3-ndx x e) true)] h)
           (fn [ver :- Nat, e :- EdgeRow, h :- (= (h3-ndx x e) true)] h)
           (:pairs acc) pre (h10-install a ds acc) h)))

(a/theorem h10-prefix-id-disjoint [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat,
                                 k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, pre :- (List Nat), d :- Nat]
  (=> (h9-entry xm w r ds mode st fresh) (= (nat-mem d ds) true)
      (And (= (comp-has (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre)
                       (pair-edge d (:pairs (await-acc w r ds mode k mine)))) false)
           (forall [e :- EdgeRow]
             (=> (List.Mem e (:edges (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre)))
                 (= (Nat.beq (:debtor e) (pair-edge d (:pairs (await-acc w r ds mode k mine)))) false)))))
  (intros ent md)
  (have support := (h9-prefix-support xm w r ds mode k mine st fresh (nat-distinct ds) (List.nil Nat) ent (h9-app-nil _)))
  (have hs := (h3-sample xm _ (And.left support)))
  (have found := (h9-prefix-pair-edge xm w r ds mode k mine st fresh (nat-distinct ds) (List.nil Nat) d ent (h9-app-nil _) (h9-distinct-complete ds d md)))
  (cases found)
  (case [intro e found]
    (have edge := (tbl-find-has EdgeRow edge-id _ e _ (And.left found)))
    (apply And.intro)
    (exact (h10-fm-not-comp (h10-install (:next-id w) ds (await-acc w r ds mode k mine))
             (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre)
             (pair-edge d (:pairs (await-acc w r ds mode k mine)))
             (h10-fm-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre)
             (h3-edge-not-comp _ _ hs edge)))
    (have after := (h10-ndx-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre
                     (pair-edge d (:pairs (await-acc w r ds mode k mine))) (h3-edge-not-debtor _ _ hs edge)))
    (intros row member)
    (exact (bnot-true _ (tbl-all-mem EdgeRow _ row _ after member)))))

(a/theorem h10-comp-not-resource [w :- World, d :- Nat]
  (=> (= (inv-sample w) true) (= (comp-has w d) true) (= (resource-has w d) false))
  (intros hs comp)
  (cases resource (resource-has w d))
  (case [false] (rfl))
  (case [true]
    (have unique := (ids-unique-of w hs)) (simp only [all-ids] at unique)
    (have rest := (nat-nodup-app-right _ _ unique))
    (have comp-member (= (nat-mem d (tbl-ids comp-id (:comps w))) true)) (rw [nat-mem-ids]) (exact comp)
    (have resource-member (= (nat-mem d (tbl-ids resource-id (:res w))) true)) (rw [nat-mem-ids]) (exact resource)
    (have disjoint := (nodup-app-disj d _ _ rest comp-member))
    (simp only [nat-mem-app resource-member Bool.or_true Bool.true_or] at disjoint) (cases disjoint)))

(a/theorem h10-nready-tasks [w :- World, d :- Nat]
  (=> (= (gl w) true) (= (fast-ready w d) false)
      (= (tbl-all (h3-tk (:runs w) d) (:tasks w)) true))
  (intros gl nonready)
  (have hs := (gl-sample w gl))
  (have not-final := (fast-not-final w d hs nonready))
  (apply all-of-mem) (intros t mt)
  (cases id (Nat.beq (:id t) d))
  (case [false] (simp only [h3-tk id Bool.not_false Bool.true_or]))
  (case [true]
    (have td := (Nat.eq_of_beq_eq_true id))
    (have task-has (= (tbl-has task-id d (:tasks w)) true))
    (have own := (has-of-mem TaskRow task-id t (:tasks w) mt)) (simp only [task-id] at own) (rw [td] at own) (exact own)
    (have source-none (= (source-find w d) (Option.none SourceRow)))
    (cases source (source-find w d))
    (case [none] (rfl))
    (case [some src]
      (have no-task := (h3-src-not-task w d hs (tbl-find-has SourceRow source-id d src (:sources w) source)))
      (rw [task-has] at no-task) (cases no-task))
    (have found (= (task-find w d) (Option.some TaskRow t)))
    (have lookup := (find-self TaskRow task-id t (:tasks w) (tasks-nodup w hs) mt)) (simp only [task-id] at lookup) (rw [td] at lookup) (exact lookup)
    (change (= (tbl-find source-id d (:sources w)) (Option.none SourceRow)) at source-none)
    (change (= (tbl-find task-id d (:tasks w)) (Option.some TaskRow t)) at found)
    (simp only [fin-st source-none found find-or task-done] at not-final)
    (have pending := (bnot-false _ not-final))
    (have run := (gl-task-has-run w t gl mt))
    (cases lookup (run-find w (:run t)))
    (case [none] (simp only [task-has-run pending Bool.not_true Bool.false_or lookup] at run) (cases run))
    (case [some q]
      (simp only [task-has-run pending Bool.not_true Bool.false_or lookup Bool.and_eq_true] at run)
      (have mq := (tbl-find-mem RunRow run-id (:run t) q (:runs w) lookup))
      (have qid (= (:id q) (:run t))) (exact (tbl-find-id RunRow run-id (:run t) q (:runs w) lookup))
      (simp only [h3-tk id Bool.not_true Bool.false_or])
      (apply (any-elim-of RunRow (h3-ral (:run t)) q (:runs w) mq))
      (simp only [h3-ral qid Nat.beq_refl Bool.true_and]) (exact (And.right run)))))

(a/theorem h10-del-self [A :- Type, idf :- (=> A Nat), x :- Nat, xs :- (List A)]
  (= (tbl-has idf x (tbl-del idf x xs)) false)
  (induction xs)
  (case [nil] (simp only [tbl-del tbl-has]))
  (case [cons e t ih]
    (cases id (Nat.beq (idf e) x))
    (case [true] (simp only [tbl-del id]) (exact ih))
    (case [false] (simp only [tbl-del id tbl-has id]) (exact ih))))

(a/theorem h10-removed-absent [w :- World, x :- Nat]
  (= (tbl-has edge-id x (:edges (remove-edge w x))) false)
  (cases found (edge-find w x))
  (case [none] (simp only [remove-edge found]) (exact (tbl-find-none-has EdgeRow edge-id x (:edges w) found)))
  (case [some e]
    (cases marked (:marked e))
    (all_goals (simp only [remove-edge found marked comp-upd edge-del set-comps set-edges]))
    (all_goals (exact (h10-del-self EdgeRow edge-id x (:edges w))))))

(a/theorem h10-free-not-armed [xm :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (h3 xm w) true) (= (edge-find w (:id e)) (Option.some EdgeRow e))
      (= (Nat.beq (:phase e) ph-armed) false) (= (h3-free xm w (:id e)) true))
  (intros h found phase)
  (have me := (tbl-find-mem EdgeRow edge-id (:id e) e (:edges w) found))
  (apply h3-free-by)
  (intros b q mb mq id owner current member nonexempt)
  (have good := (h3-ob-use xm w b q (:id e) e (h3-rest-of xm w h) mb mq id owner current member nonexempt me (rfl)))
  (have structure := (And.left good)) (simp only [h3-s Bool.and_eq_true] at structure)
  (have armed := (And.left structure)) (rw [phase] at armed) (cases armed))

(a/theorem h10-phase-is-free [xm :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (edge-find w (:id e)) (Option.some EdgeRow e))
      (= (h3 xm (edge-upd w (:id e) (edge-set-phase ph-fired))) true)
      (= (h3-free xm (edge-upd w (:id e) (edge-set-phase ph-fired)) (:id e)) true))
  (intros found h)
  (have after := (hk-find-upd EdgeRow edge-id (:id e) (edge-set-phase ph-fired) (edge-set-phase-edge-id ph-fired) (:edges w) e found))
  (exact (h10-free-not-armed xm (edge-upd w (:id e) (edge-set-phase ph-fired)) (edge-set-phase ph-fired e) h after (rfl))))

(a/theorem h10-invalidate-free [xm :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (h3 xm w) true) (= (edge-find w (:id e)) (Option.some EdgeRow e))
      (= (Nat.beq (:kind e) ek-dep) true) (= (h3-free xm (invalidate w e) (:id e)) true))
  (intros h found kind)
  (have me := (tbl-find-mem EdgeRow edge-id (:id e) e (:edges w) found))
  (have preserved := (h3-invalidate xm w e me kind h))
  (have after := (hk-find-upd EdgeRow edge-id (:id e) (edge-set-phase ph-fired) (edge-set-phase-edge-id ph-fired) (:edges w) e found))
  (exact (h10-free-not-armed xm (invalidate w e) (edge-set-phase ph-fired e) preserved after (rfl))))

(a/theorem h10-deliver-free [xm :- (List Nat), w :- World, e :- EdgeRow, a :- ActRow]
  (=> (= (h3 xm w) true) (= (edge-find w (:id e)) (Option.some EdgeRow e))
      (= (act-with-member (:id e) (:acts w)) (Option.some ActRow a))
      (= (h3-free xm (deliver-dep w e a) (:id e)) true))
  (intros h found holder)
  (have me := (tbl-find-mem EdgeRow edge-id (:id e) e (:edges w) found))
  (have ma := (act-with-member-mem (:id e) (:acts w) a holder))
  (have freeb := (h3-freeb-of xm w e a (h3-rest-of xm w h) me holder))
  (cases final (deb-final w (:debtor e)))
  (case [false]
    (simp only [deliver-dep dep-consumed final])
    (exact (h3-free-fill xm (edge-upd w (:id e) (edge-rearm (deb-value w (:debtor e)) (deb-version w (:debtor e)))) a (:id e) (deb-result w (:debtor e)) ma freeb)))
  (case [true]
    (have after-freeb := (h3-freeb-frame xm w (remove-edge w (:id e)) (:id e) (:id a)
                          (h3-acts-remove-edge w (:id e)) (runs-remove-edge w (:id e))
                          (h3-cur-remove-edge w (:id e)) freeb))
    (have after-member (List.Mem a (:acts (remove-edge w (:id e))))) (rw [h3-acts-remove-edge]) (exact ma)
    (simp only [deliver-dep dep-consumed final])
    (exact (h3-free-fill xm (remove-edge w (:id e)) a (:id e) (deb-result w (:debtor e)) after-member after-freeb))))

(a/theorem h10-fire-dep-free [xm :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (h3 xm w) true) (= (edge-find w (:id e)) (Option.some EdgeRow e))
      (= (Nat.beq (:kind e) ek-dep) true) (= (deb-avail w (:debtor e)) true)
      (= (h3-free xm (fire-dep w e) (:id e)) true))
  (intros h found kind available)
  (cases holder (act-with-member (:id e) (:acts w)))
  (case [none] (simp only [fire-dep holder]) (exact (h10-invalidate-free xm w e h found kind)))
  (case [some a]
    (cases current (run-current-of w (:run a) (:creditor e)))
    (case [false] (simp only [fire-dep holder current available Bool.false_and]) (exact (h10-invalidate-free xm w e h found kind)))
    (case [true] (simp only [fire-dep holder current available Bool.and_self]) (exact (h10-deliver-free xm w e a h found holder)))))

(a/theorem h10-fire-wait-act-free [xm :- (List Nat), res :- RunResult, w :- World, e :- EdgeRow]
  (=> (= (h3 xm w) true) (= (edge-find w (:id e)) (Option.some EdgeRow e))
      (= (Nat.beq (:kind e) ek-dep) false)
      (= (h3-free xm (fire-wait-act res w e) (:id e)) true))
  (intros h found kind)
  (have me := (tbl-find-mem EdgeRow edge-id (:id e) e (:edges w) found))
  (have preserved := (h3-fire-wait-act xm res w e found kind h))
  (cases holder (act-find w (:creditor e)))
  (case [none]
    (simp only [fire-wait-act holder] at preserved)
    (simp only [fire-wait-act holder]) (exact (h10-phase-is-free xm w e found preserved)))
  (case [some a]
    (cases current (run-current w (:run a)))
    (case [false]
      (simp only [fire-wait-act holder current] at preserved)
      (simp only [fire-wait-act holder current]) (exact (h10-phase-is-free xm w e found preserved)))
    (case [true]
      (have ma := (tbl-find-mem ActRow act-id (:creditor e) a (:acts w) holder))
      (have aid (= (:id a) (:creditor e))) (exact (tbl-find-id ActRow act-id (:creditor e) a (:acts w) holder))
      (have freeb := (h3-freeb-cred xm w e (h3-rest-of xm w h) me kind))
      (simp only [fire-wait-act holder current])
      (have fb (= (h3-freeb xm (edge-upd w (:id e) (edge-set-phase ph-fired)) (:id e) (:id a)) true))
      (rw [aid]) (exact freeb)
      (exact (h3-free-fill xm (edge-upd w (:id e) (edge-set-phase ph-fired)) a (:id e) res ma fb)))))

(a/theorem h10-fire-wait-free [xm :- (List Nat), res :- RunResult, w :- World, e :- EdgeRow]
  (=> (= (h3 xm w) true) (= (edge-find w (:id e)) (Option.some EdgeRow e))
      (= (Nat.beq (:kind e) ek-wait) true)
      (= (h3-free xm (fire-wait res w e) (:id e)) true))
  (intros h found kind)
  (have not-dep (= (Nat.beq (:kind e) ek-dep) false)) (rw [(Nat.eq_of_beq_eq_true kind)])
  (cases host (Nat.beq (:creditor e) 0))
  (case [false] (simp only [fire-wait host]) (exact (h10-fire-wait-act-free xm res w e h found not-dep)))
  (case [true]
    (have preserved := (h3-fire-wait xm res w e found kind h))
    (simp only [fire-wait host] at preserved)
    (simp only [fire-wait host])
    (exact (h3-free-noedge xm (remove-edge w (:id e)) (:id e) (h3-rest-of xm _ preserved) (h10-removed-absent w (:id e))))))

(a/theorem h10-ready-available [w :- World, d :- Nat]
  (=> (= (awake (:comps w) d) true) (= (fast-ready w d) true) (= (deb-avail w d) true))
  (intros awake ready)
  (cases found (comp-find w d))
  (case [none] (simp only [deb-avail found]))
  (case [some c]
    (have mc := (tbl-find-mem CompRow comp-id d c (:comps w) found))
    (have id (= (:id c) d)) (exact (tbl-find-id CompRow comp-id d c (:comps w) found))
    (have aw := (tbl-all-mem CompRow (not-idle-if-id d) c (:comps w) awake mc))
    (simp only [not-idle-if-id id Nat.beq_refl Bool.not_true Bool.false_or] at aw)
    (have not-idle := (bnot-true _ aw))
    (simp only [fast-ready found not-idle Bool.false_and Bool.or_false] at ready)
    (simp only [deb-avail found]) (exact ready)))

(a/theorem h10-fast-fill-free [xm :- (List Nat), ps :- (List DE), w :- World, d :- Nat]
  (=> (= (h3 xm w) true) (= (awake (:comps w) d) true) (= (fast-ready w d) true)
      (forall [e :- EdgeRow]
        (=> (= (edge-find w (pair-edge d ps)) (Option.some EdgeRow e))
            (And (= (:debtor e) d) (Or (= (Nat.beq (:kind e) ek-dep) true) (= (Nat.beq (:kind e) ek-wait) true)))))
      (= (h3-free xm (fast-fill ps w d) (pair-edge d ps)) true))
  (intros h awake ready fields)
  (cases found (edge-find w (pair-edge d ps)))
  (case [none]
    (simp only [fast-fill ready fire-edge found])
    (exact (h3-free-noedge xm w (pair-edge d ps) (h3-rest-of xm w h)
             (tbl-find-none-has EdgeRow edge-id _ (:edges w) found))))
  (case [some e]
    (have id (= (:id e) (pair-edge d ps))) (exact (tbl-find-id EdgeRow edge-id _ e (:edges w) found))
    (have found-id (= (edge-find w (:id e)) (Option.some EdgeRow e))) (rw [id]) (exact found)
    (cases phase (Nat.beq (:phase e) ph-armed))
    (case [false]
      (simp only [fast-fill ready fire-edge found phase])
      (rw [← id]) (exact (h10-free-not-armed xm w e h found-id phase)))
    (case [true]
      (have facts := (fields e found))
      (have debtor := (And.left facts))
      (have kind := (And.right facts))
      (cases kind)
      (case [inl dep]
        (simp only [fast-fill ready fire-edge found phase dep])
        (rw [← id])
        (have available (= (deb-avail w (:debtor e)) true)) (rw [debtor]) (exact (h10-ready-available w d awake ready))
        (exact (h10-fire-dep-free xm w e h found-id dep available)))
      (case [inr wait]
        (have not-dep (= (Nat.beq (:kind e) ek-dep) false)) (rw [(Nat.eq_of_beq_eq_true wait)])
        (simp only [fast-fill ready fire-edge found phase not-dep wait])
        (rw [← id]) (exact (h10-fire-wait-free xm (deb-result w d) w e h found-id wait))))))

(a/theorem h10-prefix-pair-row [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat,
                              k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, pre :- (List Nat), d :- Nat]
  (=> (h9-entry xm w r ds mode st fresh) (= (nat-mem d ds) true)
      (forall [e :- EdgeRow]
        (=> (List.Mem e (:edges (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre)))
            (= (:id e) (pair-edge d (:pairs (await-acc w r ds mode k mine))))
            (And (= (:debtor e) d) (= (:kind e) (if (as-dep (await-pre w r ds mode k mine) r d) ek-dep ek-wait))))))
  (intros ent md)
  (have found := (h9-prefix-pair-edge xm w r ds mode k mine st fresh (nat-distinct ds) (List.nil Nat) d ent (h9-app-nil _) (h9-distinct-complete ds d md)))
  (cases found)
  (case [intro e found]
    (have fields := (And.left (And.right (And.right found))))
    (have unique := (And.right (And.right (And.right found))))
    (have before
      (forall [q :- EdgeRow]
        (=> (List.Mem q (:edges (:world (await-acc w r ds mode k mine))))
            (= (:id q) (pair-edge d (:pairs (await-acc w r ds mode k mine))))
            (And (= (:debtor q) d) (= (:kind q) (if (as-dep (await-pre w r ds mode k mine) r d) ek-dep ek-wait))))))
    (intros q mq id) (rw [(unique q mq id)])
    (exact (And.intro (And.left fields) (And.left (And.right (And.right (And.right fields))))))
    (exact (h10-pair-row-frame (:next-id w) ds (await-acc w r ds mode k mine) pre
             (pair-edge d (:pairs (await-acc w r ds mode k mine))) d
             (if (as-dep (await-pre w r ds mode k mine) r d) ek-dep ek-wait) before))))

(a/theorem h10-fm-has-back [w :- World, V :- World, x :- Nat]
  (=> (h3-fm w V) (= (comp-has V x) true) (= (comp-has w x) true))
  (intros relation present)
  (cases old (comp-has w x))
  (case [true] (rfl))
  (case [false] (have no := (h10-fm-not-comp w V x relation old)) (rw [present] at no) (cases no)))

(a/theorem h10-prefix-comp-back [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat,
                               k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, pre :- (List Nat), x :- Nat]
  (=> (h9-entry xm w r ds mode st fresh)
      (= (comp-has (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre) x) true)
      (= (comp-has w x) true))
  (intros ent present)
  (have old := (h10-fm-has-back (h10-install (:next-id w) ds (await-acc w r ds mode k mine))
                 (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre) x
                 (h10-fm-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre) present))
  (have shape := (h9-prefix-shape xm w r ds mode k mine st fresh (nat-distinct ds) (List.nil Nat) ent (h9-app-nil _)))
  (have frame := ((And.right (And.right (And.right (And.right (And.right shape))))) x))
  (exact (Eq.trans (Eq.symm frame) old)))

(a/theorem h10-nready-holder-good [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat,
                                 k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, pre :- (List Nat),
                                 d :- Nat, b :- ActRow, q :- RunRow]
  (=> (h9-entry xm w r ds mode st fresh) (= (nat-mem d ds) true)
      (= (fast-ready (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre) d) false)
      (List.Mem b (:acts (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre)))
      (List.Mem q (:runs (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre))) (= (:id q) (:run b))
      (= (reach-mem (:of q) xm) false)
      (= (tbl-any (h3-cur (rk3 q)) (:comps (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre))) true)
      (= (reach-mem (pair-edge d (:pairs (await-acc w r ds mode k mine))) (act-contrib b)) true)
      (= (reach-mem (pair-edge d (:pairs (await-acc w r ds mode k mine))) xm) false)
      (= (h3-x xm (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre) b (rk3 q)
                 (pair-edge d (:pairs (await-acc w r ds mode k mine)))) true))
  (intros ent md nonready mb mq id owner current contributes nonexempt)
  (have shadow := (h10-prefix-shadow xm w r ds mode k mine st fresh pre ent))
  (have shadow-owner := (h10-prefix-owner-not-shadow xm w r ds mode k mine st fresh pre d b q
                          ent md mb mq id owner current contributes nonexempt))
  (have shadow-member (= (reach-mem (pair-edge d (:pairs (await-acc w r ds mode k mine))) (List.append Nat ds xm)) false))
  (simp only [reach-mem-append (h10-pair-not-ds xm w r ds mode k mine st fresh d ent md) nonexempt Bool.false_or])
  (have exists := (h3-ob-has (List.append Nat ds xm) _ b q _ (h3-rest-of _ _ shadow)
                     mb mq id shadow-owner current contributes shadow-member))
  (have key := (h10-prefix-holder-key xm w r ds mode k mine st fresh pre d b q
                  ent md mb mq id owner current contributes nonexempt))
  (have qof (= (:of q) (:of r))) (exact (congrArg (fn [k :- RK3] (:of k)) key))
  (have owner-has := (h10-cur-has (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre) (rk3 q) current))
  (have original-owner (= (comp-has w (:of r)) true))
  (rw [← qof])
  (exact (h10-prefix-comp-back xm w r ds mode k mine st fresh pre (:of q) ent owner-has))
  (have gd := (h10-prefix-gd xm w r ds mode k mine st fresh pre ent))
  (have gl := (h10-prefix-gl xm w r ds mode k mine st fresh pre ent))
  (have awake := (h10-prefix-awake xm w r ds mode k mine st fresh pre d ent md))
  (have waiting := (h10-fast-not-ready-waiting _ d gd awake nonready))
  (have tasks := (h10-nready-tasks _ d gl nonready))
  (simp only [h3-x Bool.or_eq_true Bool.and_eq_true])
  (apply Or.inr) (apply And.intro) (exact exists)
  (apply all-of-mem) (intros e me)
  (cases same (Nat.beq (:id e) (pair-edge d (:pairs (await-acc w r ds mode k mine)))))
  (case [false] (simp only [h3-eok same Bool.not_false Bool.true_or]))
  (case [true]
    (have row := (h10-prefix-pair-row xm w r ds mode k mine st fresh pre d ent md e me (Nat.eq_of_beq_eq_true same)))
    (have structure := (And.left (h3-ob-use (List.append Nat ds xm) _ b q _ e (h3-rest-of _ _ shadow)
                                    mb mq id shadow-owner current contributes shadow-member me (Nat.eq_of_beq_eq_true same))))
    (simp only [h3-eok same Bool.not_true Bool.false_or Bool.and_eq_true Bool.or_eq_true])
    (apply And.intro) (exact structure) (apply Or.inr)
    (simp only [h3-m (And.left row) Bool.and_eq_true Bool.or_eq_true])
    (apply And.intro) (exact tasks)
    (cases comp (comp-has (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre) d))
    (case [false] (apply Or.inl) (exact (Eq.trans (congrArg Bool.not comp) (rfl))))
    (case [true]
      (apply Or.inr) (apply And.intro)
      (have old-comp := (h10-prefix-comp-back xm w r ds mode k mine st fresh pre d ent comp))
      (have no-resource := (h10-comp-not-resource w d (h3-sample xm w (And.left (And.right ent))) old-comp))
      (have dep (= (as-dep (await-pre w r ds mode k mine) r d) true))
      (rw [(h9-as-dep-shape w r ds mode k mine (await-pre w r ds mode k mine) d (h9-shape-pre w r ds mode k mine))])
      (simp only [as-dep in-comp original-owner no-resource Bool.not_false Bool.and_self])
      (have kind := (And.right row)) (simp only [dep] at kind)
      (rw [kind])
      (exact waiting))))

(a/theorem h10-fold-append [f :- (=> World Nat World), xs :- (List Nat)]
  (forall [ys :- (List Nat), w :- World]
    (= (nat-fold f w (List.append Nat xs ys)) (nat-fold f (nat-fold f w xs) ys)))
  (induction xs)
  (case [nil] (intros ys w) (rfl))
  (case [cons d t ih] (intros ys w) (simp only [List.append nat-fold]) (exact (ih ys (f w d)))))

(a/theorem h10-prefix-snoc [a :- Nat, ds :- (List Nat), acc :- AwAcc, pre :- (List Nat), d :- Nat]
  (= (h10-fill-prefix a ds acc (List.append Nat pre (List.cons Nat d (List.nil Nat))))
     (fast-fill (:pairs acc) (h10-fill-prefix a ds acc pre) d))
  (exact (h10-fold-append (fast-fill (:pairs acc)) pre (List.cons Nat d (List.nil Nat)) (h10-install a ds acc))))

(a/theorem h10-free-widen [xm :- (List Nat), ym :- (List Nat), w :- World, x :- Nat]
  (=> (forall [y :- Nat] (=> (= (reach-mem y xm) true) (= (reach-mem y ym) true)))
      (= (h3-free xm w x) true) (= (h3-free ym w x) true))
  (intros include free)
  (apply h3-free-by)
  (intros b q mb mq id owner current member nonexempt)
  (exact (h3-free-use xm w x b q free mb mq id
           (h10-not-in-smaller xm ym (:of q) include owner) current member
           (h10-not-in-smaller xm ym x include nonexempt))))

(a/theorem h10-shadow-free-original [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat,
                                   k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, pre :- (List Nat), d :- Nat]
  (=> (h9-entry xm w r ds mode st fresh) (= (nat-mem d ds) true)
      (= (h3-free (List.append Nat ds xm) (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre)
                   (pair-edge d (:pairs (await-acc w r ds mode k mine)))) true)
      (= (h3-free xm (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre)
                   (pair-edge d (:pairs (await-acc w r ds mode k mine)))) true))
  (intros ent md free)
  (apply h3-free-by)
  (intros b q mb mq id owner current contributes nonexempt)
  (have shadow-owner := (h10-prefix-owner-not-shadow xm w r ds mode k mine st fresh pre d b q
                          ent md mb mq id owner current contributes nonexempt))
  (have shadow-member (= (reach-mem (pair-edge d (:pairs (await-acc w r ds mode k mine))) (List.append Nat ds xm)) false))
  (simp only [reach-mem-append (h10-pair-not-ds xm w r ds mode k mine st fresh d ent md) nonexempt Bool.false_or])
  (exact (h3-free-use (List.append Nat ds xm) _ _ b q free mb mq id shadow-owner current contributes shadow-member)))

(a/theorem h10-ready-prefix-free [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat,
                                k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, pre :- (List Nat), d :- Nat]
  (=> (h9-entry xm w r ds mode st fresh) (= (nat-mem d ds) true)
      (= (fast-ready (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre) d) true)
      (= (h3-free xm (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine)
                       (List.append Nat pre (List.cons Nat d (List.nil Nat))))
                   (pair-edge d (:pairs (await-acc w r ds mode k mine)))) true))
  (intros ent md ready)
  (have fields
    (forall [e :- EdgeRow]
      (=> (= (edge-find (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre)
                       (pair-edge d (:pairs (await-acc w r ds mode k mine)))) (Option.some EdgeRow e))
          (And (= (:debtor e) d) (Or (= (Nat.beq (:kind e) ek-dep) true) (= (Nat.beq (:kind e) ek-wait) true))))))
  (intros e found)
  (have row := (h10-prefix-pair-row xm w r ds mode k mine st fresh pre d ent md e
                 (tbl-find-mem EdgeRow edge-id _ e _ found) (tbl-find-id EdgeRow edge-id _ e _ found)))
  (apply And.intro) (exact (And.left row))
  (have kind := (And.right row))
  (cases dep (as-dep (await-pre w r ds mode k mine) r d))
  (case [true] (simp only [dep] at kind) (apply Or.inl) (rw [kind]))
  (case [false] (simp only [dep] at kind) (apply Or.inr) (rw [kind]))
  (have free := (h10-fast-fill-free (List.append Nat ds xm) (:pairs (await-acc w r ds mode k mine))
                  (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre) d
                  (h10-prefix-shadow xm w r ds mode k mine st fresh pre ent)
                  (h10-prefix-awake xm w r ds mode k mine st fresh pre d ent md) ready fields))
  (have after (= (h3-free (List.append Nat ds xm)
                   (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) (List.append Nat pre (List.cons Nat d (List.nil Nat))))
                   (pair-edge d (:pairs (await-acc w r ds mode k mine)))) true))
  (rw [h10-prefix-snoc]) (exact free)
  (exact (h10-shadow-free-original xm w r ds mode k mine st fresh
           (List.append Nat pre (List.cons Nat d (List.nil Nat))) d ent md after)))

(a/theorem h10-shrink-step [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat,
                          k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat,
                          pre :- (List Nat), tail :- (List Nat), d :- Nat]
  (=> (h9-entry xm w r ds mode st fresh) (= (nat-mem d ds) true)
      (= (h3 (h10-pending-exempt (:pairs (await-acc w r ds mode k mine)) (List.cons Nat d tail) xm)
             (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre)) true)
      (= (h3 (h10-pending-exempt (:pairs (await-acc w r ds mode k mine)) tail xm)
             (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine)
               (List.append Nat pre (List.cons Nat d (List.nil Nat))))) true))
  (intros ent md old)
  (have include := (h10-pending-includes (:pairs (await-acc w r ds mode k mine)) tail xm))
  (cases ready (fast-ready (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre) d))
  (case [false]
    (have disjoint := (h10-prefix-id-disjoint xm w r ds mode k mine st fresh pre d ent md))
    (have good
      (forall [b :- ActRow, q :- RunRow]
        (=> (List.Mem b (:acts (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre)))
            (List.Mem q (:runs (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre))) (= (:id q) (:run b))
            (= (reach-mem (:of q) (h10-pending-exempt (:pairs (await-acc w r ds mode k mine)) tail xm)) false)
            (= (tbl-any (h3-cur (rk3 q)) (:comps (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre))) true)
            (= (reach-mem (pair-edge d (:pairs (await-acc w r ds mode k mine))) (act-contrib b)) true)
            (= (reach-mem (pair-edge d (:pairs (await-acc w r ds mode k mine)))
                         (h10-pending-exempt (:pairs (await-acc w r ds mode k mine)) tail xm)) false)
            (= (h3-x (h10-pending-exempt (:pairs (await-acc w r ds mode k mine)) tail xm)
                     (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre) b (rk3 q)
                     (pair-edge d (:pairs (await-acc w r ds mode k mine)))) true))))
    (intros b q mb mq id owner current contributes nonexempt)
    (have original-owner := (h10-not-in-smaller xm _ (:of q) include owner))
    (have original-member := (h10-not-in-smaller xm _ (pair-edge d (:pairs (await-acc w r ds mode k mine))) include nonexempt))
    (have member-good := (h10-nready-holder-good xm w r ds mode k mine st fresh pre d b q
                           ent md ready mb mq id original-owner current contributes original-member))
    (exact (h10-x-widen xm _ _ b (rk3 q) _ include member-good))
    (have restored := (h3-undo-g (h10-pending-exempt (:pairs (await-acc w r ds mode k mine)) tail xm)
                        (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre)
                        (pair-edge d (:pairs (await-acc w r ds mode k mine)))
                        (And.left disjoint) (And.right disjoint) good (h3-rest-of _ _ old)))
    (rw [h10-prefix-snoc]) (simp only [fast-fill ready])
    (exact (h3-intro _ _ (h3-sample _ _ old) restored)))
  (case [true]
    (have after := (hm3-fast-fill
                     (h10-pending-exempt (:pairs (await-acc w r ds mode k mine)) (List.cons Nat d tail) xm)
                     (:pairs (await-acc w r ds mode k mine))
                     (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre) d old))
    (have after2
      (= (h3 (List.cons Nat (pair-edge d (:pairs (await-acc w r ds mode k mine)))
                   (h10-pending-exempt (:pairs (await-acc w r ds mode k mine)) tail xm))
             (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine)
               (List.append Nat pre (List.cons Nat d (List.nil Nat))))) true))
    (rw [h10-prefix-snoc]) (exact after)
    (have disjoint := (h10-prefix-id-disjoint xm w r ds mode k mine st fresh
                        (List.append Nat pre (List.cons Nat d (List.nil Nat))) d ent md))
    (have original-free := (h10-ready-prefix-free xm w r ds mode k mine st fresh pre d ent md ready))
    (have free := (h10-free-widen xm _ _ _ include original-free))
    (exact (h3-intro _ _ (h3-sample _ _ after2)
             (h3-undo-x (h10-pending-exempt (:pairs (await-acc w r ds mode k mine)) tail xm) _ _
               (And.left disjoint) (And.right disjoint) free (h3-rest-of _ _ after2))))))

(a/theorem h10-prefix-process [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat,
                             k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, xs :- (List Nat)]
  (forall [pre :- (List Nat), tail :- (List Nat)]
    (=> (h9-entry xm w r ds mode st fresh)
        (= (List.append Nat pre (List.append Nat xs tail)) (nat-distinct ds))
        (= (h3 (h10-pending-exempt (:pairs (await-acc w r ds mode k mine)) (List.append Nat xs tail) xm)
               (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) pre)) true)
        (= (h3 (h10-pending-exempt (:pairs (await-acc w r ds mode k mine)) tail xm)
               (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) (List.append Nat pre xs))) true)))
  (induction xs)
  (case [nil] (intros pre tail ent split old) (rw [h9-app-nil]) (exact old))
  (case [cons d t ih]
    (intros pre tail ent split old)
    (have distinct-member (= (nat-mem d (nat-distinct ds)) true))
    (rw [← split ← reach-mem-nat-mem reach-mem-append])
    (simp only [List.append reach-mem-cons Nat.beq_refl Bool.true_or Bool.or_true])
    (have md := (h9-distinct-source ds d distinct-member))
    (have step := (h10-shrink-step xm w r ds mode k mine st fresh pre (List.append Nat t tail) d ent md old))
    (have split2 (= (List.append Nat (List.append Nat pre (List.cons Nat d (List.nil Nat))) (List.append Nat t tail)) (nat-distinct ds)))
    (rw [h9-app-assoc]) (exact split)
    (have final := (ih (List.append Nat pre (List.cons Nat d (List.nil Nat))) tail ent split2 step))
    (rw [h9-app-assoc] at final) (exact final)))

(a/theorem h10-fill-prefix-h3 [xm :- (List Nat), w :- World, r :- RunRow,
         ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat),
         st :- Nat, fresh :- Nat, pre :- (List Nat), tail :- (List Nat)]
  (=> (h9-entry xm w r ds mode st fresh)
      (= (List.append Nat pre tail) (nat-distinct ds))
      (let [C (await-acc w r ds mode k mine)]
        (= (h3 (h10-pending-exempt (:pairs C) tail xm)
               (h10-fill-prefix (:next-id w) ds C pre)) true)))
  (intros ent split)
  (have initial := (h10-install-h3-exempt xm w r ds mode k mine st fresh ent))
  (rw [← split] at initial)
  (exact (h10-prefix-process xm w r ds mode k mine st fresh pre (List.nil Nat) tail ent split initial)))

(a/theorem h10-fast-fill-h3 [xm :- (List Nat), w :- World, r :- RunRow,
         ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat]
  (=> (h9-entry xm w r ds mode st fresh)
      (= (h3 xm (h10-fill-prefix (:next-id w) ds
                  (await-acc w r ds mode k mine) (nat-distinct ds))) true))
  (intro ent)
  (have restored := (h10-fill-prefix-h3 xm w r ds mode k mine st fresh (nat-distinct ds) (List.nil Nat) ent (h9-app-nil _)))
  (exact restored))

(a/theorem h10-park-h3 [xm :- (List Nat), w :- World, r :- RunRow,
         ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat]
  (=> (h9-entry xm w r ds mode st fresh)
      (= (h3 xm
           (park-if
             (h10-fill-prefix (:next-id w) ds
               (await-acc w r ds mode k mine) (nat-distinct ds))
             (:next-id w) (:id r))) true))
  (intro ent)
  (have restored := (h10-fast-fill-h3 xm w r ds mode k mine st fresh ent))
  (cases present (act-has (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) (nat-distinct ds)) (:next-id w)))
  (case [false] (simp only [park-if present]) (exact restored))
  (case [true]
    (simp only [park-if present])
    (exact (h3-run-upd-m xm _ (:id r) run-park-row run-park-row-id
             (fn [q :- RunRow] (Eq.refl (:of q))) (fn [q :- RunRow] (Eq.refl (:epoch q)))
             (fn [q :- RunRow, alive :- (= (run-alive q) true)] (Eq.refl true)) restored))))
