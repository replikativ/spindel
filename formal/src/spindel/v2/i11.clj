(ns spindel.v2.i11
  "I11a (every row is the root scope or the world record, reached by §3.2 from an obligation, a
  cleanup row, admitted by §3.4, or a finalizer ref of a reached run) through the step,
  kernel-checked (Init only).

  Bundle gw = inv-sample and: id 2 is the root scope's (a scope of kind root or with id 2 is the
  root scope with parent 0), no run scope is 2, the allocator is above 2, there are no fork markers
  (layer 1 creates none). Copied over the raw transition and normalization (`lcopy!`); overrides:
  run creation (`add-run-scope`: the new scope is next-id + 1) and detach (the re-parented scope is
  a run's scope, not 2).
  Reach: from the roots, every node is the root scope or reached from the obligations
  (`reach-roots-obl`): the other roots are obligations (pins, observe edges, open explicit scopes,
  pending activation, armed publications with handles), and the root scope's successors are the
  running tasks it owns (reached from their alive run: K.run names a run of K, from i10's g10r)
  and its fork markers (none). With I3 (`step-i3-total`: the filter keeps only live, cleanup,
  admitted and stored rows) every row is `obl-ok` (`i11a-of`); obl-reach converges with its fuel
  (`obl-converged`).
  Theorems: step-gw, i11a-of, p3d = p3c && gw && inv-i11a with step-p3d, p3d-empty and
  step-i11a-total (no honest hypothesis)."
  (:require [ansatz.core :as a]
            [clojure.string :as str]
            [spindel.v2.state :refer :all]
            [spindel.v2.edits :refer :all]
            [spindel.v2.reach :refer :all]
            [spindel.v2.retain :refer :all]
            [spindel.v2.step :refer :all]
            [spindel.v2.rule :refer :all]
            [spindel.v2.engine :refer :all]
            [spindel.v2.rank :refer :all]
            [spindel.v2.casc :refer :all]
            [spindel.v2.acts :refer :all]
            [spindel.v2.inv :refer :all]
            [spindel.v2.lit :refer :all]
            [spindel.v2.idle :refer :all]
            [spindel.v2.p3 :refer :all]
            [spindel.v2.i10 :refer :all]))

;; ===========================================================================
;; Part A. The bundle gw: id 2 is the root scope's (kind root -> id 2, parent 0), no run scope
;; is 2, the allocator is above 2, no fork markers (layer 1 creates none)
;; ===========================================================================

(a/structure SKW [] (id Nat) (kind Nat) (parent Nat))
(a/defn skw [s :- ScopeRow] SKW (SKW.mk (:id s) (:kind s) (:parent s)))
(a/defn skw-id [k :- SKW] Nat (:id k))
(a/defn skws [ss :- (List ScopeRow)] (List SKW)
  (match ss [nil (List.nil SKW)] [(cons h t) (List.cons SKW (skw h) (skws t))]))
(a/defn rscs [rs :- (List RunRow)] (List Nat)
  (match rs [nil (List.nil Nat)] [(cons h t) (List.cons Nat (:scope h) (rscs t))]))
(a/defn forks-nil [fs :- (List ForkRow)] Bool (match fs [nil true] [(cons h t) false]))
(a/defn root-ok [k :- SKW] Bool
  (Bool.or (Bool.not (Bool.or (Nat.beq (:kind k) scope-root) (Nat.beq (:id k) 2)))
           (Bool.and (Nat.beq (:id k) 2) (Bool.and (Nat.beq (:kind k) scope-root) (Nat.beq (:parent k) 0)))))
(a/defn ne2 [x :- Nat] Bool (Bool.not (Nat.beq x 2)))
(a/defn gwk [sks :- (List SKW), rss :- (List Nat), fs :- (List ForkRow), n :- Nat] Bool
  (Bool.and (tbl-all root-ok sks) (Bool.and (tbl-all ne2 rss) (Bool.and (forks-nil fs) (Nat.blt 2 n)))))
(a/defn gw-rest [w :- World] Bool (gwk (skws (:scopes w)) (rscs (:runs w)) (:forks w) (:next-id w)))
(a/defn gw [w :- World] Bool (Bool.and (inv-sample w) (gw-rest w)))

(a/theorem gw-sample [w :- World] (=> (= (gw w) true) (= (inv-sample w) true))
  (intro h) (simp only [gw Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem gw-rest-of [w :- World] (=> (= (gw w) true) (= (gw-rest w) true))
  (intro h) (simp only [gw Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem gw-intro [w :- World] (=> (= (inv-sample w) true) (= (gw-rest w) true) (= (gw w) true))
  (intros h1 h2) (simp only [gw h1 h2 Bool.and_self]))
(a/theorem gw-parts [w :- World]
  (=> (= (gw w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (gw-sample w h))))

(a/structure KWW [] (sks (List SKW)) (rss (List Nat)) (fs (List ForkRow)) (n Nat))
(a/defn kww [w :- World] KWW (KWW.mk (skws (:scopes w)) (rscs (:runs w)) (:forks w) (:next-id w)))
(a/theorem gw-rest-kw [w :- World, w2 :- World] (=> (= (kww w2) (kww w)) (= (gw-rest w2) (gw-rest w)))
  (intro e)
  (have e1 (= (skws (:scopes w2)) (skws (:scopes w)))) (exact (congrArg (fn [k :- KWW] (:sks k)) e))
  (have e2 (= (rscs (:runs w2)) (rscs (:runs w)))) (exact (congrArg (fn [k :- KWW] (:rss k)) e))
  (have e3 (= (:forks w2) (:forks w))) (exact (congrArg (fn [k :- KWW] (:fs k)) e))
  (have e4 (= (:next-id w2) (:next-id w))) (exact (congrArg (fn [k :- KWW] (:n k)) e))
  (simp only [gw-rest e1 e2 e3 e4]))

(a/theorem skws-same [x :- Nat, f :- (=> ScopeRow ScopeRow), hk :- (forall [s :- ScopeRow] (= (skw (f s)) (skw s))), ss :- (List ScopeRow)]
  (= (skws (tbl-upd scope-id x f ss)) (skws ss))
  (induction ss)
  (case [nil] (simp only [tbl-upd skws]))
  (case [cons h t ih] (cases hx (Nat.beq (scope-id h) x)) (all_goals (simp only [tbl-upd hx skws ih (hk h)]))))
(a/theorem rscs-same [x :- Nat, f :- (=> RunRow RunRow), hk :- (forall [r :- RunRow] (= (:scope (f r)) (:scope r))), rs :- (List RunRow)]
  (= (rscs (tbl-upd run-id x f rs)) (rscs rs))
  (induction rs)
  (case [nil] (simp only [tbl-upd rscs]))
  (case [cons h t ih] (cases hx (Nat.beq (run-id h) x)) (all_goals (simp only [tbl-upd hx rscs ih (hk h)]))))

(a/theorem gw-run-upd [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                       hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                       hk :- (forall [r :- RunRow] (= (:scope (f r)) (:scope r)))]
  (=> (= (gw w) true) (= (gw (run-upd w x f)) true))
  (intro h)
  (have e (= (kww (run-upd w x f)) (kww w))) (simp only [kww run-upd set-runs (rscs-same x f hk (:runs w))])
  (exact (gw-intro _ (inv-run-upd w x f hf (gw-sample w h)) (Eq.trans (gw-rest-kw w _ e) (gw-rest-of w h)))))
(a/theorem gw-scope-upd [w :- World, x :- Nat, f :- (=> ScopeRow ScopeRow),
                         hf :- (forall [s :- ScopeRow] (= (scope-id (f s)) (scope-id s))),
                         hk :- (forall [s :- ScopeRow] (= (skw (f s)) (skw s)))]
  (=> (= (gw w) true) (= (gw (scope-upd w x f)) true))
  (intro h)
  (have e (= (kww (scope-upd w x f)) (kww w))) (simp only [kww scope-upd set-scopes (skws-same x f hk (:scopes w))])
  (exact (gw-intro _ (inv-scope-upd w x f hf (gw-sample w h)) (Eq.trans (gw-rest-kw w _ e) (gw-rest-of w h)))))

;; ---- deletions, the allocator, insertions

(a/theorem skws-del [x :- Nat, ss :- (List ScopeRow)] (= (skws (tbl-del scope-id x ss)) (tbl-del skw-id x (skws ss)))
  (induction ss)
  (case [nil] (simp only [tbl-del skws]))
  (case [cons h t ih]
    (have e (= (Nat.beq (skw-id (skw h)) x) (Nat.beq (scope-id h) x))) (rfl)
    (cases hx (Nat.beq (scope-id h) x)) (all_goals (simp only [tbl-del hx skws e ih]))))
(a/defn rsc-of [r :- RunRow] Nat (:scope r))
(a/theorem all-rscs [P :- (=> Nat Bool), rs :- (List RunRow)] (= (tbl-all P (rscs rs)) (tbl-all (fn [r :- RunRow] (P (:scope r))) rs))
  (induction rs) (case [nil] (simp only [rscs tbl-all])) (case [cons h t ih] (simp only [rscs tbl-all ih])))
(a/theorem all-skws [P :- (=> SKW Bool), ss :- (List ScopeRow)] (= (tbl-all P (skws ss)) (tbl-all (fn [s :- ScopeRow] (P (skw s))) ss))
  (induction ss) (case [nil] (simp only [skws tbl-all])) (case [cons h t ih] (simp only [skws tbl-all ih])))

(a/theorem gw-rest-run-del [w :- World, x :- Nat] (=> (= (gw-rest w) true) (= (gw-rest (run-del w x)) true))
  (intro h)
  (simp only [gw-rest gwk Bool.and_eq_true] at h)
  (have a1 (= (tbl-all ne2 (rscs (tbl-del run-id x (:runs w)))) true))
  (rw [all-rscs]) (have a0 := (And.left (And.right h))) (rw [all-rscs] at a0)
  (exact (tbl-all-del RunRow run-id x _ _ (fn [r :- RunRow, p :- (= (ne2 (:scope r)) true), q :- (= (Nat.beq (run-id r) x) false)] p) _ a0))
  (simp only [gw-rest gwk run-del set-runs a1 (And.left h) (And.right (And.right h)) Bool.and_self]))
(a/theorem gw-rest-scope-del [w :- World, x :- Nat] (=> (= (gw-rest w) true) (= (gw-rest (scope-del w x)) true))
  (intro h)
  (simp only [gw-rest gwk Bool.and_eq_true] at h)
  (have a1 (= (tbl-all root-ok (skws (tbl-del scope-id x (:scopes w)))) true))
  (rw [skws-del])
  (exact (tbl-all-del SKW skw-id x _ _ (fn [k :- SKW, p :- (= (root-ok k) true), q :- (= (Nat.beq (skw-id k) x) false)] p) _ (And.left h)))
  (simp only [gw-rest gwk scope-del set-scopes a1 (And.right h) Bool.and_self]))
(a/theorem gw-rest-filter [w :- World, K :- (=> Nat Bool)] (=> (= (gw-rest w) true) (= (gw-rest (filter-world K w)) true))
  (intro h)
  (simp only [gw-rest gwk Bool.and_eq_true] at h)
  (have a1 (= (tbl-all root-ok (skws (tbl-keep K scope-id (:scopes w)))) true))
  (rw [all-skws]) (have a0 := (And.left h)) (rw [all-skws] at a0) (exact (tbl-all-keep-same ScopeRow K scope-id _ _ a0))
  (have a2 (= (tbl-all ne2 (rscs (tbl-keep K run-id (:runs w)))) true))
  (rw [all-rscs]) (have a0 := (And.left (And.right h))) (rw [all-rscs] at a0) (exact (tbl-all-keep-same RunRow K run-id _ _ a0))
  (have f0 := (And.left (And.right (And.right h))))
  (have a3 (= (forks-nil (tbl-keep K fork-id (:forks w))) true))
  (cases hf (:forks w))
  (case [nil] (simp only [tbl-keep forks-nil]))
  (case [cons fh ft] (rw [hf] at f0) (simp [forks-nil] at f0))
  (simp only [gw-rest gwk filter-world a1 a2 a3 (And.right (And.right (And.right h))) Bool.and_self]))
(a/theorem gw-rest-next [w :- World, v :- Nat]
  (=> (= (gw-rest w) true) (<= (:next-id w) v) (= (gw-rest (set-next-id w v)) true))
  (intros h hv)
  (simp only [gw-rest gwk Bool.and_eq_true Nat.blt_eq] at h)
  (have b (= (Nat.blt 2 v) true)) (simp only [Nat.blt_eq]) (have z := (And.right (And.right (And.right h)))) (omega)
  (have e1 (= (:scopes (set-next-id w v)) (:scopes w))) (rfl)
  (have e2 (= (:runs (set-next-id w v)) (:runs w))) (rfl)
  (have e3 (= (:forks (set-next-id w v)) (:forks w))) (rfl)
  (have e4 (= (:next-id (set-next-id w v)) v)) (rfl)
  (simp only [gw-rest gwk e1 e2 e3 e4 b (And.left h) (And.left (And.right h)) (And.left (And.right (And.right h))) Bool.and_self]))
(a/theorem gw-rest-bump [w :- World] (=> (= (gw-rest w) true) (= (gw-rest (bump w)) true))
  (intro h) (simp only [bump]) (exact (gw-rest-next w (+ (:next-id w) 1) h (Nat.le_succ (:next-id w)))))

;; a new scope that is not of kind root (run and explicit scopes)
(a/theorem gw-scope-ins-fresh [w :- World, r :- ScopeRow, hk :- (= (Nat.beq (:kind r) scope-root) false)]
  (=> (= (scope-id r) (:next-id w)) (= (gw w) true) (= (gw (bump (scope-ins w r))) true))
  (intros hr h)
  (have h0 := (gw-rest-of w h)) (simp only [gw-rest gwk Bool.and_eq_true] at h0)
  (have hi (= (Nat.beq (:id r) 2) false))
  (cases hb (Nat.beq (:id r) 2)) (rfl) (have z := (Nat.eq_of_beq_eq_true hb)) (have z2 := (And.right (And.right (And.right h0))))
  (simp only [Nat.blt_eq] at z2) (have z3 (= (:id r) (:next-id w))) (exact hr) (omega)
  (have ro (= (root-ok (skw r)) true)) (simp only [root-ok skw hk hi Bool.or_false Bool.not_false Bool.true_or])
  (have hrest (= (gw-rest (scope-ins w r)) true))
  (simp only [gw-rest gwk scope-ins set-scopes tbl-ins skws tbl-all ro (And.left h0) (And.right h0) Bool.and_self Bool.true_and])
  (exact (gw-intro _ (inv-scope-ins-fresh w r hr (gw-sample w h)) (gw-rest-bump _ hrest))))

;; ===========================================================================
;; Part B. The copy
;; ===========================================================================

(def GW (mk-bundle 'gw [] "gw-"
          {'inv-run-upd ['(fn [r :- RunRow] (Eq.refl (:scope r))) 4]
           'inv-scope-upd ['(fn [s :- ScopeRow] (Eq.refl (skw s))) 4]
           'inv-scope-ins-fresh ['(Eq.refl false) 2]}))
(swap! (:renames GW) assoc 'inv-parts 'gw-parts 'inv-run-upd 'gw-run-upd 'inv-scope-upd 'gw-scope-upd 'inv-scope-ins-fresh 'gw-scope-ins-fresh)
(doseq [o '[inv-pub-upd inv-source-upd inv-resource-upd inv-cleanup-upd inv-cleanup-del inv-task-upd inv-comp-upd
            inv-set-pins inv-resource-del inv-cleanup-ins inv-act-upd inv-edge-upd inv-drop-cred inv-drop-edges inv-drop-act
            inv-comp-del-unref]]
  (prim! GW o nil))
(a/theorem gw-rest-mark-edge [w :- World, x :- Nat] (= (gw-rest (mark-edge w x)) (gw-rest w))
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [mark-edge hf hm]))))
(a/theorem gw-rest-unmark-edge [w :- World, x :- Nat] (= (gw-rest (unmark-edge w x)) (gw-rest w))
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [unmark-edge hf hm]))))
(a/theorem gw-rest-remove-edge [w :- World, x :- Nat] (= (gw-rest (remove-edge w x)) (gw-rest w))
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [remove-edge hf hm]))))
(prim! GW 'mark-edge-inv-sample '(Eq.trans (gw-rest-mark-edge w x) R))
(prim! GW 'unmark-edge-inv-sample '(Eq.trans (gw-rest-unmark-edge w x) R))
(prim! GW 'inv-remove-edge '(Eq.trans (gw-rest-remove-edge w x) R))
(doseq [o '[inv-source-ins-fresh inv-resource-ins-fresh inv-act-ins-fresh inv-comp-ins-fresh inv-task-ins-fresh]]
  (prim! GW o (list 'gw-rest-bump (list (symbol (str/replace (subs (name o) 4) "-fresh" "")) 'w 'r) (list 'Eq.trans '(rfl) 'R))))
(prim! GW 'inv-bump '(gw-rest-bump w R))
(prim! GW 'insert-edge-fresh-inv-sample '(gw-rest-bump (insert-edge w (edge-set-id (:next-id w) e)) (Eq.trans (rfl) R)))
(prim! GW 'inv-run-del '(gw-rest-run-del w x R))
(prim! GW 'inv-scope-del '(gw-rest-scope-del w x R))
(prim! GW 'inv-filter-world '(gw-rest-filter w K R))

;; T4/T5/T11: the new run's scope is next-id + 1 (> 2), a run scope
(a/theorem gw-add-run-scope-o [w :- World, of :- Nat, epoch :- Nat, parent :- Nat, ei :- Nat]
  (=> (= (gw w) true) (= (gw (add-run-scope w of epoch parent ei)) true))
  (intro h)
  (have hs := (gw-sample w h))
  (have h0 := (gw-rest-of w h)) (simp only [gw-rest gwk Bool.and_eq_true Nat.blt_eq] at h0)
  (have b (= (ne2 (+ (:next-id w) 1)) true))
  (simp only [ne2]) (cases hb (Nat.beq (+ (:next-id w) 1) 2)) (rfl) (have z := (Nat.eq_of_beq_eq_true hb)) (have z2 := (And.right (And.right (And.right h0)))) (omega)
  (have h1 (= (gw (bump (run-ins w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei)))) true))
  (have r1 (= (gw-rest (run-ins w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei))) true))
  (simp only [gw-rest gwk run-ins set-runs tbl-ins rscs new-run-row tbl-all b (And.left h0) (And.left (And.right h0))
              (And.left (And.right (And.right h0))) Bool.and_self Bool.true_and])
  (have z2 := (And.right (And.right (And.right h0)))) (simp only [Nat.blt_eq]) (exact z2)
  (exact (gw-intro _ (inv-run-ins-fresh w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei) (rfl) hs) (gw-rest-bump _ r1)))
  (simp only [add-run-scope])
  (have he (= (scope-id (new-scope-row (+ (:next-id w) 1) parent)) (:next-id (bump (run-ins w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei)))))) (rfl)
  (exact (gw-scope-ins-fresh _ (new-scope-row (+ (:next-id w) 1) parent) (Eq.refl false) he h1)))
(override! GW 'inv-add-run-scope '[]
  '(a/theorem gw-add-run-scope [w :- World, of :- Nat, epoch :- Nat, parent :- Nat, ei :- Nat]
     (=> (= (gw w) true) (= (gw (add-run-scope w of epoch parent ei)) true))
     (intro h) (exact (gw-add-run-scope-o w of epoch parent ei h))))

;; detach: the task's run scope (a run's scope: not 2) gets the new parent
(a/theorem gw-set-parent [w :- World, x :- Nat, p :- Nat]
  (=> (= (Nat.beq x 2) false) (= (gw w) true) (= (gw (scope-upd w x (scope-set-parent p))) true))
  (intros hx h)
  (have hs := (gw-sample w h))
  (have h0 := (gw-rest-of w h)) (simp only [gw-rest gwk Bool.and_eq_true] at h0)
  (have a1 (= (tbl-all root-ok (skws (tbl-upd scope-id x (scope-set-parent p) (:scopes w)))) true))
  (rw [all-skws]) (have a0 := (And.left h0)) (rw [all-skws] at a0)
  (apply (tbl-all-upd ScopeRow scope-id x (scope-set-parent p) _ _ _ _ _ a0))
  (intros s q e)
  (have e2 (= (:id s) x)) (exact (Nat.eq_of_beq_eq_true e))
  (simp only [root-ok skw Bool.or_eq_true Bool.and_eq_true] at q)
  (simp only [root-ok skw scope-set-parent Bool.or_eq_true Bool.and_eq_true])
  (cases q)
  (case [inl a] (exact (Or.inl a)))
  (case [inr b] (have z := (And.left b)) (rw [e2 hx] at z) (cases z))
  (intros s q e) (exact q)
  (have hrest (= (gw-rest (scope-upd w x (scope-set-parent p))) true))
  (simp only [gw-rest gwk scope-upd set-scopes a1 (And.right h0) Bool.and_self Bool.true_and])
  (exact (gw-intro _ (inv-scope-upd w x (scope-set-parent p) (scope-set-parent-id p) hs) hrest)))

(a/theorem trs-ne2 [w :- World, t :- TaskRow] (=> (= (gw w) true) (= (Nat.beq (task-run-scope w t) 2) false))
  (intro h)
  (cases hf (run-find w (:run t)))
  (case [none] (simp only [task-run-scope hf]))
  (case [some r]
    (simp only [task-run-scope hf])
    (have h0 := (gw-rest-of w h)) (simp only [gw-rest gwk Bool.and_eq_true] at h0)
    (have a0 := (And.left (And.right h0))) (rw [all-rscs] at a0)
    (have q := (tbl-all-mem RunRow _ r _ a0 (tbl-find-mem RunRow run-id (:run t) r (:runs w) hf)))
    (simp only [ne2] at q) (exact (bnot-true _ q))))

(lcopy! GW 'inv-remove-if-empty)
(override! GW 't-detach-inv '[inv-remove-if-empty]
  '(a/theorem t-detach-gw [w :- World, k :- Nat, s :- Nat]
     (=> (= (gw w) true) (= (gw (:world (t-detach w k s))) true))
     (intro h)
     (cases hf (task-find w k))
     (case [none] (simp only [t-detach hf refuse]) (exact h))
     (case [some t]
       (cases hg (detach-ok w t s))
       (case [false] (simp only [t-detach hf hg refuse]) (exact h))
       (case [true]
         (simp only [t-detach hf hg accept remove-empty-at detach-move])
         (have h1 := (gw-task-upd w k (task-set-owner s) (task-set-owner-id s) h))
         (have hne (= (Nat.beq (task-run-scope w t) 2) false)) (exact (trs-ne2 w t h))
         (exact (gw-remove-if-empty _ _ (gw-set-parent _ (task-run-scope w t) s hne h1)))))))

(lcopy! GW 'raw-inv)
(lcopy! GW 'inv-normalize)

(a/theorem gw-rule-r-round [w :- World]
  (=> (= (gw w) true) (= (filter-safe (normalize w)) true) (= (gw (rule-r-round w)) true))
  (intros h hf) (simp only [rule-r-round]) (rw [rule-r-filter-eq])
  (exact (gw-filter-world (normalize w) (keep-fn (normalize w)) (gw-normalize w h) hf)))
(a/theorem gw-rr-loop [fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (gw w0) true) (= (rr-safe fuel w0) true) (= (gw (rr-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 h hs) (simp only [rr-safe] at hs) (simp only [rr-loop]) (exact (gw-rule-r-round w0 h hs)))
  (case [cons x f ih]
    (intros w0 h hs)
    (simp only [rr-safe Bool.and_eq_true] at hs)
    (have h1 := (gw-rule-r-round w0 h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false] (simp only [ho] at hs) (simp only [rr-loop ho]) (exact (ih (rule-r-round w0) h1 (And.right hs))))
    (case [true] (simp only [rr-loop ho]) (exact h1))))
(a/theorem gw-rule-r [w :- World] (=> (= (gw w) true) (= (rule-r-safe w) true) (= (gw (rule-r w)) true))
  (intros h hs) (simp only [rule-r-safe] at hs) (simp only [rule-r]) (exact (gw-rr-loop (rr-fuel w) w h hs)))
(a/theorem step-gw [w :- World, it :- Item]
  (=> (= (gw w) true) (= (rule-r-safe (:world (raw w it))) true) (= (gw (:world (world-step w it))) true))
  (intros h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true] (have e2 := (step-accepted w it ha)) (rw [e2]) (exact (gw-rule-r (:world (raw w it)) (raw-gw w it h) hs))))
(a/theorem gw-empty [] (= (gw empty-world) true) (rfl))

;; ===========================================================================
;; Part C. Reach from the roots is the root scope (id 2) or reach from the obligations
;; ===========================================================================

(a/theorem obl-converged [w :- World] (= (:converged (obl-reach w)) true)
  (simp only [obl-reach])
  (apply (reach-run-l-conv _ (retain-succ w) (obligations w) (all-ids w) (retain-succ-absent w)))
  (simp only [List.length list-length-append succ-all-length])
  (omega))

(a/theorem obl-iff [w :- World, x :- Nat]
  (Iff (= (reach-mem x (:visited (obl-reach w))) true) (Reach (retain-succ w) (obligations w) x))
  (have e := (reach-run-l-eq (List.cons Nat 0 (List.append Nat (obligations w) (succ-all w (all-ids w)))) (retain-succ w) (obligations w)))
  (have hc (= (ReachResult.converged (reach-run (List.length (List.cons Nat 0 (List.append Nat (obligations w) (succ-all w (all-ids w)))))
                                                 (retain-succ w) (obligations w))) true))
  (rw [← e]) (exact (obl-converged w))
  (have h := (reach-run-iff _ (retain-succ w) (obligations w) x hc))
  (rw [← e] at h)
  (simp only [obl-reach])
  (exact h))

(a/theorem scan-prop [A :- Type, idf :- (=> A Nat), p :- (=> A Bool), Q :- (=> Nat Prop), xs :- (List A),
                      h :- (forall [a :- A] (=> (List.Mem a xs) (= (p a) true) (Q (idf a)))), y :- Nat]
  (=> (= (reach-mem y (tbl-scan idf p xs)) true) (Q y))
  (induction xs)
  (case [nil] (intro hm) (simp [tbl-scan reach-mem] at hm))
  (case [cons hd t ih]
    (intro hm)
    (have ht (forall [a :- A] (=> (List.Mem a t) (= (p a) true) (Q (idf a)))))
    (intros a m pa) (exact (h a (List.Mem.tail hd m) pa))
    (cases hp (p hd))
    (case [false] (simp only [tbl-scan hp] at hm) (exact (ih ht hm)))
    (case [true]
      (simp only [tbl-scan hp reach-mem-cons Bool.or_eq_true] at hm)
      (cases hm)
      (case [inl a] (have e := (Nat.eq_of_beq_eq_true a)) (rw [e]) (exact (h hd (List.Mem.head t) hp)))
      (case [inr b] (exact (ih ht b))))))

(a/theorem gather-prop [A :- Type, p :- (=> A Bool), f :- (=> A (List Nat)), Q :- (=> Nat Prop), xs :- (List A),
                        h :- (forall [a :- A, z :- Nat] (=> (List.Mem a xs) (= (p a) true) (= (reach-mem z (f a)) true) (Q z))), y :- Nat]
  (=> (= (reach-mem y (tbl-gather p f xs)) true) (Q y))
  (induction xs)
  (case [nil] (intro hm) (simp [tbl-gather reach-mem] at hm))
  (case [cons hd t ih]
    (intro hm)
    (have ht (forall [a :- A, z :- Nat] (=> (List.Mem a t) (= (p a) true) (= (reach-mem z (f a)) true) (Q z))))
    (intros a z m pa hz) (exact (h a z (List.Mem.tail hd m) pa hz))
    (cases hp (p hd))
    (case [false] (simp only [tbl-gather hp] at hm) (exact (ih ht hm)))
    (case [true]
      (simp only [tbl-gather hp reach-mem-append Bool.or_eq_true] at hm)
      (cases hm)
      (case [inl a] (exact (h hd y (List.Mem.head t) hp a)))
      (case [inr b] (exact (ih ht b))))))

(a/theorem scan-mono [A :- Type, idf :- (=> A Nat), p :- (=> A Bool), q :- (=> A Bool), xs :- (List A),
                      h :- (forall [a :- A] (=> (= (p a) true) (= (q a) true))), y :- Nat]
  (=> (= (reach-mem y (tbl-scan idf p xs)) true) (= (reach-mem y (tbl-scan idf q xs)) true))
  (induction xs)
  (case [nil] (intro hm) (simp [tbl-scan reach-mem] at hm))
  (case [cons hd t ih]
    (intro hm)
    (cases hp (p hd))
    (case [false]
      (simp only [tbl-scan hp] at hm)
      (cases hq (q hd))
      (case [false] (simp only [tbl-scan hq]) (exact (ih hm)))
      (case [true] (simp only [tbl-scan hq reach-mem-cons (ih hm) Bool.or_true])))
    (case [true]
      (simp only [tbl-scan hp] at hm)
      (simp only [tbl-scan (h hd hp)])
      (simp only [reach-mem-cons Bool.or_eq_true] at hm) (simp only [reach-mem-cons Bool.or_eq_true])
      (cases hm) (case [inl a] (exact (Or.inl a))) (case [inr b] (exact (Or.inr (ih b)))))))

(a/theorem armed-handles [w :- World, p :- PubRow] (=> (= (armed-pub w p) true) (= (Nat.blt 0 (:handles p)) true))
  (intro h) (simp only [armed-pub Bool.and_eq_true] at h) (exact (And.left h)))
;; a root is the root scope or an obligation
(a/defn is2 [w :- World, y :- Nat] Prop (And (= y 2) (= (scope-has w 2) true)))
(a/theorem root-cases [w :- World, y :- Nat]
  (=> (= (gw w) true) (= (reach-mem y (roots w)) true) (Or (is2 w y) (= (reach-mem y (obligations w)) true)))
  (intros h hm)
  (have h0 := (gw-rest-of w h)) (simp only [gw-rest gwk Bool.and_eq_true] at h0)
  (have ro := (And.left h0)) (rw [all-skws] at ro)
  (simp only [roots reach-mem-append Bool.or_eq_true] at hm)
  (have ob (forall [z :- Nat] (=> (= (reach-mem z (obligations w)) true) (Or (is2 w y) (= (reach-mem z (obligations w)) true)))))
  (intros z hz) (exact (Or.inr hz))
  (cases hm)
  (case [inl a]
      (apply Or.inl)
      (apply (scan-prop ScopeRow scope-id is-root-scope (is2 w) (:scopes w) _ y a))
      (intros s m p)
      (have q := (tbl-all-mem ScopeRow _ s _ ro m))
      (simp only [root-ok skw] at q)
      (simp only [is-root-scope] at p)
      (simp only [p Bool.true_or Bool.not_true Bool.false_or Bool.and_eq_true] at q)
      (have e (= (scope-id s) 2)) (exact (Nat.eq_of_beq_eq_true (And.left q)))
      (have hh (= (scope-has w 2) true)) (rw [← e]) (have hm2 := (mem-ids-has ScopeRow scope-id s (:scopes w) m)) (rw [nat-mem-ids] at hm2) (exact hm2)
      (exact (And.intro e hh)))
  (case [inr b]
    (apply Or.inr)
    (simp only [obligations handled-ids reach-mem-nat-app Bool.or_eq_true])
    (cases b)
    (case [inl a] (exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl a)))))))
    (case [inr b]
      (cases b)
      (case [inl a] (exact (Or.inr (Or.inr (Or.inr (Or.inl a))))))
      (case [inr b]
        (cases b)
        (case [inl a] (exact (Or.inl a)))
        (case [inr b]
          (cases b)
          (case [inl a] (exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl a)))))))))
          (case [inr a]
            (have a2 := (scan-mono PubRow pub-id (armed-pub w) (fn [p :- PubRow] (Nat.blt 0 (:handles p))) (:pubs w)
                          (fn [p :- PubRow, q :- (= (armed-pub w p) true)] (armed-handles w p q)) y a))
            (exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr a2))))))))))))))))

;; ---- the root scope's successors are reached from the obligations

(a/theorem gather-has [A :- Type, idf :- (=> A Nat), x :- Nat, f :- (=> A (List Nat)), xs :- (List A), y :- Nat]
  (=> (= (reach-mem y (tbl-gather (id-is idf x) f xs)) true) (= (tbl-has idf x xs) true))
  (intro h)
  (apply (gather-prop A (id-is idf x) f (fn [z :- Nat] (= (tbl-has idf x xs) true)) xs _ y h))
  (intros a z m p hz)
  (have e (= (idf a) x)) (simp only [id-is] at p) (exact (Nat.eq_of_beq_eq_true p))
  (have hm := (mem-ids-has A idf a xs m)) (rw [nat-mem-ids e] at hm) (exact hm))

(a/theorem only2 [w :- World]
  (=> (= (inv-sample w) true) (= (scope-has w 2) true)
      (= (Bool.or (tbl-has comp-id 2 (:comps w)) (Bool.or (tbl-has task-id 2 (:tasks w)) (Bool.or (tbl-has run-id 2 (:runs w))
          (Bool.or (tbl-has act-id 2 (:acts w)) (Bool.or (tbl-has edge-id 2 (:edges w)) (tbl-has pub-id 2 (:pubs w))))))) false))
  (intros hs hh)
  (have u := (ids-unique-of w hs))
  (simp only [all-ids] at u)
  (have hm (= (nat-mem 2 (tbl-ids scope-id (:scopes w))) true)) (rw [nat-mem-ids]) (exact hh)
  (have d := (nodup-app-disj 2 _ _ u hm))
  (simp only [nat-mem-app Bool.or_eq_false_iff nat-mem-ids] at d)
  (simp only [Bool.or_eq_false_iff])
  (exact (And.intro (And.left d) (And.intro (And.left (And.right d)) (And.intro (And.left (And.right (And.right d)))
           (And.intro (And.left (And.right (And.right (And.right (And.right (And.right d))))))
             (And.intro (And.left (And.right (And.right (And.right (And.right d)))))
                        (And.left (And.right (And.right (And.right (And.right (And.right (And.right (And.right d)))))))))))))))

(a/theorem task-id-pos [w :- World, t :- TaskRow]
  (=> (= (inv-sample w) true) (List.Mem t (:tasks w)) (= (Nat.beq (:id t) 0) false))
  (intros hs m)
  (have hb := (ids-below-of w hs))
  (simp only [all-ids tbl-all-nat-app Bool.and_eq_true] at hb)
  (have h1 := (And.left (And.right (And.right hb))))
  (rw [all-ids-map] at h1)
  (have q := (tbl-all-mem TaskRow _ t _ h1 m))
  (simp only [id-in-range task-id Bool.and_eq_true Nat.blt_eq] at q)
  (cases hb0 (Nat.beq (:id t) 0)) (rfl)
  (have e := (Nat.eq_of_beq_eq_true hb0)) (omega))

(a/theorem succ-of [w :- World, r :- RunRow]
  (=> (List.Mem r (:runs w)) (= (run-alive r) true) (= (Nat.beq (:of r) 0) false)
      (= (reach-mem (:of r) (retain-succ w (:id r))) true))
  (intros hr ha hz)
  (simp only [retain-succ])
  (apply rm-app-r) (apply rm-app-r) (apply rm-app-r) (apply rm-app-l)
  (apply (gather-mem RunRow (id-is run-id (:id r)) (run-contrib w) r (:of r) (:runs w) hr (Nat.beq_refl (:id r))))
  (simp only [run-contrib ha])
  (apply rm-app-r) (apply rm-app-l)
  (exact (rm-nz (:of r) hz)))

(a/theorem root-task [w :- World, t :- TaskRow]
  (=> (= (gw w) true) (= (g10r w) true) (List.Mem t (:tasks w)) (= (owned-running-task w 2 t) true)
      (Reach (retain-succ w) (obligations w) (:id t)))
  (intros h h10 mt p)
  (have hs := (gw-sample w h))
  (simp only [owned-running-task task-running Bool.and_eq_true] at p)
  (have hr0 := (bnot-true _ (And.left (And.right p))))
  (have po := (And.right (And.right p)))
  (cases hf (run-find w (:run t)))
  (case [none] (simp [opt-test hf] at po))
  (case [some r]
    (simp only [opt-test hf] at po)
    (have mr := (tbl-find-mem RunRow run-id (:run t) r (:runs w) hf))
    (have er (= (:id r) (:run t))) (exact (tbl-find-id RunRow run-id (:run t) r (:runs w) hf))
    (have tp := (g10-tof (List.nil Nat) (List.nil Nat) w r t h10 mr mt))
    (have hz (= (Nat.beq (:id r) 0) false)) (rw [er]) (exact hr0)
    (have hx (= (Nat.beq (:id r) (:run t)) true)) (rw [er]) (exact (Nat.beq_refl _))
    (simp only [tof-pair rk10 tk10 hz hx Bool.not_true Bool.false_or] at tp)
    (have eo := (Nat.eq_of_beq_eq_true tp))
    (have sm (= (reach-mem (:id r) (tbl-scan run-id run-alive (:runs w))) true)) (exact (scan-mem RunRow run-id run-alive r (:runs w) mr po))
    (have om (= (reach-mem (:id r) (obligations w)) true)) (simp only [obligations reach-mem-nat-app sm Bool.true_or Bool.or_true])
    (have ro (Reach (retain-succ w) (obligations w) (:id r))) (exact (Reach.root (:id r) (Iff.mp (reach-mem-iff (:id r) (obligations w)) om)))
    (have tz := (task-id-pos w t hs mt))
    (have oz (= (Nat.beq (:of r) 0) false)) (rw [eo]) (exact tz)
    (have sc := (succ-of w r mr po oz))
    (rw [eo] at sc)
    (exact (Reach.step (:id r) (:id t) ro (Iff.mp (reach-mem-iff (:id t) (retain-succ w (:id r))) sc)))))

(a/theorem root-scope-succ [w :- World, s :- ScopeRow, z :- Nat]
  (=> (= (gw w) true) (= (g10r w) true) (List.Mem s (:scopes w)) (= (id-is scope-id 2 s) true) (= (reach-mem z (scope-contrib w s)) true)
      (Reach (retain-succ w) (obligations w) z))
  (intros h h10 m p hz)
  (have h0 := (gw-rest-of w h)) (simp only [gw-rest gwk Bool.and_eq_true] at h0)
  (have ro := (And.left h0)) (rw [all-skws] at ro)
  (have fk := (And.left (And.right (And.right h0))))
  (have q := (tbl-all-mem ScopeRow _ s _ ro m))
  (have e (= (:id s) 2)) (have p2 := p) (simp only [id-is] at p2) (exact (Nat.eq_of_beq_eq_true p2))
  (have e2 (= (Nat.beq (:id (skw s)) 2) true)) (simp only [skw]) (rw [e])
  (simp only [root-ok e2 Bool.or_true Bool.not_true Bool.false_or Bool.and_eq_true] at q)
  (have ep (= (:parent s) 0)) (exact (Nat.eq_of_beq_eq_true (And.right (And.right q))))
  (simp only [scope-contrib ep e reach-mem-append Bool.or_eq_true] at hz)
  (cases hz)
  (case [inl c] (simp [nz reach-mem] at c))
  (case [inr c]
    (cases c)
    (case [inl d]
      (exact (scan-prop TaskRow task-id (owned-running-task w 2) (Reach (retain-succ w) (obligations w)) (:tasks w)
               (fn [t :- TaskRow, mt :- (List.Mem t (:tasks w)), pt :- (= (owned-running-task w 2 t) true)] (root-task w t h h10 mt pt)) z d)))
    (case [inr d]
      (cases hf (:forks w))
      (case [nil] (rw [hf] at d) (simp [tbl-scan reach-mem] at d))
      (case [cons fh ft] (rw [hf] at fk) (simp [forks-nil] at fk)))))

(a/theorem root-succ-other [w :- World, y :- Nat]
  (=> (= (inv-sample w) true) (= (scope-has w 2) true)
      (= (Bool.or (reach-mem y (tbl-gather (id-is comp-id 2) (comp-contrib w) (:comps w)))
         (Bool.or (reach-mem y (tbl-gather (id-is task-id 2) task-contrib (:tasks w)))
         (Bool.or (reach-mem y (tbl-gather (id-is run-id 2) (run-contrib w) (:runs w)))
         (Bool.or (reach-mem y (tbl-gather (id-is act-id 2) act-contrib (:acts w)))
         (Bool.or (reach-mem y (tbl-gather (id-is edge-id 2) edge-contrib (:edges w)))
                  (reach-mem y (tbl-gather (id-is pub-id 2) pub-contrib (:pubs w)))))))) false))
  (intros hs hh)
  (have o2 := (only2 w hs hh))
  (simp only [Bool.or_eq_false_iff] at o2)
  (have g1 (forall [A :- Type, idf :- (=> A Nat), f :- (=> A (List Nat)), xs :- (List A)]
             (=> (= (tbl-has idf 2 xs) false) (= (reach-mem y (tbl-gather (id-is idf 2) f xs)) false))))
  (intros A idf f xs hn)
  (cases hc (reach-mem y (tbl-gather (id-is idf 2) f xs))) (rfl)
  (have z := (gather-has A idf 2 f xs y hc)) (rw [z] at hn) (cases hn)
  (simp only [(g1 CompRow comp-id (comp-contrib w) (:comps w) (And.left o2))
              (g1 TaskRow task-id task-contrib (:tasks w) (And.left (And.right o2)))
              (g1 RunRow run-id (run-contrib w) (:runs w) (And.left (And.right (And.right o2))))
              (g1 ActRow act-id act-contrib (:acts w) (And.left (And.right (And.right (And.right o2)))))
              (g1 EdgeRow edge-id edge-contrib (:edges w) (And.left (And.right (And.right (And.right (And.right o2))))))
              (g1 PubRow pub-id pub-contrib (:pubs w) (And.right (And.right (And.right (And.right (And.right o2))))))
              Bool.or_self]))

(a/theorem root-succ [w :- World, y :- Nat]
  (=> (= (gw w) true) (= (g10r w) true) (= (scope-has w 2) true) (= (reach-mem y (retain-succ w 2)) true)
      (Reach (retain-succ w) (obligations w) y))
  (intros h h10 hh hm)
  (have hs := (gw-sample w h))
  (have oth := (root-succ-other w y hs hh))
  (simp only [retain-succ reach-mem-append] at hm)
  (cases hsc (reach-mem y (tbl-gather (id-is scope-id 2) (scope-contrib w) (:scopes w))))
  (case [true]
    (exact (gather-prop ScopeRow (id-is scope-id 2) (scope-contrib w) (Reach (retain-succ w) (obligations w)) (:scopes w)
             (fn [s :- ScopeRow, z :- Nat, m :- (List.Mem s (:scopes w)), p :- (= (id-is scope-id 2 s) true), hz :- (= (reach-mem z (scope-contrib w s)) true)]
               (root-scope-succ w s z h h10 m p hz))
             y hsc)))
  (case [false]
    (simp only [hsc Bool.false_or] at hm)
    (rw [hm] at oth) (cases oth)))

(a/theorem reach-roots-obl [w :- World, y :- Nat]
  (=> (= (gw w) true) (= (g10r w) true) (Reach (retain-succ w) (roots w) y)
      (Or (is2 w y) (Reach (retain-succ w) (obligations w) y)))
  (intros h h10 hr)
  (induction hr)
  (case [root r hm]
    (have q := (root-cases w r h (Iff.mpr (reach-mem-iff r (roots w)) hm)))
    (cases q)
    (case [inl a] (exact (Or.inl a)))
    (case [inr b] (exact (Or.inr (Reach.root r (Iff.mp (reach-mem-iff r (obligations w)) b))))))
  (case [step p q hp hq ihp]
    (cases ihp)
    (case [inl a]
      (have ep (= p 2)) (exact (And.left a))
      (have hh (= (scope-has w 2) true)) (exact (And.right a))
      (rw [ep] at hq)
      (exact (Or.inr (root-succ w q h h10 hh (Iff.mpr (reach-mem-iff q (retain-succ w 2)) hq)))))
    (case [inr b] (exact (Or.inr (Reach.step p q b hq))))))

;; ===========================================================================
;; Part D. I11a: every row the filter keeps is the root scope, admitted, or reached from the
;; obligations (directly, or as a finalizer ref of a reached run)
;; ===========================================================================

(a/theorem live-obl [w :- World, y :- Nat]
  (=> (= (gw w) true) (= (g10r w) true) (= (reach-mem y (live-list w)) true)
      (Or (is2 w y) (= (reach-mem y (:visited (obl-reach w))) true)))
  (intros h h10 hl)
  (have r := (Iff.mp (in-live-iff w y (live-converged-all w)) hl))
  (have q := (reach-roots-obl w y h h10 r))
  (cases q)
  (case [inl a] (exact (Or.inl a)))
  (case [inr b] (exact (Or.inr (Iff.mpr (obl-iff w y) b)))))

(a/theorem storage-obl [w :- World, y :- Nat]
  (=> (= (gw w) true) (= (g10r w) true) (= (reach-mem y (storage w)) true)
      (= (reach-mem y (storage-with w (:visited (obl-reach w)))) true))
  (intros h h10 hs)
  (have hsm := (gw-sample w h))
  (have sub (forall [yy :- Nat] (=> (= (reach-mem yy (storage-gather w (live-list w))) true)
                                    (= (reach-mem yy (storage-gather w (:visited (obl-reach w)))) true))))
  (intros yy hyy)
  (simp only [storage-gather] at hyy)
  (simp only [storage-gather])
  (apply (gather-prop RunRow (stored-run (live-list w)) run-refs
           (fn [z :- Nat] (= (reach-mem z (tbl-gather (stored-run (:visited (obl-reach w))) run-refs (:runs w))) true)) (:runs w) _ yy hyy))
  (intros r z m p hz)
  (simp only [stored-run] at p)
  (have q := (live-obl w (:id r) h h10 p))
  (cases q)
  (case [inl a]
    (have e (= (:id r) 2)) (exact (And.left a))
    (have o2 := (only2 w hsm (And.right a)))
    (simp only [Bool.or_eq_false_iff] at o2)
    (have hm := (mem-ids-has RunRow run-id r (:runs w) m)) (rw [nat-mem-ids] at hm)
    (have e2 (= (run-id r) 2)) (exact e)
    (rw [e2] at hm) (rw [hm] at o2) (simp at o2))
  (case [inr b]
    (exact (gather-mem RunRow (stored-run (:visited (obl-reach w))) run-refs r z (:runs w) m b hz)))
  (have hs2 (= (reach-mem y (anc-close w (storage-gather w (live-list w)))) true)) (exact hs)
  (exact (anc-close-mono w _ _ y sub hs2)))

(a/theorem cleanup-obl [w :- World, y :- Nat]
  (=> (= (reach-mem y (cleanup-rows w)) true) (= (reach-mem y (:visited (obl-reach w))) true))
  (intro hc)
  (have om (= (reach-mem y (obligations w)) true)) (simp only [obligations handled-ids reach-mem-nat-app hc Bool.or_true])
  (exact (Iff.mpr (obl-iff w y) (Reach.root y (Iff.mp (reach-mem-iff y (obligations w)) om)))))

(a/theorem obl-ok-of [w :- World, y :- Nat]
  (=> (= (gw w) true) (= (g10r w) true) (= (keep-fn w y) true) (= (obl-ok w (:visited (obl-reach w)) y) true))
  (intros h h10 hk)
  (simp only [keep-fn keep-with Bool.or_eq_true] at hk)
  (simp only [obl-ok Bool.or_eq_true])
  (cases hk)
  (case [inl a]
    (have q := (live-obl w y h h10 a))
    (cases q)
    (case [inl b] (have e (= y 2)) (exact (And.left b)) (rw [e]) (exact (Or.inl (Nat.beq_refl _))))
    (case [inr b] (exact (Or.inr (Or.inr (Or.inl b))))))
  (case [inr b]
    (cases b)
    (case [inl c] (exact (Or.inr (Or.inr (Or.inl (cleanup-obl w y c))))))
    (case [inr c]
      (cases c)
      (case [inl d] (exact (Or.inr (Or.inr (Or.inr (Or.inl d))))))
      (case [inr d] (exact (Or.inr (Or.inr (Or.inr (Or.inr (storage-obl w y h h10 d))))))))))

(a/theorem i11a-of [w :- World]
  (=> (= (gw w) true) (= (g10r w) true) (= (tbl-all (keep-fn w) (all-ids w)) true) (= (inv-i11a w) true))
  (intros h h10 hk)
  (have a1 := (tbl-all-mono Nat (keep-fn w) (obl-ok w (:visited (obl-reach w)))
                (fn [y :- Nat, q :- (= (keep-fn w y) true)] (obl-ok-of w y h h10 q)) (all-ids w) hk))
  (simp only [inv-i11a (obl-converged w) a1 Bool.and_self]))

;; ---- the combined bundle and the step

(a/defn p3d [w :- World] Bool (Bool.and (p3c w) (Bool.and (gw w) (inv-i11a w))))
(a/theorem p3d-parts [w :- World] (=> (= (p3d w) true) (And (= (p3c w) true) (And (= (gw w) true) (= (inv-i11a w) true))))
  (intro h) (simp only [p3d Bool.and_eq_true] at h) (exact h))
(a/theorem p3d-empty [] (= (p3d empty-world) true) (rfl))
(a/theorem step-p3d [w :- World, it :- Item] (=> (= (p3d w) true) (= (p3d (:world (world-step w it))) true))
  (intro h)
  (have p := (p3d-parts w h))
  (have pc := (p3c-parts w (And.left p)))
  (have a1 := (step-p3c w it (And.left p)))
  (have a2 := (step-gw w it (And.left (And.right p)) (step-rule-r-safe w it (And.left pc))))
  (have a3 (= (inv-i11a (:world (world-step w it))) true))
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact (And.right (And.right p))))
  (case [true] (exact (i11a-of _ a2 (And.right (p3c-parts _ a1)) (step-i3-total w it ha))))
  (simp only [p3d a1 a2 a3 Bool.and_self]))
(a/theorem step-i11a-total [w :- World, it :- Item] (=> (= (p3d w) true) (= (inv-i11a (:world (world-step w it))) true))
  (intro h) (exact (And.right (And.right (p3d-parts _ (step-p3d w it h))))))
