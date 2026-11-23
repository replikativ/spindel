(ns spindel.v2.inv.i11
  "I11a (every row is the root scope or the world record, reached by §3.2 from an obligation, a
  cleanup row, admitted by §3.4, or a finalizer ref of a reached run) through the step,
  kernel-checked (Init only).

  Bundle root-scope-reserved = well-formed and: id 2 is the root scope's (a scope of kind root or with id 2 is the
  root scope with parent 0), no run scope is 2, the allocator is above 2, no fork marker is owned
  by the root scope (C1c stage B; before it: no fork markers). Restated over the raw transition and normalization by the generic tree; own proofs:
  run creation (`add-run-scope`: the new scope is next-id + 1) and detach (the re-parented scope is
  a run's scope, not 2).
  Reach: from the roots, every node is the root scope or reached from the obligations
  (`reach-roots-obl`): the other roots are obligations (pins, observe edges, open explicit scopes,
  pending activation, armed publications with handles), and the root scope's successors are the
  running tasks it owns (reached from their alive run: K.run names a run of K, from i10's i10-current)
  and its fork markers (none). With I3 (`step-i3-total`: the filter keeps only live, cleanup,
  admitted and stored rows) every row is `obl-ok` (`i11a-of`); obl-reach converges with its fuel
  (`obl-converged`).
  Theorems: step-root-scope-reserved, i11a-of, chain-to-i11a = chain-to-i10-current && root-scope-reserved && inv-i11a with step-chain-to-i11a, chain-to-i11a-empty and
  step-i11a-total (no honest hypothesis)."
  (:require [ansatz.core :as a]
            [spindel.v2.pres.tree :as tree]
            [spindel.v2.pres.frames :as frames]
            [clojure.string :as str]
            [spindel.v2.state :refer :all]
            [spindel.v2.edits :refer :all]
            [spindel.v2.reach :refer :all]
            [spindel.v2.retain :refer :all]
            [spindel.v2.step :refer :all]
            [spindel.v2.rule :refer :all]
            [spindel.v2.engine :refer :all]
            [spindel.v2.inv.rank :refer :all]
            [spindel.v2.progress.casc :refer :all]
            [spindel.v2.inv.acts :refer :all]
            [spindel.v2.inv :refer :all]
            [spindel.v2.pres.part :refer :all]
            [spindel.v2.inv.copier :refer :all]
            [spindel.v2.inv.idle :refer :all]
            [spindel.v2.inv.base :refer :all]
            [spindel.v2.inv.i10 :refer :all]))

;; ===========================================================================
;; Part A. The bundle root-scope-reserved: id 2 is the root scope's (kind root -> id 2, parent 0), no run scope
;; is 2, the allocator is above 2, no fork marker owned by the root scope (C1c stage B, `fk-ok`)
;; ===========================================================================

(a/structure RootScopeReservedScopeKey [] (id Nat) (kind Nat) (parent Nat))
(a/defn root-scope-reserved-scope-key [s :- ScopeRow] RootScopeReservedScopeKey (RootScopeReservedScopeKey.mk (:id s) (:kind s) (:parent s)))
(a/defn root-scope-reserved-scope-key-id [k :- RootScopeReservedScopeKey] Nat (:id k))
(a/defn root-scope-reserved-scope-keys [ss :- (List ScopeRow)] (List RootScopeReservedScopeKey)
  (match ss nil (List.nil RootScopeReservedScopeKey) (cons h t) (List.cons RootScopeReservedScopeKey (root-scope-reserved-scope-key h) (root-scope-reserved-scope-keys t))))
(a/defn rscs [rs :- (List RunRow)] (List Nat)
  (match rs nil (List.nil Nat) (cons h t) (List.cons Nat (:scope h) (rscs t))))
(a/defn root-ok [k :- RootScopeReservedScopeKey] Bool
  (Bool.or (Bool.not (Bool.or (Nat.beq (:kind k) scope-root) (Nat.beq (:id k) 2)))
           (Bool.and (Nat.beq (:id k) 2) (Bool.and (Nat.beq (:kind k) scope-root) (Nat.beq (:parent k) 0)))))
(a/defn ne2 [x :- Nat] Bool (Bool.not (Nat.beq x 2)))
;; C1c stage B: no fork marker is owned by the root scope (the owner is the forking run's current scope)
(a/defn fk-ok [f :- ForkRow] Bool (ne2 (:owner f)))
(a/defn root-scope-reserved-keys-ok [sks :- (List RootScopeReservedScopeKey), rss :- (List Nat), fs :- (List ForkRow), n :- Nat] Bool
  (Bool.and (tbl-all root-ok sks) (Bool.and (tbl-all ne2 rss) (Bool.and (tbl-all fk-ok fs) (Nat.blt 2 n)))))
(a/defn root-scope-reserved-rest [w :- World] Bool (root-scope-reserved-keys-ok (root-scope-reserved-scope-keys (:scopes w)) (rscs (:runs w)) (:forks w) (:next-id w)))
(a/defn root-scope-reserved [w :- World] Bool (Bool.and (well-formed w) (root-scope-reserved-rest w)))

(a/theorem root-scope-reserved-well-formed [w :- World] (=> (= (root-scope-reserved w) true) (= (well-formed w) true))
  (intro h) (simp only [root-scope-reserved Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem root-scope-reserved-rest-of [w :- World] (=> (= (root-scope-reserved w) true) (= (root-scope-reserved-rest w) true))
  (intro h) (simp only [root-scope-reserved Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem root-scope-reserved-intro [w :- World] (=> (= (well-formed w) true) (= (root-scope-reserved-rest w) true) (= (root-scope-reserved w) true))
  (intros h1 h2) (simp only [root-scope-reserved h1 h2 Bool.and_self]))
(a/theorem root-scope-reserved-parts [w :- World]
  (=> (= (root-scope-reserved w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (root-scope-reserved-well-formed w h))))

(a/structure RootScopeReservedView [] (sks (List RootScopeReservedScopeKey)) (rss (List Nat)) (fs (List ForkRow)) (n Nat))
(a/defn root-scope-reserved-view [w :- World] RootScopeReservedView (RootScopeReservedView.mk (root-scope-reserved-scope-keys (:scopes w)) (rscs (:runs w)) (:forks w) (:next-id w)))
(a/theorem root-scope-reserved-rest-frame [w :- World, w2 :- World] (=> (= (root-scope-reserved-view w2) (root-scope-reserved-view w)) (= (root-scope-reserved-rest w2) (root-scope-reserved-rest w)))
  (intro e)
  (have e1 (= (root-scope-reserved-scope-keys (:scopes w2)) (root-scope-reserved-scope-keys (:scopes w)))) (exact (congrArg (fn [k :- RootScopeReservedView] (:sks k)) e))
  (have e2 (= (rscs (:runs w2)) (rscs (:runs w)))) (exact (congrArg (fn [k :- RootScopeReservedView] (:rss k)) e))
  (have e3 (= (:forks w2) (:forks w))) (exact (congrArg (fn [k :- RootScopeReservedView] (:fs k)) e))
  (have e4 (= (:next-id w2) (:next-id w))) (exact (congrArg (fn [k :- RootScopeReservedView] (:n k)) e))
  (simp only [root-scope-reserved-rest e1 e2 e3 e4]))

(a/theorem root-scope-reserved-scope-keys-same [x :- Nat, f :- (=> ScopeRow ScopeRow), hk :- (forall [s :- ScopeRow] (= (root-scope-reserved-scope-key (f s)) (root-scope-reserved-scope-key s))), ss :- (List ScopeRow)]
  (= (root-scope-reserved-scope-keys (tbl-upd scope-id x f ss)) (root-scope-reserved-scope-keys ss))
  (induction ss)
  (case [nil] (simp only [tbl-upd root-scope-reserved-scope-keys]))
  (case [cons h t ih] (cases hx (Nat.beq (scope-id h) x)) (all_goals (simp only [tbl-upd hx root-scope-reserved-scope-keys ih (hk h)]))))
(a/theorem rscs-same [x :- Nat, f :- (=> RunRow RunRow), hk :- (forall [r :- RunRow] (= (:scope (f r)) (:scope r))), rs :- (List RunRow)]
  (= (rscs (tbl-upd run-id x f rs)) (rscs rs))
  (induction rs)
  (case [nil] (simp only [tbl-upd rscs]))
  (case [cons h t ih] (cases hx (Nat.beq (run-id h) x)) (all_goals (simp only [tbl-upd hx rscs ih (hk h)]))))

(a/theorem root-scope-reserved-run-upd [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                       hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                       hk :- (forall [r :- RunRow] (= (:scope (f r)) (:scope r)))]
  (=> (= (root-scope-reserved w) true) (= (root-scope-reserved (run-upd w x f)) true))
  (intro h)
  (have e (= (root-scope-reserved-view (run-upd w x f)) (root-scope-reserved-view w))) (simp only [root-scope-reserved-view run-upd set-runs (rscs-same x f hk (:runs w))])
  (exact (root-scope-reserved-intro _ (well-formed-run-upd w x f hf (root-scope-reserved-well-formed w h)) (Eq.trans (root-scope-reserved-rest-frame w _ e) (root-scope-reserved-rest-of w h)))))
(a/theorem root-scope-reserved-scope-upd [w :- World, x :- Nat, f :- (=> ScopeRow ScopeRow),
                         hf :- (forall [s :- ScopeRow] (= (scope-id (f s)) (scope-id s))),
                         hk :- (forall [s :- ScopeRow] (= (root-scope-reserved-scope-key (f s)) (root-scope-reserved-scope-key s)))]
  (=> (= (root-scope-reserved w) true) (= (root-scope-reserved (scope-upd w x f)) true))
  (intro h)
  (have e (= (root-scope-reserved-view (scope-upd w x f)) (root-scope-reserved-view w))) (simp only [root-scope-reserved-view scope-upd set-scopes (root-scope-reserved-scope-keys-same x f hk (:scopes w))])
  (exact (root-scope-reserved-intro _ (well-formed-scope-upd w x f hf (root-scope-reserved-well-formed w h)) (Eq.trans (root-scope-reserved-rest-frame w _ e) (root-scope-reserved-rest-of w h)))))

;; ---- deletions, the allocator, insertions

(a/theorem root-scope-reserved-scope-keys-del [x :- Nat, ss :- (List ScopeRow)] (= (root-scope-reserved-scope-keys (tbl-del scope-id x ss)) (tbl-del root-scope-reserved-scope-key-id x (root-scope-reserved-scope-keys ss)))
  (induction ss)
  (case [nil] (simp only [tbl-del root-scope-reserved-scope-keys]))
  (case [cons h t ih]
    (have e (= (Nat.beq (root-scope-reserved-scope-key-id (root-scope-reserved-scope-key h)) x) (Nat.beq (scope-id h) x))) (rfl)
    (cases hx (Nat.beq (scope-id h) x)) (all_goals (simp only [tbl-del hx root-scope-reserved-scope-keys e ih]))))
(a/defn rsc-of [r :- RunRow] Nat (:scope r))
(a/theorem all-rscs [P :- (=> Nat Bool), rs :- (List RunRow)] (= (tbl-all P (rscs rs)) (tbl-all (fn [r :- RunRow] (P (:scope r))) rs))
  (induction rs) (case [nil] (simp only [rscs tbl-all])) (case [cons h t ih] (simp only [rscs tbl-all ih])))
(a/theorem all-root-scope-reserved-scope-keys [P :- (=> RootScopeReservedScopeKey Bool), ss :- (List ScopeRow)] (= (tbl-all P (root-scope-reserved-scope-keys ss)) (tbl-all (fn [s :- ScopeRow] (P (root-scope-reserved-scope-key s))) ss))
  (induction ss) (case [nil] (simp only [root-scope-reserved-scope-keys tbl-all])) (case [cons h t ih] (simp only [root-scope-reserved-scope-keys tbl-all ih])))

(a/theorem root-scope-reserved-rest-run-del [w :- World, x :- Nat] (=> (= (root-scope-reserved-rest w) true) (= (root-scope-reserved-rest (run-del w x)) true))
  (intro h)
  (simp only [root-scope-reserved-rest root-scope-reserved-keys-ok Bool.and_eq_true] at h)
  (have a1 (= (tbl-all ne2 (rscs (tbl-del run-id x (:runs w)))) true))
  (rw [all-rscs]) (have a0 := (And.left (And.right h))) (rw [all-rscs] at a0)
  (exact (tbl-all-del RunRow run-id x _ _ (fn [r :- RunRow, p :- (= (ne2 (:scope r)) true), q :- (= (Nat.beq (run-id r) x) false)] p) _ a0))
  (simp only [root-scope-reserved-rest root-scope-reserved-keys-ok run-del set-runs a1 (And.left h) (And.right (And.right h)) Bool.and_self]))
(a/theorem root-scope-reserved-rest-scope-del [w :- World, x :- Nat] (=> (= (root-scope-reserved-rest w) true) (= (root-scope-reserved-rest (scope-del w x)) true))
  (intro h)
  (simp only [root-scope-reserved-rest root-scope-reserved-keys-ok Bool.and_eq_true] at h)
  (have a1 (= (tbl-all root-ok (root-scope-reserved-scope-keys (tbl-del scope-id x (:scopes w)))) true))
  (rw [root-scope-reserved-scope-keys-del])
  (exact (tbl-all-del RootScopeReservedScopeKey root-scope-reserved-scope-key-id x _ _ (fn [k :- RootScopeReservedScopeKey, p :- (= (root-ok k) true), q :- (= (Nat.beq (root-scope-reserved-scope-key-id k) x) false)] p) _ (And.left h)))
  (simp only [root-scope-reserved-rest root-scope-reserved-keys-ok scope-del set-scopes a1 (And.right h) Bool.and_self]))
(a/theorem root-scope-reserved-rest-filter [w :- World, K :- (=> Nat Bool)] (=> (= (root-scope-reserved-rest w) true) (= (root-scope-reserved-rest (filter-world K w)) true))
  (intro h)
  (simp only [root-scope-reserved-rest root-scope-reserved-keys-ok Bool.and_eq_true] at h)
  (have a1 (= (tbl-all root-ok (root-scope-reserved-scope-keys (tbl-keep K scope-id (:scopes w)))) true))
  (rw [all-root-scope-reserved-scope-keys]) (have a0 := (And.left h)) (rw [all-root-scope-reserved-scope-keys] at a0) (exact (tbl-all-keep-same ScopeRow K scope-id _ _ a0))
  (have a2 (= (tbl-all ne2 (rscs (tbl-keep K run-id (:runs w)))) true))
  (rw [all-rscs]) (have a0 := (And.left (And.right h))) (rw [all-rscs] at a0) (exact (tbl-all-keep-same RunRow K run-id _ _ a0))
  (have f0 := (And.left (And.right (And.right h))))
  (have a3 (= (tbl-all fk-ok (tbl-keep K fork-id (:forks w))) true)) (exact (tbl-all-keep-same ForkRow K fork-id _ _ f0))
  (simp only [root-scope-reserved-rest root-scope-reserved-keys-ok filter-world a1 a2 a3 (And.right (And.right (And.right h))) Bool.and_self]))
(a/theorem root-scope-reserved-rest-next [w :- World, v :- Nat]
  (=> (= (root-scope-reserved-rest w) true) (<= (:next-id w) v) (= (root-scope-reserved-rest (set-next-id w v)) true))
  (intros h hv)
  (simp only [root-scope-reserved-rest root-scope-reserved-keys-ok Bool.and_eq_true Nat.blt_eq] at h)
  (have b (= (Nat.blt 2 v) true)) (simp only [Nat.blt_eq]) (have z := (And.right (And.right (And.right h)))) (omega)
  (have e1 (= (:scopes (set-next-id w v)) (:scopes w))) (rfl)
  (have e2 (= (:runs (set-next-id w v)) (:runs w))) (rfl)
  (have e3 (= (:forks (set-next-id w v)) (:forks w))) (rfl)
  (have e4 (= (:next-id (set-next-id w v)) v)) (rfl)
  (simp only [root-scope-reserved-rest root-scope-reserved-keys-ok e1 e2 e3 e4 b (And.left h) (And.left (And.right h)) (And.left (And.right (And.right h))) Bool.and_self]))
(a/theorem root-scope-reserved-rest-bump [w :- World] (=> (= (root-scope-reserved-rest w) true) (= (root-scope-reserved-rest (bump w)) true))
  (intro h) (simp only [bump]) (exact (root-scope-reserved-rest-next w (+ (:next-id w) 1) h (Nat.le_succ (:next-id w)))))

;; a new scope that is not of kind root (run and explicit scopes)
(a/theorem root-scope-reserved-scope-ins-fresh [w :- World, r :- ScopeRow, hk :- (= (Nat.beq (:kind r) scope-root) false)]
  (=> (= (scope-id r) (:next-id w)) (= (root-scope-reserved w) true) (= (root-scope-reserved (bump (scope-ins w r))) true))
  (intros hr h)
  (have h0 := (root-scope-reserved-rest-of w h)) (simp only [root-scope-reserved-rest root-scope-reserved-keys-ok Bool.and_eq_true] at h0)
  (have hi (= (Nat.beq (:id r) 2) false))
  (cases hb (Nat.beq (:id r) 2)) (rfl) (have z := (Nat.eq_of_beq_eq_true hb)) (have z2 := (And.right (And.right (And.right h0))))
  (simp only [Nat.blt_eq] at z2) (have z3 (= (:id r) (:next-id w))) (exact hr) (omega)
  (have ro (= (root-ok (root-scope-reserved-scope-key r)) true)) (simp only [root-ok root-scope-reserved-scope-key hk hi Bool.or_false Bool.not_false Bool.true_or])
  (have hrest (= (root-scope-reserved-rest (scope-ins w r)) true))
  (simp only [root-scope-reserved-rest root-scope-reserved-keys-ok scope-ins set-scopes tbl-ins root-scope-reserved-scope-keys tbl-all ro (And.left h0) (And.right h0) Bool.and_self Bool.true_and])
  (exact (root-scope-reserved-intro _ (well-formed-scope-ins-fresh w r hr (root-scope-reserved-well-formed w h)) (root-scope-reserved-rest-bump _ hrest))))

;; ===========================================================================
;; Part B. The copy
;; ===========================================================================

(def GW (mk-bundle 'root-scope-reserved [] "root-scope-reserved-"
          {'well-formed-run-upd ['(fn [r :- RunRow] (Eq.refl (:scope r))) 4]
           'well-formed-scope-upd ['(fn [s :- ScopeRow] (Eq.refl (root-scope-reserved-scope-key s))) 4]
           'well-formed-scope-ins-fresh ['(Eq.refl false) 2]}))
(swap! (:renames GW) assoc 'well-formed-parts 'root-scope-reserved-parts 'well-formed-run-upd 'root-scope-reserved-run-upd 'well-formed-scope-upd 'root-scope-reserved-scope-upd 'well-formed-scope-ins-fresh 'root-scope-reserved-scope-ins-fresh)
(defpart GW :reads '[forks next-id runs scopes])
(frames/frame-theorem! 'root-scope-reserved-rest-mark-edge 'root-scope-reserved-rest 'well-formed-mark-edge)
(frames/frame-theorem! 'root-scope-reserved-rest-unmark-edge 'root-scope-reserved-rest 'well-formed-unmark-edge)
(frames/frame-theorem! 'root-scope-reserved-rest-remove-edge 'root-scope-reserved-rest 'well-formed-remove-edge)
(doseq [o '[well-formed-source-ins-fresh well-formed-resource-ins-fresh well-formed-act-ins-fresh well-formed-comp-ins-fresh well-formed-task-ins-fresh]]
  (prim! GW o (list 'root-scope-reserved-rest-bump (list (symbol (str/replace (subs (name o) 12) "-fresh" "")) 'w 'r) (list 'Eq.trans '(rfl) 'R))))
(prim! GW 'well-formed-bump '(root-scope-reserved-rest-bump w R))
(prim! GW 'well-formed-insert-edge-fresh '(root-scope-reserved-rest-bump (insert-edge w (edge-set-id (:next-id w) e)) (Eq.trans (rfl) R)))
(prim! GW 'well-formed-run-del '(root-scope-reserved-rest-run-del w x R))
(prim! GW 'well-formed-scope-del '(root-scope-reserved-rest-scope-del w x R))
(prim! GW 'well-formed-filter-world '(root-scope-reserved-rest-filter w K R))
(tree/part! GW
  :over '{well-formed-t-own         root-scope-reserved-t-own            ; own: the marker's owner is not the root scope
          well-formed-add-run-scope root-scope-reserved-add-run-scope    ; T4/T5/T11: the new run's scope is a run scope (> 2)
          well-formed-t-detach      root-scope-reserved-t-detach})       ; detach: the task's run scope is not 2

;; C1c stage B: a marker goes (fk-ok kept); own adds one whose owner is not the root scope (own-ok)
(a/theorem root-scope-reserved-rest-fork-del [w :- World, x :- Nat] (=> (= (root-scope-reserved-rest w) true) (= (root-scope-reserved-rest (fork-del w x)) true))
  (intro h)
  (simp only [root-scope-reserved-rest root-scope-reserved-keys-ok Bool.and_eq_true] at h)
  (have a (= (tbl-all fk-ok (tbl-del fork-id x (:forks w))) true))
  (exact (tbl-all-del ForkRow fork-id x _ _ (fn [f :- ForkRow, p :- (= (fk-ok f) true), q :- (= (Nat.beq (fork-id f) x) false)] p) _ (And.left (And.right (And.right h)))))
  (simp only [root-scope-reserved-rest root-scope-reserved-keys-ok fork-del set-forks a (And.left h) (And.left (And.right h)) (And.right (And.right (And.right h))) Bool.and_self]))
(prim! GW 'well-formed-fork-del '(root-scope-reserved-rest-fork-del w x R))
(a/theorem root-scope-reserved-t-own [w :- World, s :- Nat, m :- Nat]
  (=> (= (root-scope-reserved w) true) (= (root-scope-reserved (:world (t-own w s m))) true))
  (intro h)
  (cases ho (own-ok w s))
  (case [false] (simp only [t-own ho refuse]) (exact h))
  (case [true]
    (simp only [t-own ho accept])
    (have o := (own-ok-parts w s ho))
    (have f1 (= (fk-ok (ForkRow.mk (:next-id w) m s)) true)) (simp only [fk-ok ne2 (And.left (And.right o)) Bool.not_false])
    (have h0 := (root-scope-reserved-rest-of w h)) (simp only [root-scope-reserved-rest root-scope-reserved-keys-ok Bool.and_eq_true] at h0)
    (have r1 (= (root-scope-reserved-rest (fork-ins w (ForkRow.mk (:next-id w) m s))) true))
    (simp only [root-scope-reserved-rest root-scope-reserved-keys-ok fork-ins set-forks tbl-ins tbl-all f1 (And.left h0) (And.left (And.right h0))
                (And.left (And.right (And.right h0))) (And.right (And.right (And.right h0))) Bool.and_self Bool.true_and])
    (exact (root-scope-reserved-intro _ (well-formed-fork-ins-fresh w (ForkRow.mk (:next-id w) m s) (rfl) (root-scope-reserved-well-formed w h)) (root-scope-reserved-rest-bump _ r1)))))

;; T4/T5/T11: the new run's scope is next-id + 1 (> 2), a run scope
(a/theorem root-scope-reserved-add-run-scope-hand [w :- World, of :- Nat, epoch :- Nat, parent :- Nat, ei :- Nat]
  (=> (= (root-scope-reserved w) true) (= (root-scope-reserved (add-run-scope w of epoch parent ei)) true))
  (intro h)
  (have hs := (root-scope-reserved-well-formed w h))
  (have h0 := (root-scope-reserved-rest-of w h)) (simp only [root-scope-reserved-rest root-scope-reserved-keys-ok Bool.and_eq_true Nat.blt_eq] at h0)
  (have b (= (ne2 (+ (:next-id w) 1)) true))
  (simp only [ne2]) (cases hb (Nat.beq (+ (:next-id w) 1) 2)) (rfl) (have z := (Nat.eq_of_beq_eq_true hb)) (have z2 := (And.right (And.right (And.right h0)))) (omega)
  (have h1 (= (root-scope-reserved (bump (run-ins w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei)))) true))
  (have r1 (= (root-scope-reserved-rest (run-ins w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei))) true))
  (simp only [root-scope-reserved-rest root-scope-reserved-keys-ok run-ins set-runs tbl-ins rscs new-run-row tbl-all b (And.left h0) (And.left (And.right h0))
              (And.left (And.right (And.right h0))) Bool.and_self Bool.true_and])
  (have z2 := (And.right (And.right (And.right h0)))) (simp only [Nat.blt_eq]) (exact z2)
  (exact (root-scope-reserved-intro _ (well-formed-run-ins-fresh w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei) (rfl) hs) (root-scope-reserved-rest-bump _ r1)))
  (simp only [add-run-scope])
  (have he (= (scope-id (new-scope-row (+ (:next-id w) 1) parent)) (:next-id (bump (run-ins w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei)))))) (rfl)
  (exact (root-scope-reserved-scope-ins-fresh _ (new-scope-row (+ (:next-id w) 1) parent) (Eq.refl false) he h1)))
(a/theorem root-scope-reserved-add-run-scope [w :- World, of :- Nat, epoch :- Nat, parent :- Nat, ei :- Nat]
  (=> (= (root-scope-reserved w) true) (= (root-scope-reserved (add-run-scope w of epoch parent ei)) true))
  (intro h) (exact (root-scope-reserved-add-run-scope-hand w of epoch parent ei h)))

;; detach: the task's run scope (a run's scope: not 2) gets the new parent
(a/theorem root-scope-reserved-set-parent [w :- World, x :- Nat, p :- Nat]
  (=> (= (Nat.beq x 2) false) (= (root-scope-reserved w) true) (= (root-scope-reserved (scope-upd w x (scope-set-parent p))) true))
  (intros hx h)
  (have hs := (root-scope-reserved-well-formed w h))
  (have h0 := (root-scope-reserved-rest-of w h)) (simp only [root-scope-reserved-rest root-scope-reserved-keys-ok Bool.and_eq_true] at h0)
  (have a1 (= (tbl-all root-ok (root-scope-reserved-scope-keys (tbl-upd scope-id x (scope-set-parent p) (:scopes w)))) true))
  (rw [all-root-scope-reserved-scope-keys]) (have a0 := (And.left h0)) (rw [all-root-scope-reserved-scope-keys] at a0)
  (apply (tbl-all-upd ScopeRow scope-id x (scope-set-parent p) _ _ _ _ _ a0))
  (intros s q e)
  (have e2 (= (:id s) x)) (exact (Nat.eq_of_beq_eq_true e))
  (simp only [root-ok root-scope-reserved-scope-key Bool.or_eq_true Bool.and_eq_true] at q)
  (simp only [root-ok root-scope-reserved-scope-key scope-set-parent Bool.or_eq_true Bool.and_eq_true])
  (cases q)
  (case [inl a] (exact (Or.inl a)))
  (case [inr b] (have z := (And.left b)) (rw [e2 hx] at z) (cases z))
  (intros s q e) (exact q)
  (have hrest (= (root-scope-reserved-rest (scope-upd w x (scope-set-parent p))) true))
  (simp only [root-scope-reserved-rest root-scope-reserved-keys-ok scope-upd set-scopes a1 (And.right h0) Bool.and_self Bool.true_and])
  (exact (root-scope-reserved-intro _ (well-formed-scope-upd w x (scope-set-parent p) (scope-set-parent-id p) hs) hrest)))

(a/theorem trs-ne2 [w :- World, t :- TaskRow] (=> (= (root-scope-reserved w) true) (= (Nat.beq (task-run-scope w t) 2) false))
  (intro h)
  (cases hf (run-find w (:run t)))
  (case [none] (simp only [task-run-scope hf]))
  (case [some r]
    (simp only [task-run-scope hf])
    (have h0 := (root-scope-reserved-rest-of w h)) (simp only [root-scope-reserved-rest root-scope-reserved-keys-ok Bool.and_eq_true] at h0)
    (have a0 := (And.left (And.right h0))) (rw [all-rscs] at a0)
    (have q := (tbl-all-mem RunRow _ r _ a0 (tbl-find-mem RunRow run-id (:run t) r (:runs w) hf)))
    (simp only [ne2] at q) (exact (bnot-true _ q))))

(tree/restate! GW '[well-formed-remove-if-empty])
(a/theorem root-scope-reserved-t-detach [w :- World, k :- Nat, s :- Nat]
  (=> (= (root-scope-reserved w) true) (= (root-scope-reserved (:world (t-detach w k s))) true))
  (intro h)
  (cases hf (task-find w k))
  (case [none] (simp only [t-detach hf refuse]) (exact h))
  (case [some t]
    (cases hg (detach-ok w t s))
    (case [false] (simp only [t-detach hf hg refuse]) (exact h))
    (case [true]
      (simp only [t-detach hf hg accept remove-empty-at detach-move])
      (have h1 := (root-scope-reserved-task-upd w k (task-set-owner s) (task-set-owner-id s) h))
      (have hne (= (Nat.beq (task-run-scope w t) 2) false)) (exact (trs-ne2 w t h))
      (exact (root-scope-reserved-remove-if-empty _ _ (root-scope-reserved-set-parent _ (task-run-scope w t) s hne h1))))))

(tree/restate! GW '[well-formed-raw])
(tree/restate! GW '[well-formed-normalize])

(a/theorem root-scope-reserved-rule-r-round [w :- World]
  (=> (= (root-scope-reserved w) true) (= (filter-safe (normalize w)) true) (= (root-scope-reserved (rule-r-round w)) true))
  (intros h hf) (simp only [rule-r-round]) (rw [rule-r-filter-eq])
  (exact (root-scope-reserved-filter-world (normalize w) (keep-fn (normalize w)) (root-scope-reserved-normalize w h) hf)))
(a/theorem root-scope-reserved-rule-r-loop [fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (root-scope-reserved w0) true) (= (rounds-safe-loop fuel w0) true) (= (root-scope-reserved (rule-r-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 h hs) (simp only [rounds-safe-loop] at hs) (simp only [rule-r-loop]) (exact (root-scope-reserved-rule-r-round w0 h hs)))
  (case [cons x f ih]
    (intros w0 h hs)
    (simp only [rounds-safe-loop Bool.and_eq_true] at hs)
    (have h1 := (root-scope-reserved-rule-r-round w0 h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false] (simp only [ho] at hs) (simp only [rule-r-loop ho]) (exact (ih (rule-r-round w0) h1 (And.right hs))))
    (case [true] (simp only [rule-r-loop ho]) (exact h1))))
(a/theorem root-scope-reserved-rule-r [w :- World] (=> (= (root-scope-reserved w) true) (= (rule-r-safe w) true) (= (root-scope-reserved (rule-r w)) true))
  (intros h hs) (simp only [rule-r-safe] at hs) (simp only [rule-r]) (exact (root-scope-reserved-rule-r-loop (rule-r-fuel w) w h hs)))
(a/theorem step-root-scope-reserved [w :- World, it :- Item]
  (=> (= (root-scope-reserved w) true) (= (rule-r-safe (:world (raw w it))) true) (= (root-scope-reserved (:world (world-step w it))) true))
  (intros h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true] (have e2 := (step-accepted w it ha)) (rw [e2]) (exact (root-scope-reserved-rule-r (:world (raw w it)) (root-scope-reserved-raw w it h) hs))))
(a/theorem root-scope-reserved-empty [] (= (root-scope-reserved empty-world) true) (rfl))

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
  (=> (= (root-scope-reserved w) true) (= (reach-mem y (roots w)) true) (Or (is2 w y) (= (reach-mem y (obligations w)) true)))
  (intros h hm)
  (have h0 := (root-scope-reserved-rest-of w h)) (simp only [root-scope-reserved-rest root-scope-reserved-keys-ok Bool.and_eq_true] at h0)
  (have ro := (And.left h0)) (rw [all-root-scope-reserved-scope-keys] at ro)
  (simp only [roots reach-mem-append Bool.or_eq_true] at hm)
  (have ob (forall [z :- Nat] (=> (= (reach-mem z (obligations w)) true) (Or (is2 w y) (= (reach-mem z (obligations w)) true)))))
  (intros z hz) (exact (Or.inr hz))
  (cases hm)
  (case [inl a]
      (apply Or.inl)
      (apply (scan-prop ScopeRow scope-id is-root-scope (is2 w) (:scopes w) _ y a))
      (intros s m p)
      (have q := (tbl-all-mem ScopeRow _ s _ ro m))
      (simp only [root-ok root-scope-reserved-scope-key] at q)
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
  (=> (= (well-formed w) true) (= (scope-has w 2) true)
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
  (=> (= (well-formed w) true) (List.Mem t (:tasks w)) (= (Nat.beq (:id t) 0) false))
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
  (=> (= (root-scope-reserved w) true) (= (i10-current w) true) (List.Mem t (:tasks w)) (= (owned-running-task w 2 t) true)
      (Reach (retain-succ w) (obligations w) (:id t)))
  (intros h h10 mt p)
  (have hs := (root-scope-reserved-well-formed w h))
  (simp only [owned-running-task task-running Bool.and_eq_true] at p)
  (have hr0 := (bnot-true _ (And.left (And.right p))))
  (have po := (And.right (And.right p)))
  (cases hf (run-find w (:run t)))
  (case [none] (simp [opt-test hf] at po))
  (case [some r]
    (simp only [opt-test hf] at po)
    (have mr := (tbl-find-mem RunRow run-id (:run t) r (:runs w) hf))
    (have er (= (:id r) (:run t))) (exact (tbl-find-id RunRow run-id (:run t) r (:runs w) hf))
    (have tp := (i10-current-exempt-tof (List.nil Nat) (List.nil Nat) w r t h10 mr mt))
    (have hz (= (Nat.beq (:id r) 0) false)) (rw [er]) (exact hr0)
    (have hx (= (Nat.beq (:id r) (:run t)) true)) (rw [er]) (exact (Nat.beq_refl _))
    (simp only [tof-pair i10-current-run-key i10-current-task-key hz hx Bool.not_true Bool.false_or] at tp)
    (have eo := (Nat.eq_of_beq_eq_true tp))
    (have sm (= (reach-mem (:id r) (tbl-scan run-id run-alive (:runs w))) true)) (exact (scan-mem RunRow run-id run-alive r (:runs w) mr po))
    (have om (= (reach-mem (:id r) (obligations w)) true)) (simp only [obligations reach-mem-nat-app sm Bool.true_or Bool.or_true])
    (have ro (Reach (retain-succ w) (obligations w) (:id r))) (exact (Reach.root (:id r) (Iff.mp (reach-mem-iff (:id r) (obligations w)) om)))
    (have tz := (task-id-pos w t hs mt))
    (have oz (= (Nat.beq (:of r) 0) false)) (rw [eo]) (exact tz)
    (have sc := (succ-of w r mr po oz))
    (rw [eo] at sc)
    (exact (Reach.step (:id r) (:id t) ro (Iff.mp (reach-mem-iff (:id t) (retain-succ w (:id r))) sc)))))

;; a marker with fk-ok is not owned by the root scope
(a/theorem fk-root [f :- ForkRow] (=> (= (fk-ok f) true) (= (owned-fork 2 f) true) False)
  (intros h p) (simp only [fk-ok ne2 owned-fork] at h p) (rw [p] at h) (cases h))
(a/theorem root-scope-succ [w :- World, s :- ScopeRow, z :- Nat]
  (=> (= (root-scope-reserved w) true) (= (i10-current w) true) (List.Mem s (:scopes w)) (= (id-is scope-id 2 s) true) (= (reach-mem z (scope-contrib w s)) true)
      (Reach (retain-succ w) (obligations w) z))
  (intros h h10 m p hz)
  (have h0 := (root-scope-reserved-rest-of w h)) (simp only [root-scope-reserved-rest root-scope-reserved-keys-ok Bool.and_eq_true] at h0)
  (have ro := (And.left h0)) (rw [all-root-scope-reserved-scope-keys] at ro)
  (have fk := (And.left (And.right (And.right h0))))
  (have q := (tbl-all-mem ScopeRow _ s _ ro m))
  (have e (= (:id s) 2)) (have p2 := p) (simp only [id-is] at p2) (exact (Nat.eq_of_beq_eq_true p2))
  (have e2 (= (Nat.beq (:id (root-scope-reserved-scope-key s)) 2) true)) (simp only [root-scope-reserved-scope-key]) (rw [e])
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
      (exact (False.elim (scan-prop ForkRow fork-id (owned-fork 2) (fn [z :- Nat] False) (:forks w)
               (fn [f :- ForkRow, mf :- (List.Mem f (:forks w)), pf :- (= (owned-fork 2 f) true)]
                 (fk-root f (tbl-all-mem ForkRow fk-ok f (:forks w) fk mf) pf)) z d))))))

(a/theorem root-succ-other [w :- World, y :- Nat]
  (=> (= (well-formed w) true) (= (scope-has w 2) true)
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
  (=> (= (root-scope-reserved w) true) (= (i10-current w) true) (= (scope-has w 2) true) (= (reach-mem y (retain-succ w 2)) true)
      (Reach (retain-succ w) (obligations w) y))
  (intros h h10 hh hm)
  (have hs := (root-scope-reserved-well-formed w h))
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
  (=> (= (root-scope-reserved w) true) (= (i10-current w) true) (Reach (retain-succ w) (roots w) y)
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
  (=> (= (root-scope-reserved w) true) (= (i10-current w) true) (= (reach-mem y (live-list w)) true)
      (Or (is2 w y) (= (reach-mem y (:visited (obl-reach w))) true)))
  (intros h h10 hl)
  (have r := (Iff.mp (in-live-iff w y (live-converged-all w)) hl))
  (have q := (reach-roots-obl w y h h10 r))
  (cases q)
  (case [inl a] (exact (Or.inl a)))
  (case [inr b] (exact (Or.inr (Iff.mpr (obl-iff w y) b)))))

(a/theorem storage-obl [w :- World, y :- Nat]
  (=> (= (root-scope-reserved w) true) (= (i10-current w) true) (= (reach-mem y (storage w)) true)
      (= (reach-mem y (storage-with w (:visited (obl-reach w)))) true))
  (intros h h10 hs)
  (have hsm := (root-scope-reserved-well-formed w h))
  (have sub (forall [yy :- Nat] (=> (= (reach-mem yy (storage-gather w (live-list w))) true)
                                    (= (reach-mem yy (storage-gather w (:visited (obl-reach w)))) true))))
  (intros yy hyy0)
  (simp only [storage-gather reach-mem-append Bool.or_eq_true] at hyy0)
  (simp only [storage-gather reach-mem-append Bool.or_eq_true])
  (cases hyy0)
  (case [inr hf] (exact (Or.inr hf)))
  (rename_i hyy)
  (apply Or.inl)
  (simp only [storage-seeds] at hyy)
  (simp only [storage-seeds])
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
  (=> (= (root-scope-reserved w) true) (= (i10-current w) true) (= (keep-fn w y) true) (= (obl-ok w (:visited (obl-reach w)) y) true))
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
  (=> (= (root-scope-reserved w) true) (= (i10-current w) true) (= (tbl-all (keep-fn w) (all-ids w)) true) (= (inv-i11a w) true))
  (intros h h10 hk)
  (have a1 := (tbl-all-mono Nat (keep-fn w) (obl-ok w (:visited (obl-reach w)))
                (fn [y :- Nat, q :- (= (keep-fn w y) true)] (obl-ok-of w y h h10 q)) (all-ids w) hk))
  (simp only [inv-i11a (obl-converged w) a1 Bool.and_self]))

;; ---- the combined bundle and the step

(a/defn chain-to-i11a [w :- World] Bool (Bool.and (chain-to-i10-current w) (Bool.and (root-scope-reserved w) (inv-i11a w))))
(a/theorem chain-to-i11a-parts [w :- World] (=> (= (chain-to-i11a w) true) (And (= (chain-to-i10-current w) true) (And (= (root-scope-reserved w) true) (= (inv-i11a w) true))))
  (intro h) (simp only [chain-to-i11a Bool.and_eq_true] at h) (exact h))
(a/theorem chain-to-i11a-empty [] (= (chain-to-i11a empty-world) true) (rfl))
(a/theorem step-chain-to-i11a [w :- World, it :- Item] (=> (= (chain-to-i11a w) true) (= (chain-to-i11a (:world (world-step w it))) true))
  (intro h)
  (have p := (chain-to-i11a-parts w h))
  (have pc := (chain-to-i10-current-parts w (And.left p)))
  (have a1 := (step-chain-to-i10-current w it (And.left p)))
  (have a2 := (step-root-scope-reserved w it (And.left (And.right p)) (step-rule-r-safe w it (And.left pc))))
  (have a3 (= (inv-i11a (:world (world-step w it))) true))
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact (And.right (And.right p))))
  (case [true] (exact (i11a-of _ a2 (And.right (chain-to-i10-current-parts _ a1)) (step-i3-total w it ha))))
  (simp only [chain-to-i11a a1 a2 a3 Bool.and_self]))
(a/theorem step-i11a-total [w :- World, it :- Item] (=> (= (chain-to-i11a w) true) (= (inv-i11a (:world (world-step w it))) true))
  (intro h) (exact (And.right (And.right (chain-to-i11a-parts _ (step-chain-to-i11a w it h))))))
