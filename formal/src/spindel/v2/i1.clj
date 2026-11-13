(ns spindel.v2.i1
  "Literal I1, scope parents (Z#38, Z#52): the crux of the step, kernel-checked (Init only).

  Rule R's filter keeps the parent of every scope it keeps (`filter-lit-i1-scope`): a scope is kept
  because it is live (live is closed under the parent edge of §3.2, and the parent exists before
  the filter), because a cleanup entry retains it (the retained rows are closed upward under the
  CURRENT parent fields: `anc-close`, Z#52, so a detach that re-parents a scope of the chain moves
  the retention), because it is admitted (impossible: admissions are computations, sources, tasks
  and publications, and ids are unique), or as a storage ref (excluded by hypothesis: refs are
  sources, Z#3; layer 1 registers finalizers with no refs).

    anc-close-closed     a retained id's parent (scope-up) is retained
    cleanup-closed       the same for all cleanup rows
    filter-lit-i1-scope  inv-sample w, lit-i1-scope w -> lit-i1-scope (rule-r-filter w)

  Not yet proved: lit-i1-scope of the normalized world (the transition and normalization keep
  every scope's parent: new scopes get an existing parent, remove-if-empty removes whole subtrees,
  detach re-parents to an open scope), and the other I1 clauses (owners, runs' entities); see
  notes/PLAN.md, branch z52."
  (:require [ansatz.core :as a]
            [spindel.v2.state :refer :all]
            [spindel.v2.edits :refer :all]
            [spindel.v2.reach :refer :all]
            [spindel.v2.retain :refer :all]
            [spindel.v2.step :refer :all]
            [spindel.v2.rule :refer :all]
            [spindel.v2.engine :refer :all]
            [spindel.v2.inv :refer :all]
            [spindel.v2.lit :refer :all]
            [spindel.v2.casc :refer :all]
            [spindel.v2.acts :refer :all]
            [spindel.v2.idle :refer :all]
            [spindel.v2.p3 :refer :all]
            [spindel.v2.i10 :refer :all]
            [spindel.v2.i11 :refer :all]))

;; ===========================================================================
;; Part A. The retained rows are closed upward
;; ===========================================================================

(a/theorem anc-roots [w :- World, x :- Nat, p :- Nat]
  (=> (= (reach-mem p (scope-up w x)) true) (= (reach-mem p (scope-ancestors w x)) true))
  (intro hp)
  (have c := (scope-anc-conv w x))
  (rw [reach-run-l-eq] at c)
  (simp only [scope-ancestors])
  (rw [reach-run-l-eq])
  (exact (reach-run-roots _ (scope-up w) (scope-up w x) p c hp)))

(a/theorem anc-closed [w :- World, x :- Nat, y :- Nat, p :- Nat]
  (=> (= (reach-mem y (scope-ancestors w x)) true) (= (reach-mem p (scope-up w y)) true)
      (= (reach-mem p (scope-ancestors w x)) true))
  (intros hy hp)
  (have c := (scope-anc-conv w x))
  (rw [reach-run-l-eq] at c)
  (simp only [scope-ancestors] at hy)
  (rw [reach-run-l-eq] at hy)
  (simp only [scope-ancestors])
  (rw [reach-run-l-eq])
  (exact (reach-run-closed _ (scope-up w) (scope-up w x) y p c hy hp)))

(a/theorem anc-all-closed [w :- World, xs :- (List Nat), y :- Nat, p :- Nat]
  (=> (= (reach-mem y (anc-all w xs)) true) (= (reach-mem p (scope-up w y)) true) (= (reach-mem p (anc-all w xs)) true))
  (induction xs)
  (case [nil] (intros hy hp) (simp [anc-all reach-mem] at hy))
  (case [cons h t ih]
    (intros hy hp)
    (simp only [anc-all reach-mem-append reach-mem-app Bool.or_eq_true] at hy)
    (cases hy)
    (case [inl a] (simp [anc-all reach-mem-append reach-mem-app (anc-closed w h y p a hp)]))
    (case [inr b] (simp [anc-all reach-mem-append reach-mem-app (ih b hp)]))))

(a/theorem anc-close-closed [w :- World, xs :- (List Nat), y :- Nat, p :- Nat]
  (=> (= (reach-mem y (anc-close w xs)) true) (= (reach-mem p (scope-up w y)) true) (= (reach-mem p (anc-close w xs)) true))
  (intros hy hp)
  (simp only [anc-close reach-mem-append reach-mem-app Bool.or_eq_true] at hy)
  (cases hy)
  (case [inl a] (simp [anc-close reach-mem-append reach-mem-app (anc-all-of w xs y p a (anc-roots w y p hp))]))
  (case [inr b] (simp [anc-close reach-mem-append reach-mem-app (anc-all-closed w xs y p b hp)])))

(a/theorem cleanup-closed [w :- World, cs :- (List CleanupRow), y :- Nat, p :- Nat]
  (=> (= (reach-mem y (cleanup-rows-in w cs)) true) (= (reach-mem p (scope-up w y)) true)
      (= (reach-mem p (cleanup-rows-in w cs)) true))
  (induction cs)
  (case [nil] (intros hy hp) (simp [cleanup-rows-in reach-mem] at hy))
  (case [cons c t ih]
    (intros hy hp)
    (simp only [cleanup-rows-in reach-mem-append reach-mem-app Bool.or_eq_true] at hy)
    (cases hy)
    (case [inl a]
      (have q (= (reach-mem p (cleanup-contrib w c)) true)) (exact (anc-close-closed w (cleanup-base w c) y p a hp))
      (simp [cleanup-rows-in reach-mem-append reach-mem-app q]))
    (case [inr b] (simp [cleanup-rows-in reach-mem-append reach-mem-app (ih b hp)]))))

;; ===========================================================================
;; Part B. A scope row: its parent is its scope-up; it is not admitted
;; ===========================================================================

(a/theorem scopes-nodup1 [w :- World]
  (=> (= (inv-sample w) true) (= (nat-nodup (tbl-ids scope-id (:scopes w))) true))
  (intro h)
  (have u := (ids-unique-of w h))
  (simp only [all-ids] at u)
  (exact (nat-nodup-app-left _ _ u)))

(a/theorem scope-up-of-mem [w :- World, s :- ScopeRow]
  (=> (= (inv-sample w) true) (List.Mem s (:scopes w)) (= (Nat.beq (:parent s) 0) false)
      (= (reach-mem (:parent s) (scope-up w (:id s))) true))
  (intros hs ms hp)
  (have u := (uniq-all ScopeRow scope-id (fn [q :- ScopeRow] (Nat.beq (:parent q) (:parent s))) s (:scopes w)
               (scopes-nodup1 w hs) ms (Nat.beq_refl (:parent s))))
  (cases hf (scope-find w (:id s)))
  (case [none]
    (have hh (= (tbl-has scope-id (:id s) (:scopes w)) true))
    (rw [← (nat-mem-ids ScopeRow scope-id (:id s) (:scopes w))]) (exact (mem-ids-has ScopeRow scope-id s (:scopes w) ms))
    (have hn := (tbl-find-none-has ScopeRow scope-id (:id s) (:scopes w) hf))
    (rw [hh] at hn) (cases hn))
  (case [some q]
    (have mq := (tbl-find-mem ScopeRow scope-id (:id s) q (:scopes w) hf))
    (have iq := (tbl-find-id ScopeRow scope-id (:id s) q (:scopes w) hf))
    (have a1 := (tbl-all-mem ScopeRow _ q _ u mq))
    (have e2 (= (Nat.beq (scope-id q) (scope-id s)) true)) (exact (Eq.trans (congrArg (fn [z :- Nat] (Nat.beq z (:id s))) iq) (Nat.beq_refl (:id s))))
    (simp only [same-id-then e2 Bool.not_true Bool.false_or] at a1)
    (have ep (= (:parent q) (:parent s))) (exact (Nat.eq_of_beq_eq_true a1))
    (simp only [scope-up hf nz ep hp reach-mem-cons Nat.beq_refl Bool.true_or])))

(a/theorem any-id-has [A :- Type, idf :- (=> A Nat), p :- (=> A Bool), y :- Nat, xs :- (List A),
                       hp :- (forall [a :- A] (=> (= (p a) true) (= (idf a) y)))]
  (=> (= (tbl-any p xs) true) (= (tbl-has idf y xs) true))
  (induction xs)
  (case [nil] (intro h) (simp [tbl-any] at h))
  (case [cons h t ih]
    (intro ha)
    (cases hh (p h))
    (case [true]
      (have e := (hp h hh))
      (simp only [tbl-has e Nat.beq_refl Bool.true_or]))
    (case [false]
      (simp only [tbl-any hh Bool.false_or] at ha)
      (simp only [tbl-has (ih ha) Bool.or_true]))))

(a/theorem adm-comp-id [y :- Nat, c :- CompRow] (=> (= (adm-comp y c) true) (= (:id c) y))
  (intro h) (simp only [adm-comp Bool.and_eq_true] at h) (exact (Nat.eq_of_beq_eq_true (And.left h))))
(a/theorem adm-task-id [y :- Nat, c :- TaskRow] (=> (= (adm-task y c) true) (= (:id c) y))
  (intro h) (simp only [adm-task Bool.and_eq_true] at h) (exact (Nat.eq_of_beq_eq_true (And.left h))))
(a/theorem adm-source-id [y :- Nat, c :- SourceRow] (=> (= (adm-source y c) true) (= (:id c) y))
  (intro h) (simp only [adm-source Bool.and_eq_true] at h) (exact (Nat.eq_of_beq_eq_true (And.left h))))
(a/theorem adm-pub-id [y :- Nat, c :- PubRow] (=> (= (adm-pub y c) true) (= (:id c) y))
  (intro h) (simp only [adm-pub Bool.and_eq_true] at h) (exact (Nat.eq_of_beq_eq_true (And.left h))))

(a/theorem scope-not-admitted [w :- World, s :- ScopeRow]
  (=> (= (inv-sample w) true) (List.Mem s (:scopes w)) (= (admitted w (:id s)) false))
  (intros hs ms)
  (have u := (ids-unique-of w hs))
  (simp only [all-ids] at u)
  (have hm (= (nat-mem (:id s) (tbl-ids scope-id (:scopes w))) true)) (exact (mem-ids-has ScopeRow scope-id s (:scopes w) ms))
  (have d := (nodup-app-disj (:id s) _ _ u hm))
  (simp only [nat-mem-app Bool.or_eq_false_iff nat-mem-ids] at d)
  (have c0 (= (tbl-any (adm-comp (:id s)) (:comps w)) false))
  (cases ha (tbl-any (adm-comp (:id s)) (:comps w))) (rfl)
  (have z := (any-id-has CompRow comp-id (adm-comp (:id s)) (:id s) (:comps w)
               (fn [c :- CompRow, hc :- (= (adm-comp (:id s) c) true)] (adm-comp-id (:id s) c hc)) ha))
  (rw [(And.left d)] at z) (cases z)
  (have t0 (= (tbl-any (adm-task (:id s)) (:tasks w)) false))
  (cases ha (tbl-any (adm-task (:id s)) (:tasks w))) (rfl)
  (have z := (any-id-has TaskRow task-id (adm-task (:id s)) (:id s) (:tasks w)
               (fn [c :- TaskRow, hc :- (= (adm-task (:id s) c) true)] (adm-task-id (:id s) c hc)) ha))
  (rw [(And.left (And.right d))] at z) (cases z)
  (have x0 (= (tbl-any (adm-source (:id s)) (:sources w)) false))
  (cases ha (tbl-any (adm-source (:id s)) (:sources w))) (rfl)
  (have z := (any-id-has SourceRow source-id (adm-source (:id s)) (:id s) (:sources w)
               (fn [c :- SourceRow, hc :- (= (adm-source (:id s) c) true)] (adm-source-id (:id s) c hc)) ha))
  (rw [(And.left (And.right (And.right (And.right d))))] at z) (cases z)
  (have p0 (= (tbl-any (adm-pub (:id s)) (:pubs w)) false))
  (cases ha (tbl-any (adm-pub (:id s)) (:pubs w))) (rfl)
  (have z := (any-id-has PubRow pub-id (adm-pub (:id s)) (:id s) (:pubs w)
               (fn [c :- PubRow, hc :- (= (adm-pub (:id s) c) true)] (adm-pub-id (:id s) c hc)) ha))
  (rw [(And.left (And.right (And.right (And.right (And.right (And.right (And.right (And.right d))))))))] at z) (cases z)
  (simp only [admitted c0 t0 x0 p0 Bool.or_self]))

;; a live scope's parent is live (the parent edge of §3.2)
(a/theorem live-parent [w :- World, s :- ScopeRow]
  (=> (List.Mem s (:scopes w)) (= (Nat.beq (:parent s) 0) false) (= (in-live w (:id s)) true)
      (= (in-live w (:parent s)) true))
  (intros ms hp hl)
  (have g (= (reach-mem (:parent s) (tbl-gather (id-is scope-id (:id s)) (scope-contrib w) (:scopes w))) true))
  (apply (gather-mem ScopeRow (id-is scope-id (:id s)) (scope-contrib w) s (:parent s) (:scopes w) ms))
  (simp only [id-is scope-id Nat.beq_refl])
  (simp [scope-contrib nz hp reach-mem-append reach-mem-app reach-mem-cons Nat.beq_refl])
  (apply (live-close w (:id s) (:parent s) hl))
  (simp [retain-succ reach-mem-append reach-mem-app g]))

;; ===========================================================================
;; Part C. The filter keeps every kept scope's parent
;; ===========================================================================

(a/theorem tbl-all-keep-mem [A :- Type, K :- (=> Nat Bool), idf :- (=> A Nat), P :- (=> A Bool), Q :- (=> A Bool), xs :- (List A)]
  (=> (forall [r :- A] (=> (List.Mem r xs) (= (P r) true) (= (K (idf r)) true) (= (Q r) true)))
      (= (tbl-all P xs) true) (= (tbl-all Q (tbl-keep K idf xs)) true))
  (induction xs)
  (case [nil] (intros h hp) (simp [tbl-keep tbl-all]))
  (case [cons hd t ih]
    (intros h hp)
    (simp only [tbl-all Bool.and_eq_true] at hp)
    (have ht (forall [r :- A] (=> (List.Mem r t) (= (P r) true) (= (K (idf r)) true) (= (Q r) true))))
    (intros r mr pr kr) (exact (h r (List.Mem.tail hd mr) pr kr))
    (cases hk (K (idf hd)))
    (case [false] (simp only [tbl-keep hk]) (exact (ih ht (And.right hp))))
    (case [true]
      (simp only [tbl-keep hk tbl-all Bool.and_eq_true])
      (exact (And.intro (h hd (List.Mem.head t) (And.left hp) hk) (ih ht (And.right hp)))))))

(a/theorem filter-lit-i1-scope [w :- World]
  (=> (= (inv-sample w) true) (= (lit-i1-scope w) true)
      (= (lit-i1-scope (rule-r-filter w)) true))
  (intros hs hl)
  (rw [rule-r-filter-eq])
  (simp only [lit-i1-scope fw-scopes])
  (simp only [lit-i1-scope] at hl)
  (apply (tbl-all-keep-mem ScopeRow (keep-fn w) scope-id (lit-scope-parent w) (lit-scope-parent (filter-world (keep-fn w) w)) (:scopes w) _ hl))
  (intros s ms ps ks)
  (cases hk (Nat.beq (:kind s) scope-root))
  (case [true] (simp only [lit-scope-parent hk Bool.true_or]))
  (case' [false])
    (cases hp (Nat.beq (:parent s) 0))
    (case [true] (simp only [lit-scope-parent hk hp Bool.true_or Bool.false_or]))
    (case' [false])
      (have hh (= (scope-has w (:parent s)) true))
      (simp only [lit-scope-parent hk hp Bool.false_or] at ps) (exact ps)
      (have k2 (= (keep-with w (live-list w) (cleanup-rows w) (storage w) (:id s)) true)) (exact ks)
      (simp only [keep-with Bool.or_eq_true] at k2)
      (have kp (= (keep-fn w (:parent s)) true))
      (cases k2)
      (case [inl a] (exact (keep-of-live w (:parent s) (live-parent w s ms hp a))))
      (case' [inr b])
        (cases b)
        (case [inl c]
          (have q := (cleanup-closed w (:cleanup w) (:id s) (:parent s) c (scope-up-of-mem w s hs ms hp)))
          (have q2 (= (reach-mem (:parent s) (cleanup-rows w)) true)) (exact q)
          (simp only [keep-fn keep-with q2 Bool.true_or Bool.or_true]))
        (case' [inr d])
          (cases d)
          (case [inl e] (have z := (scope-not-admitted w s hs ms)) (rw [z] at e) (cases e))
          (case' [inr f])
            (have q (= (reach-mem (:parent s) (storage w)) true))
            (exact (anc-close-closed w (storage-gather w (live-list w)) (:id s) (:parent s) f (scope-up-of-mem w s hs ms hp)))
            (simp only [keep-fn keep-with q Bool.or_true])
      (simp only [lit-scope-parent hk hp scope-has fw-scopes tbl-has-keep Bool.false_or])
      (have hh2 (= (tbl-has scope-id (:parent s) (:scopes w)) true)) (exact hh)
      (simp only [kp hh2 Bool.and_self]))

;; ===========================================================================
;; Part D. The bundle g1 = inv-sample && lit-i1-scope through the transition and normalization
;; ===========================================================================

(a/defn g1-rest [w :- World] Bool (lit-i1-scope w))
(a/defn g1 [w :- World] Bool (Bool.and (inv-sample w) (g1-rest w)))
(a/theorem g1-sample [w :- World] (=> (= (g1 w) true) (= (inv-sample w) true))
  (intro h) (simp only [g1 Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem g1-rest-of [w :- World] (=> (= (g1 w) true) (= (g1-rest w) true))
  (intro h) (simp only [g1 Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem g1-intro [w :- World] (=> (= (inv-sample w) true) (= (g1-rest w) true) (= (g1 w) true))
  (intros h1 h2) (simp only [g1 h1 h2 Bool.and_self]))
(a/theorem g1-parts [w :- World]
  (=> (= (g1 w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (g1-sample w h))))

;; ---- scope rows updated in place

(a/theorem tbl-all-upd-gen [A :- Type, idf :- (=> A Nat), x :- Nat, f :- (=> A A), P :- (=> A Bool), Q :- (=> A Bool), xs :- (List A)]
  (=> (forall [r :- A] (=> (List.Mem r xs) (= (P r) true) (= (Q (f r)) true)))
      (forall [r :- A] (=> (List.Mem r xs) (= (P r) true) (= (Q r) true)))
      (= (tbl-all P xs) true) (= (tbl-all Q (tbl-upd idf x f xs)) true))
  (induction xs)
  (case [nil] (intros h1 h2 hp) (simp [tbl-upd tbl-all]))
  (case [cons hd t ih]
    (intros h1 h2 hp)
    (simp only [tbl-all Bool.and_eq_true] at hp)
    (have t1 (forall [r :- A] (=> (List.Mem r t) (= (P r) true) (= (Q (f r)) true)))) (intros r mr pr) (exact (h1 r (List.Mem.tail hd mr) pr))
    (have t2 (forall [r :- A] (=> (List.Mem r t) (= (P r) true) (= (Q r) true)))) (intros r mr pr) (exact (h2 r (List.Mem.tail hd mr) pr))
    (have r1 := (ih t1 t2 (And.right hp)))
    (cases hx (Nat.beq (idf hd) x))
    (case [true] (simp only [tbl-upd hx tbl-all r1 (h1 hd (List.Mem.head t) (And.left hp)) Bool.and_self]))
    (case [false] (simp only [tbl-upd hx tbl-all r1 (h2 hd (List.Mem.head t) (And.left hp)) Bool.and_self]))))

(a/theorem lsp-upd [w :- World, x :- Nat, f :- (=> ScopeRow ScopeRow), hf :- (forall [s :- ScopeRow] (= (scope-id (f s)) (scope-id s))), r :- ScopeRow]
  (= (lit-scope-parent (scope-upd w x f) r) (lit-scope-parent w r))
  (simp only [lit-scope-parent scope-has scope-upd set-scopes (tbl-has-upd ScopeRow scope-id x (:parent r) f hf (:scopes w))]))

(a/theorem g1-scope-upd-ok [w :- World, x :- Nat, f :- (=> ScopeRow ScopeRow),
                            hf :- (forall [s :- ScopeRow] (= (scope-id (f s)) (scope-id s))),
                            hr :- (forall [s :- ScopeRow] (=> (List.Mem s (:scopes w)) (= (lit-scope-parent w s) true) (= (lit-scope-parent w (f s)) true)))]
  (=> (= (g1 w) true) (= (g1 (scope-upd w x f)) true))
  (intro h)
  (have r (= (g1-rest (scope-upd w x f)) true))
  (have h0 := (g1-rest-of w h)) (simp only [g1-rest lit-i1-scope] at h0)
  (simp only [g1-rest lit-i1-scope])
  (apply (tbl-all-upd-gen ScopeRow scope-id x f (lit-scope-parent w) (lit-scope-parent (scope-upd w x f)) (:scopes w) _ _ h0))
  (intros s ms ps) (rw [(lsp-upd w x f hf (f s))]) (exact (hr s ms ps))
  (intros s ms ps) (rw [(lsp-upd w x f hf s)]) (exact ps)
  (exact (g1-intro _ (inv-scope-upd w x f hf (g1-sample w h)) r)))

;; the copier's form: f keeps (id, kind, parent)
(a/theorem g1-scope-upd [w :- World, x :- Nat, f :- (=> ScopeRow ScopeRow),
                         hf :- (forall [s :- ScopeRow] (= (scope-id (f s)) (scope-id s))),
                         hk :- (forall [s :- ScopeRow] (= (skw (f s)) (skw s)))]
  (=> (= (g1 w) true) (= (g1 (scope-upd w x f)) true))
  (intro h)
  (apply (g1-scope-upd-ok w x f hf _ h))
  (intros s ms ps)
  (have e1 (= (:kind (f s)) (:kind s))) (exact (congrArg (fn [k :- SKW] (:kind k)) (hk s)))
  (have e2 (= (:parent (f s)) (:parent s))) (exact (congrArg (fn [k :- SKW] (:parent k)) (hk s)))
  (simp only [lit-scope-parent e1 e2]) (exact ps))

;; detach: the run scope gets an existing parent
(a/theorem g1-set-parent [w :- World, x :- Nat, p :- Nat]
  (=> (= (scope-has w p) true) (= (g1 w) true) (= (g1 (scope-upd w x (scope-set-parent p))) true))
  (intros hp h)
  (apply (g1-scope-upd-ok w x (scope-set-parent p) (scope-set-parent-id p) _ h))
  (intros s ms ps)
  (simp only [lit-scope-parent scope-set-parent hp Bool.or_true]))

;; ---- a new scope with an existing parent (or none)

(a/theorem has-cons-r [A :- Type, idf :- (=> A Nat), y :- Nat, h :- A, t :- (List A)]
  (=> (= (tbl-has idf y t) true) (= (tbl-has idf y (List.cons A h t)) true))
  (intro e) (cases hb (Nat.beq (idf h) y)) (all_goals (simp only [tbl-has hb e Bool.true_or Bool.or_true])))

(a/theorem g1-scope-ins-fresh [w :- World, r :- ScopeRow]
  (=> (= (scope-id r) (:next-id w)) (= (Bool.or (Nat.beq (:parent r) 0) (scope-has w (:parent r))) true)
      (= (g1 w) true) (= (g1 (bump (scope-ins w r))) true))
  (intros hr hp h)
  (have h0 := (g1-rest-of w h)) (simp only [g1-rest lit-i1-scope] at h0)
  (have mono (forall [s :- ScopeRow] (=> (= (lit-scope-parent w s) true) (= (lit-scope-parent (scope-ins w r) s) true))))
  (intros s ps)
  (simp only [lit-scope-parent Bool.or_eq_true] at ps)
  (simp only [lit-scope-parent Bool.or_eq_true])
  (cases ps)
  (case [inl a] (exact (Or.inl a)))
  (case [inr b]
    (cases b)
    (case [inl c] (exact (Or.inr (Or.inl c))))
    (case [inr d] (exact (Or.inr (Or.inr (has-cons-r ScopeRow scope-id (:parent s) r (:scopes w) d))))))
  (have hnew (= (lit-scope-parent (scope-ins w r) r) true))
  (simp only [Bool.or_eq_true] at hp)
  (simp only [lit-scope-parent Bool.or_eq_true])
  (cases hp)
  (case [inl a] (exact (Or.inr (Or.inl a))))
  (case [inr b] (exact (Or.inr (Or.inr (has-cons-r ScopeRow scope-id (:parent r) r (:scopes w) b)))))
  (have r1 (= (g1-rest (scope-ins w r)) true))
  (have es (= (:scopes (scope-ins w r)) (List.cons ScopeRow r (:scopes w)))) (rfl)
  (have tm := (tbl-all-mono ScopeRow (lit-scope-parent w) (lit-scope-parent (scope-ins w r)) mono (:scopes w) h0))
  (simp only [g1-rest lit-i1-scope es tbl-all hnew tm Bool.and_self])
  (have r2 (= (g1-rest (bump (scope-ins w r))) true)) (exact r1)
  (exact (g1-intro _ (inv-scope-ins-fresh w r hr (g1-sample w h)) r2)))

;; ---- remove-if-empty: the subtree goes as a whole (no scope outside it has its parent in it)

(a/defn not-in [sub :- (List Nat), y :- Nat] Bool (Bool.not (reach-mem y sub)))
(a/theorem keep-del [A :- Type, K :- (=> Nat Bool), idf :- (=> A Nat), x :- Nat, xs :- (List A)]
  (= (tbl-keep K idf (tbl-del idf x xs)) (tbl-keep (fn [y :- Nat] (Bool.and (Bool.not (Nat.beq y x)) (K y))) idf xs))
  (induction xs)
  (case [nil] (simp only [tbl-del tbl-keep]))
  (case [cons h t ih]
    (cases hx (Nat.beq (idf h) x))
    (all_goals (cases hk (K (idf h))))
    (all_goals (simp only [tbl-del tbl-keep hx hk ih Bool.not_true Bool.not_false Bool.false_and Bool.true_and]))))
(a/theorem keep-ext [A :- Type, K :- (=> Nat Bool), K2 :- (=> Nat Bool), idf :- (=> A Nat), xs :- (List A),
                     he :- (forall [y :- Nat] (= (K y) (K2 y)))]
  (= (tbl-keep K idf xs) (tbl-keep K2 idf xs))
  (induction xs)
  (case [nil] (simp only [tbl-keep]))
  (case [cons h t ih] (simp only [tbl-keep (he (idf h)) ih])))
(a/theorem keep-true [A :- Type, idf :- (=> A Nat), xs :- (List A)]
  (= (tbl-keep (fn [y :- Nat] true) idf xs) xs)
  (induction xs) (case [nil] (simp only [tbl-keep])) (case [cons h t ih] (simp only [tbl-keep ih])))
(a/theorem scope-del-fold-k [sub :- (List Nat)]
  (forall [w :- World, K :- (=> Nat Bool)]
    (= (tbl-keep K scope-id (:scopes (nat-fold scope-del w sub))) (tbl-keep (fn [y :- Nat] (Bool.and (not-in sub y) (K y))) scope-id (:scopes w))))
  (induction sub)
  (case [nil]
    (intros w K) (simp only [nat-fold]))
  (case [cons x t ih]
    (intros w K) (simp only [nat-fold])
    (rw [(ih (scope-del w x) K)])
    (simp only [scope-del set-scopes keep-del])
    (apply keep-ext) (intro y)
    (cases hy (Nat.beq y x))
    (all_goals (simp only [not-in reach-mem-cons hy Bool.not_true Bool.not_false Bool.false_and Bool.true_and Bool.false_or Bool.true_or Bool.and_assoc]))))
(a/theorem scope-del-fold [sub :- (List Nat), w :- World]
  (= (:scopes (nat-fold scope-del w sub)) (tbl-keep (not-in sub) scope-id (:scopes w)))
  (have a := (scope-del-fold-k sub w (fn [y :- Nat] true)))
  (rw [keep-true] at a)
  (rw [a])
  (apply keep-ext) (intro y) (simp only [Bool.and_true]))
(a/theorem g1-remove-if-empty [w :- World, sub :- (List Nat)]
  (=> (= (g1 w) true) (= (g1 (remove-if-empty w sub)) true))
  (intro h)
  (have i := (inv-remove-if-empty w sub (g1-sample w h)))
  (cases he (subtree-empty w sub))
  (case [false] (simp only [remove-if-empty he]) (exact h))
  (case' [true])
  (have po (= (tbl-all (parent-outside sub) (:scopes w)) true))
  (simp only [subtree-empty Bool.and_eq_true] at he) (exact (And.left he))
  (simp only [remove-if-empty he] at i)
  (simp only [remove-if-empty he])
  (have h0 := (g1-rest-of w h)) (simp only [g1-rest lit-i1-scope] at h0)
  (have hsd (forall [y :- Nat] (= (scope-has (nat-fold scope-del w sub) y) (Bool.and (not-in sub y) (scope-has w y)))))
  (intro y) (simp only [scope-has scope-del-fold tbl-has-keep])
  (have r (= (g1-rest (nat-fold scope-del w sub)) true))
  (simp only [g1-rest lit-i1-scope])
  (rw [scope-del-fold])
  (apply (tbl-all-keep-mem ScopeRow (not-in sub) scope-id (lit-scope-parent w) (lit-scope-parent (nat-fold scope-del w sub)) (:scopes w) _ h0))
  (intros s ms ps ks)
  (have pos := (tbl-all-mem ScopeRow _ s _ po ms))
  (have nin (Or (= (Nat.beq (:kind s) scope-root) true) (Or (= (Nat.beq (:parent s) 0) true) (= (not-in sub (:parent s)) true))))
  (simp only [parent-outside Bool.or_eq_true] at pos)
  (cases pos)
  (case [inl e] (simp only [not-in scope-id e Bool.not_true] at ks) (cases ks))
  (case [inr f2] (exact (Or.inr (Or.inr f2))))
  (simp only [lit-scope-parent Bool.or_eq_true] at ps)
  (simp only [lit-scope-parent hsd Bool.or_eq_true Bool.and_eq_true])
  (cases ps)
  (case [inl a] (exact (Or.inl a)))
  (case [inr b]
    (cases b)
    (case [inl c] (exact (Or.inr (Or.inl c))))
    (case [inr d]
      (cases nin)
      (case [inl a2] (exact (Or.inl a2)))
      (case [inr b2]
        (cases b2)
        (case [inl c2] (exact (Or.inr (Or.inl c2))))
        (case [inr d2] (exact (Or.inr (Or.inr (And.intro d2 d))))))))
  (exact (g1-intro _ i r)))

(a/theorem open-at-has [w :- World, s :- Nat] (=> (= (scope-open-at w s) true) (= (scope-has w s) true))
  (intro h)
  (cases hf (scope-find w s))
  (case [none] (simp only [scope-open-at hf] at h) (cases h))
  (case [some sc] (exact (tbl-find-has ScopeRow scope-id s sc (:scopes w) hf))))

(a/theorem tsp-has [w :- World, owner :- Nat]
  (= (Bool.or (Nat.beq (task-scope-parent w owner) 0) (scope-has w (task-scope-parent w owner))) true)
  (cases hs (scope-has w owner))
  (case [true] (simp only [task-scope-parent hs Bool.or_true]))
  (case [false] (simp only [task-scope-parent hs Nat.beq_refl Bool.true_or])))

;; ---- run + run scope (T4 / T5 / T11), the parent given

(a/theorem g1-add-run-scope [w :- World, of :- Nat, epoch :- Nat, parent :- Nat, ei :- Nat]
  (=> (= (Bool.or (Nat.beq parent 0) (scope-has w parent)) true) (= (g1 w) true)
      (= (g1 (add-run-scope w of epoch parent ei)) true))
  (intros hp h)
  (simp only [add-run-scope])
  (have h1 (= (g1 (bump (run-ins w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei)))) true))
  (exact (g1-intro _ (inv-run-ins-fresh w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei) (rfl) (g1-sample w h)) (g1-rest-of w h)))
  (have he (= (scope-id (new-scope-row (+ (:next-id w) 1) parent))
              (:next-id (bump (run-ins w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei))))))
  (rfl)
  (exact (g1-scope-ins-fresh _ (new-scope-row (+ (:next-id w) 1) parent) he hp h1)))

;; ===========================================================================
;; Part E. The copy
;; ===========================================================================

(def G1 (mk-bundle 'g1 [] "g1-" {'inv-scope-upd ['(fn [s :- ScopeRow] (Eq.refl (skw s))) 4]}))
(swap! (:renames G1) assoc 'inv-parts 'g1-parts 'inv-scope-upd 'g1-scope-upd 'inv-scope-ins-fresh 'g1-scope-ins-fresh
       'inv-remove-if-empty 'g1-remove-if-empty 'inv-add-run-scope 'g1-add-run-scope)
(doseq [o '[inv-run-upd inv-pub-upd inv-source-upd inv-resource-upd inv-cleanup-upd inv-cleanup-del inv-task-upd inv-comp-upd
            inv-set-pins inv-resource-del inv-cleanup-ins inv-act-upd inv-edge-upd inv-drop-cred inv-drop-edges inv-drop-act
            inv-comp-del-unref inv-run-del inv-bump inv-source-ins-fresh inv-resource-ins-fresh inv-act-ins-fresh inv-comp-ins-fresh
            inv-task-ins-fresh insert-edge-fresh-inv-sample]]
  (prim! G1 o nil))
(a/theorem g1-rest-mark-edge [w :- World, x :- Nat] (= (g1-rest (mark-edge w x)) (g1-rest w))
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [mark-edge hf hm]))))
(a/theorem g1-rest-unmark-edge [w :- World, x :- Nat] (= (g1-rest (unmark-edge w x)) (g1-rest w))
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [unmark-edge hf hm]))))
(a/theorem g1-rest-remove-edge [w :- World, x :- Nat] (= (g1-rest (remove-edge w x)) (g1-rest w))
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [remove-edge hf hm]))))
(prim! G1 'mark-edge-inv-sample '(Eq.trans (g1-rest-mark-edge w x) R))
(prim! G1 'unmark-edge-inv-sample '(Eq.trans (g1-rest-unmark-edge w x) R))
(prim! G1 'inv-remove-edge '(Eq.trans (g1-rest-remove-edge w x) R))

;; callers of add-run-scope: a computation run scope has parent 0 (Z#26), a task run scope its owner
;; scope when that exists (task-scope-parent)
(defn- add-hp [form] (subst-forms (app-of? 'inv-add-run-scope) (fn [y] (concat (take 6 y) ['(Eq.refl true)] (drop 6 y))) form))
(patch! G1 'inv-start-raw add-hp)
(patch! G1 'inv-new-run-of add-hp)
(override! G1 'inv-spawn-rows '[]
  '(a/theorem g1-spawn-rows [w :- World, owner :- Nat, inputs :- (List Nat)]
     (=> (= (g1 w) true) (= (g1 (spawn-rows w owner inputs)) true))
     (intro h)
     (simp only [spawn-rows])
     (have h1 (= (g1 (bump (task-ins w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs)))) true))
     (exact (g1-task-ins-fresh w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs) (rfl) h))
     (exact (g1-add-run-scope (bump (task-ins w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs)))
              (:next-id w) 0 (task-scope-parent w owner) 0 (tsp-has w owner) h1))))
(override! G1 't-open-scope-inv '[]
  '(a/theorem t-open-scope-g1 [w :- World, st :- Nat, s :- Nat]
     (=> (= (g1 w) true) (= (g1 (:world (t-open-scope w st s))) true))
     (intro h)
     (cases ht (tok-run w st)) (case' [some r]) (case' [none])
     (simp only [t-open-scope ht refuse]) (exact h)
     (cases hg (Bool.and (Nat.beq s (:next-id w)) (open-ok w r)))
     (simp only [t-open-scope ht hg refuse]) (exact h)
     (have hs (= s (:next-id w))) (simp only [Bool.and_eq_true Nat.beq_eq] at hg) (exact (And.left hg))
     (have hc (= (Bool.or (Nat.beq (cur-scope w r) 0) (scope-has w (cur-scope w r))) true))
     (simp only [open-ok Bool.and_eq_true] at hg) (simp only [(And.right (And.right hg)) Bool.or_true])
     (simp only [t-open-scope ht hg accept])
     (exact (g1-scope-ins-fresh w (ScopeRow.mk s (cur-scope w r) scope-explicit true) hs hc h))))
(override! G1 't-detach-inv '[]
  '(a/theorem t-detach-g1 [w :- World, k :- Nat, s :- Nat]
     (=> (= (g1 w) true) (= (g1 (:world (t-detach w k s))) true))
     (intro h)
     (cases hf (task-find w k))
     (case [none] (simp only [t-detach hf refuse]) (exact h))
     (case [some t]
       (cases hg (detach-ok w t s))
       (case [false] (simp only [t-detach hf hg refuse]) (exact h))
       (case [true]
         (have hs2 (= (scope-has w s) true))
         (simp only [detach-ok Bool.and_eq_true] at hg) (exact (open-at-has w s (And.right (And.right hg))))
         (simp only [t-detach hf hg accept remove-empty-at detach-move])
         (have h1 := (g1-task-upd w k (task-set-owner s) (task-set-owner-id s) h))
         (exact (g1-remove-if-empty _ _ (g1-set-parent (task-upd w k (task-set-owner s)) (task-run-scope w t) s hs2 h1)))))))

(lcopy! G1 'raw-inv)
(lcopy! G1 'inv-normalize)

;; ===========================================================================
;; Part F. Rule R and the step
;; ===========================================================================

(a/theorem g1-rule-r-round [w :- World]
  (=> (= (g1 w) true) (= (filter-safe (normalize w)) true) (= (g1 (rule-r-round w)) true))
  (intros h hf)
  (have hn := (g1-normalize w h))
  (simp only [rule-r-round])
  (exact (g1-intro _ (inv-rule-r-filter (normalize w) (g1-sample _ hn) hf)
           (filter-lit-i1-scope (normalize w) (g1-sample _ hn) (g1-rest-of _ hn)))))
(a/theorem g1-rr-loop [fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (g1 w0) true) (= (rr-safe fuel w0) true) (= (g1 (rr-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 h hs) (simp only [rr-safe] at hs) (simp only [rr-loop]) (exact (g1-rule-r-round w0 h hs)))
  (case [cons x f ih]
    (intros w0 h hs)
    (simp only [rr-safe Bool.and_eq_true] at hs)
    (have h1 := (g1-rule-r-round w0 h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false] (simp only [ho] at hs) (simp only [rr-loop ho]) (exact (ih (rule-r-round w0) h1 (And.right hs))))
    (case [true] (simp only [rr-loop ho]) (exact h1))))
(a/theorem g1-rule-r [w :- World] (=> (= (g1 w) true) (= (rule-r-safe w) true) (= (g1 (rule-r w)) true))
  (intros h hs) (simp only [rule-r-safe] at hs) (simp only [rule-r]) (exact (g1-rr-loop (rr-fuel w) w h hs)))
(a/theorem step-g1 [w :- World, it :- Item]
  (=> (= (g1 w) true) (= (rule-r-safe (:world (raw w it))) true) (= (g1 (:world (world-step w it))) true))
  (intros h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true] (have e2 := (step-accepted w it ha)) (rw [e2]) (exact (g1-rule-r (:world (raw w it)) (raw-g1 w it h) hs))))
(a/theorem g1-empty [] (= (g1 empty-world) true) (rfl))

;; the combined bundle: p3e = p3d && g1 (no honest hypothesis)
(a/defn p3e [w :- World] Bool (Bool.and (p3d w) (g1 w)))
(a/theorem p3e-parts [w :- World] (=> (= (p3e w) true) (And (= (p3d w) true) (= (g1 w) true)))
  (intro h) (simp only [p3e Bool.and_eq_true] at h) (exact h))
(a/theorem p3e-empty [] (= (p3e empty-world) true) (rfl))
(a/theorem step-p3e [w :- World, it :- Item] (=> (= (p3e w) true) (= (p3e (:world (world-step w it))) true))
  (intro h)
  (have p := (p3e-parts w h))
  (have pd := (p3d-parts w (And.left p)))
  (have pc := (p3c-parts w (And.left pd)))
  (have a1 := (step-p3d w it (And.left p)))
  (have a2 := (step-g1 w it (And.right p) (step-rule-r-safe w it (And.left pc))))
  (simp only [p3e a1 a2 Bool.and_self]))
(a/theorem step-lit-i1-scope-total [w :- World, it :- Item]
  (=> (= (p3e w) true) (= (lit-i1-scope (:world (world-step w it))) true))
  (intro h) (exact (g1-rest-of _ (And.right (p3e-parts _ (step-p3e w it h))))))
