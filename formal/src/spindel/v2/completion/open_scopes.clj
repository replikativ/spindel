(ns ^:ansatz/lean spindel.v2.completion.open-scopes
  "C1c stage A, the proof stage (questions 10 and 14): every open non-root scope lies in the run-scope subtree
  of a run row, through every step, kernel-checked (Init only). So a world with no run has no open non-root
  scope (spindel.v2.completion.quiet-world `quiet-root-only`: a quiet world holds the root scope only).

    os-need s   s is open and not root-kind
    hw w y      some run row's run scope is y or on y's parent chain (`scope-within`, Z#69's chain)
    open-scopes-have-runs w       well-formed w and `open-scopes-have-runs-rest`: every scope row with os-need has hw

  Why it holds: a run scope is created with its run (`add-run-scope`); an explicit scope is opened under the
  run's current scope (`cur-scope`: the run scope or an open explicit scope below it, whose witness it inherits);
  detach re-parents a task's run scope, which its own run witnesses, and a chain through it keeps that witness;
  closing only removes obligations; scope deletion (Z#18 `remove-if-empty`) and Rule R's filter keep the parent of
  every scope they keep (`parent-outside`; i1's closure of the keep set), so kept chains are unchanged; a run row
  is deleted only by T13 (`retire-run`), after its whole run-scope subtree is closed (`scope-subtree`
  converges: `sub-conv`, so the subtree holds every scope whose chain reaches the run scope); and Rule R's filter
  keeps every run (spindel.v2.inv.i1-runs `run-kept`: normalized, i1-runs).

  Both bundles go through the generic step tree (spindel.v2.pres.tree). T13's run deletion needs, between the close of
  the subtree and the deletion, a witness other than the retiring run: the parametric bundle `open-scopes-have-runs-exempt x` (every scope
  row with os-need has a witness run whose id is not x) is copied over the source closes of `close-local`.

  Theorems: step-open-scopes-have-runs (acts-parked, i1-runs, open-scopes-have-runs, rule-r-safe raw -> open-scopes-have-runs after the step), open-scopes-have-runs-empty."
  (:require [ansatz.core :as a]
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
            [spindel.v2.pres.tree :as tree]
            [spindel.v2.pres.part :refer :all]
            [spindel.v2.inv.copier :refer :all]
            [spindel.v2.inv.base :refer :all]
            [spindel.v2.inv.acyclic :refer [cy-par]]
            [spindel.v2.inv.i1-scopes :refer [not-in]]
            [spindel.v2.inv.i1-runs :refer [i1-runs]]
            [spindel.v2.inv.i1-owners]))

;; ===========================================================================
;; Part A. The invariant
;; ===========================================================================

(a/defn os-need [s :- ScopeRow] Bool (Bool.and (:open s) (Bool.not (Nat.beq (:kind s) scope-root))))
(a/defn run-within [w :- World, y :- Nat, q :- RunRow] Bool (scope-within w y (:scope q)))
(a/defn hw [w :- World, y :- Nat] Bool (tbl-any (run-within w y) (:runs w)))
(a/defn os-ok [w :- World, s :- ScopeRow] Bool (Bool.or (Bool.not (os-need s)) (hw w (:id s))))
(a/defn open-scopes-have-runs-rest [w :- World] Bool (tbl-all (os-ok w) (:scopes w)))
(a/defn open-scopes-have-runs [w :- World] Bool (Bool.and (well-formed w) (open-scopes-have-runs-rest w)))

(a/theorem open-scopes-have-runs-well-formed [w :- World] (=> (= (open-scopes-have-runs w) true) (= (well-formed w) true))
  (intro h) (simp only [open-scopes-have-runs Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem open-scopes-have-runs-rest-of [w :- World] (=> (= (open-scopes-have-runs w) true) (= (open-scopes-have-runs-rest w) true))
  (intro h) (simp only [open-scopes-have-runs Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem open-scopes-have-runs-intro [w :- World] (=> (= (well-formed w) true) (= (open-scopes-have-runs-rest w) true) (= (open-scopes-have-runs w) true))
  (intros h1 h2) (simp only [open-scopes-have-runs h1 h2 Bool.and_self]))
(a/theorem open-scopes-have-runs-parts [w :- World]
  (=> (= (open-scopes-have-runs w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (open-scopes-have-runs-well-formed w h))))

;; ===========================================================================
;; Part B. Chains (scope-within as Reach over the parent function)
;; ===========================================================================

(a/theorem wi-of [w :- World, y :- Nat, a :- Nat]
  (=> (= (scope-within w y a) true) (Or (= y a) (Reach (scope-up w) (scope-up w y) a)))
  (intro h)
  (simp only [scope-within Bool.or_eq_true] at h)
  (cases h)
  (case [inl e] (exact (Or.inl (Nat.eq_of_beq_eq_true e))))
  (case [inr r] (exact (Or.inr (Iff.mp (cy-anc-iff w y a) r)))))
(a/theorem wi-intro [w :- World, y :- Nat, a :- Nat]
  (=> (Or (= y a) (Reach (scope-up w) (scope-up w y) a)) (= (scope-within w y a) true))
  (intro h)
  (simp only [scope-within Bool.or_eq_true])
  (cases h)
  (case [inl e] (rw [e]) (exact (Or.inl (Nat.beq_refl a))))
  (case [inr r] (exact (Or.inr (Iff.mpr (cy-anc-iff w y a) r)))))
(a/theorem wi-self [w :- World, y :- Nat] (= (scope-within w y y) true)
  (exact (wi-intro w y y (Or.inl (Eq.refl y)))))

;; more parent edges: every chain survives
(a/theorem wi-mono [w :- World, w2 :- World, y :- Nat, a :- Nat]
  (=> (forall [z :- Nat, x :- Nat] (=> (List.Mem x (scope-up w z)) (List.Mem x (scope-up w2 z))))
      (= (scope-within w y a) true) (= (scope-within w2 y a) true))
  (intros hs h)
  (apply (wi-intro w2 y a))
  (have o := (wi-of w y a h))
  (cases o)
  (case [inl e] (exact (Or.inl e)))
  (case [inr r] (exact (Or.inr (cy-reach-sub (scope-up w2) (scope-up w) (scope-up w2 y) (scope-up w y) a (hs y) hs r)))))

;; a chain from c, prefixed by c
(a/theorem reach-pre [u :- (=> Nat (List Nat)), c :- Nat, a :- Nat, R :- (List Nat)]
  (=> (List.Mem c R) (Reach u (u c) a) (Reach u R a))
  (intros hc h)
  (induction h)
  (case [root x hx] (exact (Reach.step c x (Reach.root c hc) hx)))
  (case [step p q hp hq ih] (exact (Reach.step p q ih hq))))

;; re-parenting x: a chain either survives or reaches x
(a/theorem rp-reach [u :- (=> Nat (List Nat)), v :- (=> Nat (List Nat)), x :- Nat, y :- Nat, a :- Nat]
  (=> (forall [z :- Nat] (=> (= (Nat.beq z x) false) (= (v z) (u z))))
      (Reach u (u y) a)
      (Or (Reach v (v y) a) (Or (= y x) (Reach v (v y) x))))
  (intros he h)
  (induction h)
  (case [root b hb]
    (cases hy (Nat.beq y x))
    (case [true] (exact (Or.inr (Or.inl (Nat.eq_of_beq_eq_true hy)))))
    (case [false] (rw [← (he y hy)] at hb) (exact (Or.inl (Reach.root b hb)))))
  (case [step p q hp hq ih]
    (cases ih)
    (case [inl r]
      (cases hpx (Nat.beq p x))
      (case [true] (have e := (Nat.eq_of_beq_eq_true hpx)) (rw [e] at r) (exact (Or.inr (Or.inr r))))
      (case [false] (rw [← (he p hpx)] at hq) (exact (Or.inl (Reach.step p q r hq)))))
    (case [inr o] (exact (Or.inr o)))))
(a/theorem rp-within [w :- World, w2 :- World, x :- Nat, y :- Nat, a :- Nat]
  (=> (forall [z :- Nat] (=> (= (Nat.beq z x) false) (= (scope-up w2 z) (scope-up w z))))
      (= (scope-within w y a) true)
      (Or (= (scope-within w2 y a) true) (= (scope-within w2 y x) true)))
  (intros he h)
  (have o := (wi-of w y a h))
  (cases o)
  (case [inl e] (exact (Or.inl (wi-intro w2 y a (Or.inl e)))))
  (case [inr r]
    (have o2 := (rp-reach (scope-up w) (scope-up w2) x y a he r))
    (cases o2)
    (case [inl r2] (exact (Or.inl (wi-intro w2 y a (Or.inr r2)))))
    (case [inr o3]
      (cases o3)
      (case [inl e] (exact (Or.inr (wi-intro w2 y x (Or.inl e)))))
      (case [inr r3] (exact (Or.inr (wi-intro w2 y x (Or.inr r3))))))))

;; a kept world: scopes = tbl-keep K (parents of kept scopes kept): kept chains are unchanged
(a/theorem keep-up [w :- World, w2 :- World, K :- (=> Nat Bool), z :- Nat]
  (=> (= (:scopes w2) (tbl-keep K scope-id (:scopes w))) (= (K z) true) (= (scope-up w2 z) (scope-up w z)))
  (intros es hz)
  (rw [(cy-up w2 z) (cy-up w z) es (keep-find-in ScopeRow K scope-id z (:scopes w) hz)]))
(a/theorem keep-up-k [w :- World, K :- (=> Nat Bool), z :- Nat, b :- Nat]
  (=> (forall [c :- ScopeRow] (=> (List.Mem c (:scopes w)) (= (K (:id c)) true) (= (Nat.beq (:parent c) 0) false) (= (K (:parent c)) true)))
      (= (K z) true) (List.Mem b (scope-up w z)) (= (K b) true))
  (intros hc hz hb)
  (rw [(cy-up w z)] at hb)
  (cases hf (tbl-find scope-id z (:scopes w)))
  (case [none] (rw [hf] at hb) (simp only [cy-par] at hb) (cases hb))
  (case [some c]
    (rw [hf] at hb) (simp only [cy-par] at hb)
    (have e := (cy-mem-nz (:parent c) b hb))
    (have m := (tbl-find-mem ScopeRow scope-id z c (:scopes w) hf))
    (have i (= (:id c) z)) (exact (tbl-find-id ScopeRow scope-id z c (:scopes w) hf))
    (have p0 (= (Nat.beq (:parent c) 0) false))
    (cases hp (Nat.beq (:parent c) 0)) (rfl) (simp only [nz hp] at hb) (cases hb)
    (rw [e]) (apply (hc c m _ p0)) (rw [i]) (exact hz)))
(a/theorem keep-reach [w :- World, w2 :- World, K :- (=> Nat Bool), y :- Nat, a :- Nat]
  (=> (= (:scopes w2) (tbl-keep K scope-id (:scopes w)))
      (forall [c :- ScopeRow] (=> (List.Mem c (:scopes w)) (= (K (:id c)) true) (= (Nat.beq (:parent c) 0) false) (= (K (:parent c)) true)))
      (= (K y) true) (Reach (scope-up w) (scope-up w y) a)
      (And (Reach (scope-up w2) (scope-up w2 y) a) (= (K a) true)))
  (intros es hc hy h)
  (induction h)
  (case [root b hb]
    (have e := (keep-up w w2 K y es hy))
    (have hb2 (List.Mem b (scope-up w2 y))) (rw [e]) (exact hb)
    (exact (And.intro (Reach.root b hb2) (keep-up-k w K y b hc hy hb))))
  (case [step p q hp hq ih]
    (have e := (keep-up w w2 K p es (And.right ih)))
    (have hq2 (List.Mem q (scope-up w2 p))) (rw [e]) (exact hq)
    (exact (And.intro (Reach.step p q (And.left ih) hq2) (keep-up-k w K p q hc (And.right ih) hq)))))
(a/theorem keep-within [w :- World, w2 :- World, K :- (=> Nat Bool), y :- Nat, a :- Nat]
  (=> (= (:scopes w2) (tbl-keep K scope-id (:scopes w)))
      (forall [c :- ScopeRow] (=> (List.Mem c (:scopes w)) (= (K (:id c)) true) (= (Nat.beq (:parent c) 0) false) (= (K (:parent c)) true)))
      (= (K y) true) (= (scope-within w y a) true) (= (scope-within w2 y a) true))
  (intros es hc hy h)
  (have o := (wi-of w y a h))
  (cases o)
  (case [inl e] (exact (wi-intro w2 y a (Or.inl e))))
  (case [inr r] (exact (wi-intro w2 y a (Or.inr (And.left (keep-reach w w2 K y a es hc hy r)))))))

;; ===========================================================================
;; Part C. Witnesses and transport lemmas
;; ===========================================================================

(a/theorem hw-elim [w :- World, y :- Nat, P :- Prop]
  (=> (= (hw w y) true) (forall [q :- RunRow] (=> (List.Mem q (:runs w)) (= (scope-within w y (:scope q)) true) P)) P)
  (intros h k)
  (simp only [hw] at h)
  (exact (any-elim RunRow (run-within w y) P (:runs w) h k)))
(a/theorem hw-intro [w :- World, y :- Nat, q :- RunRow]
  (=> (List.Mem q (:runs w)) (= (scope-within w y (:scope q)) true) (= (hw w y) true))
  (intros m e) (simp only [hw]) (exact (any-elim-of RunRow (run-within w y) q (:runs w) m e)))

(a/theorem os-ok-of [w :- World, s :- ScopeRow] (=> (= (os-ok w s) true) (= (os-need s) true) (= (hw w (:id s)) true))
  (intros h n) (simp only [os-ok n Bool.not_true Bool.false_or] at h) (exact h))
(a/theorem os-ok-intro [w :- World, s :- ScopeRow] (=> (=> (= (os-need s) true) (= (hw w (:id s)) true)) (= (os-ok w s) true))
  (intro h)
  (cases hn (os-need s))
  (case [false] (simp only [os-ok hn Bool.not_false Bool.true_or]))
  (case [true] (simp only [os-ok hn (h hn) Bool.not_true Bool.or_true])))
(a/theorem open-scopes-have-runs-rest-mem [w :- World, c :- ScopeRow]
  (=> (= (open-scopes-have-runs-rest w) true) (List.Mem c (:scopes w)) (= (os-need c) true) (= (hw w (:id c)) true))
  (intros h m n) (exact (os-ok-of w c (tbl-all-mem ScopeRow (os-ok w) c (:scopes w) h m) n)))
(a/theorem open-scopes-have-runs-rest-tr [w2 :- World]
  (=> (forall [c :- ScopeRow] (=> (List.Mem c (:scopes w2)) (= (os-need c) true) (= (hw w2 (:id c)) true)))
      (= (open-scopes-have-runs-rest w2) true))
  (intro h) (simp only [open-scopes-have-runs-rest])
  (apply (all-of-mem ScopeRow (os-ok w2) (:scopes w2)))
  (intros c m) (exact (os-ok-intro w2 c (h c m))))

;; a run of w2 for every run of w, with the same run scope
(a/defn rcov [rs :- (List RunRow), q :- RunRow] Bool (tbl-any (fn [q2 :- RunRow] (Nat.beq (:scope q2) (:scope q))) rs))
(a/theorem hw-tr [w :- World, w2 :- World, y :- Nat]
  (=> (forall [a :- Nat] (=> (= (scope-within w y a) true) (= (scope-within w2 y a) true)))
      (forall [q :- RunRow] (=> (List.Mem q (:runs w)) (= (rcov (:runs w2) q) true)))
      (= (hw w y) true) (= (hw w2 y) true))
  (intros hs hr h)
  (apply (hw-elim w y _ h))
  (intros q m e)
  (have c := (hr q m))
  (simp only [rcov] at c)
  (apply (any-elim RunRow _ _ (:runs w2) c))
  (intros q2 m2 e2)
  (have es (= (:scope q2) (:scope q))) (exact (Nat.eq_of_beq_eq_true e2))
  (apply (hw-intro w2 y q2 m2))
  (rw [es]) (exact (hs (:scope q) e)))
(a/theorem rcov-mem [rs :- (List RunRow), q :- RunRow] (=> (List.Mem q rs) (= (rcov rs q) true))
  (intro m) (simp only [rcov]) (exact (any-elim-of RunRow (fn [q2 :- RunRow] (Nat.beq (:scope q2) (:scope q))) q rs m (Nat.beq_refl (:scope q)))))

;; the same scope table, runs covered: a frame for open-scopes-have-runs-rest
(a/theorem open-scopes-have-runs-rest-runs [w :- World, w2 :- World]
  (=> (= (:scopes w2) (:scopes w)) (forall [q :- RunRow] (=> (List.Mem q (:runs w)) (= (rcov (:runs w2) q) true)))
      (= (open-scopes-have-runs-rest w) true) (= (open-scopes-have-runs-rest w2) true))
  (intros es hr h)
  (have su (forall [z :- Nat, x :- Nat] (=> (List.Mem x (scope-up w z)) (List.Mem x (scope-up w2 z)))))
  (intros z x hx) (have e3 := (cy-up w z)) (rw [(cy-up w2 z) es ← e3]) (exact hx)
  (apply (open-scopes-have-runs-rest-tr w2))
  (intros c m n)
  (rw [es] at m)
  (exact (hw-tr w w2 (:id c) (fn [a :- Nat, e :- (= (scope-within w (:id c) a) true)] (wi-mono w w2 (:id c) a su e)) hr
           (open-scopes-have-runs-rest-mem w c h m n))))

;; run row updates that keep the run scope
(a/theorem upd-rcov [x :- Nat, f :- (=> RunRow RunRow), hk :- (forall [r :- RunRow] (= (:scope (f r)) (:scope r))), q :- RunRow, xs :- (List RunRow)]
  (=> (List.Mem q xs) (= (rcov (tbl-upd run-id x f xs) q) true))
  (induction xs)
  (case [nil] (intro m) (cases m))
  (case [cons h t ih]
    (intro m)
    (cases m)
    (case [head]
      (cases hx (Nat.beq (run-id q) x))
      (all_goals (simp only [tbl-upd hx rcov tbl-any (hk q) Nat.beq_refl Bool.true_or])))
    (case [tail m2]
      (have c := (ih m2))
      (simp only [rcov] at c)
      (cases hx (Nat.beq (run-id h) x))
      (all_goals (simp only [tbl-upd hx rcov tbl-any c Bool.or_true])))))
(a/theorem open-scopes-have-runs-rest-run-upd [w :- World, x :- Nat, f :- (=> RunRow RunRow), hk :- (forall [r :- RunRow] (= (:scope (f r)) (:scope r)))]
  (=> (= (open-scopes-have-runs-rest w) true) (= (open-scopes-have-runs-rest (run-upd w x f)) true))
  (intro h)
  (exact (open-scopes-have-runs-rest-runs w (run-upd w x f) (rfl) (fn [q :- RunRow, m :- (List.Mem q (:runs w))] (upd-rcov x f hk q (:runs w) m)) h)))
(a/theorem open-scopes-have-runs-run-upd [w :- World, x :- Nat, f :- (=> RunRow RunRow), hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                        hk :- (forall [r :- RunRow] (= (:scope (f r)) (:scope r)))]
  (=> (= (open-scopes-have-runs w) true) (= (open-scopes-have-runs (run-upd w x f)) true))
  (intro h)
  (exact (open-scopes-have-runs-intro _ (well-formed-run-upd w x f hf (open-scopes-have-runs-well-formed w h)) (open-scopes-have-runs-rest-run-upd w x f hk (open-scopes-have-runs-rest-of w h)))))
(a/theorem open-scopes-have-runs-rest-run-ins [w :- World, r :- RunRow] (=> (= (open-scopes-have-runs-rest w) true) (= (open-scopes-have-runs-rest (bump (run-ins w r))) true))
  (intro h)
  (exact (open-scopes-have-runs-rest-runs w (bump (run-ins w r)) (rfl)
           (fn [q :- RunRow, m :- (List.Mem q (:runs w))] (rcov-mem _ q (List.Mem.tail r m))) h)))

;; scope row updates that keep the parent and do not create an obligation
(a/theorem open-scopes-have-runs-rest-scope-upd [w :- World, x :- Nat, f :- (=> ScopeRow ScopeRow),
                               hf :- (forall [s :- ScopeRow] (= (scope-id (f s)) (scope-id s))),
                               hk :- (forall [s :- ScopeRow] (And (= (:parent (f s)) (:parent s)) (=> (= (os-need (f s)) true) (= (os-need s) true))))]
  (=> (= (open-scopes-have-runs-rest w) true) (= (open-scopes-have-runs-rest (scope-upd w x f)) true))
  (intro h)
  (have es (= (:scopes (scope-upd w x f)) (tbl-upd scope-id x f (:scopes w)))) (rfl)
  (have eu (forall [z :- Nat] (= (scope-up (scope-upd w x f) z) (scope-up w z))))
  (intro z) (rw [(cy-up (scope-upd w x f) z) (cy-up w z) es (cy-par-upd x f hf (fn [s :- ScopeRow] (And.left (hk s))) z (:scopes w))])
  (have su (forall [z :- Nat, b :- Nat] (=> (List.Mem b (scope-up w z)) (List.Mem b (scope-up (scope-upd w x f) z)))))
  (intros z b hb) (rw [(eu z)]) (exact hb)
  (have tr (forall [y :- Nat] (=> (= (hw w y) true) (= (hw (scope-upd w x f) y) true))))
  (intros y hy)
  (exact (hw-tr w (scope-upd w x f) y (fn [a :- Nat, e :- (= (scope-within w y a) true)] (wi-mono w _ y a su e))
           (fn [q :- RunRow, m :- (List.Mem q (:runs w))] (rcov-mem _ q m)) hy))
  (simp only [open-scopes-have-runs-rest] at h) (simp only [open-scopes-have-runs-rest]) (try (rw [es]))
  (apply (tbl-all-upd ScopeRow scope-id x f (os-ok w) (os-ok (scope-upd w x f)) _ _ (:scopes w) h))
  (intros s q e)
  (apply (os-ok-intro _ (f s))) (intro n)
  (have n0 := (And.right (hk s) n))
  (have i (= (:id (f s)) (:id s))) (exact (hf s))
  (rw [i]) (exact (tr (:id s) (os-ok-of w s q n0)))
  (intros s q e)
  (apply (os-ok-intro _ s)) (intro n) (exact (tr (:id s) (os-ok-of w s q n))))
(a/theorem open-scopes-have-runs-scope-upd [w :- World, x :- Nat, f :- (=> ScopeRow ScopeRow),
                          hf :- (forall [s :- ScopeRow] (= (scope-id (f s)) (scope-id s))),
                          hk :- (forall [s :- ScopeRow] (And (= (:parent (f s)) (:parent s)) (=> (= (os-need (f s)) true) (= (os-need s) true))))]
  (=> (= (open-scopes-have-runs w) true) (= (open-scopes-have-runs (scope-upd w x f)) true))
  (intro h)
  (exact (open-scopes-have-runs-intro _ (well-formed-scope-upd w x f hf (open-scopes-have-runs-well-formed w h)) (open-scopes-have-runs-rest-scope-upd w x f hf hk (open-scopes-have-runs-rest-of w h)))))
(a/theorem close-hk [s :- ScopeRow]
  (And (= (:parent (scope-close s)) (:parent s)) (=> (= (os-need (scope-close s)) true) (= (os-need s) true)))
  (apply And.intro) (rfl) (intro q) (simp [os-need scope-close] at q))

;; the kept rows of a world (scope deletion, Rule R's filter): parents of kept scopes kept, runs covered
(a/theorem open-scopes-have-runs-rest-keep [w :- World, w2 :- World, K :- (=> Nat Bool)]
  (=> (= (:scopes w2) (tbl-keep K scope-id (:scopes w)))
      (forall [c :- ScopeRow] (=> (List.Mem c (:scopes w)) (= (K (:id c)) true) (= (Nat.beq (:parent c) 0) false) (= (K (:parent c)) true)))
      (forall [q :- RunRow] (=> (List.Mem q (:runs w)) (= (rcov (:runs w2) q) true)))
      (= (open-scopes-have-runs-rest w) true) (= (open-scopes-have-runs-rest w2) true))
  (intros es hc hr h)
  (simp only [open-scopes-have-runs-rest] at h) (simp only [open-scopes-have-runs-rest]) (rw [es])
  (apply (tbl-all-keep-mem ScopeRow K scope-id (os-ok w) (os-ok w2) (:scopes w) _ h))
  (intros c m q k)
  (apply (os-ok-intro w2 c)) (intro n)
  (exact (hw-tr w w2 (:id c) (fn [a :- Nat, e :- (= (scope-within w (:id c) a) true)] (keep-within w w2 K (:id c) a es hc k e)) hr
           (os-ok-of w c q n))))

;; ===========================================================================
;; Part D. The run-scope subtree converges (Z#18 `scope-subtree`): it holds every scope whose chain reaches it
;; ===========================================================================

(a/defn sc-pars [ss :- (List ScopeRow)] (List Nat)
  (match ss nil (List.nil Nat) (cons h t) (List.cons Nat (:parent h) (sc-pars t))))
(a/defn nd-ins [x :- Nat, acc :- (List Nat)] (List Nat) (if (nat-mem x acc) acc (List.cons Nat x acc)))
(a/defn nd-list [xs :- (List Nat)] (List Nat) (match xs nil (List.nil Nat) (cons h t) (nd-ins h (nd-list t))))

(a/theorem nd-nodup [xs :- (List Nat)] (= (nat-nodup (nd-list xs)) true)
  (induction xs)
  (case [nil] (simp only [nd-list nat-nodup]))
  (case [cons h t ih]
    (cases hm (nat-mem h (nd-list t)))
    (case [true] (simp only [nd-list nd-ins hm]) (exact ih))
    (case [false] (simp only [nd-list nd-ins hm nat-nodup ih Bool.not_false Bool.and_self]))))
(a/theorem nd-ins-keep [x :- Nat, y :- Nat, acc :- (List Nat)] (=> (= (nat-mem y acc) true) (= (nat-mem y (nd-ins x acc)) true))
  (intro h)
  (cases hm (nat-mem x acc))
  (case [true] (simp only [nd-ins hm]) (exact h))
  (case [false] (simp only [nd-ins hm nat-mem]) (cases hb (Nat.beq x y)) (all_goals (simp only [hb h]))))
(a/theorem nd-ins-self [x :- Nat, acc :- (List Nat)] (= (nat-mem x (nd-ins x acc)) true)
  (cases hm (nat-mem x acc))
  (case [true] (simp only [nd-ins hm]))
  (case [false] (simp only [nd-ins hm nat-mem Nat.beq_refl])))
(a/theorem nd-mem [x :- Nat, xs :- (List Nat)] (=> (= (nat-mem x xs) true) (= (nat-mem x (nd-list xs)) true))
  (induction xs)
  (case [nil] (intro h) (simp only [nat-mem] at h) (cases h))
  (case [cons h t ih]
    (intro hx)
    (cases hb (Nat.beq h x))
    (case [true] (have e := (Nat.eq_of_beq_eq_true hb)) (rw [← e]) (simp only [nd-list]) (exact (nd-ins-self h (nd-list t))))
    (case [false] (simp only [nat-mem hb] at hx) (simp only [nd-list]) (exact (nd-ins-keep h x (nd-list t) (ih hx))))))

(a/theorem pars-mem [ss :- (List ScopeRow), s :- ScopeRow] (=> (List.Mem s ss) (= (nat-mem (:parent s) (sc-pars ss)) true))
  (induction ss)
  (case [nil] (intro m) (cases m))
  (case [cons h t ih]
    (intro m) (cases m)
    (case [head] (simp only [sc-pars nat-mem Nat.beq_refl]))
    (case [tail m2] (simp only [sc-pars nat-mem]) (cases hb (Nat.beq (:parent h) (:parent s))) (all_goals (simp only [hb (ih m2)])))))

(a/theorem scan-nil [ss :- (List ScopeRow), x :- Nat, us :- (List Nat)]
  (=> (forall [s :- ScopeRow] (=> (List.Mem s ss) (= (nat-mem (:parent s) us) true))) (= (nat-mem x us) false)
      (= (tbl-scan scope-id (parent-is x) ss) (List.nil Nat)))
  (induction ss)
  (case [nil] (intros h hx) (simp only [tbl-scan]))
  (case [cons h t ih]
    (intros hs hx)
    (have ht (forall [s :- ScopeRow] (=> (List.Mem s t) (= (nat-mem (:parent s) us) true))))
    (intros s m) (exact (hs s (List.Mem.tail h m)))
    (cases hp (parent-is x h))
    (case [false] (simp only [tbl-scan hp]) (exact (ih ht hx)))
    (case [true]
      (have e (= (:parent h) x)) (simp only [parent-is] at hp) (exact (Nat.eq_of_beq_eq_true hp))
      (have z := (hs h (List.Mem.head t))) (rw [e hx] at z) (cases z))))

(a/theorem scan-len [A :- Type, idf :- (=> A Nat), p :- (=> A Bool), xs :- (List A)]
  (= (List.length (tbl-scan idf p xs)) (tbl-count p xs))
  (induction xs)
  (case [nil] (simp only [tbl-scan tbl-count List.length]))
  (case [cons h t ih] (cases hp (p h)) (all_goals (simp only [tbl-scan tbl-count hp List.length ih]))))
(a/theorem cnt-le [A :- Type, p :- (=> A Bool), xs :- (List A)] (<= (tbl-count p xs) (List.length xs))
  (induction xs)
  (case [nil] (simp only [tbl-count List.length]) (omega))
  (case [cons h t ih] (cases hp (p h)) (all_goals (simp only [tbl-count hp List.length])) (all_goals (omega))))
(a/theorem cnt-or [A :- Type, p :- (=> A Bool), q :- (=> A Bool), hd :- (forall [a :- A] (=> (= (p a) true) (= (q a) false))), xs :- (List A)]
  (= (+ (tbl-count p xs) (tbl-count q xs)) (tbl-count (fn [a :- A] (Bool.or (p a) (q a))) xs))
  (induction xs)
  (case [nil] (simp only [tbl-count]))
  (case [cons h t ih]
    (cases hp (p h))
    (case [true] (simp only [tbl-count hp (hd h hp) Bool.true_or]) (omega))
    (case [false] (cases hq (q h)) (all_goals (simp only [tbl-count hp hq Bool.false_or])) (all_goals (omega)))))
(a/theorem cnt-congr [A :- Type, p :- (=> A Bool), q :- (=> A Bool), he :- (forall [a :- A] (= (p a) (q a))), xs :- (List A)]
  (= (tbl-count p xs) (tbl-count q xs))
  (induction xs)
  (case [nil] (simp only [tbl-count]))
  (case [cons h t ih] (simp only [tbl-count (he h) ih])))

(a/defn pc-sum [ss :- (List ScopeRow), us :- (List Nat)] Nat
  (match us nil 0 (cons u t) (+ (tbl-count (parent-is u) ss) (pc-sum ss t))))
(a/defn par-in [us :- (List Nat), s :- ScopeRow] Bool (nat-mem (:parent s) us))
(a/theorem os-beq-comm [a :- Nat, b :- Nat] (= (Nat.beq a b) (Nat.beq b a))
  (cases h (Nat.beq a b))
  (case [true] (have e := (Nat.eq_of_beq_eq_true h)) (rw [e Nat.beq_refl]))
  (case [false] (exact (Eq.symm (beq-symm-false a b h)))))
(a/theorem par-in-cons [u :- Nat, t :- (List Nat), s :- ScopeRow]
  (= (par-in (List.cons Nat u t) s) (Bool.or (parent-is u s) (par-in t s)))
  (simp only [par-in parent-is nat-mem])
  (cases hb (Nat.beq u (:parent s)))
  (case [true]
    (have e := (Nat.eq_of_beq_eq_true hb))
    (have hb2 (= (Nat.beq (:parent s) u) true)) (rw [e]) (exact (Nat.beq_refl (:parent s)))
    (simp only [hb hb2 Bool.true_or]))
  (case [false]
    (have hb2 := (beq-symm-false u (:parent s) hb))
    (simp only [hb hb2 Bool.false_or])))
(a/theorem pc-le [ss :- (List ScopeRow), us :- (List Nat)] (=> (= (nat-nodup us) true) (<= (pc-sum ss us) (tbl-count (par-in us) ss)))
  (induction us)
  (case [nil] (intro h) (simp only [pc-sum]) (omega))
  (case [cons u t ih]
    (intro hn)
    (simp only [nat-nodup Bool.and_eq_true] at hn)
    (have i := (ih (And.right hn)))
    (have hd (forall [s :- ScopeRow] (=> (= (parent-is u s) true) (= (par-in t s) false))))
    (intros s hs) (simp only [parent-is] at hs) (have e := (Nat.eq_of_beq_eq_true hs))
    (simp only [par-in e]) (cases hm (nat-mem u t)) (rfl) (have z := (And.left hn)) (rw [hm] at z) (simp at z)
    (have o := (cnt-or ScopeRow (parent-is u) (par-in t) hd ss))
    (have c := (cnt-congr ScopeRow (fn [s :- ScopeRow] (Bool.or (parent-is u s) (par-in t s))) (par-in (List.cons Nat u t))
                 (fn [s :- ScopeRow] (Eq.symm (par-in-cons u t s))) ss))
    (simp only [pc-sum]) (omega)))

(a/theorem unseen-pc [w :- World, us :- (List Nat)]
  (= (unseen-cost (child-scopes w) (List.nil Nat) us) (pc-sum (:scopes w) us))
  (induction us)
  (case [nil] (simp only [unseen-cost pc-sum]))
  (case [cons u t ih] (simp only [unseen-cost pc-sum reach-mem child-scopes scan-len ih])))
(a/theorem os-ids-len [A :- Type, idf :- (=> A Nat), xs :- (List A)] (= (List.length (tbl-ids idf xs)) (List.length xs))
  (induction xs)
  (case [nil] (simp only [tbl-ids List.length]))
  (case [cons h t ih] (simp only [tbl-ids List.length ih])))

(a/theorem nm-tail [x :- Nat, y :- Nat, l :- (List Nat)] (=> (= (nat-mem x l) true) (= (nat-mem x (List.cons Nat y l)) true))
  (intro h) (simp only [nat-mem]) (cases hb (Nat.beq y x)) (all_goals (simp only [hb h])))
(a/theorem sub-conv [w :- World, s :- Nat]
  (= (:converged (reach-run-l (List.cons Nat 0 (List.cons Nat 0 (tbl-ids scope-id (:scopes w)))) (child-scopes w) (nz s))) true)
  (have pm (forall [c :- ScopeRow] (=> (List.Mem c (:scopes w)) (= (nat-mem (:parent c) (nd-list (List.cons Nat s (sc-pars (:scopes w))))) true))))
  (intros c m) (apply nd-mem) (exact (nm-tail (:parent c) s _ (pars-mem (:scopes w) c m)))
  (apply (reach-run-l-conv _ (child-scopes w) (nz s) (nd-list (List.cons Nat s (sc-pars (:scopes w))))))
  (intros x hx) (rw [reach-mem-nat-mem] at hx) (simp only [child-scopes]) (exact (scan-nil (:scopes w) x _ pm hx))
  (rw [unseen-pc])
  (have a := (pc-le (:scopes w) _ (nd-nodup (List.cons Nat s (sc-pars (:scopes w))))))
  (have b := (cnt-le ScopeRow (par-in (nd-list (List.cons Nat s (sc-pars (:scopes w))))) (:scopes w)))
  (have c := (nz-len s))
  (simp only [List.length os-ids-len])
  (omega))

(a/theorem sub-closed [w :- World, s :- Nat, a :- Nat, b :- Nat]
  (=> (= (reach-mem a (scope-subtree w s)) true) (= (reach-mem b (child-scopes w a)) true) (= (reach-mem b (scope-subtree w s)) true))
  (intros ha hb)
  (have c := (sub-conv w s))
  (simp only [scope-subtree] at ha) (simp only [scope-subtree])
  (rw [reach-run-l-eq] at c ha) (rw [reach-run-l-eq])
  (exact (reach-run-closed _ (child-scopes w) (nz s) a b c ha hb)))
(a/theorem sub-root [w :- World, s :- Nat] (=> (= (Nat.beq s 0) false) (= (reach-mem s (scope-subtree w s)) true))
  (intro hs)
  (have c := (sub-conv w s))
  (simp only [scope-subtree]) (rw [reach-run-l-eq] at c) (rw [reach-run-l-eq])
  (apply (reach-run-roots _ (child-scopes w) (nz s) s c))
  (simp only [nz hs reach-mem Nat.beq_refl]))
(a/theorem child-of-up [w :- World, z :- Nat, b :- Nat] (=> (List.Mem b (scope-up w z)) (= (reach-mem z (child-scopes w b)) true))
  (intro hb)
  (rw [(cy-up w z)] at hb)
  (cases hf (tbl-find scope-id z (:scopes w)))
  (case [none] (rw [hf] at hb) (simp only [cy-par] at hb) (cases hb))
  (case [some c]
    (rw [hf] at hb) (simp only [cy-par] at hb)
    (have e := (cy-mem-nz (:parent c) b hb))
    (have m := (tbl-find-mem ScopeRow scope-id z c (:scopes w) hf))
    (have i (= (scope-id c) z)) (exact (tbl-find-id ScopeRow scope-id z c (:scopes w) hf))
    (have p (= (parent-is b c) true)) (simp only [parent-is e Nat.beq_refl])
    (have r := (scan-mem ScopeRow scope-id (parent-is b) c (:scopes w) m p))
    (rw [i] at r) (simp only [child-scopes]) (exact r)))
(a/theorem up-nz [w :- World, y :- Nat, z :- Nat] (=> (List.Mem z (scope-up w y)) (= (Nat.beq z 0) false))
  (intro hq)
  (rw [(cy-up w y)] at hq)
  (cases hf (tbl-find scope-id y (:scopes w)))
  (case [none] (rw [hf] at hq) (simp only [cy-par] at hq) (cases hq))
  (case [some c]
    (rw [hf] at hq) (simp only [cy-par] at hq)
    (have e := (cy-mem-nz (:parent c) z hq))
    (cases hp0 (Nat.beq (:parent c) 0))
    (case [true] (simp only [nz hp0] at hq) (cases hq))
    (case [false] (rw [e]) (exact hp0))))
(a/theorem reach-nz [w :- World, y :- Nat, a :- Nat] (=> (Reach (scope-up w) (scope-up w y) a) (= (Nat.beq a 0) false))
  (intro h)
  (induction h)
  (case [root x hx] (exact (up-nz w y x hx)))
  (case [step p q hp hq ih] (exact (up-nz w p q hq))))

;; completeness: a scope whose chain reaches s (or s itself) is in s's subtree
(a/theorem sub-reach [w :- World, s :- Nat, y :- Nat, z :- Nat]
  (=> (Reach (scope-up w) (scope-up w y) z) (= (reach-mem z (scope-subtree w s)) true) (= (reach-mem y (scope-subtree w s)) true))
  (intro h)
  (induction h)
  (case [root x hx] (intro hz) (exact (sub-closed w s x y hz (child-of-up w y x hx))))
  (case [step p q hp hq ih] (intro hz) (exact (ih (sub-closed w s q p hz (child-of-up w p q hq))))))
(a/theorem sub-within [w :- World, s :- Nat, y :- Nat]
  (=> (= (Nat.beq y 0) false) (= (scope-within w y s) true) (= (reach-mem y (scope-subtree w s)) true))
  (intros hy h)
  (have o := (wi-of w y s h))
  (cases o)
  (case [inl e] (rw [e] at hy) (rw [e]) (exact (sub-root w s hy)))
  (case [inr r] (exact (sub-reach w s y s r (sub-root w s (reach-nz w y s r))))))

;; ===========================================================================
;; Part E. The run's current scope is its run scope or an open explicit scope (open-scope's parent)
;; ===========================================================================

(a/theorem nm-cases [xs :- (List Nat)]
  (forall [m :- Nat] (Or (= (nat-max m xs) m) (= (reach-mem (nat-max m xs) xs) true)))
  (induction xs)
  (case [nil] (intro m) (apply Or.inl) (simp only [nat-max]))
  (case [cons h t ih]
    (intro m)
    (have o := (ih (if (Nat.blt m h) h m)))
    (simp only [nat-max])
    (cases o)
    (case [inl e]
      (rw [e])
      (cases hb (Nat.blt m h))
      (case [true] (apply Or.inr) (simp only [hb reach-mem-cons Nat.beq_refl Bool.true_or]))
      (case [false] (apply Or.inl) (simp only [hb])))
    (case [inr r] (apply Or.inr) (simp only [reach-mem-cons r Bool.or_true]))))
(a/theorem vis-sound [fuel :- (List Nat), succ :- (=> Nat (List Nat)), roots :- (List Nat), v :- Nat]
  (=> (= (reach-mem v (:visited (reach-run-l fuel succ roots))) true) (Reach succ roots v))
  (intro h) (rw [reach-run-l-eq] at h) (exact (reach-run-sound _ succ roots v h)))
(a/theorem mem1 [x :- Nat, y :- Nat] (=> (List.Mem x (List.cons Nat y (List.nil Nat))) (= x y))
  (intro hm) (cases hm) (rfl) (rename_i hm2) (cases hm2))
(a/theorem oec-need [p :- Nat, c :- ScopeRow] (=> (= (open-explicit-child p c) true) (= (os-need c) true))
  (intro h)
  (simp only [open-explicit-child Bool.and_eq_true] at h)
  (have e (= (:kind c) scope-explicit)) (exact (Nat.eq_of_beq_eq_true (And.left (And.right h))))
  (simp only [os-need e (And.right (And.right h))]))
(a/theorem oec-cases [w :- World, R0 :- (List Nat), z :- Nat, P :- Prop]
  (=> (Reach (open-explicit-children w) R0 z) (=> (List.Mem z R0) P)
      (forall [c :- ScopeRow] (=> (List.Mem c (:scopes w)) (= (:id c) z) (= (os-need c) true) P)) P)
  (intro h)
  (induction h)
  (case [root x hx] (intros h1 h2) (exact (h1 hx)))
  (case [step p q hp hq ih]
    (intros h1 h2)
    (have hq2 (= (reach-mem q (tbl-scan scope-id (open-explicit-child p) (:scopes w))) true))
    (exact (Iff.mpr (reach-mem-iff q _) hq))
    (exact (scan-prop ScopeRow scope-id (open-explicit-child p)
             (fn [z :- Nat] (=> (forall [c :- ScopeRow] (=> (List.Mem c (:scopes w)) (= (:id c) z) (= (os-need c) true) P)) P))
             (:scopes w)
             (fn [a :- ScopeRow, ma :- (List.Mem a (:scopes w)), pa :- (= (open-explicit-child p a) true),
                  k :- (forall [c :- ScopeRow] (=> (List.Mem c (:scopes w)) (= (:id c) (scope-id a)) (= (os-need c) true) P))]
               (k a ma (rfl) (oec-need p a pa)))
             q hq2 h2))))
(a/theorem cur-cases [w :- World, r :- RunRow, P :- Prop]
  (=> (=> (= (cur-scope w r) (:scope r)) P)
      (forall [c :- ScopeRow] (=> (List.Mem c (:scopes w)) (= (:id c) (cur-scope w r)) (= (os-need c) true) P))
      P)
  (intros h1 h2)
  (have o (Or (= (cur-scope w r) (:scope r))
              (= (reach-mem (cur-scope w r) (:visited (reach-run-l (List.cons Nat 0 (List.cons Nat 0 (tbl-ids scope-id (:scopes w))))
                                                                     (open-explicit-children w) (List.cons Nat (:scope r) (List.nil Nat))))) true)))
  (exact (nm-cases _ (:scope r)))
  (cases o)
  (case [inl e] (exact (h1 e)))
  (case [inr m]
    (exact (oec-cases w (List.cons Nat (:scope r) (List.nil Nat)) (cur-scope w r) P (vis-sound _ _ _ _ m)
             (fn [hm :- (List.Mem (cur-scope w r) (List.cons Nat (:scope r) (List.nil Nat)))] (h1 (mem1 _ _ hm))) h2))))

;; a child's chain is its parent's, prefixed
(a/theorem wi-child [w :- World, s :- Nat, c :- Nat, a :- Nat]
  (=> (List.Mem c (scope-up w s)) (= (scope-within w c a) true) (= (scope-within w s a) true))
  (intros mc h)
  (apply (wi-intro w s a))
  (have o := (wi-of w c a h))
  (cases o)
  (case [inl e] (rw [← e]) (exact (Or.inr (Reach.root c mc))))
  (case [inr r] (exact (Or.inr (reach-pre (scope-up w) c a (scope-up w s) mc r)))))

;; a fresh scope row (id next-id): every old chain survives
(a/theorem ins-up [w :- World, r :- ScopeRow, z :- Nat, b :- Nat]
  (=> (= (scope-id r) (:next-id w)) (= (well-formed w) true) (List.Mem b (scope-up w z)) (List.Mem b (scope-up (bump (scope-ins w r)) z)))
  (intros hr hs hb)
  (have es (= (:scopes (bump (scope-ins w r))) (List.cons ScopeRow r (:scopes w)))) (rfl)
  (rw [(cy-up (bump (scope-ins w r)) z) es])
  (rw [(cy-up w z)] at hb)
  (cases hz (Nat.beq (scope-id r) z))
  (case [false] (simp only [tbl-find hz]) (exact hb))
  (case [true]
    (have e (= z (:next-id w))) (rw [← hr]) (exact (Eq.symm (Nat.eq_of_beq_eq_true hz)))
    (cases hf (tbl-find scope-id z (:scopes w)))
    (case [none] (rw [hf] at hb) (simp only [cy-par] at hb) (cases hb))
    (case [some c]
      (have hh := (tbl-find-has ScopeRow scope-id z c (:scopes w) hf))
      (have lt := (cy-scope-below w z hs hh))
      (rw [e] at lt) (omega))))
(a/theorem open-scopes-have-runs-scope-ins [w :- World, r :- ScopeRow]
  (=> (= (scope-id r) (:next-id w)) (=> (= (os-need r) true) (= (hw (bump (scope-ins w r)) (:id r)) true))
      (= (open-scopes-have-runs w) true) (= (open-scopes-have-runs (bump (scope-ins w r))) true))
  (intros hr hn h)
  (have hs := (open-scopes-have-runs-well-formed w h))
  (have rest (= (open-scopes-have-runs-rest (bump (scope-ins w r))) true))
  (apply (open-scopes-have-runs-rest-tr (bump (scope-ins w r))))
  (intros c m n)
  (have m1 (List.Mem c (List.cons ScopeRow r (:scopes w)))) (exact m)
  (cases m1)
  (case [head] (exact (hn n)))
  (case [tail m2]
    (exact (hw-tr w _ (:id c)
             (fn [a :- Nat, e :- (= (scope-within w (:id c) a) true)]
               (wi-mono w _ (:id c) a (fn [z :- Nat, b :- Nat, hb :- (List.Mem b (scope-up w z))] (ins-up w r z b hr hs hb)) e))
             (fn [q :- RunRow, mq :- (List.Mem q (:runs w))] (rcov-mem _ q mq)) (open-scopes-have-runs-rest-mem w c (open-scopes-have-runs-rest-of w h) m2 n))))
  (exact (open-scopes-have-runs-intro _ (well-formed-scope-ins-fresh w r hr hs) rest)))

;; open-scope: the new explicit scope inherits the witness of the run's current scope
(a/theorem open-scopes-have-runs-open [w :- World, r :- RunRow, s :- Nat]
  (=> (= s (:next-id w)) (= (scope-has w (cur-scope w r)) true) (List.Mem r (:runs w)) (= (open-scopes-have-runs w) true)
      (= (open-scopes-have-runs (bump (scope-ins w (ScopeRow.mk s (cur-scope w r) scope-explicit true)))) true))
  (intros hs hc mr h)
  (have hsm := (open-scopes-have-runs-well-formed w h))
  (apply (open-scopes-have-runs-scope-ins w (ScopeRow.mk s (cur-scope w r) scope-explicit true) hs _ h))
  (intro n)
  (have cz := (scope-pos w (cur-scope w r) hsm hc))
  (have mc (List.Mem (cur-scope w r) (scope-up (bump (scope-ins w (ScopeRow.mk s (cur-scope w r) scope-explicit true))) s)))
  (rw [(cy-up _ s)])
  (simp only [bump scope-ins set-next-id set-scopes tbl-ins tbl-find scope-id Nat.beq_refl cy-par nz cz])
  (exact (List.Mem.head _))
  (have tr (forall [a :- Nat] (=> (= (scope-within w (cur-scope w r) a) true)
                                  (= (scope-within (bump (scope-ins w (ScopeRow.mk s (cur-scope w r) scope-explicit true))) s a) true))))
  (intros a e)
  (exact (wi-child _ s (cur-scope w r) a mc
           (wi-mono w _ (cur-scope w r) a
             (fn [z :- Nat, b :- Nat, hb :- (List.Mem b (scope-up w z))] (ins-up w (ScopeRow.mk s (cur-scope w r) scope-explicit true) z b hs hsm hb)) e)))
  (apply (cur-cases w r _))
  (intro e)
  (have e2 (= (scope-within w (cur-scope w r) (:scope r)) true)) (rw [e]) (exact (wi-self w (:scope r)))
  (exact (hw-intro (bump (scope-ins w (ScopeRow.mk s (cur-scope w r) scope-explicit true))) s r mr (tr (:scope r) e2)))
  (intros c mc2 ic nc)
  (have hw0 := (open-scopes-have-runs-rest-mem w c (open-scopes-have-runs-rest-of w h) mc2 nc))
  (rw [ic] at hw0)
  (apply (hw-elim w (cur-scope w r) _ hw0))
  (intros q mq eq)
  (exact (hw-intro (bump (scope-ins w (ScopeRow.mk s (cur-scope w r) scope-explicit true))) s q mq (tr (:scope q) eq))))

;; detach: x is re-parented; x is a run's scope (or no scope row)
(a/theorem open-scopes-have-runs-set-parent [w :- World, x :- Nat, p :- Nat]
  (=> (forall [Q :- Prop] (=> (forall [q :- RunRow] (=> (List.Mem q (:runs w)) (= (:scope q) x) Q)) (=> (= (scope-has w x) false) Q) Q))
      (= (open-scopes-have-runs w) true) (= (open-scopes-have-runs (scope-upd w x (scope-set-parent p))) true))
  (intros hx h)
  (have i := (well-formed-scope-upd w x (scope-set-parent p) (scope-set-parent-id p) (open-scopes-have-runs-well-formed w h)))
  (apply (open-scopes-have-runs-intro _ i))
  (apply (hx _))
  (intros q mq eq)
  (have es (= (:scopes (scope-upd w x (scope-set-parent p))) (tbl-upd scope-id x (scope-set-parent p) (:scopes w)))) (rfl)
  (have he (forall [z :- Nat] (=> (= (Nat.beq z x) false) (= (scope-up (scope-upd w x (scope-set-parent p)) z) (scope-up w z)))))
  (intros z hz)
  (rw [(cy-up _ z) (cy-up w z) es (tbl-find-upd-ne ScopeRow scope-id x z (scope-set-parent p) (scope-set-parent-id p) (:scopes w) hz)])
  (have hwx (= (hw (scope-upd w x (scope-set-parent p)) x) true))
  (apply (hw-intro (scope-upd w x (scope-set-parent p)) x q mq)) (rw [eq]) (exact (wi-self _ x))
  (have h0 := (open-scopes-have-runs-rest-of w h))
  (simp only [open-scopes-have-runs-rest] at h0) (simp only [open-scopes-have-runs-rest]) (try (rw [es]))
  (apply (tbl-all-upd ScopeRow scope-id x (scope-set-parent p) (os-ok w) (os-ok (scope-upd w x (scope-set-parent p))) _ _ (:scopes w) h0))
  (intros c qc ec)
  (apply (os-ok-intro _ (scope-set-parent p c)))
  (intro n)
  (have ix (= (:id (scope-set-parent p c)) x)) (exact (Nat.eq_of_beq_eq_true ec))
  (rw [ix]) (exact hwx)
  (intros c qc ec)
  (apply (os-ok-intro _ c))
  (intro n)
  (apply (hw-elim w (:id c) _ (os-ok-of w c qc n)))
  (intros q2 mq2 e2)
  (have o := (rp-within w _ x (:id c) (:scope q2) he e2))
  (cases o)
  (case [inl a1] (exact (hw-intro (scope-upd w x (scope-set-parent p)) (:id c) q2 mq2 a1)))
  (case [inr a2] (apply (hw-intro (scope-upd w x (scope-set-parent p)) (:id c) q mq)) (rw [eq]) (exact a2))
  (intro ha)
  (have es (= (:scopes (scope-upd w x (scope-set-parent p))) (:scopes w)))
  (exact (tbl-upd-absent ScopeRow scope-id x (scope-set-parent p) (:scopes w) ha))
  (exact (open-scopes-have-runs-rest-runs w _ es (fn [q :- RunRow, mq :- (List.Mem q (:runs w))] (rcov-mem _ q mq)) (open-scopes-have-runs-rest-of w h))))
(a/theorem open-scopes-have-runs-set-parent-tr [w :- World, k :- Nat, s :- Nat, t :- TaskRow]
  (=> (= (open-scopes-have-runs (task-upd w k (task-set-owner s))) true)
      (= (open-scopes-have-runs (scope-upd (task-upd w k (task-set-owner s)) (task-run-scope w t) (scope-set-parent s))) true))
  (intro h)
  (apply (open-scopes-have-runs-set-parent _ (task-run-scope w t) s _ h))
  (intros Q k1 k2)
  (cases hr (run-find w (:run t)))
  (case [none]
    (apply k2) (simp only [task-run-scope hr])
    (cases hz (scope-has (task-upd w k (task-set-owner s)) 0))
    (case [false] (rfl))
    (case [true] (have z := (scope-pos _ 0 (open-scopes-have-runs-well-formed _ h) hz)) (simp at z)))
  (case [some q]
    (apply (k1 q))
    (exact (tbl-find-mem RunRow run-id (:run t) q (:runs w) hr))
    (simp only [task-run-scope hr])))

;; scope deletion of a removable subtree: kept chains unchanged
(a/theorem del-fold-runs [sub :- (List Nat)] (forall [w :- World] (= (:runs (nat-fold scope-del w sub)) (:runs w)))
  (induction sub)
  (case [nil] (intro w) (simp only [nat-fold]))
  (case [cons x t ih] (intro w) (simp only [nat-fold]) (rw [(ih (scope-del w x))]) (try (rfl))))

;; ===========================================================================
;; Part F. T13: the subtree is closed before the run row goes (bundle open-scopes-have-runs-exempt over the source closes)
;; ===========================================================================

(a/theorem del-mem [A :- Type, idf :- (=> A Nat), x :- Nat, q :- A, xs :- (List A)]
  (=> (List.Mem q xs) (= (Nat.beq (idf q) x) false) (List.Mem q (tbl-del idf x xs)))
  (induction xs)
  (case [nil] (intros m e) (cases m))
  (case [cons h t ih]
    (intros m e)
    (cases m)
    (case [head] (simp only [tbl-del e]) (exact (List.Mem.head _)))
    (case [tail m2]
      (cases hx (Nat.beq (idf h) x))
      (case [true] (simp only [tbl-del hx]) (exact (ih m2 e)))
      (case [false] (simp only [tbl-del hx]) (exact (List.Mem.tail _ (ih m2 e)))))))
(a/theorem find-uniq [A :- Type, idf :- (=> A Nat), xs :- (List A), q :- A, r :- A]
  (=> (= (nat-nodup (tbl-ids idf xs)) true) (List.Mem q xs) (= (tbl-find idf (idf q) xs) (Option.some A r)) (= q r))
  (induction xs)
  (case [nil] (intros hn m hf) (cases m))
  (case [cons h t ih]
    (intros hn m hf)
    (simp only [tbl-ids nat-nodup Bool.and_eq_true] at hn)
    (cases m)
    (case [head] (simp only [tbl-find Nat.beq_refl] at hf) (cases hf) (rfl))
    (case [tail m2]
      (cases hb (Nat.beq (idf h) (idf q)))
      (case [true]
        (have e := (Nat.eq_of_beq_eq_true hb))
        (have mm := (mem-ids-has A idf q t m2))
        (rw [← e] at mm)
        (have z := (And.left hn)) (rw [mm] at z) (simp at z))
      (case [false] (simp only [tbl-find hb] at hf) (exact (ih (And.right hn) m2 hf))))))
(a/theorem os-runs-nodup [w :- World] (=> (= (well-formed w) true) (= (nat-nodup (tbl-ids run-id (:runs w))) true))
  (intro h)
  (have u := (ids-unique-of w h))
  (simp only [all-ids] at u)
  (exact (nat-nodup-app-left _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ u))))))
(a/theorem rf-self [w :- World, rid :- Nat, r :- RunRow]
  (=> (= (run-find w rid) (Option.some RunRow r)) (= (run-find w (:id r)) (Option.some RunRow r)))
  (intro h)
  (have i (= (:id r) rid)) (exact (tbl-find-id RunRow run-id rid r (:runs w) h))
  (rw [i]) (exact h))

;; clear-comp-run touches no scope or run row
(a/theorem cc-scopes [w :- World, r :- RunRow] (= (:scopes (clear-comp-run w r)) (:scopes w))
  (cases hc (comp-find w (:of r)))
  (case [some c]
    (cases he (Nat.beq (:run c) (:id r)))
    (all_goals (simp only [clear-comp-run hc he comp-upd set-comps])))
  (case [none]
    (cases ht (task-find w (:of r)))
    (case [none] (simp only [clear-comp-run hc clear-task-run ht]))
    (case [some t]
      (cases he (Nat.beq (:run t) (:id r)))
      (all_goals (simp only [clear-comp-run hc clear-task-run ht he task-upd set-tasks])))))
(a/theorem cc-runs [w :- World, r :- RunRow] (= (:runs (clear-comp-run w r)) (:runs w))
  (cases hc (comp-find w (:of r)))
  (case [some c]
    (cases he (Nat.beq (:run c) (:id r)))
    (all_goals (simp only [clear-comp-run hc he comp-upd set-comps])))
  (case [none]
    (cases ht (task-find w (:of r)))
    (case [none] (simp only [clear-comp-run hc clear-task-run ht]))
    (case [some t]
      (cases he (Nat.beq (:run t) (:id r)))
      (all_goals (simp only [clear-comp-run hc clear-task-run ht he task-upd set-tasks])))))
(a/theorem cc-tabs [w :- World, r :- RunRow] (And (= (:scopes (clear-comp-run w r)) (:scopes w)) (= (:runs (clear-comp-run w r)) (:runs w)))
  (exact (And.intro (cc-scopes w r) (cc-runs w r))))

;; the fold of scope closes: runs and parents unchanged, every row of the subtree closed
(a/theorem csf-runs [sub :- (List Nat)] (forall [w :- World] (= (:runs (nat-fold close-scope-id w sub)) (:runs w)))
  (induction sub)
  (case [nil] (intro w) (simp only [nat-fold]))
  (case [cons x t ih] (intro w) (simp only [nat-fold]) (rw [(ih (close-scope-id w x))]) (try (rfl))))
(a/theorem csf-up [sub :- (List Nat)] (forall [w :- World, z :- Nat] (= (scope-up (nat-fold close-scope-id w sub) z) (scope-up w z)))
  (induction sub)
  (case [nil] (intros w z) (simp only [nat-fold]))
  (case [cons x t ih]
    (intros w z) (simp only [nat-fold]) (rw [(ih (close-scope-id w x) z)])
    (have es (= (:scopes (close-scope-id w x)) (tbl-upd scope-id x scope-close (:scopes w)))) (rfl)
    (rw [(cy-up (close-scope-id w x) z) (cy-up w z) es (cy-par-upd x scope-close scope-close-scope-id (fn [s :- ScopeRow] (Eq.refl (:parent s))) z (:scopes w))])))
(a/defn cl-by [D :- (=> Nat Bool), s :- ScopeRow] Bool (Bool.or (Bool.not (D (:id s))) (Bool.not (:open s))))
(a/theorem clb-nil [D :- (=> Nat Bool), s :- ScopeRow]
  (= (cl-by (fn [y :- Nat] (Bool.or (D y) (reach-mem y (List.nil Nat)))) s) (cl-by D s))
  (simp only [cl-by reach-mem Bool.or_false]))
(a/theorem clb-cons [D :- (=> Nat Bool), x :- Nat, t :- (List Nat), s :- ScopeRow]
  (= (cl-by (fn [y :- Nat] (Bool.or (D y) (reach-mem y (List.cons Nat x t)))) s)
     (cl-by (fn [y :- Nat] (Bool.or (Bool.or (D y) (Nat.beq y x)) (reach-mem y t))) s))
  (simp only [cl-by reach-mem-cons Bool.or_assoc]))
(a/theorem clb-false [s :- ScopeRow] (= (cl-by (fn [y :- Nat] false) s) true)
  (simp only [cl-by Bool.not_false Bool.true_or]))
(a/theorem csf-closed [sub :- (List Nat)]
  (forall [w :- World, D :- (=> Nat Bool)]
    (=> (= (tbl-all (cl-by D) (:scopes w)) true)
        (= (tbl-all (cl-by (fn [y :- Nat] (Bool.or (D y) (reach-mem y sub)))) (:scopes (nat-fold close-scope-id w sub))) true)))
  (induction sub)
  (case [nil]
    (intros w D h) (simp only [nat-fold])
    (rw [(tbl-all-congr ScopeRow _ (cl-by D) (fn [s :- ScopeRow] (clb-nil D s)) (:scopes w))])
    (exact h))
  (case [cons x t ih]
    (intros w D h) (simp only [nat-fold])
    (have h1 (= (tbl-all (cl-by (fn [y :- Nat] (Bool.or (D y) (Nat.beq y x)))) (:scopes (close-scope-id w x))) true))
    (have es (= (:scopes (close-scope-id w x)) (tbl-upd scope-id x scope-close (:scopes w)))) (rfl)
    (rw [es])
    (apply (tbl-all-upd ScopeRow scope-id x scope-close (cl-by D) _ _ _ (:scopes w) h))
    (intros c q e) (simp only [cl-by scope-close Bool.not_false Bool.or_true])
    (intros c q e)
    (have e2 (= (Nat.beq (:id c) x) false)) (exact e)
    (simp only [cl-by] at q) (simp only [cl-by e2 Bool.or_false]) (exact q)
    (have r := (ih (close-scope-id w x) _ h1))
    (rw [(tbl-all-congr ScopeRow _ (cl-by (fn [y :- Nat] (Bool.or (Bool.or (D y) (Nat.beq y x)) (reach-mem y t))))
           (fn [s :- ScopeRow] (clb-cons D x t s))
           (:scopes (nat-fold close-scope-id (close-scope-id w x) t)))])
    (exact r)))
(a/theorem csf-open [sub :- (List Nat), w :- World, c :- ScopeRow]
  (=> (List.Mem c (:scopes (nat-fold close-scope-id w sub))) (= (os-need c) true) (= (reach-mem (:id c) sub) false))
  (intros m n)
  (have a := (csf-closed sub w (fn [y :- Nat] false) (all-of-mem ScopeRow _ (:scopes w) (fn [s :- ScopeRow, ms :- (List.Mem s (:scopes w))] (clb-false s)))))
  (have b := (tbl-all-mem ScopeRow _ c _ a m))
  (simp only [os-need Bool.and_eq_true] at n)
  (simp only [cl-by (And.left n) Bool.false_or Bool.not_true Bool.or_false] at b)
  (exact (cy-not-true _ b)))

;; ---- the bundle open-scopes-have-runs-exempt x: every scope row with os-need has a witness run whose id is not x
(a/defn run-within-ne [w :- World, y :- Nat, x :- Nat, q :- RunRow] Bool
  (Bool.and (Bool.not (Nat.beq (:id q) x)) (scope-within w y (:scope q))))
(a/defn hwx [w :- World, y :- Nat, x :- Nat] Bool (tbl-any (run-within-ne w y x) (:runs w)))
(a/defn ox-ok [x :- Nat, w :- World, s :- ScopeRow] Bool (Bool.or (Bool.not (os-need s)) (hwx w (:id s) x)))
(a/defn open-scopes-have-runs-exempt-rest [xr9 :- Nat, w :- World] Bool (tbl-all (ox-ok xr9 w) (:scopes w)))
(a/defn open-scopes-have-runs-exempt [xr9 :- Nat, w :- World] Bool (Bool.and (well-formed w) (open-scopes-have-runs-exempt-rest xr9 w)))
(a/theorem open-scopes-have-runs-exempt-well-formed [xr9 :- Nat, w :- World] (=> (= (open-scopes-have-runs-exempt xr9 w) true) (= (well-formed w) true))
  (intro h) (simp only [open-scopes-have-runs-exempt Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem open-scopes-have-runs-exempt-rest-of [xr9 :- Nat, w :- World] (=> (= (open-scopes-have-runs-exempt xr9 w) true) (= (open-scopes-have-runs-exempt-rest xr9 w) true))
  (intro h) (simp only [open-scopes-have-runs-exempt Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem open-scopes-have-runs-exempt-intro [xr9 :- Nat, w :- World] (=> (= (well-formed w) true) (= (open-scopes-have-runs-exempt-rest xr9 w) true) (= (open-scopes-have-runs-exempt xr9 w) true))
  (intros h1 h2) (simp only [open-scopes-have-runs-exempt h1 h2 Bool.and_self]))
(a/theorem open-scopes-have-runs-exempt-parts [xr9 :- Nat, w :- World]
  (=> (= (open-scopes-have-runs-exempt xr9 w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (open-scopes-have-runs-exempt-well-formed xr9 w h))))

(a/theorem upd-cov2 [x :- Nat, f :- (=> RunRow RunRow), hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                     hk :- (forall [r :- RunRow] (= (:scope (f r)) (:scope r))), q :- RunRow, xs :- (List RunRow), P :- Prop]
  (=> (List.Mem q xs) (forall [q2 :- RunRow] (=> (List.Mem q2 (tbl-upd run-id x f xs)) (= (:id q2) (:id q)) (= (:scope q2) (:scope q)) P)) P)
  (induction xs)
  (case [nil] (intros m k) (cases m))
  (case [cons h t ih]
    (intros m k)
    (cases m)
    (case [head]
      (cases hx (Nat.beq (run-id q) x))
      (case [false] (apply (k q)) (simp only [tbl-upd hx]) (exact (List.Mem.head _)) (rfl) (rfl))
      (case [true] (apply (k (f q))) (simp only [tbl-upd hx]) (exact (List.Mem.head _)) (exact (hf q)) (exact (hk q))))
    (case [tail m2]
      (apply (ih m2))
      (intros q2 mq2 e1 e2)
      (apply (k q2 _ e1 e2))
      (cases hx (Nat.beq (run-id h) x))
      (all_goals (simp only [tbl-upd hx]))
      (all_goals (exact (List.Mem.tail _ mq2))))))
(a/theorem open-scopes-have-runs-exempt-run-upd [xr9 :- Nat, w :- World, x :- Nat, f :- (=> RunRow RunRow), hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                        hk :- (forall [r :- RunRow] (= (:scope (f r)) (:scope r)))]
  (=> (= (open-scopes-have-runs-exempt xr9 w) true) (= (open-scopes-have-runs-exempt xr9 (run-upd w x f)) true))
  (intro h)
  (apply (open-scopes-have-runs-exempt-intro _ _ (well-formed-run-upd w x f hf (open-scopes-have-runs-exempt-well-formed xr9 w h))))
  (have h0 := (open-scopes-have-runs-exempt-rest-of xr9 w h))
  (simp only [open-scopes-have-runs-exempt-rest] at h0)
  (simp only [open-scopes-have-runs-exempt-rest])
  (apply (tbl-all-mono ScopeRow (ox-ok xr9 w) (ox-ok xr9 (run-upd w x f)) _ (:scopes w) h0))
  (intros c q)
  (cases hn (os-need c))
  (case [false] (simp only [ox-ok hn Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [ox-ok hn Bool.not_true Bool.false_or] at q)
    (simp only [ox-ok hn Bool.not_true Bool.false_or])
    (apply (any-elim RunRow (run-within-ne w (:id c) xr9) _ (:runs w) q))
    (intros q1 m1 e1)
    (apply (upd-cov2 x f hf hk q1 (:runs w) _ m1))
    (intros q2 m2 i2 s2)
    (apply (any-elim-of RunRow _ q2 _ m2))
    (simp only [run-within-ne i2 s2])
    (exact e1)))
(a/theorem open-scopes-have-runs-exempt-rest-mark-edge [xr9 :- Nat, w :- World, x :- Nat] (= (open-scopes-have-runs-exempt-rest xr9 (mark-edge w x)) (open-scopes-have-runs-exempt-rest xr9 w))
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [mark-edge hf hm]))))
(a/theorem open-scopes-have-runs-exempt-rest-unmark-edge [xr9 :- Nat, w :- World, x :- Nat] (= (open-scopes-have-runs-exempt-rest xr9 (unmark-edge w x)) (open-scopes-have-runs-exempt-rest xr9 w))
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [unmark-edge hf hm]))))
(a/theorem open-scopes-have-runs-exempt-rest-remove-edge [xr9 :- Nat, w :- World, x :- Nat] (= (open-scopes-have-runs-exempt-rest xr9 (remove-edge w x)) (open-scopes-have-runs-exempt-rest xr9 w))
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [remove-edge hf hm]))))

(def GOX (mk-bundle 'open-scopes-have-runs-exempt '[xr9 :- Nat] "open-scopes-have-runs-exempt-" {'well-formed-run-upd ['(fn [r :- RunRow] (Eq.refl (:scope r))) 4]}))
(swap! (:renames GOX) assoc 'well-formed-parts 'open-scopes-have-runs-exempt-parts 'well-formed-run-upd 'open-scopes-have-runs-exempt-run-upd)
(doseq [o '[well-formed-pub-upd well-formed-source-upd well-formed-resource-upd well-formed-cleanup-upd well-formed-cleanup-del well-formed-comp-upd well-formed-task-upd
            well-formed-set-pins well-formed-resource-del well-formed-cleanup-ins well-formed-act-upd well-formed-edge-upd well-formed-drop-cred-edges well-formed-drop-edges well-formed-drop-act
            well-formed-comp-del-unref well-formed-source-ins-fresh well-formed-fork-ins-fresh well-formed-resource-ins-fresh well-formed-act-ins-fresh well-formed-comp-ins-fresh
            well-formed-task-ins-fresh well-formed-bump well-formed-insert-edge-fresh well-formed-fork-del]]
  (prim! GOX o nil))
(prim! GOX 'well-formed-mark-edge '(Eq.trans (open-scopes-have-runs-exempt-rest-mark-edge xr9 w x) R))
(prim! GOX 'well-formed-unmark-edge '(Eq.trans (open-scopes-have-runs-exempt-rest-unmark-edge xr9 w x) R))
(prim! GOX 'well-formed-remove-edge '(Eq.trans (open-scopes-have-runs-exempt-rest-remove-edge xr9 w x) R))
(tree/restate! GOX '[well-formed-nat-fold well-formed-close-source])

;; ===========================================================================
;; Part G. The copy of open-scopes-have-runs
;; ===========================================================================


(def GOS (mk-bundle 'open-scopes-have-runs [] "open-scopes-have-runs-"
           {'well-formed-run-upd ['(fn [r :- RunRow] (Eq.refl (:scope r))) 4]
            'well-formed-scope-upd ['(fn [s :- ScopeRow] (And.intro (Eq.refl (:parent s)) (fn [q :- (= (os-need s) true)] q))) 4]}))
(swap! (:renames GOS) assoc 'well-formed-parts 'open-scopes-have-runs-parts 'well-formed-run-upd 'open-scopes-have-runs-run-upd 'well-formed-scope-upd 'open-scopes-have-runs-scope-upd)
(defpart GOS :reads '[runs scopes])
(frames/frame-theorem! 'open-scopes-have-runs-rest-mark-edge 'open-scopes-have-runs-rest 'well-formed-mark-edge)
(frames/frame-theorem! 'open-scopes-have-runs-rest-unmark-edge 'open-scopes-have-runs-rest 'well-formed-unmark-edge)
(frames/frame-theorem! 'open-scopes-have-runs-rest-remove-edge 'open-scopes-have-runs-rest 'well-formed-remove-edge)
(prim! GOS 'well-formed-run-ins-fresh '(open-scopes-have-runs-rest-run-ins w r R))
(prim! GOS 'well-formed-close-scope-id '(open-scopes-have-runs-rest-scope-upd w x scope-close scope-close-scope-id close-hk R))

;; open-scopes-have-runs on the generic tree (spindel.v2.pres.tree): its table. Its own proofs follow.
(tree/part! GOS
  :over '{well-formed-add-run-scope   open-scopes-have-runs-add-run-scope
          well-formed-t-open-scope    open-scopes-have-runs-t-open-scope
          well-formed-remove-if-empty open-scopes-have-runs-remove-if-empty
          well-formed-t-detach        open-scopes-have-runs-t-detach
          well-formed-retire-run    open-scopes-have-runs-retire-run}
  ;; ---- T13's retired run is the row run-find finds at its own id
  :ctx '{well-formed-retire-run [(= (run-find w (:id r)) (Option.some RunRow r))]}
  :pass '{well-formed-job-apply {well-formed-retire-run [(rf-self w rid r hf)]}})

;; run creation: the run scope is the new run's
(a/theorem open-scopes-have-runs-add-run-scope [w :- World, of :- Nat, epoch :- Nat, parent :- Nat, ei :- Nat]
  (=> (= (open-scopes-have-runs w) true) (= (open-scopes-have-runs (add-run-scope w of epoch parent ei)) true))
  (intro h)
  (simp only [add-run-scope])
  (have h1 (= (open-scopes-have-runs (bump (run-ins w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei)))) true))
  (exact (open-scopes-have-runs-intro _ (well-formed-run-ins-fresh w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei) (rfl) (open-scopes-have-runs-well-formed w h))
           (open-scopes-have-runs-rest-run-ins w _ (open-scopes-have-runs-rest-of w h))))
  (apply (open-scopes-have-runs-scope-ins (bump (run-ins w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei))) (new-scope-row (+ (:next-id w) 1) parent) (rfl) _ h1))
  (intro n)
  (have mr (List.Mem (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei)
                     (List.cons RunRow (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei) (:runs w))))
  (exact (List.Mem.head _))
  (exact (hw-intro (bump (scope-ins (bump (run-ins w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei))) (new-scope-row (+ (:next-id w) 1) parent))) (+ (:next-id w) 1) (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei) mr (wi-self _ _))))
;; open-scope: under the run's current scope
(a/theorem open-scopes-have-runs-t-open-scope [w :- World, st :- Nat, s :- Nat]
  (=> (= (open-scopes-have-runs w) true) (= (open-scopes-have-runs (:world (t-open-scope w st s))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t-open-scope ht refuse]) (exact h)
  (cases hg (Bool.and (Nat.beq s (:next-id w)) (open-ok w r)))
  (simp only [t-open-scope ht hg refuse]) (exact h)
  (have hs (= s (:next-id w))) (simp only [Bool.and_eq_true Nat.beq_eq] at hg) (exact (And.left hg))
  (have hc (= (scope-has w (cur-scope w r)) true))
  (simp only [open-ok Bool.and_eq_true] at hg) (exact (And.right (And.right hg)))
  (simp only [t-open-scope ht hg accept])
  (exact (open-scopes-have-runs-open w r s hs hc (And.left (tok-facts w st r ht)) h)))
;; scope deletion (Z#18): the kept scopes' parents are kept (parent-outside)
(a/theorem open-scopes-have-runs-remove-if-empty [w :- World, sub :- (List Nat)]
  (=> (= (open-scopes-have-runs w) true) (= (open-scopes-have-runs (remove-if-empty w sub)) true))
  (intro h)
  (have i := (well-formed-remove-if-empty w sub (open-scopes-have-runs-well-formed w h)))
  (cases he (subtree-empty w sub))
  (case [false] (simp only [remove-if-empty he]) (exact h))
  (case [true]
    (have po (= (tbl-all (parent-outside sub) (:scopes w)) true))
    (simp only [subtree-empty Bool.and_eq_true] at he) (exact (And.left he))
    (simp only [remove-if-empty he] at i)
    (simp only [remove-if-empty he])
    (apply (open-scopes-have-runs-intro _ i))
    (apply (open-scopes-have-runs-rest-keep w (nat-fold scope-del w sub) (not-in sub) (scope-del-fold sub w) _ _ (open-scopes-have-runs-rest-of w h)))
    (intros c m k p0)
    (have pc := (tbl-all-mem ScopeRow (parent-outside sub) c (:scopes w) po m))
    (simp only [parent-outside Bool.or_eq_true] at pc)
    (cases pc)
    (case [inl a1] (simp only [not-in a1 Bool.not_true] at k) (cases k))
    (case [inr b1] (simp only [not-in]) (exact b1))
    (intros q mq) (rw [(del-fold-runs sub w)]) (exact (rcov-mem _ q mq))))
;; detach: the run scope is its run's
(tree/restate! GOS '[well-formed-task-upd])
(a/theorem open-scopes-have-runs-t-detach [w :- World, k :- Nat, s :- Nat]
  (=> (= (open-scopes-have-runs w) true) (= (open-scopes-have-runs (:world (t-detach w k s))) true))
  (intro h)
  (cases hf (task-find w k))
  (case [none] (simp only [t-detach hf refuse]) (exact h))
  (case [some t]
    (cases hg (detach-ok w t s))
    (case [false] (simp only [t-detach hf hg refuse]) (exact h))
    (case [true]
      (simp only [t-detach hf hg accept remove-empty-at detach-move])
      (have h1 := (open-scopes-have-runs-task-upd w k (task-set-owner s) (task-set-owner-id s) h))
      (exact (open-scopes-have-runs-remove-if-empty _ _ (open-scopes-have-runs-set-parent-tr w k s t h1))))))
;; T13: the run row goes after its run scope's subtree is closed (the witness open-scopes-have-runs-exempt)
(tree/restate! GOS '[well-formed-clear-comp-run well-formed-close-scope-id well-formed-nat-fold well-formed-cleanup-del])
(a/theorem open-scopes-have-runs-retire-run [w :- World, r :- RunRow]
  (=> (= (run-find w (:id r)) (Option.some RunRow r)) (= (open-scopes-have-runs w) true) (= (open-scopes-have-runs (retire-run w r)) true))
  (intros hfr h)
  (have hs := (open-scopes-have-runs-well-formed w h))
  (have cc := (cc-tabs w r))
  (have g1 := (open-scopes-have-runs-clear-comp-run w r h))
  (have g1c := (open-scopes-have-runs-nat-fold close-scope-id open-scopes-have-runs-close-scope-id (scope-subtree w (:scope r)) (clear-comp-run w r) g1))
  (have ox (= (open-scopes-have-runs-exempt (:id r) (nat-fold close-scope-id (clear-comp-run w r) (scope-subtree w (:scope r)))) true))
  (apply (open-scopes-have-runs-exempt-intro _ _ (open-scopes-have-runs-well-formed _ g1c)))
  (simp only [open-scopes-have-runs-exempt-rest])
  (apply (all-of-mem ScopeRow _ _))
  (intros c m)
  (cases hn (os-need c))
  (case [false] (simp only [ox-ok hn Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [ox-ok hn Bool.not_true Bool.false_or])
    (have nin := (csf-open (scope-subtree w (:scope r)) (clear-comp-run w r) c m hn))
    (have hw1 := (open-scopes-have-runs-rest-mem _ c (open-scopes-have-runs-rest-of _ g1c) m hn))
    (apply (hw-elim _ (:id c) _ hw1))
    (intros q mq eq)
    (cases hq (Nat.beq (:id q) (:id r)))
    (case [false]
      (apply (any-elim-of RunRow _ q _ mq))
      (simp only [run-within-ne hq Bool.not_false Bool.true_and]) (exact eq))
    (case [true]
      (have mq0 (List.Mem q (:runs w)))
      (rw [(csf-runs (scope-subtree w (:scope r)) (clear-comp-run w r)) (And.right cc)] at mq) (exact mq)
      (have ef (= (tbl-find run-id (run-id q) (:runs w)) (Option.some RunRow r)))
      (have e (= (run-id q) (:id r))) (exact (Nat.eq_of_beq_eq_true hq))
      (rw [e]) (exact hfr)
      (have qr := (find-uniq RunRow run-id (:runs w) q r (os-runs-nodup w hs) mq0 ef))
      (have ew (= (scope-within w (:id c) (:scope r)) true))
      (rw [← qr])
      (apply (wi-mono _ w (:id c) (:scope q) _ eq))
      (intros z b hb)
      (rw [(csf-up (scope-subtree w (:scope r)) (clear-comp-run w r) z)] at hb)
      (have e3 := (cy-up w z)) (rw [(cy-up _ z) (And.left cc) ← e3] at hb)
      (exact hb)
      (have cp (= (Nat.beq (:id c) 0) false))
      (apply (scope-pos _ (:id c) (open-scopes-have-runs-well-formed _ g1c)))
      (simp only [scope-has]) (rw [← (nat-mem-ids ScopeRow scope-id (:id c) _)]) (exact (mem-ids-has ScopeRow scope-id c _ m))
      (have ins := (sub-within w (:scope r) (:id c) cp ew))
      (rw [ins] at nin) (cases nin)))
  (have ox2 := (open-scopes-have-runs-exempt-nat-fold (:id r) close-source (open-scopes-have-runs-exempt-close-source (:id r))
                 (tbl-scan source-id (source-owned-in (scope-subtree w (:scope r))) (:sources (clear-comp-run w r))) _ ox))
  (simp only [retire-run t13-retire-with-subtree close-local])
  (have g3 (= (open-scopes-have-runs (run-del (nat-fold close-source (nat-fold close-scope-id (clear-comp-run w r) (scope-subtree w (:scope r)))
                               (tbl-scan source-id (source-owned-in (scope-subtree w (:scope r))) (:sources (clear-comp-run w r))))
                             (:id r))) true))
  (apply (open-scopes-have-runs-intro _ (well-formed-run-del _ (:id r) (open-scopes-have-runs-exempt-well-formed _ _ ox2))))
  (apply (open-scopes-have-runs-rest-tr _))
  (intros c m n)
  (have hx (= (hwx (nat-fold close-source (nat-fold close-scope-id (clear-comp-run w r) (scope-subtree w (:scope r)))
                     (tbl-scan source-id (source-owned-in (scope-subtree w (:scope r))) (:sources (clear-comp-run w r)))) (:id c) (:id r)) true))
  (have o := (tbl-all-mem ScopeRow _ c _ (open-scopes-have-runs-exempt-rest-of _ _ ox2) m))
  (simp only [ox-ok n Bool.not_true Bool.false_or] at o) (exact o)
  (simp only [hwx] at hx)
  (apply (any-elim RunRow _ _ _ hx))
  (intros q mq e)
  (simp only [run-within-ne Bool.and_eq_true] at e)
  (apply (hw-intro (run-del (nat-fold close-source (nat-fold close-scope-id (clear-comp-run w r) (scope-subtree w (:scope r))) (tbl-scan source-id (source-owned-in (scope-subtree w (:scope r))) (:sources (clear-comp-run w r)))) (:id r)) (:id c) q (del-mem RunRow run-id (:id r) q _ mq (cy-not-true _ (And.left e)))))
  (exact (And.right e))
  (exact (open-scopes-have-runs-remove-if-empty _ (scope-subtree w (:scope r)) (open-scopes-have-runs-cleanup-del _ (:id r) g3))))
(tree/restate! GOS '[well-formed-raw well-formed-normalize])

;; ===========================================================================
;; Part H. Rule R and the step: the filter keeps every run (i1-runs, normalized) and every kept scope's parent
;; ===========================================================================

(a/theorem keep-parent [w :- World, c :- ScopeRow]
  (=> (= (well-formed w) true) (List.Mem c (:scopes w)) (= (keep-fn w (:id c)) true) (= (Nat.beq (:parent c) 0) false)
      (= (keep-fn w (:parent c)) true))
  (intros hs ms ks hp)
  (have k2 (= (keep-with w (live-list w) (cleanup-rows w) (storage w) (:id c)) true)) (exact ks)
  (simp only [keep-with Bool.or_eq_true] at k2)
  (cases k2)
  (case [inl a1] (exact (keep-of-live w (:parent c) (live-parent w c ms hp a1))))
  (case' [inr b])
  (cases b)
  (case [inl c1]
    (have q := (cleanup-closed w (:cleanup w) (:id c) (:parent c) c1 (scope-up-of-mem w c hs ms hp)))
    (have q2 (= (reach-mem (:parent c) (cleanup-rows w)) true)) (exact q)
    (simp only [keep-fn keep-with q2 Bool.true_or Bool.or_true]))
  (case' [inr d])
  (cases d)
  (case [inl e] (have z := (scope-not-admitted w c hs ms)) (rw [z] at e) (cases e))
  (case' [inr f])
  (have q (= (reach-mem (:parent c) (storage w)) true))
  (exact (anc-close-closed w (storage-gather w (live-list w)) (:id c) (:parent c) f (scope-up-of-mem w c hs ms hp)))
  (simp only [keep-fn keep-with q Bool.or_true]))

(a/theorem open-scopes-have-runs-filter [W :- World]
  (=> (= (normalized W) true) (= (i1-runs W) true) (= (open-scopes-have-runs W) true) (= (filter-safe W) true) (= (open-scopes-have-runs (rule-r-filter W)) true))
  (intros hn hg h hf)
  (rw [rule-r-filter-eq])
  (apply (open-scopes-have-runs-intro _ (well-formed-filter-world W (keep-fn W) (open-scopes-have-runs-well-formed W h) hf)))
  (apply (open-scopes-have-runs-rest-keep W (filter-world (keep-fn W) W) (keep-fn W) (rfl) _ _ (open-scopes-have-runs-rest-of W h)))
  (intros c m k p0) (exact (keep-parent W c (open-scopes-have-runs-well-formed W h) m k p0))
  (intros q mq)
  (have e (= (:runs (filter-world (keep-fn W) W)) (:runs W)))
  (simp only [filter-world])
  (exact (keep-all-of RunRow (keep-fn W) run-id (:runs W)
           (fn [q2 :- RunRow, m2 :- (List.Mem q2 (:runs W))] (And.left (run-kept W q2 hn hg m2)))))
  (rw [e]) (exact (rcov-mem _ q mq)))

(a/theorem open-scopes-have-runs-rule-r-round [w :- World]
  (=> (= (acts-alive w) true) (= (i1-runs w) true) (= (open-scopes-have-runs w) true) (= (filter-safe (normalize w)) true) (= (open-scopes-have-runs (rule-r-round w)) true))
  (intros ha hg h hf)
  (simp only [rule-r-round])
  (exact (open-scopes-have-runs-filter (normalize w) (normalized-ok w (open-scopes-have-runs-well-formed w h) ha) (i1-runs-normalize-aa w ha hg) (open-scopes-have-runs-normalize w h) hf)))
(a/theorem open-scopes-have-runs-rule-r-loop [fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (acts-alive w0) true) (= (i1-runs w0) true) (= (open-scopes-have-runs w0) true) (= (rounds-safe-loop fuel w0) true)
                            (= (open-scopes-have-runs (rule-r-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 ha hg h hs) (simp only [rounds-safe-loop] at hs) (simp only [rule-r-loop]) (exact (open-scopes-have-runs-rule-r-round w0 ha hg h hs)))
  (case [cons x f ih]
    (intros w0 ha hg h hs)
    (have hs0 := (rounds-safe-loop-head x f w0 hs))
    (have h1 := (open-scopes-have-runs-rule-r-round w0 ha hg h hs0))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false]
      (rw [(rule-r-loop-f x f (rule-r-round w0) ho)])
      (exact (ih (rule-r-round w0) (acts-alive-round w0 (open-scopes-have-runs-well-formed w0 h) ha) (i1-runs-rule-r-round w0 ha hg hs0) h1
               (And.right (rounds-safe-loop-f x f w0 hs ho)))))
    (case [true] (rw [(rule-r-loop-t x f (rule-r-round w0) ho)]) (exact h1))))
(a/theorem open-scopes-have-runs-rule-r [w :- World]
  (=> (= (acts-alive w) true) (= (i1-runs w) true) (= (open-scopes-have-runs w) true) (= (rule-r-safe w) true) (= (open-scopes-have-runs (rule-r w)) true))
  (intros ha hg h hs)
  (have hs2 (= (rounds-safe-loop (List.cons Nat 0 (all-ids w)) w) true)) (exact hs)
  (rw [rule-r-eq5])
  (exact (open-scopes-have-runs-rule-r-loop (List.cons Nat 0 (all-ids w)) w ha hg h hs2)))

;; Theorem: every open non-root scope lies in a run's run-scope subtree, after every step
(a/theorem step-open-scopes-have-runs [w :- World, it :- Item]
  (=> (= (acts-parked w) true) (= (i1-runs w) true) (= (open-scopes-have-runs w) true) (= (rule-r-safe (:world (raw w it))) true)
      (= (open-scopes-have-runs (:world (world-step w it))) true))
  (intros hga hg h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true]
    (have e2 := (step-accepted w it ha)) (rw [e2])
    (exact (open-scopes-have-runs-rule-r (:world (raw w it)) (raw-acts-alive w it hga) (i1-runs-raw w it hga hg) (open-scopes-have-runs-raw w it h) hs))))
(a/theorem open-scopes-have-runs-empty [] (= (open-scopes-have-runs empty-world) true) (rfl))
