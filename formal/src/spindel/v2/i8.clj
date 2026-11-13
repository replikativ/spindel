(ns spindel.v2.i8
  "I8 (closed scopes: a closed scope owns no run with act /= done and no open source) through the
  model's step `world-step`, kernel-checked (Init only).

  Reading (inv.clj `lit-i8-runs`, `lit-i8-sources`): no alive run of a task whose owner is a closed
  scope; no open source whose owner is a closed scope.

  Bundle g8 xs w = inv-sample w && every alive run of a task owned by a closed scope is in the escape
  list xs && every open source's owner is not a closed scope. Stated over key lists (run keys (id, of,
  alive), task keys (id, owner), scope keys (id, open), source keys (id, owner, open)), so an edit that
  keeps them is a frame. Closedness is `tbl-any` over the key lists (monotone under the filter, no
  unique-ids argument).
    - closing a subtree (`close-local`: T16, T13's step 2, T21): every scope of the subtree closes and
      every source it owns closes in the same edit; the runs of the tasks it owns are still alive and
      join the escape list: they are exactly the cancel jobs the cascade queues next (`owned-runs`).
      Through the cascade the escape list is the list of pending cancel jobs (`g8-cascade`); a cancel
      job discharges its run (the run is dead after its job, bundle d8); the worklist empties (P4,
      `casc-done-ok` with acts-alive), so the escape list is empty when the cascade returns.
    - new tasks and sources get an owner that is not a closed scope: a computation (ids are unique),
      an open top-level scope (guard), an open detach target (guard), 0 (Rule R's detach), or the
      run's current scope (guard `cur-open`, Z#57 pass: reachable-equivalent, tripwired; the proof
      that an alive task run's current scope is open is obligation P10).

  Theorems:
    step-g8              ga w, g8 [] w, rule-r-safe raw -> g8 [] (world-step w it)
    p3i = p3h && g8 []   step-p3i, p3i-empty
    step-lit-i8-total    p3i w -> lit-i8-runs (world-step w it) && lit-i8-sources (world-step w it)"
  (:require [ansatz.core :as a]
            [clojure.string :as str]
            [clojure.walk :as walk]
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
            [spindel.v2.i10 :refer :all]
            [spindel.v2.i11 :refer :all]
            [spindel.v2.i1 :refer :all]
            [spindel.v2.i5 :refer :all]
            [spindel.v2.i1o :refer :all]
            [spindel.v2.i1r :refer :all]))

;; ===========================================================================
;; Part A. Keys and the bundle
;; ===========================================================================

(a/structure T8K [] (id Nat) (owner Nat))
(a/defn t8k [t :- TaskRow] T8K (T8K.mk (:id t) (:owner t)))
(a/defn t8k-id [k :- T8K] Nat (:id k))
(a/defn t8ks [ts :- (List TaskRow)] (List T8K)
  (match ts [nil (List.nil T8K)] [(cons h t) (List.cons T8K (t8k h) (t8ks t))]))
(a/structure S8K [] (id Nat) (open Bool))
(a/defn s8k [s :- ScopeRow] S8K (S8K.mk (:id s) (:open s)))
(a/defn s8k-id [k :- S8K] Nat (:id k))
(a/defn s8ks [ss :- (List ScopeRow)] (List S8K)
  (match ss [nil (List.nil S8K)] [(cons h t) (List.cons S8K (s8k h) (s8ks t))]))
(a/structure X8K [] (id Nat) (owner Nat) (open Bool))
(a/defn x8k [s :- SourceRow] X8K (X8K.mk (:id s) (:owner s) (:open s)))
(a/defn x8k-id [k :- X8K] Nat (:id k))
(a/defn x8ks [ss :- (List SourceRow)] (List X8K)
  (match ss [nil (List.nil X8K)] [(cons h t) (List.cons X8K (x8k h) (x8ks t))]))
(a/structure KW8 [] (rks (List RKey)) (tks (List T8K)) (sks (List S8K)) (xks (List X8K)))
(a/defn kw8 [w :- World] KW8 (KW8.mk (rkeys (:runs w)) (t8ks (:tasks w)) (s8ks (:scopes w)) (x8ks (:sources w))))

;; closedness: some scope row with id x is closed; some task row with id t has a closed owner
(a/defn sclosed-k [x :- Nat, k :- S8K] Bool (Bool.and (Nat.beq (:id k) x) (Bool.not (:open k))))
(a/defn sclosed [sks :- (List S8K), x :- Nat] Bool (tbl-any (sclosed-k x) sks))
(a/defn tclosed-k [sks :- (List S8K), t :- Nat, k :- T8K] Bool (Bool.and (Nat.beq (:id k) t) (sclosed sks (:owner k))))
(a/defn tclosed [tks :- (List T8K), sks :- (List S8K), t :- Nat] Bool (tbl-any (tclosed-k sks t) tks))
(a/defn r8 [xs :- (List Nat), tks :- (List T8K), sks :- (List S8K), k :- RKey] Bool
  (Bool.or (Bool.not (:alive k)) (Bool.or (reach-mem (:id k) xs) (Bool.not (tclosed tks sks (:of k))))))
(a/defn x8 [sks :- (List S8K), k :- X8K] Bool (Bool.or (Bool.not (:open k)) (Bool.not (sclosed sks (:owner k)))))
(a/defn i8k [xs :- (List Nat), rks :- (List RKey), tks :- (List T8K), sks :- (List S8K), xks :- (List X8K)] Bool
  (Bool.and (tbl-all (r8 xs tks sks) rks) (tbl-all (x8 sks) xks)))
(a/defn g8-rest [x8s :- (List Nat), w :- World] Bool
  (i8k x8s (rkeys (:runs w)) (t8ks (:tasks w)) (s8ks (:scopes w)) (x8ks (:sources w))))
(a/defn g8 [x8s :- (List Nat), w :- World] Bool (Bool.and (inv-sample w) (g8-rest x8s w)))

(a/theorem g8-sample [x8s :- (List Nat), w :- World] (=> (= (g8 x8s w) true) (= (inv-sample w) true))
  (intro h) (simp only [g8 Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem g8-rest-of [x8s :- (List Nat), w :- World] (=> (= (g8 x8s w) true) (= (g8-rest x8s w) true))
  (intro h) (simp only [g8 Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem g8-intro [x8s :- (List Nat), w :- World] (=> (= (inv-sample w) true) (= (g8-rest x8s w) true) (= (g8 x8s w) true))
  (intros h1 h2) (simp only [g8 h1 h2 Bool.and_self]))
(a/theorem g8-parts [x8s :- (List Nat), w :- World]
  (=> (= (g8 x8s w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (g8-sample x8s w h))))
(a/theorem g8-rest-kw [x8s :- (List Nat), w :- World, w2 :- World]
  (=> (= (kw8 w2) (kw8 w)) (= (g8-rest x8s w2) (g8-rest x8s w)))
  (intro e)
  (have e1 (= (rkeys (:runs w2)) (rkeys (:runs w)))) (exact (congrArg (fn [k :- KW8] (:rks k)) e))
  (have e2 (= (t8ks (:tasks w2)) (t8ks (:tasks w)))) (exact (congrArg (fn [k :- KW8] (:tks k)) e))
  (have e3 (= (s8ks (:scopes w2)) (s8ks (:scopes w)))) (exact (congrArg (fn [k :- KW8] (:sks k)) e))
  (have e4 (= (x8ks (:sources w2)) (x8ks (:sources w)))) (exact (congrArg (fn [k :- KW8] (:xks k)) e))
  (simp only [g8-rest e1 e2 e3 e4]))
(a/theorem g8-of-kw [x8s :- (List Nat), w :- World, w2 :- World]
  (=> (= (inv-sample w2) true) (= (kw8 w2) (kw8 w)) (= (g8 x8s w) true) (= (g8 x8s w2) true))
  (intros hs e h) (exact (g8-intro x8s w2 hs (Eq.trans (g8-rest-kw x8s w w2 e) (g8-rest-of x8s w h)))))

;; tripwire for the raw0 guard `cur-closed` (engine.clj): an alive normal task run's current scope is open
;; (obligation P10; checked on the random drivers and the oracle samples, i8_test)
(a/defn run-cur-ok [w :- World, r :- RunRow] Bool
  (Bool.or (Bool.not (Bool.and (run-alive r) (Nat.beq (:mode r) mode-normal))) (Bool.not (run-cur-closed w r))))
(a/defn cur-open-ok [w :- World] Bool (tbl-all (run-cur-ok w) (:runs w)))

;; ===========================================================================
;; Part B. Key lists under the table edits; closedness is monotone under sublists
;; ===========================================================================

(a/theorem toks-upd [x :- Nat, f :- (=> TaskRow TaskRow), hk :- (forall [t :- TaskRow] (= (t8k (f t)) (t8k t))), ts :- (List TaskRow)]
  (= (t8ks (tbl-upd task-id x f ts)) (t8ks ts))
  (induction ts)
  (case [nil] (simp only [tbl-upd t8ks]))
  (case [cons h t ih] (cases hx (Nat.beq (task-id h) x)) (all_goals (simp only [tbl-upd hx t8ks ih (hk h)]))))
(a/theorem soks-upd [x :- Nat, f :- (=> ScopeRow ScopeRow), hk :- (forall [s :- ScopeRow] (= (s8k (f s)) (s8k s))), ss :- (List ScopeRow)]
  (= (s8ks (tbl-upd scope-id x f ss)) (s8ks ss))
  (induction ss)
  (case [nil] (simp only [tbl-upd s8ks]))
  (case [cons h t ih] (cases hx (Nat.beq (scope-id h) x)) (all_goals (simp only [tbl-upd hx s8ks ih (hk h)]))))
(a/theorem xoks-upd [x :- Nat, f :- (=> SourceRow SourceRow), hk :- (forall [s :- SourceRow] (= (x8k (f s)) (x8k s))), ss :- (List SourceRow)]
  (= (x8ks (tbl-upd source-id x f ss)) (x8ks ss))
  (induction ss)
  (case [nil] (simp only [tbl-upd x8ks]))
  (case [cons h t ih] (cases hx (Nat.beq (source-id h) x)) (all_goals (simp only [tbl-upd hx x8ks ih (hk h)]))))

(a/theorem toks-upd-g [x :- Nat, f :- (=> TaskRow TaskRow), g :- (=> T8K T8K),
                       hc :- (forall [t :- TaskRow] (= (t8k (f t)) (g (t8k t)))), ts :- (List TaskRow)]
  (= (t8ks (tbl-upd task-id x f ts)) (tbl-upd t8k-id x g (t8ks ts)))
  (induction ts)
  (case [nil] (simp only [tbl-upd t8ks]))
  (case [cons h t ih]
    (cases hx (Nat.beq (task-id h) x))
    (case [false] (have hx2 (= (Nat.beq (t8k-id (t8k h)) x) false)) (exact hx) (simp only [tbl-upd hx t8ks hx2 ih]))
    (case [true] (have hx2 (= (Nat.beq (t8k-id (t8k h)) x) true)) (exact hx) (simp only [tbl-upd hx t8ks hx2 ih (hc h)]))))
(a/theorem soks-upd-g [x :- Nat, f :- (=> ScopeRow ScopeRow), g :- (=> S8K S8K),
                       hc :- (forall [s :- ScopeRow] (= (s8k (f s)) (g (s8k s)))), ss :- (List ScopeRow)]
  (= (s8ks (tbl-upd scope-id x f ss)) (tbl-upd s8k-id x g (s8ks ss)))
  (induction ss)
  (case [nil] (simp only [tbl-upd s8ks]))
  (case [cons h t ih]
    (cases hx (Nat.beq (scope-id h) x))
    (case [false] (have hx2 (= (Nat.beq (s8k-id (s8k h)) x) false)) (exact hx) (simp only [tbl-upd hx s8ks hx2 ih]))
    (case [true] (have hx2 (= (Nat.beq (s8k-id (s8k h)) x) true)) (exact hx) (simp only [tbl-upd hx s8ks hx2 ih (hc h)]))))
(a/theorem xoks-upd-g [x :- Nat, f :- (=> SourceRow SourceRow), g :- (=> X8K X8K),
                       hc :- (forall [s :- SourceRow] (= (x8k (f s)) (g (x8k s)))), ss :- (List SourceRow)]
  (= (x8ks (tbl-upd source-id x f ss)) (tbl-upd x8k-id x g (x8ks ss)))
  (induction ss)
  (case [nil] (simp only [tbl-upd x8ks]))
  (case [cons h t ih]
    (cases hx (Nat.beq (source-id h) x))
    (case [false] (have hx2 (= (Nat.beq (x8k-id (x8k h)) x) false)) (exact hx) (simp only [tbl-upd hx x8ks hx2 ih]))
    (case [true] (have hx2 (= (Nat.beq (x8k-id (x8k h)) x) true)) (exact hx) (simp only [tbl-upd hx x8ks hx2 ih (hc h)]))))

(a/theorem toks-del [x :- Nat, ts :- (List TaskRow)] (= (t8ks (tbl-del task-id x ts)) (tbl-del t8k-id x (t8ks ts)))
  (induction ts)
  (case [nil] (simp only [tbl-del t8ks]))
  (case [cons h t ih]
    (have e (= (Nat.beq (t8k-id (t8k h)) x) (Nat.beq (task-id h) x))) (rfl)
    (cases hx (Nat.beq (task-id h) x)) (all_goals (simp only [tbl-del hx t8ks e ih]))))
(a/theorem soks-del [x :- Nat, ss :- (List ScopeRow)] (= (s8ks (tbl-del scope-id x ss)) (tbl-del s8k-id x (s8ks ss)))
  (induction ss)
  (case [nil] (simp only [tbl-del s8ks]))
  (case [cons h t ih]
    (have e (= (Nat.beq (s8k-id (s8k h)) x) (Nat.beq (scope-id h) x))) (rfl)
    (cases hx (Nat.beq (scope-id h) x)) (all_goals (simp only [tbl-del hx s8ks e ih]))))
(a/theorem xoks-del [x :- Nat, ss :- (List SourceRow)] (= (x8ks (tbl-del source-id x ss)) (tbl-del x8k-id x (x8ks ss)))
  (induction ss)
  (case [nil] (simp only [tbl-del x8ks]))
  (case [cons h t ih]
    (have e (= (Nat.beq (x8k-id (x8k h)) x) (Nat.beq (source-id h) x))) (rfl)
    (cases hx (Nat.beq (source-id h) x)) (all_goals (simp only [tbl-del hx x8ks e ih]))))
(a/theorem toks-keep [K :- (=> Nat Bool), ts :- (List TaskRow)] (= (t8ks (tbl-keep K task-id ts)) (tbl-keep K t8k-id (t8ks ts)))
  (induction ts)
  (case [nil] (simp only [tbl-keep t8ks]))
  (case [cons h t ih]
    (have e (= (K (t8k-id (t8k h))) (K (task-id h)))) (rfl)
    (cases hx (K (task-id h))) (all_goals (simp only [tbl-keep hx t8ks e ih]))))
(a/theorem soks-keep [K :- (=> Nat Bool), ss :- (List ScopeRow)] (= (s8ks (tbl-keep K scope-id ss)) (tbl-keep K s8k-id (s8ks ss)))
  (induction ss)
  (case [nil] (simp only [tbl-keep s8ks]))
  (case [cons h t ih]
    (have e (= (K (s8k-id (s8k h))) (K (scope-id h)))) (rfl)
    (cases hx (K (scope-id h))) (all_goals (simp only [tbl-keep hx s8ks e ih]))))
(a/theorem xoks-keep [K :- (=> Nat Bool), ss :- (List SourceRow)] (= (x8ks (tbl-keep K source-id ss)) (tbl-keep K x8k-id (x8ks ss)))
  (induction ss)
  (case [nil] (simp only [tbl-keep x8ks]))
  (case [cons h t ih]
    (have e (= (K (x8k-id (x8k h))) (K (source-id h)))) (rfl)
    (cases hx (K (source-id h))) (all_goals (simp only [tbl-keep hx x8ks e ih]))))

;; sublists: every `tbl-any` on the smaller list holds on the larger one
(a/theorem any8-del [A :- Type, idf :- (=> A Nat), x :- Nat, p :- (=> A Bool), xs :- (List A)]
  (=> (= (tbl-any p (tbl-del idf x xs)) true) (= (tbl-any p xs) true))
  (induction xs)
  (case [nil] (intro h) (simp only [tbl-del] at h) (exact h))
  (case [cons h t ih]
    (intro q)
    (cases hx (Nat.beq (idf h) x))
    (case [true] (simp only [tbl-del hx] at q) (simp only [tbl-any (ih q) Bool.or_true]))
    (case [false]
      (simp only [tbl-del hx tbl-any Bool.or_eq_true] at q)
      (simp only [tbl-any Bool.or_eq_true])
      (cases q) (case [inl a] (exact (Or.inl a))) (case [inr b] (exact (Or.inr (ih b)))))))
(a/theorem any8-keep [A :- Type, K :- (=> Nat Bool), idf :- (=> A Nat), p :- (=> A Bool), xs :- (List A)]
  (=> (= (tbl-any p (tbl-keep K idf xs)) true) (= (tbl-any p xs) true))
  (induction xs)
  (case [nil] (intro h) (simp only [tbl-keep] at h) (exact h))
  (case [cons h t ih]
    (intro q)
    (cases hx (K (idf h)))
    (case [false] (simp only [tbl-keep hx] at q) (simp only [tbl-any (ih q) Bool.or_true]))
    (case [true]
      (simp only [tbl-keep hx tbl-any Bool.or_eq_true] at q)
      (simp only [tbl-any Bool.or_eq_true])
      (cases q) (case [inl a] (exact (Or.inl a))) (case [inr b] (exact (Or.inr (ih b)))))))

;; ---- r8/x8 under smaller closedness and a larger escape list
(a/theorem r8-mono [xs :- (List Nat), ys :- (List Nat), tks :- (List T8K), sks :- (List S8K), tks2 :- (List T8K), sks2 :- (List S8K),
                    ht :- (forall [t :- Nat] (=> (= (tclosed tks2 sks2 t) true) (= (tclosed tks sks t) true))),
                    hx :- (forall [x :- Nat] (=> (= (reach-mem x xs) true) (= (reach-mem x ys) true))), k :- RKey]
  (=> (= (r8 xs tks sks k) true) (= (r8 ys tks2 sks2 k) true))
  (intro h)
  (simp only [r8 Bool.or_eq_true] at h)
  (simp only [r8 Bool.or_eq_true])
  (cases h)
  (case [inl a] (exact (Or.inl a)))
  (case [inr b]
    (cases b)
    (case [inl c] (exact (Or.inr (Or.inl (hx _ c)))))
    (case [inr d]
      (apply Or.inr) (apply Or.inr)
      (cases hc (tclosed tks2 sks2 (:of k)))
      (case [false] (simp only [hc Bool.not_false]))
      (case [true] (have z := (ht _ hc)) (simp only [z Bool.not_true] at d) (cases d)))))
(a/theorem x8-mono [sks :- (List S8K), sks2 :- (List S8K),
                    hs :- (forall [x :- Nat] (=> (= (sclosed sks2 x) true) (= (sclosed sks x) true))), k :- X8K]
  (=> (= (x8 sks k) true) (= (x8 sks2 k) true))
  (intro h)
  (simp only [x8 Bool.or_eq_true] at h)
  (simp only [x8 Bool.or_eq_true])
  (cases h)
  (case [inl a] (exact (Or.inl a)))
  (case [inr d]
    (apply Or.inr)
    (cases hc (sclosed sks2 (:owner k)))
    (case [false] (simp only [hc Bool.not_false]))
    (case [true] (have z := (hs _ hc)) (simp only [z Bool.not_true] at d) (cases d))))
;; tclosed is monotone in both lists
(a/theorem tclosed-k-mono [sks :- (List S8K), sks2 :- (List S8K),
                           hs :- (forall [x :- Nat] (=> (= (sclosed sks2 x) true) (= (sclosed sks x) true))), t :- Nat, k :- T8K]
  (=> (= (tclosed-k sks2 t k) true) (= (tclosed-k sks t k) true))
  (intro h) (simp only [tclosed-k Bool.and_eq_true] at h) (simp only [tclosed-k Bool.and_eq_true])
  (exact (And.intro (And.left h) (hs _ (And.right h)))))
(a/theorem tclosed-mono [tks :- (List T8K), sks :- (List S8K), tks2 :- (List T8K), sks2 :- (List S8K),
                         hts :- (forall [p :- (=> T8K Bool)] (=> (= (tbl-any p tks2) true) (= (tbl-any p tks) true))),
                         hs :- (forall [x :- Nat] (=> (= (sclosed sks2 x) true) (= (sclosed sks x) true))), t :- Nat]
  (=> (= (tclosed tks2 sks2 t) true) (= (tclosed tks sks t) true))
  (intro h)
  (simp only [tclosed] at h)
  (have a1 (= (tbl-any (tclosed-k sks t) tks2) true))
  (exact (tbl-any-mono T8K (tclosed-k sks2 t) (tclosed-k sks t) (tclosed-k-mono sks sks2 hs t) tks2 h))
  (simp only [tclosed]) (exact (hts _ a1)))

;; ===========================================================================
;; Part C. The primitive edits
;; ===========================================================================

;; ---- frames: the keys stay
(a/theorem g8-run-upd [x8s :- (List Nat), w :- World, x :- Nat, f :- (=> RunRow RunRow),
                       hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                       hk :- (forall [r :- RunRow] (= (rkey (f r)) (rkey r)))]
  (=> (= (g8 x8s w) true) (= (g8 x8s (run-upd w x f)) true))
  (intro h)
  (have e (= (kw8 (run-upd w x f)) (kw8 w))) (simp only [kw8 run-upd set-runs (rkeys-upd x f hk (:runs w))])
  (exact (g8-of-kw x8s w _ (inv-run-upd w x f hf (g8-sample x8s w h)) e h)))
(a/theorem g8-task-upd [x8s :- (List Nat), w :- World, x :- Nat, f :- (=> TaskRow TaskRow),
                        hf :- (forall [t :- TaskRow] (= (task-id (f t)) (task-id t))),
                        hk :- (forall [t :- TaskRow] (= (t8k (f t)) (t8k t)))]
  (=> (= (g8 x8s w) true) (= (g8 x8s (task-upd w x f)) true))
  (intro h)
  (have e (= (kw8 (task-upd w x f)) (kw8 w))) (simp only [kw8 task-upd set-tasks (toks-upd x f hk (:tasks w))])
  (exact (g8-of-kw x8s w _ (inv-task-upd w x f hf (g8-sample x8s w h)) e h)))
(a/theorem g8-scope-upd [x8s :- (List Nat), w :- World, x :- Nat, f :- (=> ScopeRow ScopeRow),
                         hf :- (forall [s :- ScopeRow] (= (scope-id (f s)) (scope-id s))),
                         hk :- (forall [s :- ScopeRow] (= (s8k (f s)) (s8k s)))]
  (=> (= (g8 x8s w) true) (= (g8 x8s (scope-upd w x f)) true))
  (intro h)
  (have e (= (kw8 (scope-upd w x f)) (kw8 w))) (simp only [kw8 scope-upd set-scopes (soks-upd x f hk (:scopes w))])
  (exact (g8-of-kw x8s w _ (inv-scope-upd w x f hf (g8-sample x8s w h)) e h)))
(a/theorem g8-source-upd [x8s :- (List Nat), w :- World, x :- Nat, f :- (=> SourceRow SourceRow),
                          hf :- (forall [s :- SourceRow] (= (source-id (f s)) (source-id s))),
                          hk :- (forall [s :- SourceRow] (= (x8k (f s)) (x8k s)))]
  (=> (= (g8 x8s w) true) (= (g8 x8s (source-upd w x f)) true))
  (intro h)
  (have e (= (kw8 (source-upd w x f)) (kw8 w))) (simp only [kw8 source-upd set-sources (xoks-upd x f hk (:sources w))])
  (exact (g8-of-kw x8s w _ (inv-source-upd w x f hf (g8-sample x8s w h)) e h)))

;; ---- a run made done, a source closed: the predicate only gets weaker demands
(a/theorem r8-down [xs :- (List Nat), tks :- (List T8K), sks :- (List S8K), k :- RKey] (= (r8 xs tks sks (rk-down k)) true)
  (simp only [r8 rk-down Bool.not_false Bool.true_or]))
(a/defn xk-shut [k :- X8K] X8K (X8K.mk (:id k) (:owner k) false))
(a/theorem x8-shut [sks :- (List S8K), k :- X8K] (= (x8 sks (xk-shut k)) true)
  (simp only [x8 xk-shut Bool.not_false Bool.true_or]))
(a/defn xk-orphan [k :- X8K] X8K (X8K.mk (:id k) 0 false))
(a/theorem x8-orphan [sks :- (List S8K), k :- X8K] (= (x8 sks (xk-orphan k)) true)
  (simp only [x8 xk-orphan Bool.not_false Bool.true_or]))

(a/theorem g8-run-kill [x8s :- (List Nat), w :- World, x :- Nat, f :- (=> RunRow RunRow),
                        hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                        hk :- (forall [r :- RunRow] (= (rkey (f r)) (rk-down (rkey r))))]
  (=> (= (g8 x8s w) true) (= (g8 x8s (run-upd w x f)) true))
  (intro h)
  (have r := (g8-rest-of x8s w h)) (simp only [g8-rest i8k Bool.and_eq_true] at r)
  (have e := (rkeys-upd-g x f rk-down hk (:runs w)))
  (have a1 (= (tbl-all (r8 x8s (t8ks (:tasks w)) (s8ks (:scopes w))) (tbl-upd rkey-id x rk-down (rkeys (:runs w)))) true))
  (exact (tbl-all-upd RKey rkey-id x rk-down (r8 x8s (t8ks (:tasks w)) (s8ks (:scopes w))) (r8 x8s (t8ks (:tasks w)) (s8ks (:scopes w)))
           (fn [k :- RKey, p :- (= (r8 x8s (t8ks (:tasks w)) (s8ks (:scopes w)) k) true), q :- (= (Nat.beq (rkey-id k) x) true)]
             (r8-down x8s (t8ks (:tasks w)) (s8ks (:scopes w)) k))
           (fn [k :- RKey, p :- (= (r8 x8s (t8ks (:tasks w)) (s8ks (:scopes w)) k) true), q :- (= (Nat.beq (rkey-id k) x) false)] p)
           (rkeys (:runs w)) (And.left r)))
  (have hr (= (g8-rest x8s (run-upd w x f)) true))
  (simp only [g8-rest i8k run-upd set-runs e a1 (And.right r) Bool.and_self])
  (exact (g8-intro x8s _ (inv-run-upd w x f hf (g8-sample x8s w h)) hr)))

(a/theorem g8-source-shut [x8s :- (List Nat), w :- World, x :- Nat, f :- (=> SourceRow SourceRow), g :- (=> X8K X8K),
                           hf :- (forall [s :- SourceRow] (= (source-id (f s)) (source-id s))),
                           hk :- (forall [s :- SourceRow] (= (x8k (f s)) (g (x8k s)))),
                           hg :- (forall [sks :- (List S8K), k :- X8K] (= (x8 sks (g k)) true))]
  (=> (= (g8 x8s w) true) (= (g8 x8s (source-upd w x f)) true))
  (intro h)
  (have r := (g8-rest-of x8s w h)) (simp only [g8-rest i8k Bool.and_eq_true] at r)
  (have e := (xoks-upd-g x f g hk (:sources w)))
  (have a1 (= (tbl-all (x8 (s8ks (:scopes w))) (tbl-upd x8k-id x g (x8ks (:sources w)))) true))
  (exact (tbl-all-upd X8K x8k-id x g (x8 (s8ks (:scopes w))) (x8 (s8ks (:scopes w)))
           (fn [k :- X8K, p :- (= (x8 (s8ks (:scopes w)) k) true), q :- (= (Nat.beq (x8k-id k) x) true)] (hg (s8ks (:scopes w)) k))
           (fn [k :- X8K, p :- (= (x8 (s8ks (:scopes w)) k) true), q :- (= (Nat.beq (x8k-id k) x) false)] p)
           (x8ks (:sources w)) (And.right r)))
  (have hr (= (g8-rest x8s (source-upd w x f)) true))
  (simp only [g8-rest i8k source-upd set-sources e a1 (And.left r) Bool.and_self])
  (exact (g8-intro x8s _ (inv-source-upd w x f hf (g8-sample x8s w h)) hr)))
(a/theorem xok-close [s :- SourceRow] (= (x8k (source-close-row s)) (xk-shut (x8k s))) (rfl))
(a/theorem xok-detach [s :- SourceRow] (= (x8k (source-detach-row s)) (xk-orphan (x8k s))) (rfl))
(a/theorem g8-source-close [x8s :- (List Nat), w :- World, x :- Nat]
  (=> (= (g8 x8s w) true) (= (g8 x8s (source-upd w x source-close-row)) true))
  (intro h) (exact (g8-source-shut x8s w x source-close-row xk-shut source-close-row-id xok-close x8-shut h)))
(a/theorem g8-source-detach [x8s :- (List Nat), w :- World, x :- Nat]
  (=> (= (g8 x8s w) true) (= (g8 x8s (source-upd w x source-detach-row)) true))
  (intro h) (exact (g8-source-shut x8s w x source-detach-row xk-orphan source-detach-row-id xok-detach x8-orphan h)))

;; ---- deletions and the filter: closedness only shrinks
(a/theorem any8-sub-r8 [xs :- (List Nat), tks :- (List T8K), sks :- (List S8K), tks2 :- (List T8K), sks2 :- (List S8K), rks :- (List RKey),
                        hts :- (forall [p :- (=> T8K Bool)] (=> (= (tbl-any p tks2) true) (= (tbl-any p tks) true))),
                        hss :- (forall [p :- (=> S8K Bool)] (=> (= (tbl-any p sks2) true) (= (tbl-any p sks) true)))]
  (=> (= (tbl-all (r8 xs tks sks) rks) true) (= (tbl-all (r8 xs tks2 sks2) rks) true))
  (intro h)
  (have hs (forall [x :- Nat] (=> (= (sclosed sks2 x) true) (= (sclosed sks x) true))))
  (intros x q) (simp only [sclosed] at q) (simp only [sclosed]) (exact (hss _ q))
  (exact (tbl-all-mono RKey (r8 xs tks sks) (r8 xs tks2 sks2)
           (r8-mono xs xs tks sks tks2 sks2 (tclosed-mono tks sks tks2 sks2 hts hs) (fn [x :- Nat, q :- (= (reach-mem x xs) true)] q))
           rks h)))
(a/theorem any8-sub-x8 [sks :- (List S8K), sks2 :- (List S8K), xks :- (List X8K),
                        hss :- (forall [p :- (=> S8K Bool)] (=> (= (tbl-any p sks2) true) (= (tbl-any p sks) true)))]
  (=> (= (tbl-all (x8 sks) xks) true) (= (tbl-all (x8 sks2) xks) true))
  (intro h)
  (have hs (forall [x :- Nat] (=> (= (sclosed sks2 x) true) (= (sclosed sks x) true))))
  (intros x q) (simp only [sclosed] at q) (simp only [sclosed]) (exact (hss _ q))
  (exact (tbl-all-mono X8K (x8 sks) (x8 sks2) (x8-mono sks sks2 hs) xks h)))
(a/theorem any8-refl [A :- Type, xs :- (List A)] (forall [p :- (=> A Bool)] (=> (= (tbl-any p xs) true) (= (tbl-any p xs) true)))
  (intros p h) (exact h))

(a/theorem g8-rest-run-del [x8s :- (List Nat), w :- World, x :- Nat] (=> (= (g8-rest x8s w) true) (= (g8-rest x8s (run-del w x)) true))
  (intro h) (simp only [g8-rest i8k Bool.and_eq_true] at h)
  (have a1 (= (tbl-all (r8 x8s (t8ks (:tasks w)) (s8ks (:scopes w))) (tbl-del rkey-id x (rkeys (:runs w)))) true))
  (exact (tbl-all-del RKey rkey-id x _ _ (fn [k :- RKey, p :- (= (r8 x8s (t8ks (:tasks w)) (s8ks (:scopes w)) k) true), q :- (= (Nat.beq (rkey-id k) x) false)] p) _ (And.left h)))
  (simp only [g8-rest i8k run-del set-runs rkeys-del a1 (And.right h) Bool.and_self]))
(a/theorem g8-rest-scope-del [x8s :- (List Nat), w :- World, x :- Nat] (=> (= (g8-rest x8s w) true) (= (g8-rest x8s (scope-del w x)) true))
  (intro h) (simp only [g8-rest i8k Bool.and_eq_true] at h)
  (have hss (forall [p :- (=> S8K Bool)] (=> (= (tbl-any p (tbl-del s8k-id x (s8ks (:scopes w)))) true) (= (tbl-any p (s8ks (:scopes w))) true))))
  (intros p q) (exact (any8-del S8K s8k-id x p _ q))
  (have a1 := (any8-sub-r8 x8s (t8ks (:tasks w)) (s8ks (:scopes w)) (t8ks (:tasks w)) _ (rkeys (:runs w)) (any8-refl T8K _) hss (And.left h)))
  (have a2 := (any8-sub-x8 (s8ks (:scopes w)) _ (x8ks (:sources w)) hss (And.right h)))
  (simp only [g8-rest i8k scope-del set-scopes soks-del a1 a2 Bool.and_self]))
(a/theorem g8-rest-filter [x8s :- (List Nat), w :- World, K :- (=> Nat Bool)] (=> (= (g8-rest x8s w) true) (= (g8-rest x8s (filter-world K w)) true))
  (intro h) (simp only [g8-rest i8k Bool.and_eq_true] at h)
  (have hss (forall [p :- (=> S8K Bool)] (=> (= (tbl-any p (tbl-keep K s8k-id (s8ks (:scopes w)))) true) (= (tbl-any p (s8ks (:scopes w))) true))))
  (intros p q) (exact (any8-keep S8K K s8k-id p _ q))
  (have hts (forall [p :- (=> T8K Bool)] (=> (= (tbl-any p (tbl-keep K t8k-id (t8ks (:tasks w)))) true) (= (tbl-any p (t8ks (:tasks w))) true))))
  (intros p q) (exact (any8-keep T8K K t8k-id p _ q))
  (have a1 := (any8-sub-r8 x8s (t8ks (:tasks w)) (s8ks (:scopes w)) _ _ (rkeys (:runs w)) hts hss (And.left h)))
  (have a1k (= (tbl-all (r8 x8s (tbl-keep K t8k-id (t8ks (:tasks w))) (tbl-keep K s8k-id (s8ks (:scopes w)))) (tbl-keep K rkey-id (rkeys (:runs w)))) true))
  (exact (tbl-all-keep-same RKey K rkey-id _ _ a1))
  (have a2 := (any8-sub-x8 (s8ks (:scopes w)) _ (x8ks (:sources w)) hss (And.right h)))
  (have a2k (= (tbl-all (x8 (tbl-keep K s8k-id (s8ks (:scopes w)))) (tbl-keep K x8k-id (x8ks (:sources w)))) true))
  (exact (tbl-all-keep-same X8K K x8k-id _ _ a2))
  (simp only [g8-rest i8k filter-world rkeys-keep toks-keep soks-keep xoks-keep a1k a2k Bool.and_self]))
(a/theorem g8-filter-world [x8s :- (List Nat), w :- World, K :- (=> Nat Bool)]
  (=> (= (g8 x8s w) true) (= (filter-safe-k K w) true) (= (g8 x8s (filter-world K w)) true))
  (intros h hf)
  (exact (g8-intro x8s _ (inv-filter-world w K (g8-sample x8s w h) hf) (g8-rest-filter x8s w K (g8-rest-of x8s w h)))))

;; ---- the allocator and insertions
(a/theorem g8-bump [x8s :- (List Nat), w :- World] (=> (= (g8 x8s w) true) (= (g8 x8s (bump w)) true))
  (intro h) (exact (g8-intro x8s _ (inv-bump w (g8-sample x8s w h)) (g8-rest-of x8s w h))))
(a/theorem r8-all-mono [xs :- (List Nat), tks :- (List T8K), sks :- (List S8K), tks2 :- (List T8K), sks2 :- (List S8K),
                        ht :- (forall [t :- Nat] (=> (= (tclosed tks2 sks2 t) true) (= (tclosed tks sks t) true))), rks :- (List RKey)]
  (=> (= (tbl-all (r8 xs tks sks) rks) true) (= (tbl-all (r8 xs tks2 sks2) rks) true))
  (intro h)
  (exact (tbl-all-mono RKey (r8 xs tks sks) (r8 xs tks2 sks2)
           (r8-mono xs xs tks sks tks2 sks2 ht (fn [x :- Nat, q :- (= (reach-mem x xs) true)] q)) rks h)))
(a/theorem x8-all-mono [sks :- (List S8K), sks2 :- (List S8K),
                        hs :- (forall [x :- Nat] (=> (= (sclosed sks2 x) true) (= (sclosed sks x) true))), xks :- (List X8K)]
  (=> (= (tbl-all (x8 sks) xks) true) (= (tbl-all (x8 sks2) xks) true))
  (intro h) (exact (tbl-all-mono X8K (x8 sks) (x8 sks2) (x8-mono sks sks2 hs) xks h)))
(a/theorem r8-esc-all [xs :- (List Nat), ys :- (List Nat), tks :- (List T8K), sks :- (List S8K),
                       hx :- (forall [x :- Nat] (=> (= (reach-mem x xs) true) (= (reach-mem x ys) true))), rks :- (List RKey)]
  (=> (= (tbl-all (r8 xs tks sks) rks) true) (= (tbl-all (r8 ys tks sks) rks) true))
  (intro h)
  (exact (tbl-all-mono RKey (r8 xs tks sks) (r8 ys tks sks)
           (r8-mono xs ys tks sks tks sks (fn [t :- Nat, q :- (= (tclosed tks sks t) true)] q) hx) rks h)))
(a/theorem sclosed-cons-open [k :- S8K, sks :- (List S8K), x :- Nat]
  (=> (= (:open k) true) (= (sclosed (List.cons S8K k sks) x) true) (= (sclosed sks x) true))
  (intros ho h) (simp only [sclosed tbl-any sclosed-k ho Bool.not_true Bool.and_false Bool.false_or] at h) (exact h))
(a/theorem tclosed-cons-free [k :- T8K, tks :- (List T8K), sks :- (List S8K), t :- Nat]
  (=> (= (sclosed sks (:owner k)) false) (= (tclosed (List.cons T8K k tks) sks t) true) (= (tclosed tks sks t) true))
  (intros ho h) (simp only [tclosed tbl-any tclosed-k ho Bool.and_false Bool.false_or] at h) (exact h))

(a/theorem g8-scope-ins [x8s :- (List Nat), w :- World, r :- ScopeRow, ho :- (= (:open r) true)]
  (=> (= (scope-id r) (:next-id w)) (= (g8 x8s w) true) (= (g8 x8s (bump (scope-ins w r))) true))
  (intros hr h)
  (have h0 := (g8-rest-of x8s w h)) (simp only [g8-rest i8k Bool.and_eq_true] at h0)
  (have hs (forall [x :- Nat] (=> (= (sclosed (List.cons S8K (s8k r) (s8ks (:scopes w))) x) true) (= (sclosed (s8ks (:scopes w)) x) true))))
  (intros x q) (exact (sclosed-cons-open (s8k r) _ x ho q))
  (have ht (forall [t :- Nat] (=> (= (tclosed (t8ks (:tasks w)) (List.cons S8K (s8k r) (s8ks (:scopes w))) t) true)
                                   (= (tclosed (t8ks (:tasks w)) (s8ks (:scopes w)) t) true))))
  (exact (tclosed-mono (t8ks (:tasks w)) (s8ks (:scopes w)) (t8ks (:tasks w)) _ (any8-refl T8K _) hs))
  (have a1 := (r8-all-mono x8s _ _ _ _ ht _ (And.left h0)))
  (have a2 := (x8-all-mono _ _ hs _ (And.right h0)))
  (have hrest (= (g8-rest x8s (bump (scope-ins w r))) true))
  (simp only [g8-rest i8k bump set-next-id scope-ins set-scopes tbl-ins s8ks a1 a2 Bool.and_self])
  (exact (g8-intro x8s _ (inv-scope-ins-fresh w r hr (g8-sample x8s w h)) hrest)))

(a/theorem g8-task-ins [x8s :- (List Nat), w :- World, r :- TaskRow]
  (=> (= (task-id r) (:next-id w)) (= (sclosed (s8ks (:scopes w)) (:owner r)) false) (= (g8 x8s w) true)
      (= (g8 x8s (bump (task-ins w r))) true))
  (intros hr ho h)
  (have h0 := (g8-rest-of x8s w h)) (simp only [g8-rest i8k Bool.and_eq_true] at h0)
  (have ht (forall [t :- Nat] (=> (= (tclosed (List.cons T8K (t8k r) (t8ks (:tasks w))) (s8ks (:scopes w)) t) true)
                                   (= (tclosed (t8ks (:tasks w)) (s8ks (:scopes w)) t) true))))
  (intros t q) (exact (tclosed-cons-free (t8k r) _ _ t ho q))
  (have a1 := (r8-all-mono x8s _ _ _ _ ht _ (And.left h0)))
  (have hrest (= (g8-rest x8s (bump (task-ins w r))) true))
  (simp only [g8-rest i8k bump set-next-id task-ins set-tasks tbl-ins t8ks a1 (And.right h0) Bool.and_self])
  (exact (g8-intro x8s _ (inv-task-ins-fresh w r hr (g8-sample x8s w h)) hrest)))

(a/theorem g8-source-ins [x8s :- (List Nat), w :- World, r :- SourceRow]
  (=> (= (source-id r) (:next-id w)) (= (x8 (s8ks (:scopes w)) (x8k r)) true) (= (g8 x8s w) true)
      (= (g8 x8s (bump (source-ins w r))) true))
  (intros hr ho h)
  (have h0 := (g8-rest-of x8s w h)) (simp only [g8-rest i8k Bool.and_eq_true] at h0)
  (have hrest (= (g8-rest x8s (bump (source-ins w r))) true))
  (simp only [g8-rest i8k bump set-next-id source-ins set-sources tbl-ins x8ks tbl-all ho (And.left h0) (And.right h0) Bool.and_self])
  (exact (g8-intro x8s _ (inv-source-ins-fresh w r hr (g8-sample x8s w h)) hrest)))

(a/theorem g8-run-ins [x8s :- (List Nat), w :- World, r :- RunRow]
  (=> (= (run-id r) (:next-id w)) (= (r8 x8s (t8ks (:tasks w)) (s8ks (:scopes w)) (rkey r)) true) (= (g8 x8s w) true)
      (= (g8 x8s (bump (run-ins w r))) true))
  (intros hr ho h)
  (have h0 := (g8-rest-of x8s w h)) (simp only [g8-rest i8k Bool.and_eq_true] at h0)
  (have hrest (= (g8-rest x8s (bump (run-ins w r))) true))
  (simp only [g8-rest i8k bump set-next-id run-ins set-runs tbl-ins rkeys tbl-all ho (And.left h0) (And.right h0) Bool.and_self])
  (exact (g8-intro x8s _ (inv-run-ins-fresh w r hr (g8-sample x8s w h)) hrest)))

;; a new run of an entity with no task of closed owner, with its fresh open run scope
(a/theorem g8-add-run-scope-o [x8s :- (List Nat), w :- World, of :- Nat, epoch :- Nat, parent :- Nat, ei :- Nat]
  (=> (= (tclosed (t8ks (:tasks w)) (s8ks (:scopes w)) of) false) (= (g8 x8s w) true) (= (g8 x8s (add-run-scope w of epoch parent ei)) true))
  (intros hc h)
  (have r8n (= (r8 x8s (t8ks (:tasks w)) (s8ks (:scopes w)) (rkey (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei))) true))
  (simp only [r8 rkey new-run-row hc Bool.not_false Bool.or_true])
  (have h1 := (g8-run-ins x8s w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei) (rfl) r8n h))
  (simp only [add-run-scope])
  (have he (= (scope-id (new-scope-row (+ (:next-id w) 1) parent)) (:next-id (bump (run-ins w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei)))))) (rfl)
  (exact (g8-scope-ins x8s _ (new-scope-row (+ (:next-id w) 1) parent) (rfl) he h1)))

;; ===========================================================================
;; Part D. Closing a subtree (close-local): the closed scopes join, the owned runs escape
;; ===========================================================================

;; ---- frames for the waking and T10 (lit's kw chain, with the task, scope and source keys)
(a/theorem kw8-fold [f :- (=> World Nat World), hf :- (forall [w :- World, x :- Nat] (= (kw8 (f w x)) (kw8 w))), xs :- (List Nat)]
  (forall [w :- World] (= (kw8 (nat-fold f w xs)) (kw8 w)))
  (induction xs)
  (case [nil] (intro w) (simp only [nat-fold]))
  (case [cons h t ih] (intro w) (simp only [nat-fold]) (exact (Eq.trans (ih (f w h)) (hf w h)))))

(a/theorem kw8-fin-loop [fuel :- (List Nat)]
  (forall [w :- World, ds :- (List Nat)] (= (kw8 (:world (fin-loop fuel w ds))) (kw8 w)))
  (induction fuel)
  (case [nil] (intros w ds) (simp only [fin-loop]))
  (case [cons h f ih]
    (intros w ds)
    (cases ds)
    (simp only [fin-loop])
    (rename_i d t)
    (simp only [fin-loop])
    (exact (ih (finalize-one w d) _))))

;; Z#53: closing a source wakes its waiters (T9): a fill may wake a parked run (still alive), so
;; the run keys stay
(a/theorem kw8-resume [w :- World, a :- ActRow] (= (kw8 (resume w a)) (kw8 w))
  (simp only [resume kw8 run-upd set-runs])
  (rw [(rkeys-upd (:run a) run-wake rkey-run-wake (:runs w))]))
(a/theorem kw8-fill-slot [w :- World, a :- ActRow, y :- Nat, v :- RunResult] (= (kw8 (fill-slot w a y v)) (kw8 w))
  (cases hm (act-ready (act-fill y v a)))
  (simp only [fill-slot hm])
  (simp only [fill-slot hm]) (exact (kw8-resume w a)))
(a/theorem kw8-remove-edge [w :- World, y :- Nat] (= (kw8 (remove-edge w y)) (kw8 w))
  (cases hf (edge-find w y)) (case' [some e]) (case' [none])
  (simp only [remove-edge hf])
  (cases hm (:marked e))
  (all_goals (simp only [remove-edge hf hm])))
(a/theorem kw8-fire-dep [w :- World, e :- EdgeRow] (= (kw8 (fire-dep w e)) (kw8 w))
  (cases ha (act-with-member (:id e) (:acts w))) (case' [some a]) (case' [none])
  (simp only [fire-dep ha invalidate])
  (cases hc (Bool.and (run-current-of w (:run a) (:creditor e)) (deb-avail w (:debtor e))))
  (simp only [fire-dep ha hc invalidate])
  (simp only [fire-dep ha hc deliver-dep])
  (have e1 (= (kw8 (dep-consumed w e)) (kw8 w)))
  (cases hf (deb-final w (:debtor e)))
  (simp only [dep-consumed hf])
  (simp only [dep-consumed hf]) (exact (kw8-remove-edge w (:id e)))
  (exact (Eq.trans (kw8-fill-slot _ a _ _) e1)))
(a/theorem kw8-fire-wait [res :- RunResult, w :- World, e :- EdgeRow] (= (kw8 (fire-wait res w e)) (kw8 w))
  (cases hc (Nat.beq (:creditor e) 0))
  (case [true] (simp only [fire-wait hc]) (exact (kw8-remove-edge w (:id e))))
  (case [false]
    (simp only [fire-wait hc])
    (cases ha (act-find w (:creditor e))) (case' [some a]) (case' [none])
    (simp only [fire-wait-act ha])
    (cases hr (run-current w (:run a)))
    (simp only [fire-wait-act ha hr])
    (simp only [fire-wait-act ha hr]) (exact (kw8-fill-slot _ a _ _))))
(a/theorem kw8-fire-edge [res :- RunResult, w :- World, y :- Nat] (= (kw8 (fire-edge res w y)) (kw8 w))
  (cases hf (edge-find w y)) (case' [some e]) (case' [none])
  (simp only [fire-edge hf])
  (cases hp (Nat.beq (:phase e) ph-armed))
  (simp only [fire-edge hf hp])
  (cases hk1 (Nat.beq (:kind e) ek-dep))
  (cases hk2 (Nat.beq (:kind e) ek-wait))
  (cases hk3 (Nat.beq (:kind e) ek-observe))
  (simp only [fire-edge hf hp hk1 hk2 hk3 fire-savepoint-todo])
  (cases ho (observe-new e (deb-version w (:debtor e))))
  (simp only [fire-edge hf hp hk1 hk2 hk3 fire-observe ho])
  (simp only [fire-edge hf hp hk1 hk2 hk3 fire-observe ho])
  (simp only [fire-edge hf hp hk1 hk2]) (exact (kw8-fire-wait res w e))
  (simp only [fire-edge hf hp hk1]) (exact (kw8-fire-dep w e)))
(a/theorem kw8-wake-closed [w :- World, x :- Nat] (= (kw8 (wake-closed w x)) (kw8 w))
  (simp only [wake-closed])
  (exact (kw8-fold (fire-edge (deb-result w x)) (kw8-fire-edge (deb-result w x)) _ w)))


;; ---- closing a source and a scope, on the keys
(a/defn sk-shut [k :- S8K] S8K (S8K.mk (:id k) false))
(a/theorem sok-close [s :- ScopeRow] (= (s8k (scope-close s)) (sk-shut (s8k s))) (rfl))
(a/theorem kw8-close-source [w :- World, x :- Nat]
  (= (kw8 (close-source w x))
     (KW8.mk (rkeys (:runs w)) (t8ks (:tasks w)) (s8ks (:scopes w)) (tbl-upd x8k-id x xk-shut (x8ks (:sources w)))))
  (simp only [close-source finalize-debtor])
  (have e1 := (kw8-fin-loop (fin-fuel (wake-closed (source-upd w x source-close-row) x)) (wake-closed (source-upd w x source-close-row) x) (List.cons Nat x (List.nil Nat))))
  (have e2 := (kw8-wake-closed (source-upd w x source-close-row) x))
  (have e3 (= (kw8 (source-upd w x source-close-row))
              (KW8.mk (rkeys (:runs w)) (t8ks (:tasks w)) (s8ks (:scopes w)) (tbl-upd x8k-id x xk-shut (x8ks (:sources w))))))
  (simp only [kw8 source-upd set-sources (xoks-upd-g x source-close-row xk-shut xok-close (:sources w))])
  (exact (Eq.trans e1 (Eq.trans e2 e3))))
(a/theorem kw8-close-scope-id [w :- World, x :- Nat]
  (= (kw8 (close-scope-id w x))
     (KW8.mk (rkeys (:runs w)) (t8ks (:tasks w)) (tbl-upd s8k-id x sk-shut (s8ks (:scopes w))) (x8ks (:sources w))))
  (simp only [close-scope-id kw8 scope-upd set-scopes (soks-upd-g x scope-close sk-shut sok-close (:scopes w))]))

(a/defn xk-fold [ks :- (List X8K), xs :- (List Nat)] (List X8K)
  (match xs [nil ks] [(cons x t) (xk-fold (tbl-upd x8k-id x xk-shut ks) t)]))
(a/defn sk-fold [ks :- (List S8K), xs :- (List Nat)] (List S8K)
  (match xs [nil ks] [(cons x t) (sk-fold (tbl-upd s8k-id x sk-shut ks) t)]))
(a/defn kw8-xs [k :- KW8, xs :- (List Nat)] KW8 (KW8.mk (:rks k) (:tks k) (:sks k) (xk-fold (:xks k) xs)))
(a/defn kw8-ss [k :- KW8, xs :- (List Nat)] KW8 (KW8.mk (:rks k) (:tks k) (sk-fold (:sks k) xs) (:xks k)))

(a/theorem kw8-src-fold [xs :- (List Nat)] (forall [w :- World] (= (kw8 (nat-fold close-source w xs)) (kw8-xs (kw8 w) xs)))
  (induction xs)
  (case [nil] (intro w) (simp only [nat-fold kw8-xs xk-fold kw8]))
  (case [cons x t ih]
    (intro w)
    (simp only [nat-fold])
    (rw [(ih (close-source w x))])
    (rw [(kw8-close-source w x)])))
(a/theorem kw8-scope-fold [xs :- (List Nat)] (forall [w :- World] (= (kw8 (nat-fold close-scope-id w xs)) (kw8-ss (kw8 w) xs)))
  (induction xs)
  (case [nil] (intro w) (simp only [nat-fold kw8-ss sk-fold kw8]))
  (case [cons x t ih]
    (intro w)
    (simp only [nat-fold])
    (rw [(ih (close-scope-id w x))])
    (rw [(kw8-close-scope-id w x)])))
(a/theorem fold8-field [B :- Type, P :- (=> World B), f :- (=> World Nat World), hf :- (forall [q :- World, y :- Nat] (= (P (f q y)) (P q))),
                        xs :- (List Nat)]
  (forall [w :- World] (= (P (nat-fold f w xs)) (P w)))
  (induction xs)
  (case [nil] (intro w) (simp only [nat-fold]))
  (case [cons h t ih] (intro w) (simp only [nat-fold]) (exact (Eq.trans (ih (f w h)) (hf w h)))))
(a/theorem kw8-close-local [w :- World, sub :- (List Nat)]
  (= (kw8 (close-local w sub))
     (KW8.mk (rkeys (:runs w)) (t8ks (:tasks w)) (sk-fold (s8ks (:scopes w)) sub)
             (xk-fold (x8ks (:sources w)) (tbl-scan source-id (source-owned-in sub) (:sources w)))))
  (simp only [close-local])
  (rw [(kw8-src-fold (tbl-scan source-id (source-owned-in sub) (:sources w)) (nat-fold close-scope-id w sub))])
  (exact (congrArg (fn [k :- KW8] (kw8-xs k (tbl-scan source-id (source-owned-in sub) (:sources w)))) (kw8-scope-fold sub w))))

;; ---- closedness after the folds
(a/theorem sclosed-upd-shut [y :- Nat, x :- Nat, sks :- (List S8K)]
  (=> (= (sclosed (tbl-upd s8k-id x sk-shut sks) y) true) (Or (= (sclosed sks y) true) (= (Nat.beq y x) true)))
  (induction sks)
  (case [nil] (intro h) (simp only [tbl-upd] at h) (exact (Or.inl h)))
  (case [cons k t ih]
    (intro h)
    (cases hx (Nat.beq (s8k-id k) x))
    (case [false]
      (simp only [tbl-upd hx sclosed tbl-any Bool.or_eq_true] at h)
      (cases h)
      (case [inl a] (apply Or.inl) (simp only [sclosed tbl-any a Bool.true_or]))
      (case [inr b]
        (have q := (ih b))
        (cases q)
        (case [inl c] (apply Or.inl) (simp only [sclosed] at c) (simp only [sclosed tbl-any c Bool.or_true]))
        (case [inr d] (exact (Or.inr d)))))
    (case [true]
      (simp only [tbl-upd hx sclosed tbl-any Bool.or_eq_true] at h)
      (cases h)
      (case [inl a]
        (apply Or.inr)
        (simp only [sclosed-k sk-shut Bool.and_eq_true] at a)
        (have e1 (= (:id k) y)) (exact (Nat.eq_of_beq_eq_true (And.left a)))
        (have e2 (= (:id k) x)) (exact (Nat.eq_of_beq_eq_true hx))
        (have e3 (= y x)) (omega)
        (rw [e3]) (exact (Nat.beq_refl x)))
      (case [inr b]
        (have q := (ih b))
        (cases q)
        (case [inl c] (apply Or.inl) (simp only [sclosed] at c) (simp only [sclosed tbl-any c Bool.or_true]))
        (case [inr d] (exact (Or.inr d)))))))
(a/theorem sclosed-skfold [xs :- (List Nat)]
  (forall [sks :- (List S8K), y :- Nat]
    (=> (= (sclosed (sk-fold sks xs) y) true) (Or (= (sclosed sks y) true) (= (reach-mem y xs) true))))
  (induction xs)
  (case [nil] (intros sks y h) (simp only [sk-fold] at h) (exact (Or.inl h)))
  (case [cons x t ih]
    (intros sks y h)
    (simp only [sk-fold] at h)
    (have q := (ih _ y h))
    (cases q)
    (case [inl a]
      (have q2 := (sclosed-upd-shut y x sks a))
      (cases q2)
      (case [inl c] (exact (Or.inl c)))
      (case [inr d] (apply Or.inr) (simp only [reach-mem-cons d Bool.true_or])))
    (case [inr b] (apply Or.inr) (simp only [reach-mem-cons b Bool.or_true]))))

;; a run of a task owned in the subtree is covered by ys; a source owned in it is closed by the fold
(a/defn towned-k [sub :- (List Nat), t :- Nat, k :- T8K] Bool (Bool.and (Nat.beq (:id k) t) (reach-mem (:owner k) sub)))
(a/defn cov8 [ys :- (List Nat), sub :- (List Nat), tks :- (List T8K), k :- RKey] Bool
  (Bool.or (Bool.not (:alive k)) (Bool.or (reach-mem (:id k) ys) (Bool.not (tbl-any (towned-k sub (:of k)) tks)))))
(a/defn lcov8 [L :- (List Nat), sub :- (List Nat), k :- X8K] Bool
  (Bool.or (Bool.not (reach-mem (:owner k) sub)) (reach-mem (:id k) L)))

(a/theorem tclosed-skfold [sub :- (List Nat), sks :- (List S8K), t :- Nat, tks :- (List T8K)]
  (=> (= (tclosed tks (sk-fold sks sub) t) true) (Or (= (tclosed tks sks t) true) (= (tbl-any (towned-k sub t) tks) true)))
  (induction tks)
  (case [nil] (intro h) (simp only [tclosed tbl-any] at h) (cases h))
  (case [cons k tl ih]
    (intro h)
    (simp only [tclosed tbl-any Bool.or_eq_true] at h)
    (cases h)
    (case [inl a]
      (simp only [tclosed-k Bool.and_eq_true] at a)
      (have q := (sclosed-skfold sub sks (:owner k) (And.right a)))
      (cases q)
      (case [inl c] (apply Or.inl) (simp only [tclosed tbl-any tclosed-k (And.left a) c Bool.and_self Bool.true_or]))
      (case [inr d] (apply Or.inr) (simp only [tbl-any towned-k (And.left a) d Bool.and_self Bool.true_or])))
    (case [inr b]
      (have q := (ih b))
      (cases q)
      (case [inl c] (apply Or.inl) (simp only [tclosed] at c) (simp only [tclosed tbl-any c Bool.or_true]))
      (case [inr d] (apply Or.inr) (simp only [tbl-any d Bool.or_true])))))

(a/theorem r8-close [xs :- (List Nat), ys :- (List Nat), sub :- (List Nat), tks :- (List T8K), sks :- (List S8K), k :- RKey]
  (=> (= (r8 xs tks sks k) true) (= (cov8 ys sub tks k) true) (= (r8 (List.append Nat xs ys) tks (sk-fold sks sub) k) true))
  (intros h c)
  (cases ha (:alive k))
  (case [false] (simp only [r8 ha Bool.not_false Bool.true_or]))
  (case [true]
    (cases hx (reach-mem (:id k) xs))
    (case [true] (simp only [r8 ha reach-mem-append hx Bool.true_or Bool.or_true]))
    (case [false]
      (cases hy (reach-mem (:id k) ys))
      (case [true] (simp only [r8 ha reach-mem-append hy Bool.true_or Bool.or_true]))
      (case [false]
        (simp only [r8 ha hx Bool.not_true Bool.false_or] at h)
        (simp only [cov8 ha hy Bool.not_true Bool.false_or] at c)
        (simp only [r8 ha reach-mem-append hx hy Bool.not_true Bool.false_or Bool.or_false])
        (cases hc (tclosed tks (sk-fold sks sub) (:of k)))
        (case [false] (simp only [hc Bool.not_false]))
        (case [true]
          (have q := (tclosed-skfold sub sks (:of k) tks hc))
          (cases q)
          (case [inl a] (simp only [a Bool.not_true] at h) (cases h))
          (case [inr b] (simp only [b Bool.not_true] at c) (cases c)))))))

(a/defn j8 [L :- (List Nat), sub :- (List Nat), sks :- (List S8K), k :- X8K] Bool
  (Bool.or (Bool.not (:open k))
   (Bool.or (reach-mem (:id k) L) (Bool.and (Bool.not (reach-mem (:owner k) sub)) (x8 sks k)))))
(a/theorem j8-step [x :- Nat, t :- (List Nat), sub :- (List Nat), sks :- (List S8K), ks :- (List X8K)]
  (=> (= (tbl-all (j8 (List.cons Nat x t) sub sks) ks) true) (= (tbl-all (j8 t sub sks) (tbl-upd x8k-id x xk-shut ks)) true))
  (intro h)
  (apply (tbl-all-upd X8K x8k-id x xk-shut (j8 (List.cons Nat x t) sub sks) (j8 t sub sks) _ _ ks h))
  (intros k p q) (simp only [j8 xk-shut Bool.not_false Bool.true_or])
  (intros k p q)
  (have q2 (= (Nat.beq (:id k) x) false)) (exact q)
  (simp only [j8 reach-mem-cons q2 Bool.false_or] at p) (exact p))
(a/theorem j8-fold [sub :- (List Nat), sks :- (List S8K), L :- (List Nat)]
  (forall [ks :- (List X8K)] (=> (= (tbl-all (j8 L sub sks) ks) true) (= (tbl-all (j8 (List.nil Nat) sub sks) (xk-fold ks L)) true)))
  (induction L)
  (case [nil] (intros ks h) (simp only [xk-fold]) (exact h))
  (case [cons x t ih] (intros ks h) (simp only [xk-fold]) (exact (ih _ (j8-step x t sub sks ks h)))))
(a/theorem x8-close [L :- (List Nat), sub :- (List Nat), sks :- (List S8K), xks :- (List X8K)]
  (=> (= (tbl-all (x8 sks) xks) true) (= (tbl-all (lcov8 L sub) xks) true)
      (= (tbl-all (x8 (sk-fold sks sub)) (xk-fold xks L)) true))
  (intros h c)
  (have j0 (= (tbl-all (j8 L sub sks) xks) true))
  (apply (tbl-all-mono2 X8K (x8 sks) (lcov8 L sub) (j8 L sub sks) _ xks h c))
  (intros k p q)
  (cases ho (reach-mem (:owner k) sub))
  (case [true] (simp only [lcov8 ho Bool.not_true Bool.false_or] at q) (simp only [j8 q Bool.true_or Bool.or_true]))
  (case [false] (simp only [j8 ho p Bool.not_false Bool.true_and Bool.or_true]))
  (have j1 := (j8-fold sub sks L xks j0))
  (apply (tbl-all-mono X8K (j8 (List.nil Nat) sub sks) (x8 (sk-fold sks sub)) _ _ j1))
  (intros k p)
  (cases hk (:open k))
  (case [false] (simp only [x8 hk Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [j8 hk reach-mem Bool.not_true Bool.false_or Bool.and_eq_true] at p)
    (have p1 := (bnot-true _ (And.left p)))
    (have p2 := (And.right p))
    (simp only [x8 hk Bool.not_true Bool.false_or] at p2)
    (have p3 := (bnot-true _ p2))
    (simp only [x8 hk Bool.not_true Bool.false_or])
    (cases hc (sclosed (sk-fold sks sub) (:owner k)))
    (case [false] (simp only [hc Bool.not_false]))
    (case [true]
      (have q := (sclosed-skfold sub sks (:owner k) hc))
      (cases q)
      (case [inl a] (simp only [a] at p3) (cases p3))
      (case [inr b] (simp only [b] at p1) (cases p1)))))

(a/theorem i8k-close [xs :- (List Nat), ys :- (List Nat), sub :- (List Nat), L :- (List Nat),
                      rks :- (List RKey), tks :- (List T8K), sks :- (List S8K), xks :- (List X8K)]
  (=> (= (i8k xs rks tks sks xks) true) (= (tbl-all (cov8 ys sub tks) rks) true) (= (tbl-all (lcov8 L sub) xks) true)
      (= (i8k (List.append Nat xs ys) rks tks (sk-fold sks sub) (xk-fold xks L)) true))
  (intros h c l)
  (simp only [i8k Bool.and_eq_true] at h)
  (have a1 (= (tbl-all (r8 (List.append Nat xs ys) tks (sk-fold sks sub)) rks) true))
  (apply (tbl-all-mono2 RKey (r8 xs tks sks) (cov8 ys sub tks) _ _ rks (And.left h) c))
  (intros k p q) (exact (r8-close xs ys sub tks sks k p q))
  (have a2 := (x8-close L sub sks xks (And.right h) l))
  (simp only [i8k a1 a2 Bool.and_self]))

;; ---- coverage in a world: the owned runs, the owned sources
(a/defn on-xok [P :- (=> X8K Bool), s :- SourceRow] Bool (P (x8k s)))
(a/theorem all-xoks [P :- (=> X8K Bool), ss :- (List SourceRow)] (= (tbl-all P (x8ks ss)) (tbl-all (on-xok P) ss))
  (induction ss) (case [nil] (simp only [x8ks tbl-all])) (case [cons h t ih] (simp only [x8ks tbl-all on-xok ih])))
(a/theorem towned-scan [sub :- (List Nat), t :- Nat, ts :- (List TaskRow)]
  (=> (= (tbl-any (towned-k sub t) (t8ks ts)) true) (= (reach-mem t (tbl-scan task-id (task-owned-in sub) ts)) true))
  (induction ts)
  (case [nil] (intro h) (simp only [t8ks tbl-any] at h) (cases h))
  (case [cons k tl ih]
    (intro h)
    (simp only [t8ks tbl-any Bool.or_eq_true] at h)
    (cases h)
    (case [inl a]
      (simp only [towned-k t8k Bool.and_eq_true] at a)
      (have e (= (:id k) t)) (exact (Nat.eq_of_beq_eq_true (And.left a)))
      (have o (= (task-owned-in sub k) true)) (simp only [task-owned-in]) (exact (And.right a))
      (have e2 (= (Nat.beq t (task-id k)) true)) (simp only [task-id e Nat.beq_refl])
      (simp only [tbl-scan o reach-mem-cons e2 Bool.true_or]))
    (case [inr b]
      (have q := (ih b))
      (cases o (task-owned-in sub k))
      (case [false] (simp only [tbl-scan o]) (exact q))
      (case [true] (simp only [tbl-scan o reach-mem-cons q Bool.or_true])))))
(a/theorem cov-owned [w :- World, sub :- (List Nat)]
  (=> (= (inv-sample w) true) (= (tbl-all (cov8 (owned-runs w sub) sub (t8ks (:tasks w))) (rkeys (:runs w))) true))
  (intro hs)
  (rw [all-rkeys])
  (apply (all-of-mem RunRow _ (:runs w)))
  (intros r hm)
  (simp only [on-rkey])
  (cases ha (run-alive r))
  (case [false] (simp only [cov8 rkey ha Bool.not_false Bool.true_or]))
  (case [true]
    (cases ht (tbl-any (towned-k sub (:of r)) (t8ks (:tasks w))))
    (case [false] (simp only [cov8 rkey ht Bool.not_false Bool.or_true]))
    (case [true]
      (have f := (scan-mem-find TaskRow task-id (task-owned-in sub) (:of r) (:tasks w) (towned-scan sub (:of r) (:tasks w) ht) (tasks-nodup w hs)))
      (have p (= (run-owned-by w sub r) true)) (simp only [run-owned-by ha task-find f Bool.true_and])
      (have m := (scan-mem RunRow run-id (run-owned-by w sub) r (:runs w) hm p))
      (have m2 (= (reach-mem (:id (rkey r)) (owned-runs w sub)) true)) (exact m)
      (simp only [cov8 m2 Bool.true_or Bool.or_true]))))
(a/theorem lcov-owned [w :- World, sub :- (List Nat)]
  (= (tbl-all (lcov8 (tbl-scan source-id (source-owned-in sub) (:sources w)) sub) (x8ks (:sources w))) true)
  (rw [all-xoks])
  (apply (all-of-mem SourceRow _ (:sources w)))
  (intros s hm)
  (simp only [on-xok])
  (cases ho (reach-mem (:owner s) sub))
  (case [false] (simp only [lcov8 x8k ho Bool.not_false Bool.true_or]))
  (case [true]
    (have p (= (source-owned-in sub s) true)) (simp only [source-owned-in]) (exact ho)
    (have m := (scan-mem SourceRow source-id (source-owned-in sub) s (:sources w) hm p))
    (have m2 (= (reach-mem (:id (x8k s)) (tbl-scan source-id (source-owned-in sub) (:sources w))) true)) (exact m)
    (simp only [lcov8 m2 Bool.or_true])))

(a/theorem g8-rest-mk [x8s :- (List Nat), w :- World, a :- (List RKey), b :- (List T8K), c :- (List S8K), d :- (List X8K)]
  (=> (= (kw8 w) (KW8.mk a b c d)) (= (g8-rest x8s w) (i8k x8s a b c d)))
  (intro e)
  (have e1 (= (rkeys (:runs w)) a)) (exact (congrArg (fn [k :- KW8] (:rks k)) e))
  (have e2 (= (t8ks (:tasks w)) b)) (exact (congrArg (fn [k :- KW8] (:tks k)) e))
  (have e3 (= (s8ks (:scopes w)) c)) (exact (congrArg (fn [k :- KW8] (:sks k)) e))
  (have e4 (= (x8ks (:sources w)) d)) (exact (congrArg (fn [k :- KW8] (:xks k)) e))
  (simp only [g8-rest e1 e2 e3 e4]))

;; Closing a subtree: the runs of the tasks it owns join the escape list
(a/theorem g8-close-local-cov [x8s :- (List Nat), ys :- (List Nat), w :- World, sub :- (List Nat)]
  (=> (= (g8 x8s w) true) (= (tbl-all (cov8 ys sub (t8ks (:tasks w))) (rkeys (:runs w))) true)
      (= (g8 (List.append Nat x8s ys) (close-local w sub)) true))
  (intros h hc)
  (have hs := (g8-sample x8s w h))
  (have r := (g8-rest-of x8s w h)) (simp only [g8-rest] at r)
  (have c := (i8k-close x8s ys sub (tbl-scan source-id (source-owned-in sub) (:sources w))
               _ _ _ _ r hc (lcov-owned w sub)))
  (exact (g8-intro _ _ (inv-close-local w sub hs) (Eq.trans (g8-rest-mk _ _ _ _ _ _ (kw8-close-local w sub)) c))))
(a/theorem g8-close-local [x8s :- (List Nat), w :- World, sub :- (List Nat)]
  (=> (= (g8 x8s w) true) (= (g8 (List.append Nat x8s (owned-runs w sub)) (close-local w sub)) true))
  (intro h) (exact (g8-close-local-cov x8s (owned-runs w sub) w sub h (cov-owned w sub (g8-sample x8s w h)))))

;; ===========================================================================
;; Part E. The copy over the raw transition and Rule R
;; ===========================================================================

(a/theorem g8-rest-mark-edge [x8s :- (List Nat), w :- World, x :- Nat] (= (g8-rest x8s (mark-edge w x)) (g8-rest x8s w))
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [mark-edge hf hm]))))
(a/theorem g8-rest-unmark-edge [x8s :- (List Nat), w :- World, x :- Nat] (= (g8-rest x8s (unmark-edge w x)) (g8-rest x8s w))
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [unmark-edge hf hm]))))
(a/theorem g8-rest-remove-edge [x8s :- (List Nat), w :- World, x :- Nat] (= (g8-rest x8s (remove-edge w x)) (g8-rest x8s w))
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [remove-edge hf hm]))))

;; a run row made alive that was alive already (every row with that id is alive)
(a/theorem rkeys-upd-al [x :- Nat, f :- (=> RunRow RunRow), rs :- (List RunRow)]
  (=> (= (tbl-all (run-ok-for x) rs) true) (forall [r :- RunRow] (=> (= (run-alive r) true) (= (rkey (f r)) (rkey r))))
      (= (rkeys (tbl-upd run-id x f rs)) (rkeys rs)))
  (induction rs)
  (case [nil] (intros h1 h2) (simp only [tbl-upd rkeys]))
  (case [cons h t ih]
    (intros h1 h2)
    (simp only [tbl-all Bool.and_eq_true] at h1)
    (cases hx (Nat.beq (run-id h) x))
    (case [false] (simp only [tbl-upd hx rkeys (ih (And.right h1) h2)]))
    (case [true]
      (have a (= (run-alive h) true))
      (have q := (And.left h1)) (have hx2 (= (Nat.beq (:id h) x) true)) (exact hx)
      (simp only [run-ok-for hx2 Bool.not_true Bool.false_or] at q) (exact q)
      (simp only [tbl-upd hx rkeys (ih (And.right h1) h2) (h2 h a)]))))
(a/theorem g8-run-upd-up [x8s :- (List Nat), w :- World, x :- Nat, f :- (=> RunRow RunRow),
                          hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                          hk :- (forall [r :- RunRow] (= (run-alive (f r)) true)),
                          ho :- (forall [r :- RunRow] (= (:of (f r)) (:of r)))]
  (=> (= (tbl-all (run-ok-for x) (:runs w)) true) (= (g8 x8s w) true) (= (g8 x8s (run-upd w x f)) true))
  (intros hal h)
  (have e (= (rkeys (tbl-upd run-id x f (:runs w))) (rkeys (:runs w))))
  (apply (rkeys-upd-al x f (:runs w) hal))
  (intros r q) (have i (= (:id (f r)) (:id r))) (exact (hf r)) (simp only [rkey i (hk r) (ho r) q])
  (have e2 (= (kw8 (run-upd w x f)) (kw8 w))) (simp only [kw8 run-upd set-runs e])
  (exact (g8-of-kw x8s w _ (inv-run-upd w x f hf (g8-sample x8s w h)) e2 h)))

(def G8 (mk-bundle 'g8 '[x8s :- (List Nat)] "g8-"
          {'inv-run-upd ['(fn [r :- RunRow] (Eq.refl (rkey r))) 4]
           'inv-task-upd ['(fn [t :- TaskRow] (Eq.refl (t8k t))) 4]
           'inv-scope-upd ['(fn [s :- ScopeRow] (Eq.refl (s8k s))) 4]
           'inv-source-upd ['(fn [s :- SourceRow] (Eq.refl (x8k s))) 4]
           'inv-scope-ins-fresh ['(Eq.refl true) 2]}))
(swap! (:renames G8) assoc 'inv-parts 'g8-parts 'inv-run-upd 'g8-run-upd 'inv-task-upd 'g8-task-upd
       'inv-scope-upd 'g8-scope-upd 'inv-source-upd 'g8-source-upd 'inv-scope-ins-fresh 'g8-scope-ins
       'inv-bump 'g8-bump 'inv-filter-world 'g8-filter-world)
(doseq [o '[inv-pub-upd inv-resource-upd inv-cleanup-upd inv-cleanup-del inv-cleanup-ins inv-set-pins inv-resource-del
            inv-act-upd inv-comp-upd inv-edge-upd inv-drop-cred inv-drop-act inv-drop-edges inv-comp-del-unref
            inv-act-ins-fresh inv-comp-ins-fresh inv-resource-ins-fresh insert-edge-fresh-inv-sample]]
  (prim! G8 o nil))
(prim! G8 'mark-edge-inv-sample '(Eq.trans (g8-rest-mark-edge x8s w x) R))
(prim! G8 'unmark-edge-inv-sample '(Eq.trans (g8-rest-unmark-edge x8s w x) R))
(prim! G8 'inv-remove-edge '(Eq.trans (g8-rest-remove-edge x8s w x) R))
(prim! G8 'inv-run-del '(g8-rest-run-del x8s w x R))
(prim! G8 'inv-scope-del '(g8-rest-scope-del x8s w x R))

;; ===========================================================================
;; Part F. The cascade: the escape list is the list of pending cancel jobs
;; ===========================================================================

;; ---- keys through T14's local part: only the cancelled run's key goes down
(a/theorem tok-cancel-result [t :- TaskRow] (= (t8k (task-cancel-result t)) (t8k t))
  (cases hn (Nat.beq (:tag (:result t)) res-none))
  (case [true] (simp only [task-cancel-result hn t8k]))
  (case [false] (simp only [task-cancel-result hn])))
(a/theorem kw8-invalidate [w :- World, e :- EdgeRow] (= (kw8 (invalidate w e)) (kw8 w)) (rfl))
(a/theorem kw8-invalidate-id [w :- World, x :- Nat] (= (kw8 (invalidate-id w x)) (kw8 w))
  (cases hf (edge-find w x))
  (case [none] (simp only [invalidate-id hf]))
  (case [some e] (cases hp (Nat.beq (:phase e) ph-armed)) (all_goals (simp only [invalidate-id hf hp kw8-invalidate]))))
(a/theorem kw8-debtor-side [w :- World, r :- RunRow] (= (kw8 (debtor-side w r)) (kw8 w))
  (cases hc (comp-find w (:of r)))
  (case [none]
    (simp only [debtor-side hc fire-task-cancelled finalize-debtor])
    (have e1 := (kw8-fin-loop (fin-fuel (nat-fold (fire-edge res-cancelled) (task-upd w (:of r) task-cancel-result)
                                           (tbl-scan edge-id (on-task (:of r)) (:edges (task-upd w (:of r) task-cancel-result)))))
                              (nat-fold (fire-edge res-cancelled) (task-upd w (:of r) task-cancel-result)
                                  (tbl-scan edge-id (on-task (:of r)) (:edges (task-upd w (:of r) task-cancel-result))))
                              (List.cons Nat (:of r) (List.nil Nat))))
    (have e2 := (kw8-fold (fire-edge res-cancelled) (kw8-fire-edge res-cancelled)
                          (tbl-scan edge-id (on-task (:of r)) (:edges (task-upd w (:of r) task-cancel-result)))
                          (task-upd w (:of r) task-cancel-result)))
    (have e3 (= (kw8 (task-upd w (:of r) task-cancel-result)) (kw8 w)))
    (simp only [kw8 task-upd set-tasks (toks-upd (:of r) task-cancel-result tok-cancel-result (:tasks w))])
    (exact (Eq.trans e1 (Eq.trans e2 e3))))
  (case [some c]
    (cases he (Nat.beq (:epoch r) (:epoch c)))
    (case [false] (simp only [debtor-side hc he]))
    (case [true]
      (simp only [debtor-side hc he invalidate-dependents fire-waits-cancelled])
      (exact (Eq.trans (kw8-fold invalidate-id kw8-invalidate-id _ _)
                       (kw8-fold (fire-edge res-cancelled) (kw8-fire-edge res-cancelled) _ w))))))
(a/theorem kw8-cancel-debtor [rep :- Bool, w :- World, r :- RunRow] (= (kw8 (cancel-debtor rep w r)) (kw8 w))
  (cases hc (Bool.and rep (comp-has w (:of r))))
  (case [true] (simp only [cancel-debtor hc]))
  (case [false] (simp only [cancel-debtor hc]) (exact (kw8-debtor-side w r))))
(a/theorem kw8-drop-act [w :- World, x :- Nat] (= (kw8 (drop-act w x)) (kw8 w)) (rfl))
(a/theorem kw8-res-cancel [w :- World, x :- Nat] (= (kw8 (res-cancel w x)) (kw8 w)) (rfl))
(a/theorem kw8-cancel-run-local [w :- World, r :- RunRow, rep :- Bool]
  (= (kw8 (cancel-run-local w r rep))
     (KW8.mk (tbl-upd rkey-id (:id r) rk-down (rkeys (:runs w))) (t8ks (:tasks w)) (s8ks (:scopes w)) (x8ks (:sources w))))
  (simp only [cancel-run-local])
  (have e1 := (kw8-cancel-debtor rep (cleanup-set (cancel-res (cancel-acts (run-upd w (:id r) run-cancel-row) (:id r)) r) (:id r) (cleanup-rows-of w r)) r))
  (have e2 (= (kw8 (cleanup-set (cancel-res (cancel-acts (run-upd w (:id r) run-cancel-row) (:id r)) r) (:id r) (cleanup-rows-of w r)))
              (kw8 (cancel-res (cancel-acts (run-upd w (:id r) run-cancel-row) (:id r)) r))))
  (rfl)
  (have e3 := (kw8-fold res-cancel kw8-res-cancel (:resources r) (cancel-acts (run-upd w (:id r) run-cancel-row) (:id r))))
  (have e4 (= (kw8 (cancel-acts (run-upd w (:id r) run-cancel-row) (:id r))) (kw8 (run-upd w (:id r) run-cancel-row))))
  (simp only [cancel-acts]) (exact (kw8-fold drop-act kw8-drop-act _ _))
  (have e5 (= (kw8 (run-upd w (:id r) run-cancel-row))
              (KW8.mk (tbl-upd rkey-id (:id r) rk-down (rkeys (:runs w))) (t8ks (:tasks w)) (s8ks (:scopes w)) (x8ks (:sources w)))))
  (simp only [kw8 run-upd set-runs (rkeys-upd-g (:id r) run-cancel-row rk-down (fn [q :- RunRow] (Eq.refl (rk-down (rkey q)))) (:runs w))])
  (exact (Eq.trans e1 (Eq.trans e2 (Eq.trans e3 (Eq.trans e4 e5))))))

;; ---- the escape list
(a/defn job-cid [j :- Job] (List Nat)
  (match j [(jcancel r rep) (List.cons Nat r (List.nil Nat))] [(jretire r) (List.nil Nat)] [(jclose s) (List.nil Nat)]))
(a/defn cj [js :- (List Job)] (List Nat) (match js [nil (List.nil Nat)] [(cons j t) (List.append Nat (job-cid j) (cj t))]))
(a/theorem cj-append [x :- Nat, t :- (List Job), u :- (List Job)]
  (= (reach-mem x (cj (List.append Job t u))) (Bool.or (reach-mem x (cj t)) (reach-mem x (cj u))))
  (induction t)
  (case [nil] (simp only [cj List.nil_append reach-mem Bool.false_or]))
  (case [cons j tl ih]
    (change (= (reach-mem x (cj (List.cons Job j (List.append Job tl u)))) (Bool.or (reach-mem x (cj (List.cons Job j tl))) (reach-mem x (cj u)))))
    (simp only [cj reach-mem-append ih Bool.or_assoc])))
(a/theorem cj-cancel-jobs [x :- Nat, xs :- (List Nat)] (= (reach-mem x (cj (cancel-jobs xs))) (reach-mem x xs))
  (induction xs)
  (case [nil] (simp only [cancel-jobs cj]))
  (case [cons h t ih] (simp only [cancel-jobs cj job-cid reach-mem-append ih reach-mem-cons reach-mem Bool.or_false])))

(a/theorem g8-esc-mono [xs :- (List Nat), ys :- (List Nat), w :- World,
                        hx :- (forall [x :- Nat] (=> (= (reach-mem x xs) true) (= (reach-mem x ys) true)))]
  (=> (= (g8 xs w) true) (= (g8 ys w) true))
  (intro h)
  (have r := (g8-rest-of xs w h)) (simp only [g8-rest i8k Bool.and_eq_true] at r)
  (have a1 := (r8-esc-all xs ys (t8ks (:tasks w)) (s8ks (:scopes w)) hx (rkeys (:runs w)) (And.left r)))
  (have hr (= (g8-rest ys w) true)) (simp only [g8-rest i8k a1 (And.right r) Bool.and_self])
  (exact (g8-intro ys w (g8-sample xs w h) hr)))

;; discharge: a run id whose rows are all dead (or absent) leaves the escape list
(a/defn dead-k [x :- Nat, k :- RKey] Bool (Bool.or (Bool.not (Nat.beq (:id k) x)) (Bool.not (:alive k))))
(a/theorem g8-disch [x :- Nat, xs :- (List Nat), w :- World]
  (=> (= (g8 (List.cons Nat x xs) w) true) (= (tbl-all (dead-k x) (rkeys (:runs w))) true) (= (g8 xs w) true))
  (intros h hd)
  (have r := (g8-rest-of _ w h)) (simp only [g8-rest i8k Bool.and_eq_true] at r)
  (have a1 (= (tbl-all (r8 xs (t8ks (:tasks w)) (s8ks (:scopes w))) (rkeys (:runs w))) true))
  (apply (tbl-all-mono2 RKey (r8 (List.cons Nat x xs) (t8ks (:tasks w)) (s8ks (:scopes w))) (dead-k x) _ _ _ (And.left r) hd))
  (intros k p q)
  (cases ha (:alive k))
  (case [false] (simp only [r8 ha Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [dead-k ha Bool.not_true Bool.or_false] at q)
    (have q2 := (bnot-true _ q))
    (simp only [r8 ha reach-mem-cons q2 Bool.false_or] at p)
    (simp only [r8 ha]) (exact p))
  (have hr (= (g8-rest xs w) true)) (simp only [g8-rest i8k a1 (And.right r) Bool.and_self])
  (exact (g8-intro xs w (g8-sample _ w h) hr)))

(a/theorem dead-upd-down [x :- Nat, ks :- (List RKey)] (= (tbl-all (dead-k x) (tbl-upd rkey-id x rk-down ks)) true)
  (induction ks)
  (case [nil] (simp only [tbl-upd tbl-all]))
  (case [cons k t ih]
    (cases hx (Nat.beq (rkey-id k) x))
    (case [true] (simp only [tbl-upd hx tbl-all dead-k rk-down ih Bool.not_false Bool.or_true Bool.and_self]))
    (case [false]
      (have hx2 (= (Nat.beq (:id k) x) false)) (exact hx)
      (simp only [tbl-upd hx tbl-all dead-k hx2 ih Bool.not_false Bool.true_or Bool.and_self]))))
(a/theorem i8k-kill [xs :- (List Nat), x :- Nat, rks :- (List RKey), tks :- (List T8K), sks :- (List S8K), xks :- (List X8K)]
  (=> (= (i8k xs rks tks sks xks) true) (= (i8k xs (tbl-upd rkey-id x rk-down rks) tks sks xks) true))
  (intro h) (simp only [i8k Bool.and_eq_true] at h)
  (have a1 (= (tbl-all (r8 xs tks sks) (tbl-upd rkey-id x rk-down rks)) true))
  (exact (tbl-all-upd RKey rkey-id x rk-down (r8 xs tks sks) (r8 xs tks sks)
           (fn [k :- RKey, p :- (= (r8 xs tks sks k) true), q :- (= (Nat.beq (rkey-id k) x) true)] (r8-down xs tks sks k))
           (fn [k :- RKey, p :- (= (r8 xs tks sks k) true), q :- (= (Nat.beq (rkey-id k) x) false)] p)
           rks (And.left h)))
  (simp only [i8k a1 (And.right h) Bool.and_self]))

;; T14's local part, then the cancelled id leaves the escape list
(a/theorem g8-cancel-run-local-x [x :- Nat, xs :- (List Nat), w :- World, r :- RunRow, rep :- Bool]
  (=> (= (g8 (List.cons Nat (:id r) xs) w) true) (= (g8 xs (cancel-run-local w r rep)) true))
  (intro h)
  (have hs := (g8-sample _ w h))
  (have r0 := (g8-rest-of _ w h)) (simp only [g8-rest] at r0)
  (have e := (g8-rest-mk (List.cons Nat (:id r) xs) _ _ _ _ _ (kw8-cancel-run-local w r rep)))
  (have h1 := (g8-intro _ _ (inv-cancel-run-local w r rep hs) (Eq.trans e (i8k-kill _ (:id r) _ _ _ _ r0))))
  (have er (= (rkeys (:runs (cancel-run-local w r rep))) (tbl-upd rkey-id (:id r) rk-down (rkeys (:runs w)))))
  (exact (congrArg (fn [k :- KW8] (:rks k)) (kw8-cancel-run-local w r rep)))
  (have hd (= (tbl-all (dead-k (:id r)) (rkeys (:runs (cancel-run-local w r rep)))) true))
  (rw [er]) (exact (dead-upd-down (:id r) _))
  (exact (g8-disch (:id r) xs _ h1 hd)))

;; T13 (retire-with) and T16 (close-with): the subtree's owned runs join the escape list
(a/theorem kw8-clear-comp-run [w :- World, r :- RunRow] (= (kw8 (clear-comp-run w r)) (kw8 w))
  (cases hc (comp-find w (:of r)))
  (case [some c] (cases hr (Nat.beq (:run c) (:id r))) (all_goals (simp only [clear-comp-run hc hr])))
  (case [none]
    (simp only [clear-comp-run hc])
    (cases ht (task-find w (:of r)))
    (case [none] (simp only [clear-task-run ht]))
    (case [some t]
      (cases hr (Nat.beq (:run t) (:id r)))
      (case [false] (simp only [clear-task-run ht hr]))
      (case [true]
        (simp only [clear-task-run ht hr kw8 task-upd set-tasks
                    (toks-upd (:of r) task-clear-run (fn [q :- TaskRow] (Eq.refl (t8k q))) (:tasks w))])))))
(a/theorem g8-scope-del-fold [xs :- (List Nat), sub :- (List Nat)]
  (forall [w :- World] (=> (= (g8 xs w) true) (= (g8 xs (nat-fold scope-del w sub)) true)))
  (induction sub)
  (case [nil] (intros w h) (simp only [nat-fold]) (exact h))
  (case [cons x t ih]
    (intros w h) (simp only [nat-fold])
    (exact (ih _ (g8-intro xs _ (inv-scope-del w x (g8-sample xs w h)) (g8-rest-scope-del xs w x (g8-rest-of xs w h)))))))
(a/theorem g8-remove-if-empty-x [xs :- (List Nat), w :- World, sub :- (List Nat)]
  (=> (= (g8 xs w) true) (= (g8 xs (remove-if-empty w sub)) true))
  (intro h)
  (cases he (subtree-empty w sub))
  (case [false] (simp only [remove-if-empty he]) (exact h))
  (case [true] (simp only [remove-if-empty he]) (exact (g8-scope-del-fold xs sub w h))))
(a/theorem g8-retire-with-x [xs :- (List Nat), w :- World, r :- RunRow, sub :- (List Nat)]
  (=> (= (g8 xs w) true) (= (g8 (List.append Nat xs (owned-runs w sub)) (retire-with w r sub)) true))
  (intro h)
  (have hs := (g8-sample xs w h))
  (have e := (kw8-clear-comp-run w r))
  (have h1 := (g8-of-kw xs w _ (inv-clear-comp-run w r hs) e h))
  (have er (= (rkeys (:runs (clear-comp-run w r))) (rkeys (:runs w)))) (exact (congrArg (fn [k :- KW8] (:rks k)) e))
  (have et (= (t8ks (:tasks (clear-comp-run w r))) (t8ks (:tasks w)))) (exact (congrArg (fn [k :- KW8] (:tks k)) e))
  (have cv (= (tbl-all (cov8 (owned-runs w sub) sub (t8ks (:tasks (clear-comp-run w r)))) (rkeys (:runs (clear-comp-run w r)))) true))
  (rw [er, et]) (exact (cov-owned w sub hs))
  (have h2 := (g8-close-local-cov xs (owned-runs w sub) _ sub h1 cv))
  (have h3 := (g8-intro _ _ (inv-run-del _ (:id r) (g8-sample _ _ h2)) (g8-rest-run-del _ _ (:id r) (g8-rest-of _ _ h2))))
  (have h4 := (g8-intro _ _ (inv-cleanup-del _ (:id r) (g8-sample _ _ h3)) (g8-rest-of _ _ h3)))
  (simp only [retire-with])
  (exact (g8-remove-if-empty-x _ _ sub h4)))
(a/theorem g8-close-with-x [xs :- (List Nat), w :- World, sub :- (List Nat)]
  (=> (= (g8 xs w) true) (= (g8 (List.append Nat xs (owned-runs w sub)) (close-with w sub)) true))
  (intro h) (simp only [close-with]) (exact (g8-remove-if-empty-x _ _ sub (g8-close-local xs w sub h))))

;; ---- one job, then the whole cascade
(a/theorem esc-sub [x :- Nat, base :- (List Nat), t :- (List Job), u :- (List Job)]
  (=> (= (reach-mem x (List.append Nat base (cj t))) true) (= (reach-mem x (List.append Nat base (cj (List.append Job t u)))) true))
  (intro h) (simp only [reach-mem-append cj-append Bool.or_eq_true] at h) (simp only [reach-mem-append cj-append Bool.or_eq_true])
  (cases h) (case [inl a] (exact (Or.inl a))) (case [inr b] (exact (Or.inr (Or.inl b)))))
(a/theorem esc-next [x :- Nat, base :- (List Nat), t :- (List Job), ys :- (List Nat)]
  (=> (= (reach-mem x (List.append Nat (List.append Nat base (cj t)) ys)) true)
      (= (reach-mem x (List.append Nat base (cj (List.append Job t (cancel-jobs ys))))) true))
  (intro h) (simp only [reach-mem-append cj-append cj-cancel-jobs Bool.or_eq_true] at h)
  (simp only [reach-mem-append cj-append cj-cancel-jobs Bool.or_eq_true])
  (cases h)
  (case [inl a] (cases a) (case [inl b] (exact (Or.inl b))) (case [inr c] (exact (Or.inr (Or.inl c)))))
  (case [inr d] (exact (Or.inr (Or.inr d)))))
(a/theorem esc-next2 [x :- Nat, base :- (List Nat), t :- (List Job), ys :- (List Nat), rid :- Nat]
  (=> (= (reach-mem x (List.append Nat base (cj t))) true)
      (= (reach-mem x (List.append Nat base (cj (List.append Job t (List.append Job (cancel-jobs ys) (List.cons Job (Job.jretire rid) (List.nil Job))))))) true))
  (intro h) (exact (esc-sub x base t _ h)))
(a/theorem cancel-esc [x :- Nat, rid :- Nat, rep :- Bool, base :- (List Nat), t :- (List Job)]
  (=> (= (reach-mem x (List.append Nat base (cj (List.cons Job (Job.jcancel rid rep) t)))) true)
      (= (reach-mem x (List.cons Nat rid (List.append Nat base (cj t)))) true))
  (intro h)
  (simp only [cj job-cid reach-mem-append reach-mem-cons reach-mem Bool.or_eq_true Bool.or_false List.cons_append List.nil_append] at h)
  (simp only [reach-mem-cons reach-mem-append Bool.or_eq_true])
  (cases h)
  (case [inl a] (exact (Or.inr (Or.inl a))))
  (case [inr b] (cases b) (case [inl c] (exact (Or.inl c))) (case [inr d] (exact (Or.inr (Or.inr d))))))
(a/theorem dead-of-none [w :- World, rid :- Nat]
  (=> (= (run-find w rid) (Option.none RunRow)) (= (tbl-all (dead-k rid) (rkeys (:runs w))) true))
  (intro hf)
  (have n := (ne-of-none w rid hf)) (simp only [neb-rest] at n)
  (rw [all-rkeys])
  (apply (tbl-all-mono RunRow (ne-ok rid) (on-rkey (dead-k rid)) _ (:runs w) n))
  (intros q p) (simp only [ne-ok] at p) (simp only [on-rkey dead-k rkey p Bool.true_or]))
(a/theorem dead-of-find [w :- World, rid :- Nat, r :- RunRow]
  (=> (= (inv-sample w) true) (= (run-find w rid) (Option.some RunRow r)) (= (run-alive r) false)
      (= (tbl-all (dead-k rid) (rkeys (:runs w))) true))
  (intros hs hf ha)
  (have m := (tbl-find-mem RunRow run-id rid r (:runs w) hf))
  (have i (= (run-id r) rid)) (exact (tbl-find-id RunRow run-id rid r (:runs w) hf))
  (have nd (= (Bool.not (run-alive r)) true)) (simp only [ha Bool.not_false])
  (have u := (uniq-all RunRow run-id (fn [q :- RunRow] (Bool.not (run-alive q))) r (:runs w) (lit-runs-nodup w hs) m nd))
  (rw [i] at u)
  (rw [all-rkeys])
  (apply (tbl-all-mono RunRow _ (on-rkey (dead-k rid)) _ (:runs w) u))
  (intros q p) (simp only [same-id-then] at p) (simp only [on-rkey dead-k rkey]) (exact p))
;; the escape after a job: the pending cancels of the tail and of the job's follow-up jobs
(a/defn esc8 [base :- (List Nat), w :- World, j :- Job, t :- (List Job)] (List Nat)
  (List.append Nat base (cj (List.append Job t (job-next w j)))))
(a/theorem esc-tail [x :- Nat, base :- (List Nat), w :- World, j :- Job, t :- (List Job)]
  (=> (= (reach-mem x (List.append Nat base (cj t))) true) (= (reach-mem x (esc8 base w j t)) true))
  (intro h) (simp only [esc8]) (exact (esc-sub x base t (job-next w j) h)))
(a/theorem esc-owned [x :- Nat, base :- (List Nat), w :- World, j :- Job, t :- (List Job), ys :- (List Nat)]
  (=> (= (job-next w j) (cancel-jobs ys)) (= (reach-mem x (List.append Nat (List.append Nat base (cj t)) ys)) true)
      (= (reach-mem x (esc8 base w j t)) true))
  (intros e h) (simp only [esc8 e]) (exact (esc-next x base t ys h)))

(a/theorem g8-job-cancel [base :- (List Nat), w :- World, rid :- Nat, rep :- Bool, t :- (List Job)]
  (=> (= (g8 (List.append Nat base (cj (List.cons Job (Job.jcancel rid rep) t))) w) true)
      (= (g8 (esc8 base w (Job.jcancel rid rep) t) (job-apply w (Job.jcancel rid rep))) true))
  (intro h)
  (have hs := (g8-sample _ w h))
  (have h0 := (g8-esc-mono (List.append Nat base (cj (List.cons Job (Job.jcancel rid rep) t))) (List.cons Nat rid (List.append Nat base (cj t))) w
                (fn [x :- Nat, q :- (= (reach-mem x (List.append Nat base (cj (List.cons Job (Job.jcancel rid rep) t)))) true)]
                  (cancel-esc x rid rep base t q)) h))
  (apply (g8-esc-mono (List.append Nat base (cj t)) (esc8 base w (Job.jcancel rid rep) t) (job-apply w (Job.jcancel rid rep))
           (fn [x :- Nat, q :- (= (reach-mem x (List.append Nat base (cj t))) true)] (esc-tail x base w (Job.jcancel rid rep) t q))))
  (cases hf (run-find w rid))
  (case [none]
    (simp only [job-apply hf])
    (exact (g8-disch rid (List.append Nat base (cj t)) w h0 (dead-of-none w rid hf))))
  (case [some r]
    (cases ha (run-alive r))
    (case [false]
      (simp only [job-apply hf ha])
      (exact (g8-disch rid (List.append Nat base (cj t)) w h0 (dead-of-find w rid r hs hf ha))))
    (case [true]
      (have i (= (:id r) rid)) (exact (tbl-find-id RunRow run-id rid r (:runs w) hf))
      (simp only [job-apply hf ha])
      (rw [← i] at h0)
      (exact (g8-cancel-run-local-x rid (List.append Nat base (cj t)) w r rep h0)))))

(a/theorem g8-job-retire [base :- (List Nat), w :- World, rid :- Nat, t :- (List Job)]
  (=> (= (g8 (List.append Nat base (cj (List.cons Job (Job.jretire rid) t))) w) true)
      (= (g8 (esc8 base w (Job.jretire rid) t) (job-apply w (Job.jretire rid))) true))
  (intro h)
  (have h0 (= (g8 (List.append Nat base (cj t)) w) true)) (exact h)
  (cases hf (run-find w rid))
  (case [none]
    (simp only [job-apply hf])
    (exact (g8-esc-mono (List.append Nat base (cj t)) (esc8 base w (Job.jretire rid) t) w
             (fn [x :- Nat, q :- (= (reach-mem x (List.append Nat base (cj t))) true)] (esc-tail x base w (Job.jretire rid) t q)) h0)))
  (case [some r]
    (cases hr (retirable r))
    (case [false]
      (simp only [job-apply hf hr])
      (exact (g8-esc-mono (List.append Nat base (cj t)) (esc8 base w (Job.jretire rid) t) w
               (fn [x :- Nat, q :- (= (reach-mem x (List.append Nat base (cj t))) true)] (esc-tail x base w (Job.jretire rid) t q)) h0)))
    (case [true]
      (have e (= (job-next w (Job.jretire rid)) (cancel-jobs (owned-runs w (scope-subtree w (:scope r)))))) (simp only [job-next hf hr])
      (have h1 := (g8-retire-with-x (List.append Nat base (cj t)) w r (scope-subtree w (:scope r)) h0))
      (simp only [job-apply hf hr retire-local])
      (exact (g8-esc-mono _ (esc8 base w (Job.jretire rid) t) (retire-with w r (scope-subtree w (:scope r)))
               (fn [x :- Nat, q :- (= (reach-mem x (List.append Nat (List.append Nat base (cj t)) (owned-runs w (scope-subtree w (:scope r))))) true)]
                 (esc-owned x base w (Job.jretire rid) t _ e q)) h1)))))

(a/theorem g8-job-close [base :- (List Nat), w :- World, s :- Nat, t :- (List Job)]
  (=> (= (g8 (List.append Nat base (cj (List.cons Job (Job.jclose s) t))) w) true)
      (= (g8 (esc8 base w (Job.jclose s) t) (job-apply w (Job.jclose s))) true))
  (intro h)
  (have h0 (= (g8 (List.append Nat base (cj t)) w) true)) (exact h)
  (cases hc (scope-has w s))
  (case [false]
    (simp only [job-apply hc])
    (exact (g8-esc-mono (List.append Nat base (cj t)) (esc8 base w (Job.jclose s) t) w
             (fn [x :- Nat, q :- (= (reach-mem x (List.append Nat base (cj t))) true)] (esc-tail x base w (Job.jclose s) t q)) h0)))
  (case [true]
    (have e (= (job-next w (Job.jclose s)) (cancel-jobs (owned-runs w (scope-subtree w s))))) (simp only [job-next hc])
    (have h1 := (g8-close-with-x (List.append Nat base (cj t)) w (scope-subtree w s) h0))
    (simp only [job-apply hc close-scope-local])
    (exact (g8-esc-mono _ (esc8 base w (Job.jclose s) t) (close-with w (scope-subtree w s))
             (fn [x :- Nat, q :- (= (reach-mem x (List.append Nat (List.append Nat base (cj t)) (owned-runs w (scope-subtree w s)))) true)]
               (esc-owned x base w (Job.jclose s) t _ e q)) h1))))

(a/theorem g8-job [base :- (List Nat), w :- World, j :- Job, t :- (List Job)]
  (=> (= (g8 (List.append Nat base (cj (List.cons Job j t))) w) true)
      (= (g8 (List.append Nat base (cj (List.append Job t (job-next w j)))) (job-apply w j)) true))
  (intro h)
  (cases j)
  (case [jcancel rid rep] (exact (g8-job-cancel base w rid rep t h)))
  (case [jretire rid] (exact (g8-job-retire base w rid t h)))
  (case [jclose s] (exact (g8-job-close base w s t h))))

(a/theorem g8-cascade [base :- (List Nat), fuel :- (List Nat)]
  (forall [w :- World, js :- (List Job)]
    (=> (= (g8 (List.append Nat base (cj js)) w) true)
        (= (g8 (List.append Nat base (cj (:rest (cascade fuel w js)))) (:world (cascade fuel w js))) true)))
  (induction fuel)
  (case [nil] (intros w js h) (simp only [cascade]) (exact h))
  (case [cons u f ih]
    (intros w js h)
    (cases js)
    (case [nil] (simp only [cascade]) (exact h))
    (case [cons j t] (simp only [cascade]) (exact (ih _ _ (g8-job base w j t h))))))

(a/theorem esc-base [x :- Nat, base :- (List Nat), js :- (List Job)]
  (=> (= (reach-mem x base) true) (= (reach-mem x (List.append Nat base (cj js))) true))
  (intro h) (simp only [reach-mem-append h Bool.true_or]))
(a/theorem esc-done [x :- Nat, base :- (List Nat)]
  (=> (= (reach-mem x (List.append Nat base (cj (List.nil Job)))) true) (= (reach-mem x base) true))
  (intro h) (simp only [reach-mem-append cj reach-mem Bool.or_false] at h) (exact h))
;; a cascade whose worklist empties keeps g8 (the escape list of pending cancels is then empty)
(a/theorem g8-cascade-done [x8s :- (List Nat), w :- World, js :- (List Job)]
  (=> (= (casc-done w js) true) (= (g8 x8s w) true) (= (g8 x8s (run-cascade w js)) true))
  (intros hd h)
  (have h0 := (g8-esc-mono x8s (List.append Nat x8s (cj js)) w (fn [x :- Nat, q :- (= (reach-mem x x8s) true)] (esc-base x x8s js q)) h))
  (have c := (g8-cascade x8s (casc-fuel w js) w js h0))
  (have d := (jobs-nil (:rest (cascade-run w js)) hd))
  (have d2 (= (:rest (cascade (casc-fuel w js) w js)) (List.nil Job))) (exact d)
  (rw [d2] at c)
  (exact (g8-esc-mono _ x8s _ (fn [x :- Nat, q :- (= (reach-mem x (List.append Nat x8s (cj (List.nil Job)))) true)] (esc-done x x8s q)) c)))
(a/theorem g8-run-cascade-aa [x8s :- (List Nat), w :- World, js :- (List Job)]
  (=> (= (acts-alive w) true) (= (g8 x8s w) true) (= (g8 x8s (run-cascade w js)) true))
  (intros ha h) (exact (g8-cascade-done x8s w js (casc-done-ok w js (g8-sample x8s w h) ha) h)))
(a/theorem g8-run-cascade-ga [x8s :- (List Nat), w :- World, js :- (List Job)]
  (=> (= (ga w) true) (= (g8 x8s w) true) (= (g8 x8s (run-cascade w js)) true))
  (intros hga h) (exact (g8-cascade-done x8s w js (casc-done-ga w js hga) h)))

;; ===========================================================================
;; Part G. Owners of new tasks and sources; task owners that change
;; ===========================================================================

(a/theorem scopes-nodup8 [w :- World] (=> (= (inv-sample w) true) (= (nat-nodup (tbl-ids scope-id (:scopes w))) true))
  (intro h) (have u := (ids-unique-of w h)) (simp only [all-ids] at u) (exact (nat-nodup-app-left _ _ u)))
(a/theorem sclosed-has [x :- Nat, ss :- (List ScopeRow)] (=> (= (sclosed (s8ks ss) x) true) (= (tbl-has scope-id x ss) true))
  (induction ss)
  (case [nil] (intro h) (simp only [s8ks sclosed tbl-any] at h) (cases h))
  (case [cons s t ih]
    (intro h)
    (simp only [s8ks sclosed tbl-any Bool.or_eq_true] at h)
    (cases h)
    (case [inl a]
      (simp only [sclosed-k s8k Bool.and_eq_true] at a)
      (have e (= (Nat.beq (scope-id s) x) true)) (exact (And.left a))
      (simp only [tbl-has e]))
    (case [inr b]
      (have q := (ih b))
      (cases e (Nat.beq (scope-id s) x))
      (case [true] (simp only [tbl-has e]))
      (case [false] (simp only [tbl-has e]) (exact q)))))
(a/theorem sclosed-zero [w :- World] (=> (= (inv-sample w) true) (= (sclosed (s8ks (:scopes w)) 0) false))
  (intro h)
  (cases hc (sclosed (s8ks (:scopes w)) 0))
  (case [false] (rfl))
  (case [true] (have p := (scope-pos w 0 h (sclosed-has 0 (:scopes w) hc))) (simp only [Nat.beq_refl] at p) (cases p)))
(a/theorem no-closed-of [x :- Nat, ss :- (List ScopeRow)]
  (=> (= (tbl-all (same-id-then scope-id x (fn [q :- ScopeRow] (:open q))) ss) true) (= (sclosed (s8ks ss) x) false))
  (induction ss)
  (case [nil] (intro h) (simp only [s8ks sclosed tbl-any]))
  (case [cons s t ih]
    (intro h)
    (simp only [tbl-all Bool.and_eq_true] at h)
    (have r := (ih (And.right h)))
    (simp only [sclosed] at r)
    (have a := (And.left h))
    (simp only [same-id-then Bool.or_eq_true] at a)
    (have k (= (sclosed-k x (s8k s)) false))
    (cases a)
    (case [inl b] (have b2 := (bnot-true _ b)) (have b3 (= (Nat.beq (:id s) x) false)) (exact b2) (simp only [sclosed-k s8k b3 Bool.false_and]))
    (case [inr c] (simp only [sclosed-k s8k c Bool.not_true Bool.and_false]))
    (simp only [s8ks sclosed tbl-any k r Bool.or_self])))
(a/theorem tclosed-absent [c :- Nat, ts :- (List TaskRow), sks :- (List S8K)]
  (=> (= (nat-mem c (tbl-ids task-id ts)) false) (= (tclosed (t8ks ts) sks c) false))
  (induction ts)
  (case [nil] (intro h) (simp only [t8ks tclosed tbl-any]))
  (case [cons t tl ih]
    (intro h)
    (cases hb (Nat.beq (task-id t) c))
    (case [true] (simp [tbl-ids nat-mem hb] at h))
    (case [false]
      (simp only [tbl-ids nat-mem hb] at h)
      (have r := (ih h)) (simp only [tclosed] at r)
      (have e (= (Nat.beq (:id t) c) false)) (exact hb)
      (simp only [t8ks tclosed tbl-any tclosed-k t8k e r Bool.false_and Bool.or_self]))))
(a/theorem open-not-closed [w :- World, s :- Nat] (=> (= (inv-sample w) true) (= (scope-open-at w s) true) (= (sclosed (s8ks (:scopes w)) s) false))
  (intros h ho)
  (cases hf (scope-find w s))
  (case [none] (simp only [scope-open-at hf] at ho) (cases ho))
  (case [some sc]
    (simp only [scope-open-at hf] at ho)
    (have m := (tbl-find-mem ScopeRow scope-id s sc (:scopes w) hf))
    (have i (= (scope-id sc) s)) (exact (tbl-find-id ScopeRow scope-id s sc (:scopes w) hf))
    (have u := (uniq-all ScopeRow scope-id (fn [q :- ScopeRow] (:open q)) sc (:scopes w) (scopes-nodup8 w h) m ho))
    (rw [i] at u)
    (exact (no-closed-of s (:scopes w) u))))
(a/theorem comp-not-tclosed [w :- World, c :- Nat, sks :- (List S8K)]
  (=> (= (inv-sample w) true) (= (comp-has w c) true) (= (tclosed (t8ks (:tasks w)) sks c) false))
  (intros h hc)
  (have n := (comp-not-task w c h hc))
  (exact (tclosed-absent c (:tasks w) sks n)))
(a/theorem tasks-below8 [w :- World] (=> (= (inv-sample w) true) (= (tbl-all (id-in-range (:next-id w)) (tbl-ids task-id (:tasks w))) true))
  (intro h) (have b := (ids-below-of w h)) (simp only [all-ids tbl-all-nat-app Bool.and_eq_true] at b) (exact (And.left (And.right (And.right b)))))
(a/theorem tclosed-fresh [w :- World, sks :- (List S8K)] (=> (= (inv-sample w) true) (= (tclosed (t8ks (:tasks w)) sks (:next-id w)) false))
  (intro h) (exact (tclosed-absent _ _ sks (range-not-mem _ _ (tasks-below8 w h)))))
(a/theorem comp-not-sclosed [w :- World, c :- Nat] (=> (= (inv-sample w) true) (= (comp-has w c) true) (= (sclosed (s8ks (:scopes w)) c) false))
  (intros h hc)
  (cases hs (sclosed (s8ks (:scopes w)) c))
  (case [false] (rfl))
  (case [true]
    (have u := (ids-unique-of w h)) (simp only [all-ids] at u)
    (have hm (= (nat-mem c (tbl-ids scope-id (:scopes w))) true)) (rw [nat-mem-ids]) (exact (sclosed-has c (:scopes w) hs))
    (have hm2 (= (nat-mem c (tbl-ids comp-id (:comps w))) true)) (rw [nat-mem-ids]) (exact hc)
    (have d := (nodup-app-disj c _ _ u hm))
    (simp only [nat-mem-app Bool.or_eq_false_iff] at d)
    (have d1 := (And.left d)) (rw [hm2] at d1) (cases d1)))

;; ---- T4: spawn rows with an owner that is not a closed scope
(a/theorem g8-spawn-rows-o [x8s :- (List Nat), w :- World, owner :- Nat, inputs :- (List Nat)]
  (=> (= (sclosed (s8ks (:scopes w)) owner) false) (= (g8 x8s w) true) (= (g8 x8s (spawn-rows w owner inputs)) true))
  (intros ho h)
  (have hs := (g8-sample x8s w h))
  (have h1 := (g8-task-ins x8s w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs) (rfl) ho h))
  (have tf := (tclosed-fresh w (s8ks (:scopes w)) hs))
  (have tc (= (tclosed (t8ks (:tasks (bump (task-ins w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs)))))
                       (s8ks (:scopes (bump (task-ins w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs))))) (:next-id w)) false))
  (simp only [tclosed] at tf)
  (simp only [bump set-next-id task-ins set-tasks tbl-ins t8ks tclosed tbl-any tclosed-k t8k new-task-row ho tf Bool.and_false Bool.false_or])
  (simp only [spawn-rows])
  (exact (g8-add-run-scope-o x8s _ (:next-id w) 0 _ 0 tc h1)))
(a/theorem owner-ok8 [w :- World, r :- RunRow]
  (=> (= (inv-sample w) true) (= (run-cur-closed w r) false) (= (sclosed (s8ks (:scopes w)) (spawn-owner w r)) false))
  (intros h hc)
  (cases hi (in-comp w r))
  (case [true] (simp only [spawn-owner hi]) (exact (comp-not-sclosed w (:of r) h hi)))
  (case [false]
    (simp only [spawn-owner hi])
    (simp only [run-cur-closed hi Bool.not_false Bool.true_and] at hc)
    (exact (open-not-closed w (cur-scope w r) h (bnot-false _ hc)))))
(a/theorem src-owner-ok8 [w :- World, r :- RunRow]
  (=> (= (inv-sample w) true) (= (run-cur-closed w r) false) (= (sclosed (s8ks (:scopes w)) (src-owner-cur w r)) false))
  (intros h hc)
  (have e (= (src-owner-cur w r) (spawn-owner w r))) (rfl)
  (rw [e]) (exact (owner-ok8 w r h hc)))
(a/theorem cur-of-tok [w :- World, st :- Nat, r :- RunRow]
  (=> (= (cur-closed w st) false) (= (tok-run w st) (Option.some RunRow r)) (= (run-cur-closed w r) false))
  (intros h ht) (simp only [cur-closed ht opt-test] at h) (exact h))
(a/theorem bshut-cur [w :- World, st :- Nat] (=> (= (body-shut w st) false) (= (cur-closed w st) false))
  (intro h) (simp only [body-shut Bool.or_eq_false_iff] at h) (exact (And.right h)))

;; ---- task owners that change: detach (an open scope, Q10) and Rule R's detach (0)
(a/defn tk-own [o :- Nat, k :- T8K] T8K (T8K.mk (:id k) o))
(a/theorem any8-upd [A :- Type, idf :- (=> A Nat), x :- Nat, g :- (=> A A), p :- (=> A Bool),
                     hg :- (forall [k :- A] (=> (= (p (g k)) true) (= (p k) true))), xs :- (List A)]
  (=> (= (tbl-any p (tbl-upd idf x g xs)) true) (= (tbl-any p xs) true))
  (induction xs)
  (case [nil] (intro h) (simp only [tbl-upd] at h) (exact h))
  (case [cons k t ih]
    (intro q)
    (cases hx (Nat.beq (idf k) x))
    (case [true]
      (simp only [tbl-upd hx tbl-any Bool.or_eq_true] at q) (simp only [tbl-any Bool.or_eq_true])
      (cases q) (case [inl a] (exact (Or.inl (hg k a)))) (case [inr b] (exact (Or.inr (ih b)))))
    (case [false]
      (simp only [tbl-upd hx tbl-any Bool.or_eq_true] at q) (simp only [tbl-any Bool.or_eq_true])
      (cases q) (case [inl a] (exact (Or.inl a))) (case [inr b] (exact (Or.inr (ih b)))))))
(a/theorem g8-task-owner [x8s :- (List Nat), w :- World, x :- Nat, f :- (=> TaskRow TaskRow), o :- Nat,
                          hf :- (forall [t :- TaskRow] (= (task-id (f t)) (task-id t))),
                          hk :- (forall [t :- TaskRow] (= (t8k (f t)) (tk-own o (t8k t))))]
  (=> (= (sclosed (s8ks (:scopes w)) o) false) (= (g8 x8s w) true) (= (g8 x8s (task-upd w x f)) true))
  (intros ho h)
  (have r := (g8-rest-of x8s w h)) (simp only [g8-rest i8k Bool.and_eq_true] at r)
  (have e := (toks-upd-g x f (tk-own o) hk (:tasks w)))
  (have ht (forall [t :- Nat] (=> (= (tclosed (tbl-upd t8k-id x (tk-own o) (t8ks (:tasks w))) (s8ks (:scopes w)) t) true)
                                   (= (tclosed (t8ks (:tasks w)) (s8ks (:scopes w)) t) true))))
  (intros t q)
  (simp only [tclosed] at q) (simp only [tclosed])
  (apply (any8-upd T8K t8k-id x (tk-own o) (tclosed-k (s8ks (:scopes w)) t) _ (t8ks (:tasks w)) q))
  (intros k p) (simp only [tclosed-k tk-own ho Bool.and_false] at p) (cases p)
  (have a1 := (r8-all-mono x8s _ _ _ _ ht _ (And.left r)))
  (have hr (= (g8-rest x8s (task-upd w x f)) true)) (simp only [g8-rest i8k task-upd set-tasks e a1 (And.right r) Bool.and_self])
  (exact (g8-intro x8s _ (inv-task-upd w x f hf (g8-sample x8s w h)) hr)))
(a/theorem tok-detach [t :- TaskRow] (= (t8k (task-detach-row t)) (tk-own 0 (t8k t))) (rfl))
(a/theorem tok-set-owner [s :- Nat, t :- TaskRow] (= (t8k (task-set-owner s t)) (tk-own s (t8k t))) (rfl))
(a/theorem g8-task-detach [x8s :- (List Nat), w :- World, x :- Nat]
  (=> (= (g8 x8s w) true) (= (g8 x8s (task-upd w x task-detach-row)) true))
  (intro h) (exact (g8-task-owner x8s w x task-detach-row 0 task-detach-row-id tok-detach (sclosed-zero w (g8-sample x8s w h)) h)))

(lcopy! G8 'inv-insert-edge-checked)
(lcopy! G8 'inv-record-basis)
(swap! (:renames G8) assoc 'inv-task-ins-fresh 'g8-task-ins 'inv-source-ins-fresh 'g8-source-ins 'inv-run-ins-fresh 'g8-run-ins
       'inv-close-local 'g8-close-local)

;; ---- park sites: a run made parked (alive) was alive (the awaiting / taking run)
(a/theorem g8-take-park-o [x8s :- (List Nat), w :- World, r :- RunRow, x :- Nat, k :- Nat]
  (=> (List.Mem r (:runs w)) (= (run-alive r) true) (= (g8 x8s w) true) (= (g8 x8s (take-park w r x k)) true))
  (intros hm hal h)
  (have o := (run-ok-of-mem w r (g8-sample x8s w h) hm hal))
  (have h1 := (g8-insert-edge-checked x8s _ (take-edge r (:next-id w) x) (g8-act-ins-fresh x8s w (take-act w r k) (rfl) h)))
  (have o2 (= (tbl-all (run-ok-for (:id r)) (:runs (insert-edge-checked (bump (act-ins w (take-act w r k))) (take-edge r (:next-id w) x)))) true))
  (rw [runs-iec]) (exact o)
  (simp only [take-park])
  (exact (g8-run-upd-up x8s _ (:id r) run-tick-park run-tick-park-id tick-park-alive (fn [q :- RunRow] (Eq.refl (:of q))) o2 h1)))

(a/theorem tick-park-alive8 [r :- RunRow] (= (run-alive (run-tick-park r)) true) (simp [run-alive run-tick-park act-parked act-done]))
(a/theorem park-alive8 [r :- RunRow] (= (run-alive (run-park-row r)) true) (simp [run-alive run-park-row act-parked act-done]))

;; ===========================================================================
;; Part H. Overrides: creations, parks, the cascades (with ga: P4), Rule R (with acts-alive)
;; ===========================================================================

(override! G8 'inv-add-run-scope '[]
  '(a/theorem g8-add-run-scope [x8s :- (List Nat), w :- World, of :- Nat, epoch :- Nat, parent :- Nat, ei :- Nat]
     (=> (= (tclosed (t8ks (:tasks w)) (s8ks (:scopes w)) of) false) (= (g8 x8s w) true) (= (g8 x8s (add-run-scope w of epoch parent ei)) true))
     (intros hc h) (exact (g8-add-run-scope-o x8s w of epoch parent ei hc h))))
(override! G8 'inv-spawn-rows '[inv-add-run-scope]
  '(a/theorem g8-spawn-rows [x8s :- (List Nat), w :- World, owner :- Nat, inputs :- (List Nat)]
     (=> (= (sclosed (s8ks (:scopes w)) owner) false) (= (g8 x8s w) true) (= (g8 x8s (spawn-rows w owner inputs)) true))
     (intros ho h) (exact (g8-spawn-rows-o x8s w owner inputs ho h))))
(override! G8 't4-inv '[inv-spawn-rows inv-record-basis]
  '(a/theorem t4-g8 [x8s :- (List Nat), w :- World, st :- Nat, body :- Nat, fresh :- Nat, inputs :- (List Nat)]
     (=> (= (cur-closed w st) false) (= (g8 x8s w) true) (= (g8 x8s (:world (t4-spawn w st body fresh inputs))) true))
     (intros hcc h)
     (cases ht (tok-run w st)) (case' [some r]) (case' [none])
     (simp only [t4-spawn ht refuse]) (exact h)
     (have ho := (owner-ok8 w r (g8-sample x8s w h) (cur-of-tok w st r hcc ht)))
     (cases hp (respawn-target w r fresh))
     (case [none]
       (cases hf (Nat.beq fresh (:next-id w)))
       (case [false] (simp only [t4-spawn ht hp hf refuse]) (exact h))
       (case [true]
         (simp only [t4-spawn ht hp hf accept])
         (exact (g8-run-upd x8s _ (:id r) run-tick run-tick-run-id (fn [q :- RunRow] (Eq.refl (rkey q)))
                  (g8-record-basis x8s _ r fresh (g8-spawn-rows x8s w (spawn-owner w r) inputs ho h))))))
     (case [some t]
       (cases he (nat-list-eq inputs (:inputs t)))
       (case [false] (simp only [t4-spawn ht hp he refuse]) (exact h))
       (case [true]
         (simp only [t4-spawn ht hp he accept respawn-raw])
         (exact (g8-run-upd x8s _ (:id r) run-tick run-tick-run-id (fn [q :- RunRow] (Eq.refl (rkey q)))
                  (g8-comp-upd x8s w (:of r) _ (comp-rebasis-id _) (comp-rebasis-pending _) h)))))))
(override! G8 't4-top-inv '[inv-spawn-rows]
  '(a/theorem t4-top-g8 [x8s :- (List Nat), w :- World, scope :- Nat, body :- Nat, fresh :- Nat, inputs :- (List Nat)]
     (=> (= (g8 x8s w) true) (= (g8 x8s (:world (t4-spawn-top w scope body fresh inputs))) true))
     (intro h)
     (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (scope-open-at w scope)))
     (simp only [t4-spawn-top hg refuse]) (exact h)
     (have hso (= (scope-open-at w scope) true)) (simp only [Bool.and_eq_true] at hg) (exact (And.right hg))
     (simp only [t4-spawn-top hg accept])
     (exact (g8-spawn-rows x8s w scope inputs (open-not-closed w scope (g8-sample x8s w h) hso) h))))
(override! G8 'inv-create-source-cur '[inv-record-basis]
  '(a/theorem g8-create-source-cur [x8s :- (List Nat), w :- World, r :- RunRow, kind :- Nat, v :- Nat]
     (=> (= (run-cur-closed w r) false) (= (g8 x8s w) true) (= (g8 x8s (create-source-cur w r kind v)) true))
     (intros hc h)
     (have ho := (src-owner-ok8 w r (g8-sample x8s w h) hc))
     (have hx (= (x8 (s8ks (:scopes w)) (x8k (new-source (:next-id w) (src-owner-cur w r) kind v))) true))
     (simp only [x8 x8k new-source ho Bool.not_false Bool.or_true])
     (simp only [create-source-cur])
     (exact (g8-run-upd x8s _ (:id r) run-tick run-tick-run-id (fn [q :- RunRow] (Eq.refl (rkey q)))
              (g8-record-basis x8s _ r (:next-id w) (g8-source-ins x8s w (new-source (:next-id w) (src-owner-cur w r) kind v) (rfl) hx h))))))
(override! G8 't1-full-inv '[inv-create-source-cur]
  '(a/theorem t1-full-g8 [x8s :- (List Nat), w :- World, st :- Nat, kind :- Nat, v :- Nat, fresh :- Nat]
     (=> (= (cur-closed w st) false) (= (g8 x8s w) true) (= (g8 x8s (:world (t1-full w st kind v fresh))) true))
     (intros hcc h)
     (cases ht (tok-run w st)) (case' [some r]) (case' [none])
     (simp only [t1-full ht refuse]) (exact h)
     (cases ho (readopt-source w r fresh))
     (case [none]
       (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (src-kind-ok kind)))
       (case [false] (simp only [t1-full ht ho hg refuse]) (exact h))
       (case [true] (simp only [t1-full ht ho hg accept]) (exact (g8-create-source-cur x8s w r kind v (cur-of-tok w st r hcc ht) h))))
     (case [some x]
       (cases hk (Nat.beq (:kind x) kind))
       (case [false] (simp only [t1-full ht ho hk refuse]) (exact h))
       (case [true]
         (simp only [t1-full ht ho hk accept respawn-raw])
         (exact (g8-run-upd x8s _ (:id r) run-tick run-tick-run-id (fn [q :- RunRow] (Eq.refl (rkey q)))
                  (g8-comp-upd x8s w (:of r) _ (comp-rebasis-id _) (comp-rebasis-pending _) h)))))))
(override! G8 't1-top-inv '[]
  '(a/theorem t1-top-g8 [x8s :- (List Nat), w :- World, scope :- Nat, kind :- Nat, v :- Nat, fresh :- Nat]
     (=> (= (g8 x8s w) true) (= (g8 x8s (:world (t1-create-source-top w scope kind v fresh))) true))
     (intro h)
     (cases hg (Bool.and (Bool.and (Nat.beq fresh (:next-id w)) (src-kind-ok kind)) (scope-open-at w scope)))
     (simp only [t1-create-source-top hg refuse]) (exact h)
     (have hso (= (scope-open-at w scope) true)) (simp only [Bool.and_eq_true] at hg) (exact (And.right hg))
     (have hx (= (x8 (s8ks (:scopes w)) (x8k (new-source (:next-id w) scope kind v))) true))
     (simp only [x8 x8k new-source (open-not-closed w scope (g8-sample x8s w h) hso) Bool.not_false Bool.or_true])
     (simp only [t1-create-source-top hg accept])
     (exact (g8-source-ins x8s w (new-source (:next-id w) scope kind v) (rfl) hx h))))
(override! G8 'inv-start-raw '[inv-add-run-scope]
  '(a/theorem g8-start-raw [x8s :- (List Nat), w :- World, c :- CompRow]
     (=> (= (comp-has w (:id c)) true) (= (g8 x8s w) true) (= (g8 x8s (start-raw w c)) true))
     (intros hc h)
     (simp only [start-raw])
     (exact (g8-comp-upd x8s _ (:id c) (comp-start-row (:next-id w)) (comp-start-row-id (:next-id w)) (comp-start-row-pending (:next-id w))
              (g8-add-run-scope x8s w (:id c) (start-epoch c) 0 0 (comp-not-tclosed w (:id c) (s8ks (:scopes w)) (g8-sample x8s w h) hc) h)))))
(a/theorem comp-has-find8 [w :- World, cid :- Nat, c :- CompRow] (=> (= (comp-find w cid) (Option.some CompRow c)) (= (comp-has w (:id c)) true))
  (intro hf)
  (have i (= (comp-id c) cid)) (exact (tbl-find-id CompRow comp-id cid c (:comps w) hf))
  (have e (= (:id c) cid)) (exact i)
  (rw [e]) (exact (tbl-find-has CompRow comp-id cid c (:comps w) hf)))
(override! G8 't5-inv '[inv-start-raw]
  '(a/theorem t5-g8 [x8s :- (List Nat), w :- World, cid :- Nat, fresh :- Nat]
     (=> (= (g8 x8s w) true) (= (g8 x8s (:world (t5-start w cid fresh))) true))
     (intro h)
     (cases hc (comp-find w cid)) (case' [some c]) (case' [none])
     (simp only [t5-start hc refuse]) (exact h)
     (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (startable w c)))
     (simp only [t5-start hc hg refuse]) (exact h)
     (simp only [t5-start hc hg accept]) (exact (g8-start-raw x8s w c (comp-has-find8 w cid c hc) h))))

;; ---- the copy's patches: keys kept by lemma (wake, consume), shut sources, orphaned tasks
(a/theorem x8k-consume [s :- SourceRow] (= (x8k (source-consume s)) (x8k s))
  (cases ha (src-available s)) (all_goals (cases h (Nat.beq (:kind s) sk-mailbox)))
  (all_goals (simp only [source-consume x8k ha h])))
(defn g8-patch [form]
  (->> form
       (subst-forms (fn [y] (and (seq? y) (= 'inv-run-upd (first y)) (= 'run-wake (nth y 3 nil))))
                    (fn [[_ w x f hid & more]] (apply list 'g8-run-upd 'x8s w x f hid 'run-wake-rkey more)))
       (subst-forms (fn [y] (and (seq? y) (= 'inv-source-upd (first y)) (= 'source-consume (nth y 3 nil))))
                    (fn [[_ w x f hid & more]] (apply list 'g8-source-upd 'x8s w x f hid 'x8k-consume more)))
       (subst-forms (fn [y] (and (seq? y) (= 'inv-source-upd (first y)) (= 'source-close-row (nth y 3 nil))))
                    (fn [[_ w x f hid h]] (list 'g8-source-close 'x8s w x h)))
       (subst-forms (fn [y] (and (seq? y) (= 'inv-source-upd (first y)) (= 'source-detach-row (nth y 3 nil))))
                    (fn [[_ w x f hid h]] (list 'g8-source-detach 'x8s w x h)))
       (subst-forms (fn [y] (and (seq? y) (= 'inv-task-upd (first y)) (= 'task-detach-row (nth y 3 nil))))
                    (fn [[_ w x f hid h]] (list 'g8-task-detach 'x8s w x h)))
       (subst-forms (fn [y] (and (seq? y) (= 'inv-task-upd (first y)) (= 'task-cancel-result (nth y 3 nil))))
                    (fn [[_ w x f hid & more]] (apply list 'g8-task-upd 'x8s w x f hid 'tok-cancel-result more)))))
(doseq [[n _] @@#'spindel.v2.lit/source-theorems] (patch! G8 n g8-patch))

(override! G8 'inv-serve-or '[inv-fire-edge]
  '(a/theorem g8-serve-or [x8s :- (List Nat), w :- World, x :- Nat, res :- RunResult, keep :- (=> SourceRow SourceRow),
                           hk :- (forall [s :- SourceRow] (= (source-id (keep s)) (source-id s))),
                           hx :- (forall [s :- SourceRow] (= (x8k (keep s)) (x8k s)))]
     (=> (= (g8 x8s w) true) (= (g8 x8s (serve-or w x res keep)) true))
     (intro h)
     (cases hz (Nat.beq (oldest-waiter w x) 0))
     (simp only [serve-or hz]) (exact (g8-fire-edge x8s res w _ h))
     (simp only [serve-or hz]) (exact (g8-source-upd x8s w x keep hk hx h))))
(def G8 (assoc G8 :extra-args (assoc (:extra-args G8) 'inv-serve-or ['(fn [s :- SourceRow] (Eq.refl (x8k s))) 5])))

;; ---- KA k: every run row with id k is alive (the awaiting run, through the await's wiring and fills)
(a/defn ka-rest [k8a :- Nat, w :- World] Bool (tbl-all (run-ok-for k8a) (:runs w)))
(a/defn ka [k8a :- Nat, w :- World] Bool (Bool.and (inv-sample w) (ka-rest k8a w)))
(a/theorem ka-sample [k8a :- Nat, w :- World] (=> (= (ka k8a w) true) (= (inv-sample w) true))
  (intro h) (simp only [ka Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem ka-rest-of [k8a :- Nat, w :- World] (=> (= (ka k8a w) true) (= (ka-rest k8a w) true))
  (intro h) (simp only [ka Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem ka-intro [k8a :- Nat, w :- World] (=> (= (inv-sample w) true) (= (ka-rest k8a w) true) (= (ka k8a w) true))
  (intros h1 h2) (simp only [ka h1 h2 Bool.and_self]))
(a/theorem ka-parts [k8a :- Nat, w :- World]
  (=> (= (ka k8a w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (ka-sample k8a w h))))
(a/theorem ka-run-upd [k8a :- Nat, w :- World, x :- Nat, f :- (=> RunRow RunRow),
                       hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                       hk :- (forall [r :- RunRow] (= (run-alive (f r)) (run-alive r)))]
  (=> (= (ka k8a w) true) (= (ka k8a (run-upd w x f)) true))
  (intro h)
  (have r0 := (ka-rest-of k8a w h)) (simp only [ka-rest] at r0)
  (have r1 (= (ka-rest k8a (run-upd w x f)) true))
  (simp only [ka-rest run-upd set-runs])
  (apply (tbl-all-upd RunRow run-id x f (run-ok-for k8a) (run-ok-for k8a) _ _ (:runs w) r0))
  (intros q p e) (have i (= (:id (f q)) (:id q))) (exact (hf q)) (simp only [run-ok-for i (hk q)]) (simp only [run-ok-for] at p) (exact p)
  (intros q p e) (exact p)
  (exact (ka-intro k8a _ (inv-run-upd w x f hf (ka-sample k8a w h)) r1)))
(def KA (mk-bundle 'ka '[k8a :- Nat] "ka-" {'inv-run-upd ['(fn [r :- RunRow] (Eq.refl (run-alive r))) 4]}))
(swap! (:renames KA) assoc 'inv-parts 'ka-parts 'inv-run-upd 'ka-run-upd)
(doseq [o '[inv-scope-upd inv-pub-upd inv-source-upd inv-resource-upd inv-cleanup-upd inv-cleanup-del inv-cleanup-ins inv-set-pins
            inv-resource-del inv-scope-del inv-act-upd inv-task-upd inv-comp-upd inv-bump inv-edge-upd inv-drop-cred inv-drop-act
            inv-drop-edges inv-comp-del-unref inv-act-ins-fresh inv-task-ins-fresh inv-comp-ins-fresh inv-scope-ins-fresh
            inv-resource-ins-fresh inv-source-ins-fresh insert-edge-fresh-inv-sample]]
  (prim! KA o nil))
(a/theorem ka-rest-same [k8a :- Nat, w :- World, w2 :- World] (=> (= (:runs w2) (:runs w)) (= (ka-rest k8a w2) (ka-rest k8a w)))
  (intro e) (simp only [ka-rest e]))
(prim! KA 'inv-remove-edge '(Eq.trans (ka-rest-same k8a w (remove-edge w x) (runs-remove-edge w x)) R))
(prim! KA 'mark-edge-inv-sample '(Eq.trans (ka-rest-same k8a w (mark-edge w x) (runs-mark-edge w x)) R))
(prim! KA 'unmark-edge-inv-sample '(Eq.trans (ka-rest-same k8a w (unmark-edge w x) (runs-unmark-edge w x)) R))
(prim! KA 'inv-run-del '(all-sub-del RunRow (run-ok-for k8a) run-id x (:runs w) R))
(defn ka-patch [form]
  (subst-forms (fn [y] (and (seq? y) (= 'inv-run-upd (first y)) (= 'run-wake (nth y 3 nil))))
               (fn [[_ w x f hid & more]] (apply list 'ka-run-upd 'k8a w x f hid 'run-wake-alive more)) form))
(doseq [[n _] @@#'spindel.v2.lit/source-theorems] (patch! KA n ka-patch))
(lcopy! KA 'inv-await-pre)
(lcopy! KA 'inv-await-wire)
(lcopy! KA 'inv-fast-fill)

;; ---- parks: the run made parked was alive (take/arm: the slice holder; await: KA through the wiring)
(override! G8 'inv-take-park '[inv-insert-edge-checked]
  '(a/theorem g8-take-park [x8s :- (List Nat), w :- World, r :- RunRow, x :- Nat, k :- Nat]
     (=> (List.Mem r (:runs w)) (= (run-alive r) true) (= (g8 x8s w) true) (= (g8 x8s (take-park w r x k)) true))
     (intros hm hal h) (exact (g8-take-park-o x8s w r x k hm hal h))))
(override! G8 't-take-inv '[inv-take-park inv-take-now]
  '(a/theorem t-take-g8 [x8s :- (List Nat), w :- World, st :- Nat, x :- Nat, k :- Nat, fresh :- Nat]
     (=> (= (g8 x8s w) true) (= (g8 x8s (:world (t-take w st x k fresh))) true))
     (intro h)
     (cases ht (tok-run w st)) (case' [some r]) (case' [none])
     (simp only [t-take ht refuse]) (exact h)
     (have p := (tok-facts w st r ht))
     (cases hs (source-find w x)) (case' [some s]) (case' [none])
     (simp only [t-take ht hs refuse]) (exact h)
     (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (run-normal r) (takeable s))))
     (simp only [t-take ht hs hg refuse]) (exact h)
     (have hn (= (run-normal r) true)) (simp only [Bool.and_eq_true] at hg) (exact (And.left (And.right hg)))
     (cases hv (take-ready s))
     (simp only [t-take ht hs hg hv accept]) (exact (g8-take-park x8s w r x k (And.left p) (normal-alive r hn) h))
     (simp only [t-take ht hs hg hv accept]) (exact (g8-take-now x8s w r x h))))
(override! G8 'inv-arm-park '[inv-take-park inv-arm-raw]
  '(a/theorem g8-arm-park [x8s :- (List Nat), w :- World, r :- RunRow, kind :- Nat, k :- Nat]
     (=> (List.Mem r (:runs w)) (= (run-alive r) true) (= (g8 x8s w) true) (= (g8 x8s (arm-park w r kind k)) true))
     (intros hm ha h)
     (simp only [arm-park])
     (exact (g8-take-park x8s _ (run-arm (:next-id w) r) (:next-id w) k (arm-raw-mem w r kind hm) ha (g8-arm-raw x8s w r kind h)))))
(override! G8 't17-inv '[inv-arm-park]
  '(a/theorem t17-g8 [x8s :- (List Nat), w :- World, st :- Nat, kind :- Nat, k :- Nat, fresh :- Nat]
     (=> (= (g8 x8s w) true) (= (g8 x8s (:world (t17-arm w st kind k fresh))) true))
     (intro h)
     (cases ht (tok-run w st)) (case' [some r]) (case' [none])
     (simp only [t17-arm ht refuse]) (exact h)
     (have p := (tok-facts w st r ht))
     (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (run-normal r) (arm-kind-ok kind))))
     (simp only [t17-arm ht hg refuse]) (exact h)
     (have hn (= (run-normal r) true)) (simp only [Bool.and_eq_true] at hg) (exact (And.left (And.right hg)))
     (simp only [t17-arm ht hg accept]) (exact (g8-arm-park x8s w r kind k (And.left p) (normal-alive r hn) h))))
(override! G8 'inv-park-if '[]
  '(a/theorem g8-park-if [x8s :- (List Nat), w :- World, a :- Nat, rid :- Nat]
     (=> (= (tbl-all (run-ok-for rid) (:runs w)) true) (= (g8 x8s w) true) (= (g8 x8s (park-if w a rid)) true))
     (intros hk h)
     (cases ha (act-has w a))
     (simp only [park-if ha]) (exact h)
     (simp only [park-if ha]) (exact (g8-run-upd-up x8s w rid run-park-row run-park-row-id park-alive8 (fn [q :- RunRow] (Eq.refl (:of q))) hk h))))
(override! G8 'inv-await-post '[inv-park-if inv-fast-fill inv-fin-if-final nat-fold-inv]
  '(a/theorem g8-await-post [x8s :- (List Nat), a :- Nat, rid :- Nat, ds :- (List Nat), acc :- AwAcc]
     (=> (= (ka rid (:world acc)) true) (= (g8 x8s (:world acc)) true) (= (g8 x8s (await-post a rid ds acc)) true))
     (intros hk h)
     (have h2 := (g8-act-upd x8s (:world acc) a (act-set-members (mk-members (:pairs acc) 0 ds)) (act-set-members-id (mk-members (:pairs acc) 0 ds)) h))
     (have k2 := (ka-act-upd rid (:world acc) a (act-set-members (mk-members (:pairs acc) 0 ds)) (act-set-members-id (mk-members (:pairs acc) 0 ds)) hk))
     (have h3 := (nat-fold-g8 x8s (fast-fill (:pairs acc)) (g8-fast-fill x8s (:pairs acc)) (nat-distinct ds)
                   (act-upd (:world acc) a (act-set-members (mk-members (:pairs acc) 0 ds))) h2))
     (have k3 := (nat-fold-ka rid (fast-fill (:pairs acc)) (ka-fast-fill rid (:pairs acc)) (nat-distinct ds)
                   (act-upd (:world acc) a (act-set-members (mk-members (:pairs acc) 0 ds))) k2))
     (have h4 := (g8-park-if x8s _ a rid (ka-rest-of rid _ k3) h3))
     (simp only [await-post])
     (exact (nat-fold-g8 x8s fin-if-final (g8-fin-if-final x8s) (nat-distinct ds) _ h4))))
(override! G8 'inv-await-raw '[inv-await-wire inv-await-pre inv-await-post]
  '(a/theorem g8-await-raw [x8s :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
     (=> (List.Mem r (:runs w)) (= (run-alive r) true) (= (g8 x8s w) true) (= (g8 x8s (await-raw w r ds mode k mine)) true))
     (intros hm hal h)
     (have hs := (g8-sample x8s w h))
     (have k0 := (ka-intro (:id r) w hs (run-ok-of-mem w r hs hm hal)))
     (have k1 := (ka-await-wire (:id r) r (:next-id w) mode k (nat-distinct ds)
                   (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) (ka-await-pre (:id r) w r ds mode k mine k0)))
     (have h1 := (g8-await-wire x8s r (:next-id w) mode k (nat-distinct ds)
                   (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) (g8-await-pre x8s w r ds mode k mine h)))
     (exact (g8-await-post x8s (:next-id w) (:id r) ds (await-acc w r ds mode k mine) k1 h1))))
(override! G8 't6-inv '[inv-await-raw]
  '(a/theorem t6-g8 [x8s :- (List Nat), w :- World, st :- Nat, ds :- (List Nat), mode :- Nat, k :- Nat, fresh :- Nat, mine :- (List Nat)]
     (=> (= (g8 x8s w) true) (= (g8 x8s (:world (t6-await w st ds mode k fresh mine))) true))
     (intro h)
     (cases ht (tok-run w st)) (case' [some r]) (case' [none])
     (simp only [t6-await ht refuse]) (exact h)
     (have p := (tok-facts w st r ht))
     (cases hg (Bool.and (await-ok w r ds mode fresh) (:ok (await-acc w r ds mode k mine))))
     (simp only [t6-await ht hg refuse]) (exact h)
     (have hn (= (run-normal r) true)) (simp only [await-ok Bool.and_eq_true] at hg) (exact (And.left (And.right (And.left hg))))
     (simp only [t6-await ht hg accept]) (exact (g8-await-raw x8s w r ds mode k mine (And.left p) (normal-alive r hn) h))))

;; ---- detach (Q10): the task's new owner is an open scope
(override! G8 't-detach-inv '[inv-remove-if-empty]
  '(a/theorem t-detach-g8 [x8s :- (List Nat), w :- World, k :- Nat, s :- Nat]
     (=> (= (g8 x8s w) true) (= (g8 x8s (:world (t-detach w k s))) true))
     (intro h)
     (cases hf (task-find w k)) (case' [some t]) (case' [none])
     (simp only [t-detach hf refuse]) (exact h)
     (cases hg (detach-ok w t s))
     (simp only [t-detach hf hg refuse]) (exact h)
     (have hso (= (scope-open-at w s) true)) (simp only [detach-ok Bool.and_eq_true] at hg) (exact (And.right (And.right hg)))
     (simp only [t-detach hf hg accept remove-empty-at detach-move])
     (exact (g8-remove-if-empty-x x8s _ _
              (g8-scope-upd x8s _ _ (scope-set-parent s) (scope-set-parent-id s) (fn [q :- ScopeRow] (Eq.refl (s8k q)))
                (g8-task-owner x8s w k (task-set-owner s) s (task-set-owner-id s) (tok-set-owner s)
                  (open-not-closed w s (g8-sample x8s w h) hso) h))))))

;; ---- the cascades: with ga, the worklist empties (P4, casc-done-ga) and the escape list with it
(swap! (:renames G8) assoc 'inv-run-cascade 'g8-run-cascade-ga)
(override! G8 't14-inv '[]
  '(a/theorem t14-g8 [x8s :- (List Nat), w :- World, rid :- Nat, rep :- Bool]
     (=> (= (ga w) true) (= (g8 x8s w) true) (= (g8 x8s (:world (t14-cancel w rid rep))) true))
     (intros hga h)
     (cases hf (run-find w rid)) (case' [some r]) (case' [none])
     (simp only [t14-cancel hf refuse]) (exact h)
     (cases ha (run-alive r))
     (simp only [t14-cancel hf ha refuse]) (exact h)
     (simp only [t14-cancel hf ha accept]) (exact (g8-run-cascade-ga x8s w _ hga h))))
(override! G8 't-cancel-inv '[t14-inv]
  '(a/theorem t-cancel-g8 [x8s :- (List Nat), w :- World, rid :- Nat]
     (=> (= (ga w) true) (= (g8 x8s w) true) (= (g8 x8s (:world (t-cancel w rid))) true))
     (intros hga h)
     (cases hf (run-find w rid)) (case' [some r]) (case' [none])
     (simp only [t-cancel hf refuse]) (exact h)
     (cases hg (host-cancel-ok w r))
     (simp only [t-cancel hf hg refuse]) (exact h)
     (simp only [t-cancel hf hg]) (exact (t14-g8 x8s w rid false hga h))))
(override! G8 't16-inv '[]
  '(a/theorem t16-g8 [x8s :- (List Nat), w :- World, s :- Nat]
     (=> (= (ga w) true) (= (g8 x8s w) true) (= (g8 x8s (:world (t16-close-scope w s))) true))
     (intros hga h)
     (cases hs (scope-has w s))
     (simp only [t16-close-scope hs refuse]) (exact h)
     (simp only [t16-close-scope hs accept]) (exact (g8-run-cascade-ga x8s w _ hga h))))
(override! G8 't-close-scope-inv '[t16-inv]
  '(a/theorem t-close-scope-g8 [x8s :- (List Nat), w :- World, s :- Nat]
     (=> (= (ga w) true) (= (g8 x8s w) true) (= (g8 x8s (:world (t-close-scope w s))) true))
     (intros hga h)
     (cases hg (scope-explicit-at w s))
     (simp only [t-close-scope hg refuse]) (exact h)
     (simp only [t-close-scope hg]) (exact (t16-g8 x8s w s hga h))))
(override! G8 't15-full-inv '[inv-ack-raw]
  '(a/theorem t15-full-g8 [x8s :- (List Nat), w :- World, z :- Nat]
     (=> (= (ga w) true) (= (g8 x8s w) true) (= (g8 x8s (:world (t15-full w z))) true))
     (intros hga h)
     (cases hk (ack-tok-ok w z))
     (simp only [t15-full hk refuse]) (exact h)
     (cases hf (resource-find w z)) (case' [some zr]) (case' [none])
     (simp only [t15-full hk hf refuse]) (exact h)
     (simp only [t15-full hk hf accept retire-full])
     (have hu (= (tbl-all (no-debtor z) (:edges w)) true))
     (simp only [ack-tok-ok Bool.and_eq_true] at hk) (exact (And.right hk))
     (exact (g8-run-cascade-ga x8s _ _ (ga-ack-raw w z (:owner zr) hu hga) (g8-ack-raw x8s w z (:owner zr) hu h)))))
(override! G8 't-slice-exit-inv '[]
  '(a/theorem t-slice-exit-g8 [x8s :- (List Nat), w :- World, rid :- Nat]
     (=> (= (ga w) true) (= (g8 x8s w) true) (= (g8 x8s (:world (t-slice-exit w rid))) true))
     (intros hga h)
     (cases hf (run-find w rid)) (case' [some r]) (case' [none])
     (simp only [t-slice-exit hf refuse]) (exact h)
     (cases hg (exit-ready r))
     (simp only [t-slice-exit hf hg refuse]) (exact h)
     (have p := (find-facts w rid r hf))
     (have hg2 := hg)
     (simp only [exit-ready Bool.and_eq_true] at hg2)
     (have hn := (no-act-bad w r hga (And.left p) (done-not-good r (And.left hg2))))
     (rw [(And.right p)] at hn)
     (simp only [t-slice-exit hf hg accept retire-full])
     (exact (g8-run-cascade-ga x8s _ _ (ga-run-upd-free w rid run-fin-pop-end run-fin-pop-end-id hn hga)
              (g8-run-upd x8s w rid run-fin-pop-end run-fin-pop-end-id (fn [q :- RunRow] (Eq.refl (rkey q))) h)))))
(override! G8 't-release-world-inv '[inv-zero-handles inv-revoke-roots]
  '(a/theorem t-release-world-g8 [x8s :- (List Nat), w :- World]
     (=> (= (ga w) true) (= (g8 x8s w) true) (= (g8 x8s (:world (t-release-world w))) true))
     (intros hga h)
     (cases hr (:released w))
     (simp only [t-release-world hr accept release-world-raw])
     (exact (g8-run-cascade-ga x8s _ _ (ga-zero-handles _ (ga-revoke-roots w hga)) (g8-zero-handles x8s _ (g8-revoke-roots x8s w h))))
     (simp only [t-release-world hr refuse]) (exact h)))
(override! G8 'inv-complete-raw '[inv-fin-if-final inv-retire-after inv-complete-body]
  '(a/theorem g8-complete-raw [x8s :- (List Nat), w :- World, r :- RunRow, res :- RunResult]
     (=> (= (tbl-any (act-of-run (:id r)) (:acts w)) false) (= (ga w) true) (= (g8 x8s w) true) (= (g8 x8s (complete-raw w r res)) true))
     (intros hn hga h)
     (have h0 := (g8-run-kill x8s w (:id r) run-complete-row run-complete-row-id (fn [q :- RunRow] (Eq.refl (rk-down (rkey q)))) h))
     (have g2 := (ga-retire-after _ (:id r) (ga-complete-body _ r res (ga-run-upd-free w (:id r) run-complete-row run-complete-row-id hn hga))))
     (simp only [complete-raw])
     (exact (g8-fin-if-final x8s _ (:of r) (g8-run-cascade-ga x8s _ _ g2 (g8-retire-after x8s _ (:id r) (g8-complete-body x8s _ r res h0)))))))
(override! G8 't12-inv '[inv-complete-raw]
  '(a/theorem t12-g8 [x8s :- (List Nat), w :- World, st :- Nat, tag :- Nat, v :- Nat]
     (=> (= (ga w) true) (= (g8 x8s w) true) (= (g8 x8s (:world (t12-complete w st tag v))) true))
     (intros hga h)
     (cases ht (tok-run w st)) (case' [some r]) (case' [none])
     (simp only [t12-complete ht refuse]) (exact h)
     (cases hn (run-normal r))
     (simp only [t12-complete ht hn refuse]) (exact h)
     (simp only [t12-complete ht hn accept]) (exact (g8-complete-raw x8s w r _ (ga-free-of-tok w st r hga ht) hga h))))

;; ---- T11: the predecessor's cancel keeps the task keys; the new run is a computation's
(a/theorem tasks-sdel-fold [sub :- (List Nat)] (forall [w :- World] (= (:tasks (nat-fold scope-del w sub)) (:tasks w)))
  (induction sub)
  (case [nil] (intro w) (simp only [nat-fold]))
  (case [cons x t ih] (intro w) (simp only [nat-fold]) (exact (ih (scope-del w x)))))
(a/theorem t8ks-retire-with [w :- World, r :- RunRow, sub :- (List Nat)] (= (t8ks (:tasks (retire-with w r sub))) (t8ks (:tasks w)))
  (simp only [retire-with remove-if-empty])
  (cases he (subtree-empty (cleanup-del (run-del (close-local (clear-comp-run w r) sub) (:id r)) (:id r)) sub))
  (case [false]
    (simp only [he])
    (exact (Eq.trans (congrArg (fn [k :- KW8] (:tks k)) (kw8-close-local (clear-comp-run w r) sub))
                     (congrArg (fn [k :- KW8] (:tks k)) (kw8-clear-comp-run w r)))))
  (case [true]
    (simp only [he])
    (rw [(tasks-sdel-fold sub _)])
    (exact (Eq.trans (congrArg (fn [k :- KW8] (:tks k)) (kw8-close-local (clear-comp-run w r) sub))
                     (congrArg (fn [k :- KW8] (:tks k)) (kw8-clear-comp-run w r))))))
(a/theorem t8ks-close-with [w :- World, sub :- (List Nat)] (= (t8ks (:tasks (close-with w sub))) (t8ks (:tasks w)))
  (simp only [close-with remove-if-empty])
  (cases he (subtree-empty (close-local w sub) sub))
  (case [false] (simp only [he]) (exact (congrArg (fn [k :- KW8] (:tks k)) (kw8-close-local w sub))))
  (case [true]
    (simp only [he])
    (rw [(tasks-sdel-fold sub _)])
    (exact (congrArg (fn [k :- KW8] (:tks k)) (kw8-close-local w sub)))))
(a/theorem t8ks-job [w :- World, j :- Job] (= (t8ks (:tasks (job-apply w j))) (t8ks (:tasks w)))
  (cases j)
  (case [jcancel rid rep]
    (cases hf (run-find w rid))
    (case [none] (simp only [job-apply hf]))
    (case [some r]
      (cases ha (run-alive r))
      (case [false] (simp only [job-apply hf ha]))
      (case [true] (simp only [job-apply hf ha]) (exact (congrArg (fn [k :- KW8] (:tks k)) (kw8-cancel-run-local w r rep))))))
  (case [jretire rid]
    (cases hf (run-find w rid))
    (case [none] (simp only [job-apply hf]))
    (case [some r]
      (cases hr (retirable r))
      (case [false] (simp only [job-apply hf hr]))
      (case [true] (simp only [job-apply hf hr retire-local]) (exact (t8ks-retire-with w r _)))))
  (case [jclose s]
    (cases hs (scope-has w s))
    (case [false] (simp only [job-apply hs]))
    (case [true] (simp only [job-apply hs close-scope-local]) (exact (t8ks-close-with w _)))))
(a/theorem t8ks-cascade [fuel :- (List Nat)]
  (forall [w :- World, js :- (List Job)] (= (t8ks (:tasks (:world (cascade fuel w js)))) (t8ks (:tasks w))))
  (induction fuel)
  (case [nil] (intros w js) (simp only [cascade]))
  (case [cons u f ih]
    (intros w js)
    (cases js)
    (case [nil] (simp only [cascade]))
    (case [cons j t] (simp only [cascade]) (exact (Eq.trans (ih _ _) (t8ks-job w j))))))
(a/theorem t8ks-cancel-pred [w :- World, c :- CompRow] (= (t8ks (:tasks (cancel-pred w c))) (t8ks (:tasks w)))
  (cases hr (run-find w (:run c)))
  (case [none] (simp only [cancel-pred hr]))
  (case [some r]
    (cases ha (run-alive r))
    (case [false] (simp only [cancel-pred hr ha]))
    (case [true] (simp only [cancel-pred hr ha run-cascade cascade-run]) (exact (t8ks-cascade _ w _)))))
(override! G8 'inv-cancel-pred '[]
  '(a/theorem g8-cancel-pred [x8s :- (List Nat), w :- World, c :- CompRow]
     (=> (= (ga w) true) (= (g8 x8s w) true) (= (g8 x8s (cancel-pred w c)) true))
     (intros hga h)
     (cases hr (run-find w (:run c))) (case' [some r]) (case' [none])
     (simp only [cancel-pred hr]) (exact h)
     (cases ha (run-alive r))
     (simp only [cancel-pred hr ha]) (exact h)
     (simp only [cancel-pred hr ha]) (exact (g8-run-cascade-ga x8s w _ hga h))))
(a/theorem kw8-consume-entry [w :- World, e :- EdgeRow] (= (kw8 (consume-entry w e)) (kw8 w))
  (cases hf (deb-final w (:debtor e)))
  (case [true] (simp only [consume-entry hf]) (exact (kw8-remove-edge w (:id e))))
  (case [false] (cases hr (Nat.beq (:cont e) cont-restart)) (all_goals (simp only [consume-entry hf hr kw8 edge-upd set-edges]))))
(a/theorem kw8-cut-suffix [w :- World, c :- Nat, has :- Bool, cut :- Nat, cid :- Nat] (= (kw8 (cut-suffix w c has cut cid)) (kw8 w)) (rfl))
(a/theorem tclosed-kw8 [w :- World, w2 :- World, c :- Nat]
  (=> (= (kw8 w2) (kw8 w)) (= (tclosed (t8ks (:tasks w2)) (s8ks (:scopes w2)) c) (tclosed (t8ks (:tasks w)) (s8ks (:scopes w)) c)))
  (intro e)
  (have e2 (= (t8ks (:tasks w2)) (t8ks (:tasks w)))) (exact (congrArg (fn [k :- KW8] (:tks k)) e))
  (have e3 (= (s8ks (:scopes w2)) (s8ks (:scopes w)))) (exact (congrArg (fn [k :- KW8] (:sks k)) e))
  (rw [e2, e3]))
(override! G8 'inv-new-run-of '[inv-add-run-scope]
  '(a/theorem g8-new-run-of [x8s :- (List Nat), w :- World, c :- CompRow, ei :- Nat]
     (=> (= (tclosed (t8ks (:tasks w)) (s8ks (:scopes w)) (:id c)) false) (= (g8 x8s w) true) (= (g8 x8s (new-run-of w c ei)) true))
     (intros hc h)
     (simp only [new-run-of])
     (exact (g8-comp-upd x8s _ (:id c) (comp-set-run (:next-id w)) (comp-set-run-id (:next-id w))
              (comp-set-run-pending (:next-id w)) (g8-add-run-scope x8s w (:id c) (:epoch c) 0 ei hc h)))))
(override! G8 'inv-dispatch-raw '[inv-cancel-pred inv-cut-suffix inv-consume-entry inv-new-run-of]
  '(a/theorem g8-dispatch-raw [x8s :- (List Nat), w :- World, c :- CompRow]
     (=> (= (ga w) true) (= (comp-has w (:id c)) true) (= (g8 x8s w) true) (= (g8 x8s (dispatch-raw w c)) true))
     (intros hga hc h)
     (have h1 := (g8-cancel-pred x8s w c hga h))
     (have tc (= (tclosed (t8ks (:tasks (cancel-pred w c))) (s8ks (:scopes (cancel-pred w c))) (:id c)) false))
     (rw [(t8ks-cancel-pred w c)])
     (exact (comp-not-tclosed w (:id c) (s8ks (:scopes (cancel-pred w c))) (g8-sample x8s w h) hc))
     (cases he (entry-edge w (:id c))) (case' [some e]) (case' [none])
     (simp only [dispatch-raw he])
     (have tc0 := (Eq.trans (tclosed-kw8 (cancel-pred w c) (cut-suffix (cancel-pred w c) (:id c) false 0 0) (:id c)
                              (kw8-cut-suffix (cancel-pred w c) (:id c) false 0 0)) tc))
     (exact (g8-new-run-of x8s (cut-suffix (cancel-pred w c) (:id c) false 0 0) c 0 tc0
              (g8-cut-suffix x8s (cancel-pred w c) (:id c) false 0 0 h1)))
     (simp only [dispatch-raw he])
     (have tc1 := (Eq.trans (tclosed-kw8 (cancel-pred w c) (consume-entry (cut-suffix (cancel-pred w c) (:id c) true (:at e) (:id e)) e) (:id c)
                              (Eq.trans (kw8-consume-entry (cut-suffix (cancel-pred w c) (:id c) true (:at e) (:id e)) e)
                                        (kw8-cut-suffix (cancel-pred w c) (:id c) true (:at e) (:id e)))) tc))
     (exact (g8-new-run-of x8s (consume-entry (cut-suffix (cancel-pred w c) (:id c) true (:at e) (:id e)) e) c (entry-ei e) tc1
              (g8-consume-entry x8s (cut-suffix (cancel-pred w c) (:id c) true (:at e) (:id e)) e
                (g8-cut-suffix x8s (cancel-pred w c) (:id c) true (:at e) (:id e) h1))))))
(override! G8 't11-inv '[inv-dispatch-raw]
  '(a/theorem t11-g8 [x8s :- (List Nat), w :- World, cid :- Nat, fresh :- Nat]
     (=> (= (ga w) true) (= (g8 x8s w) true) (= (g8 x8s (:world (t11-dispatch w cid fresh))) true))
     (intros hga h)
     (cases hc (comp-find w cid)) (case' [some c]) (case' [none])
     (simp only [t11-dispatch hc refuse]) (exact h)
     (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (Bool.not (:idle c)) (Bool.and (needs-run w c) (eligible w c)))))
     (simp only [t11-dispatch hc hg refuse]) (exact h)
     (simp only [t11-dispatch hc hg accept]) (exact (g8-dispatch-raw x8s w c hga (comp-has-find8 w cid c hc) h))))

;; ---- raw0 / raw0g / raw: ga threaded to the cascade sites, the body-shut guard to T1/T4
(def g8-ga-calls
  '{(t-cancel-inv w _ h) (t-cancel-inv w _ hga h)
    (t-close-scope-inv w _ h) (t-close-scope-inv w _ hga h)
    (t15-full-inv w _ h) (t15-full-inv w _ hga h)
    (t-slice-exit-inv w _ h) (t-slice-exit-inv w _ hga h)
    (t-release-world-inv w h) (t-release-world-inv w hga h)
    (t11-inv w _ _ h) (t11-inv w _ _ hga h)
    (t12-inv w _ _ _ h) (t12-inv w _ _ _ hga h)
    (t1-full-inv w _ _ _ _ h) (t1-full-inv w st kind v fresh (bshut-cur w st hc) h)
    (t4-inv w _ _ _ _ h) (t4-inv w st b fresh ins (bshut-cur w st hc) h)})
(defn- g8-add-ga [form calls]
  (let [[hd nm binders stmt & proof] form
        stmt2 (apply list '=> '(= (ga w) true) (rest stmt))
        proof2 (map (fn [t] (if (= t '(intro h)) '(intros hga h) t)) proof)]
    (subst-forms #(contains? calls %) calls (apply list hd nm binders stmt2 proof2))))
(patch! G8 'raw0-inv (fn [form] (g8-add-ga (g8-patch form) g8-ga-calls)))
(patch! G8 'raw0g-inv (fn [form] (g8-add-ga (g8-patch form) '{(raw0-inv w it h) (raw0-inv w it hga h)})))
(override! G8 'raw-inv '[raw0g-inv]
  '(a/theorem raw-g8 [x8s :- (List Nat), w :- World, it :- Item]
     (=> (= (ga w) true) (= (g8 x8s w) true) (= (g8 x8s (:world (raw w it))) true))
     (intros hga h)
     (have h0 := (raw0g-g8 x8s w it hga h))
     (cases ha (:accepted (raw0g w it)))
     (simp only [raw post ha]) (exact h0)
     (simp only [raw post ha accept cancel-losers])
     (exact (g8-run-cascade-ga x8s _ _ (raw0g-ga w it hga) h0))))
(lcopy! G8 'raw-inv)

;; ===========================================================================
;; Part I. Rule R (normalization with acts-alive: demote's and the strays' cascades), the step
;; ===========================================================================

(lcopy! G8 'inv-detach)
(lcopy! G8 'inv-demote-epoch)
(lcopy! G8 'inv-demote-finish)

(a/theorem g8-demote-aa [x8s :- (List Nat), w :- World, cid :- Nat]
  (=> (= (acts-alive w) true) (= (g8 x8s w) true) (= (g8 x8s (demote w cid)) true))
  (intros ha h)
  (cases hf (comp-find w cid))
  (case [none] (simp only [demote hf]) (exact h))
  (case [some c]
    (cases hi (:idle c))
    (case [true] (simp only [demote hf hi]) (exact h))
    (case [false]
      (simp only [demote hf hi demote-edges])
      (exact (g8-demote-finish x8s _ cid _ (g8-drop-edges x8s _ (not-dep-of cid)
               (g8-demote-epoch x8s _ cid _ (g8-run-cascade-aa x8s w _ ha h))))))))
(a/theorem g8-demote-fold [x8s :- (List Nat), a :- Nat, k :- Nat, L :- (List Nat)]
  (forall [W :- World] (=> (= (bn a k W) true) (= (g8 x8s W) true) (= (g8 x8s (nat-fold demote W L)) true)))
  (induction L)
  (case [nil] (intros W hb h) (simp only [nat-fold]) (exact h))
  (case [cons x t ih]
    (intros W hb h)
    (simp only [nat-fold])
    (have p := (bn-parts a k W hb))
    (exact (ih (demote W x) (bn-demote a k W x hb) (g8-demote-aa x8s W x (And.left (And.right p)) h)))))
(a/theorem g8-norm-round-aa [x8s :- (List Nat), w :- World]
  (=> (= (acts-alive w) true) (= (g8 x8s w) true) (= (g8 x8s (norm-round w)) true))
  (intros ha h)
  (have hs := (g8-sample x8s w h))
  (have b0 := (bn-intro (alive-cnt w) (act-cnt w) w hs ha (Nat.le_refl _) (Nat.le_refl _)))
  (simp only [norm-round norm-round-lv])
  (exact (g8-detach x8s _ (g8-demote-fold x8s (alive-cnt w) (act-cnt w) _ _
           (bn-run-cascade (alive-cnt w) (act-cnt w) w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w))) b0)
           (g8-run-cascade-aa x8s w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w))) ha h)))))
(a/theorem g8-norm-loop-aa [x8s :- (List Nat), fuel :- (List Nat)]
  (forall [w :- World] (=> (= (acts-alive w) true) (= (g8 x8s w) true) (= (g8 x8s (norm-loop fuel w)) true)))
  (induction fuel)
  (case [nil] (intros w ha h) (simp only [norm-loop]) (exact h))
  (case [cons x f ih]
    (intros w ha h)
    (cases hn (normalized w))
    (case [true] (simp only [norm-loop hn]) (exact h))
    (case [false]
      (have p := (bn-round w (g8-sample x8s w h) ha))
      (simp only [norm-loop hn])
      (exact (ih (norm-round w) (And.right p) (g8-norm-round-aa x8s w ha h))))))
(a/theorem g8-normalize-aa [x8s :- (List Nat), w :- World]
  (=> (= (acts-alive w) true) (= (g8 x8s w) true) (= (g8 x8s (normalize w)) true))
  (intros ha h)
  (have hs := (g8-sample x8s w h))
  (have p := (bn-parts _ _ _ (bn-detach (alive-cnt w) (act-cnt w) w (bn-intro _ _ w hs ha (Nat.le_refl _) (Nat.le_refl _)))))
  (simp only [normalize])
  (exact (g8-norm-loop-aa x8s _ (detach w) (And.left (And.right p)) (g8-detach x8s w h))))
(a/theorem g8-rule-r-round [x8s :- (List Nat), w :- World]
  (=> (= (acts-alive w) true) (= (g8 x8s w) true) (= (filter-safe (normalize w)) true) (= (g8 x8s (rule-r-round w)) true))
  (intros ha h hf)
  (simp only [rule-r-round]) (rw [rule-r-filter-eq])
  (exact (g8-filter-world x8s (normalize w) (keep-fn (normalize w)) (g8-normalize-aa x8s w ha h) hf)))
(a/theorem g8-rr-loop [x8s :- (List Nat), fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (acts-alive w0) true) (= (g8 x8s w0) true) (= (rr-safe fuel w0) true)
                            (= (g8 x8s (rr-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 ha h hs) (simp only [rr-safe] at hs) (simp only [rr-loop]) (exact (g8-rule-r-round x8s w0 ha h hs)))
  (case [cons x f ih]
    (intros w0 ha h hs)
    (have hs0 := (rr-safe-head x f w0 hs))
    (have h1 := (g8-rule-r-round x8s w0 ha h hs0))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false]
      (rw [(rr-loop-f x f (rule-r-round w0) ho)])
      (exact (ih (rule-r-round w0) (acts-alive-round w0 (g8-sample x8s w0 h) ha) h1 (And.right (rr-safe-f x f w0 hs ho)))))
    (case [true] (rw [(rr-loop-t x f (rule-r-round w0) ho)]) (exact h1))))
(a/theorem g8-rule-r [x8s :- (List Nat), w :- World]
  (=> (= (acts-alive w) true) (= (g8 x8s w) true) (= (rule-r-safe w) true) (= (g8 x8s (rule-r w)) true))
  (intros ha h hs)
  (have hs2 (= (rr-safe (List.cons Nat 0 (all-ids w)) w) true)) (exact hs)
  (rw [rule-r-eq5])
  (exact (g8-rr-loop x8s (List.cons Nat 0 (all-ids w)) w ha h hs2)))
(a/theorem step-g8 [x8s :- (List Nat), w :- World, it :- Item]
  (=> (= (ga w) true) (= (g8 x8s w) true) (= (rule-r-safe (:world (raw w it))) true) (= (g8 x8s (:world (world-step w it))) true))
  (intros hg h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true] (have e2 := (step-accepted w it ha)) (rw [e2])
    (exact (g8-rule-r x8s (:world (raw w it)) (raw-acts-alive w it hg) (raw-g8 x8s w it hg h) hs))))
(a/theorem g8-empty [] (= (g8 (List.nil Nat) empty-world) true) (rfl))

;; ---- literal I8 from g8 []
(a/theorem any-t8ks [p :- (=> T8K Bool), t :- TaskRow, ts :- (List TaskRow)]
  (=> (List.Mem t ts) (= (p (t8k t)) true) (= (tbl-any p (t8ks ts)) true))
  (induction ts)
  (case [nil] (intros hm hp) (cases hm))
  (case [cons h tl ih]
    (intros hm hp)
    (cases hm)
    (case [head] (simp only [t8ks tbl-any hp Bool.true_or]))
    (case [tail] (rename_i hm2) (simp only [t8ks tbl-any (ih hm2 hp) Bool.or_true]))))
(a/theorem any-s8ks [p :- (=> S8K Bool), s :- ScopeRow, ss :- (List ScopeRow)]
  (=> (List.Mem s ss) (= (p (s8k s)) true) (= (tbl-any p (s8ks ss)) true))
  (induction ss)
  (case [nil] (intros hm hp) (cases hm))
  (case [cons h tl ih]
    (intros hm hp)
    (cases hm)
    (case [head] (simp only [s8ks tbl-any hp Bool.true_or]))
    (case [tail] (rename_i hm2) (simp only [s8ks tbl-any (ih hm2 hp) Bool.or_true]))))
(a/theorem sclosed-of-row [s :- ScopeRow, ss :- (List ScopeRow)]
  (=> (List.Mem s ss) (= (:open s) false) (= (sclosed (s8ks ss) (:id s)) true))
  (intros hm ho)
  (simp only [sclosed])
  (exact (any-s8ks (sclosed-k (:id s)) s ss hm (Eq.trans (congrArg (fn [b :- Bool] (Bool.and (Nat.beq (:id s) (:id s)) (Bool.not b))) ho)
                                                        (Eq.trans (congrArg (fn [b :- Bool] (Bool.and b true)) (Nat.beq_refl (:id s))) (rfl))))))
(a/theorem i8-runs-of [w :- World] (=> (= (g8 (List.nil Nat) w) true) (= (lit-i8-runs w) true))
  (intro h)
  (have r := (g8-rest-of _ w h)) (simp only [g8-rest i8k Bool.and_eq_true] at r)
  (have rr := (And.left r)) (rw [all-rkeys] at rr)
  (simp only [lit-i8-runs])
  (apply (all-of-mem ScopeRow _ (:scopes w)))
  (intros s hm)
  (cases ho (:open s))
  (case [true] (simp only [closed-scope-runs-ok ho Bool.true_or]))
  (case [false]
    (simp only [closed-scope-runs-ok ho Bool.false_or])
    (apply bnot-of-false)
    (apply (all-bnot-any RunRow (run-of-owned-task w (:id s)) (:runs w)))
    (apply (all-of-mem RunRow _ (:runs w)))
    (intros q hq)
    (simp only [bnot-of])
    (cases hx (run-of-owned-task w (:id s) q))
    (case [false] (simp only [Bool.not_false]))
    (case [true]
      (have k := (tbl-all-mem RunRow (on-rkey (r8 (List.nil Nat) (t8ks (:tasks w)) (s8ks (:scopes w)))) q (:runs w) rr hq))
      (simp only [run-of-owned-task Bool.and_eq_true] at hx)
      (cases hf (task-find w (:of q)))
      (case [none] (simp only [hf opt-test] at hx) (have hz := (And.right hx)) (cases hz))
      (case [some t]
        (simp only [hf opt-test] at hx)
        (have tm := (tbl-find-mem TaskRow task-id (:of q) t (:tasks w) hf))
        (have ti0 (= (:id t) (:of q))) (exact (tbl-find-id TaskRow task-id (:of q) t (:tasks w) hf))
        (have ti (= (Nat.beq (:id t) (:of q)) true)) (rw [ti0]) (exact (Nat.beq_refl _))
        (have eo (= (:owner t) (:id s))) (exact (Nat.eq_of_beq_eq_true (And.right hx)))
        (have sc := (sclosed-of-row s (:scopes w) hm ho))
        (rw [← eo] at sc)
        (have tc (= (tclosed (t8ks (:tasks w)) (s8ks (:scopes w)) (:of q)) true))
        (simp only [tclosed])
        (exact (any-t8ks (tclosed-k (s8ks (:scopes w)) (:of q)) t (:tasks w) tm (Eq.trans (congrArg (fn [b :- Bool] (Bool.and b (sclosed (s8ks (:scopes w)) (:owner t)))) ti) (Eq.trans (congrArg (fn [b :- Bool] (Bool.and true b)) sc) (rfl)))))
        (simp only [on-rkey r8 rkey (And.left hx) tc reach-mem Bool.not_true Bool.false_or] at k)
        (cases k)))))
(a/theorem i8-sources-of [w :- World] (=> (= (g8 (List.nil Nat) w) true) (= (lit-i8-sources w) true))
  (intro h)
  (have r := (g8-rest-of _ w h)) (simp only [g8-rest i8k Bool.and_eq_true] at r)
  (have rx := (And.right r)) (rw [all-xoks] at rx)
  (simp only [lit-i8-sources])
  (apply (all-of-mem ScopeRow _ (:scopes w)))
  (intros s hm)
  (cases ho (:open s))
  (case [true] (simp only [closed-scope-sources-ok ho Bool.true_or]))
  (case [false]
    (simp only [closed-scope-sources-ok ho Bool.false_or])
    (apply bnot-of-false)
    (apply (all-bnot-any SourceRow (open-source-of (:id s)) (:sources w)))
    (apply (all-of-mem SourceRow _ (:sources w)))
    (intros x hx)
    (simp only [bnot-of])
    (cases hy (open-source-of (:id s) x))
    (case [false] (simp only [Bool.not_false]))
    (case [true]
      (have k := (tbl-all-mem SourceRow (on-xok (x8 (s8ks (:scopes w)))) x (:sources w) rx hx))
      (simp only [open-source-of Bool.and_eq_true] at hy)
      (have eo (= (:owner x) (:id s))) (exact (Nat.eq_of_beq_eq_true (And.right hy)))
      (have sc := (sclosed-of-row s (:scopes w) hm ho))
      (rw [← eo] at sc)
      (simp only [on-xok x8 x8k (And.left hy) sc Bool.not_true Bool.false_or] at k)
      (cases k))))

;; ---- the combined bundle
(a/defn p3i [w :- World] Bool (Bool.and (p3h w) (g8 (List.nil Nat) w)))
(a/theorem p3i-parts [w :- World] (=> (= (p3i w) true) (And (= (p3h w) true) (= (g8 (List.nil Nat) w) true)))
  (intro h) (simp only [p3i Bool.and_eq_true] at h) (exact h))
(a/theorem p3i-empty [] (= (p3i empty-world) true) (rfl))
(a/theorem p3i-ga [w :- World] (=> (= (p3h w) true) (= (p3b w) true))
  (intro h)
  (have pg := (p3g-parts w (And.left (p3h-parts w h))))
  (have pf := (p3f-parts w (And.left pg)))
  (have pe := (p3e-parts w (And.left pf)))
  (have pd := (p3d-parts w (And.left pe)))
  (exact (And.left (p3c-parts w (And.left pd)))))
(a/theorem step-p3i [w :- World, it :- Item] (=> (= (p3i w) true) (= (p3i (:world (world-step w it))) true))
  (intro h)
  (have p := (p3i-parts w h))
  (have pb := (p3i-ga w (And.left p)))
  (have a1 := (step-p3h w it (And.left p)))
  (have a2 := (step-g8 (List.nil Nat) w it (And.left (p3b-parts w pb)) (And.right p) (step-rule-r-safe w it pb)))
  (simp only [p3i a1 a2 Bool.and_self]))
;; Theorem: literal I8 (a closed scope owns no alive run of a task and no open source), through every step
(a/theorem step-lit-i8-total [w :- World, it :- Item]
  (=> (= (p3i w) true) (And (= (lit-i8-runs (:world (world-step w it))) true) (= (lit-i8-sources (:world (world-step w it))) true)))
  (intro h)
  (have g := (And.right (p3i-parts _ (step-p3i w it h))))
  (exact (And.intro (i8-runs-of _ g) (i8-sources-of _ g))))
