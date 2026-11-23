(ns spindel.v2.inv.i8
  "I8 (closed scopes: a closed scope owns no run with act /= done and no open source) through the
  model's step `world-step`, kernel-checked (Init only).

  Reading (inv.clj `lit-i8-runs`, `lit-i8-sources`): no alive run of a task whose owner is a closed
  scope; no open source whose owner is a closed scope.

  Bundle i8-closed xs w = well-formed w && every alive run of a task owned by a closed scope is in the escape
  list xs && every open source's owner is not a closed scope. Stated over key lists (run keys (id, of,
  alive), task keys (id, owner), scope keys (id, open), source keys (id, owner, open)), so an edit that
  keeps them is a frame. Closedness is `tbl-any` over the key lists (monotone under the filter, no
  unique-ids argument).
    - closing a subtree (`close-local`: T16, T13's step 2, T21): every scope of the subtree closes and
      every source it owns closes in the same edit; the runs of the tasks it owns are still alive and
      join the escape list: they are exactly the cancel jobs the cascade queues next (`owned-runs`).
      Through the cascade the escape list is the list of pending cancel jobs (`i8-closed-cascade`); a cancel
      job discharges its run (the run is dead after its job, bundle d8); the worklist empties (P4,
      `cascade-done-ok` with acts-alive), so the escape list is empty when the cascade returns.
    - new tasks and sources get an owner that is not a closed scope: a computation (ids are unique),
      an open top-level scope (guard), an open detach target (guard), 0 (Rule R's detach), or the
      run's current scope (guard `cur-open`, Z#57 pass: reachable-equivalent, tripwired; the proof
      that an alive task run's current scope is open is obligation P10).

  Theorems:
    step-i8-closed              acts-parked w, i8-closed [] w, rule-r-safe raw -> i8-closed [] (world-step w it)
    chain-to-i8-closed = chain-to-i1-runs && i8-closed []   step-chain-to-i8-closed, chain-to-i8-closed-empty
    step-lit-i8-total    chain-to-i8-closed w -> lit-i8-runs (world-step w it) && lit-i8-sources (world-step w it)"
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
            [spindel.v2.inv.rank :refer :all]
            [spindel.v2.inv.rank-step :refer :all]
            [spindel.v2.progress.casc :refer :all]
            [spindel.v2.inv.acts :refer :all]
            [spindel.v2.inv :refer :all]
            [spindel.v2.pres.part :refer :all]
            [spindel.v2.inv.copier :refer :all]
            [spindel.v2.inv.idle :refer :all]
            [spindel.v2.inv.base :refer :all]
            [spindel.v2.inv.i10 :refer :all]
            [spindel.v2.inv.i11 :refer :all]
            [spindel.v2.inv.i1-scopes :refer :all]
            [spindel.v2.inv.i5 :refer :all]
            [spindel.v2.inv.i1-owners :refer :all]
            [spindel.v2.inv.i1-runs :refer :all]
            [spindel.v2.pres.frames :as frames]
            [spindel.v2.pres.exempt :as exempt]
            [spindel.v2.pres.tree :as tree]))

;; ===========================================================================
;; Part A. Keys and the bundle
;; ===========================================================================

(a/structure I8ClosedTaskKey [] (id Nat) (owner Nat))
(a/defn i8-closed-task-key [t :- TaskRow] I8ClosedTaskKey (I8ClosedTaskKey.mk (:id t) (:owner t)))
(a/defn i8-closed-task-key-id [k :- I8ClosedTaskKey] Nat (:id k))
(a/defn i8-closed-task-keys [ts :- (List TaskRow)] (List I8ClosedTaskKey)
  (match ts nil (List.nil I8ClosedTaskKey) (cons h t) (List.cons I8ClosedTaskKey (i8-closed-task-key h) (i8-closed-task-keys t))))
(a/structure I8ClosedScopeKey [] (id Nat) (open Bool))
(a/defn i8-closed-scope-key [s :- ScopeRow] I8ClosedScopeKey (I8ClosedScopeKey.mk (:id s) (:open s)))
(a/defn i8-closed-scope-key-id [k :- I8ClosedScopeKey] Nat (:id k))
(a/defn i8-closed-scope-keys [ss :- (List ScopeRow)] (List I8ClosedScopeKey)
  (match ss nil (List.nil I8ClosedScopeKey) (cons h t) (List.cons I8ClosedScopeKey (i8-closed-scope-key h) (i8-closed-scope-keys t))))
(a/structure I8ClosedSourceKey [] (id Nat) (owner Nat) (open Bool))
(a/defn i8-closed-source-key [s :- SourceRow] I8ClosedSourceKey (I8ClosedSourceKey.mk (:id s) (:owner s) (:open s)))
(a/defn i8-closed-source-key-id [k :- I8ClosedSourceKey] Nat (:id k))
(a/defn i8-closed-source-keys [ss :- (List SourceRow)] (List I8ClosedSourceKey)
  (match ss nil (List.nil I8ClosedSourceKey) (cons h t) (List.cons I8ClosedSourceKey (i8-closed-source-key h) (i8-closed-source-keys t))))
(a/structure I8ClosedView [] (rks (List RunKey)) (tks (List I8ClosedTaskKey)) (sks (List I8ClosedScopeKey)) (xks (List I8ClosedSourceKey)))
(a/defn i8-closed-view [w :- World] I8ClosedView (I8ClosedView.mk (run-keys (:runs w)) (i8-closed-task-keys (:tasks w)) (i8-closed-scope-keys (:scopes w)) (i8-closed-source-keys (:sources w))))

;; closedness: some scope row with id x is closed; some task row with id t has a closed owner
(a/defn sclosed-k [x :- Nat, k :- I8ClosedScopeKey] Bool (Bool.and (Nat.beq (:id k) x) (Bool.not (:open k))))
(a/defn sclosed [sks :- (List I8ClosedScopeKey), x :- Nat] Bool (tbl-any (sclosed-k x) sks))
(a/defn tclosed-k [sks :- (List I8ClosedScopeKey), t :- Nat, k :- I8ClosedTaskKey] Bool (Bool.and (Nat.beq (:id k) t) (sclosed sks (:owner k))))
(a/defn tclosed [tks :- (List I8ClosedTaskKey), sks :- (List I8ClosedScopeKey), t :- Nat] Bool (tbl-any (tclosed-k sks t) tks))
(a/defn i8-closed-run-ok [xs :- (List Nat), tks :- (List I8ClosedTaskKey), sks :- (List I8ClosedScopeKey), k :- RunKey] Bool
  (Bool.or (Bool.not (:alive k)) (Bool.or (reach-mem (:id k) xs) (Bool.not (tclosed tks sks (:of k))))))
(a/defn i8-closed-source-ok [sks :- (List I8ClosedScopeKey), k :- I8ClosedSourceKey] Bool (Bool.or (Bool.not (:open k)) (Bool.not (sclosed sks (:owner k)))))
(a/defn i8-closed-keys-ok [xs :- (List Nat), rks :- (List RunKey), tks :- (List I8ClosedTaskKey), sks :- (List I8ClosedScopeKey), xks :- (List I8ClosedSourceKey)] Bool
  (Bool.and (tbl-all (i8-closed-run-ok xs tks sks) rks) (tbl-all (i8-closed-source-ok sks) xks)))
(a/defn i8-closed-rest [x8s :- (List Nat), w :- World] Bool
  (i8-closed-keys-ok x8s (run-keys (:runs w)) (i8-closed-task-keys (:tasks w)) (i8-closed-scope-keys (:scopes w)) (i8-closed-source-keys (:sources w))))
(a/defn i8-closed [x8s :- (List Nat), w :- World] Bool (Bool.and (well-formed w) (i8-closed-rest x8s w)))

(a/theorem i8-closed-well-formed [x8s :- (List Nat), w :- World] (=> (= (i8-closed x8s w) true) (= (well-formed w) true))
  (intro h) (simp only [i8-closed Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem i8-closed-rest-of [x8s :- (List Nat), w :- World] (=> (= (i8-closed x8s w) true) (= (i8-closed-rest x8s w) true))
  (intro h) (simp only [i8-closed Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem i8-closed-intro [x8s :- (List Nat), w :- World] (=> (= (well-formed w) true) (= (i8-closed-rest x8s w) true) (= (i8-closed x8s w) true))
  (intros h1 h2) (simp only [i8-closed h1 h2 Bool.and_self]))
(a/theorem i8-closed-parts [x8s :- (List Nat), w :- World]
  (=> (= (i8-closed x8s w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (i8-closed-well-formed x8s w h))))
(a/theorem i8-closed-rest-frame [x8s :- (List Nat), w :- World, w2 :- World]
  (=> (= (i8-closed-view w2) (i8-closed-view w)) (= (i8-closed-rest x8s w2) (i8-closed-rest x8s w)))
  (intro e)
  (have e1 (= (run-keys (:runs w2)) (run-keys (:runs w)))) (exact (congrArg (fn [k :- I8ClosedView] (:rks k)) e))
  (have e2 (= (i8-closed-task-keys (:tasks w2)) (i8-closed-task-keys (:tasks w)))) (exact (congrArg (fn [k :- I8ClosedView] (:tks k)) e))
  (have e3 (= (i8-closed-scope-keys (:scopes w2)) (i8-closed-scope-keys (:scopes w)))) (exact (congrArg (fn [k :- I8ClosedView] (:sks k)) e))
  (have e4 (= (i8-closed-source-keys (:sources w2)) (i8-closed-source-keys (:sources w)))) (exact (congrArg (fn [k :- I8ClosedView] (:xks k)) e))
  (simp only [i8-closed-rest e1 e2 e3 e4]))
(a/theorem i8-closed-of-view [x8s :- (List Nat), w :- World, w2 :- World]
  (=> (= (well-formed w2) true) (= (i8-closed-view w2) (i8-closed-view w)) (= (i8-closed x8s w) true) (= (i8-closed x8s w2) true))
  (intros hs e h) (exact (i8-closed-intro x8s w2 hs (Eq.trans (i8-closed-rest-frame x8s w w2 e) (i8-closed-rest-of x8s w h)))))

;; tripwire for the transition guard `cur-closed` (engine.clj): an alive normal task run's current scope is open
;; (obligation P10; checked on the random drivers and the oracle samples, i8_test)
(a/defn run-cur-ok [w :- World, r :- RunRow] Bool
  (Bool.or (Bool.not (Bool.and (run-alive r) (Nat.beq (:mode r) mode-normal))) (Bool.not (run-cur-closed w r))))
(a/defn cur-open-ok [w :- World] Bool (tbl-all (run-cur-ok w) (:runs w)))

;; ===========================================================================
;; Part B. Key lists under the table edits; closedness is monotone under sublists
;; ===========================================================================

(a/theorem toks-upd [x :- Nat, f :- (=> TaskRow TaskRow), hk :- (forall [t :- TaskRow] (= (i8-closed-task-key (f t)) (i8-closed-task-key t))), ts :- (List TaskRow)]
  (= (i8-closed-task-keys (tbl-upd task-id x f ts)) (i8-closed-task-keys ts))
  (induction ts)
  (case [nil] (simp only [tbl-upd i8-closed-task-keys]))
  (case [cons h t ih] (cases hx (Nat.beq (task-id h) x)) (all_goals (simp only [tbl-upd hx i8-closed-task-keys ih (hk h)]))))
(a/theorem soks-upd [x :- Nat, f :- (=> ScopeRow ScopeRow), hk :- (forall [s :- ScopeRow] (= (i8-closed-scope-key (f s)) (i8-closed-scope-key s))), ss :- (List ScopeRow)]
  (= (i8-closed-scope-keys (tbl-upd scope-id x f ss)) (i8-closed-scope-keys ss))
  (induction ss)
  (case [nil] (simp only [tbl-upd i8-closed-scope-keys]))
  (case [cons h t ih] (cases hx (Nat.beq (scope-id h) x)) (all_goals (simp only [tbl-upd hx i8-closed-scope-keys ih (hk h)]))))
(a/theorem xoks-upd [x :- Nat, f :- (=> SourceRow SourceRow), hk :- (forall [s :- SourceRow] (= (i8-closed-source-key (f s)) (i8-closed-source-key s))), ss :- (List SourceRow)]
  (= (i8-closed-source-keys (tbl-upd source-id x f ss)) (i8-closed-source-keys ss))
  (induction ss)
  (case [nil] (simp only [tbl-upd i8-closed-source-keys]))
  (case [cons h t ih] (cases hx (Nat.beq (source-id h) x)) (all_goals (simp only [tbl-upd hx i8-closed-source-keys ih (hk h)]))))

(a/theorem toks-upd-g [x :- Nat, f :- (=> TaskRow TaskRow), g :- (=> I8ClosedTaskKey I8ClosedTaskKey),
                       hc :- (forall [t :- TaskRow] (= (i8-closed-task-key (f t)) (g (i8-closed-task-key t)))), ts :- (List TaskRow)]
  (= (i8-closed-task-keys (tbl-upd task-id x f ts)) (tbl-upd i8-closed-task-key-id x g (i8-closed-task-keys ts)))
  (induction ts)
  (case [nil] (simp only [tbl-upd i8-closed-task-keys]))
  (case [cons h t ih]
    (cases hx (Nat.beq (task-id h) x))
    (case [false] (have hx2 (= (Nat.beq (i8-closed-task-key-id (i8-closed-task-key h)) x) false)) (exact hx) (simp only [tbl-upd hx i8-closed-task-keys hx2 ih]))
    (case [true] (have hx2 (= (Nat.beq (i8-closed-task-key-id (i8-closed-task-key h)) x) true)) (exact hx) (simp only [tbl-upd hx i8-closed-task-keys hx2 ih (hc h)]))))
(a/theorem soks-upd-g [x :- Nat, f :- (=> ScopeRow ScopeRow), g :- (=> I8ClosedScopeKey I8ClosedScopeKey),
                       hc :- (forall [s :- ScopeRow] (= (i8-closed-scope-key (f s)) (g (i8-closed-scope-key s)))), ss :- (List ScopeRow)]
  (= (i8-closed-scope-keys (tbl-upd scope-id x f ss)) (tbl-upd i8-closed-scope-key-id x g (i8-closed-scope-keys ss)))
  (induction ss)
  (case [nil] (simp only [tbl-upd i8-closed-scope-keys]))
  (case [cons h t ih]
    (cases hx (Nat.beq (scope-id h) x))
    (case [false] (have hx2 (= (Nat.beq (i8-closed-scope-key-id (i8-closed-scope-key h)) x) false)) (exact hx) (simp only [tbl-upd hx i8-closed-scope-keys hx2 ih]))
    (case [true] (have hx2 (= (Nat.beq (i8-closed-scope-key-id (i8-closed-scope-key h)) x) true)) (exact hx) (simp only [tbl-upd hx i8-closed-scope-keys hx2 ih (hc h)]))))
(a/theorem xoks-upd-g [x :- Nat, f :- (=> SourceRow SourceRow), g :- (=> I8ClosedSourceKey I8ClosedSourceKey),
                       hc :- (forall [s :- SourceRow] (= (i8-closed-source-key (f s)) (g (i8-closed-source-key s)))), ss :- (List SourceRow)]
  (= (i8-closed-source-keys (tbl-upd source-id x f ss)) (tbl-upd i8-closed-source-key-id x g (i8-closed-source-keys ss)))
  (induction ss)
  (case [nil] (simp only [tbl-upd i8-closed-source-keys]))
  (case [cons h t ih]
    (cases hx (Nat.beq (source-id h) x))
    (case [false] (have hx2 (= (Nat.beq (i8-closed-source-key-id (i8-closed-source-key h)) x) false)) (exact hx) (simp only [tbl-upd hx i8-closed-source-keys hx2 ih]))
    (case [true] (have hx2 (= (Nat.beq (i8-closed-source-key-id (i8-closed-source-key h)) x) true)) (exact hx) (simp only [tbl-upd hx i8-closed-source-keys hx2 ih (hc h)]))))

(a/theorem toks-del [x :- Nat, ts :- (List TaskRow)] (= (i8-closed-task-keys (tbl-del task-id x ts)) (tbl-del i8-closed-task-key-id x (i8-closed-task-keys ts)))
  (induction ts)
  (case [nil] (simp only [tbl-del i8-closed-task-keys]))
  (case [cons h t ih]
    (have e (= (Nat.beq (i8-closed-task-key-id (i8-closed-task-key h)) x) (Nat.beq (task-id h) x))) (rfl)
    (cases hx (Nat.beq (task-id h) x)) (all_goals (simp only [tbl-del hx i8-closed-task-keys e ih]))))
(a/theorem soks-del [x :- Nat, ss :- (List ScopeRow)] (= (i8-closed-scope-keys (tbl-del scope-id x ss)) (tbl-del i8-closed-scope-key-id x (i8-closed-scope-keys ss)))
  (induction ss)
  (case [nil] (simp only [tbl-del i8-closed-scope-keys]))
  (case [cons h t ih]
    (have e (= (Nat.beq (i8-closed-scope-key-id (i8-closed-scope-key h)) x) (Nat.beq (scope-id h) x))) (rfl)
    (cases hx (Nat.beq (scope-id h) x)) (all_goals (simp only [tbl-del hx i8-closed-scope-keys e ih]))))
(a/theorem xoks-del [x :- Nat, ss :- (List SourceRow)] (= (i8-closed-source-keys (tbl-del source-id x ss)) (tbl-del i8-closed-source-key-id x (i8-closed-source-keys ss)))
  (induction ss)
  (case [nil] (simp only [tbl-del i8-closed-source-keys]))
  (case [cons h t ih]
    (have e (= (Nat.beq (i8-closed-source-key-id (i8-closed-source-key h)) x) (Nat.beq (source-id h) x))) (rfl)
    (cases hx (Nat.beq (source-id h) x)) (all_goals (simp only [tbl-del hx i8-closed-source-keys e ih]))))
(a/theorem toks-keep [K :- (=> Nat Bool), ts :- (List TaskRow)] (= (i8-closed-task-keys (tbl-keep K task-id ts)) (tbl-keep K i8-closed-task-key-id (i8-closed-task-keys ts)))
  (induction ts)
  (case [nil] (simp only [tbl-keep i8-closed-task-keys]))
  (case [cons h t ih]
    (have e (= (K (i8-closed-task-key-id (i8-closed-task-key h))) (K (task-id h)))) (rfl)
    (cases hx (K (task-id h))) (all_goals (simp only [tbl-keep hx i8-closed-task-keys e ih]))))
(a/theorem soks-keep [K :- (=> Nat Bool), ss :- (List ScopeRow)] (= (i8-closed-scope-keys (tbl-keep K scope-id ss)) (tbl-keep K i8-closed-scope-key-id (i8-closed-scope-keys ss)))
  (induction ss)
  (case [nil] (simp only [tbl-keep i8-closed-scope-keys]))
  (case [cons h t ih]
    (have e (= (K (i8-closed-scope-key-id (i8-closed-scope-key h))) (K (scope-id h)))) (rfl)
    (cases hx (K (scope-id h))) (all_goals (simp only [tbl-keep hx i8-closed-scope-keys e ih]))))
(a/theorem xoks-keep [K :- (=> Nat Bool), ss :- (List SourceRow)] (= (i8-closed-source-keys (tbl-keep K source-id ss)) (tbl-keep K i8-closed-source-key-id (i8-closed-source-keys ss)))
  (induction ss)
  (case [nil] (simp only [tbl-keep i8-closed-source-keys]))
  (case [cons h t ih]
    (have e (= (K (i8-closed-source-key-id (i8-closed-source-key h))) (K (source-id h)))) (rfl)
    (cases hx (K (source-id h))) (all_goals (simp only [tbl-keep hx i8-closed-source-keys e ih]))))

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

;; ---- i8-closed-run-ok/i8-closed-source-ok under smaller closedness and a larger escape list
(a/theorem i8-closed-run-ok-mono [xs :- (List Nat), ys :- (List Nat), tks :- (List I8ClosedTaskKey), sks :- (List I8ClosedScopeKey), tks2 :- (List I8ClosedTaskKey), sks2 :- (List I8ClosedScopeKey),
                    ht :- (forall [t :- Nat] (=> (= (tclosed tks2 sks2 t) true) (= (tclosed tks sks t) true))),
                    hx :- (forall [x :- Nat] (=> (= (reach-mem x xs) true) (= (reach-mem x ys) true))), k :- RunKey]
  (=> (= (i8-closed-run-ok xs tks sks k) true) (= (i8-closed-run-ok ys tks2 sks2 k) true))
  (intro h)
  (simp only [i8-closed-run-ok Bool.or_eq_true] at h)
  (simp only [i8-closed-run-ok Bool.or_eq_true])
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
(a/theorem i8-closed-source-ok-mono [sks :- (List I8ClosedScopeKey), sks2 :- (List I8ClosedScopeKey),
                    hs :- (forall [x :- Nat] (=> (= (sclosed sks2 x) true) (= (sclosed sks x) true))), k :- I8ClosedSourceKey]
  (=> (= (i8-closed-source-ok sks k) true) (= (i8-closed-source-ok sks2 k) true))
  (intro h)
  (simp only [i8-closed-source-ok Bool.or_eq_true] at h)
  (simp only [i8-closed-source-ok Bool.or_eq_true])
  (cases h)
  (case [inl a] (exact (Or.inl a)))
  (case [inr d]
    (apply Or.inr)
    (cases hc (sclosed sks2 (:owner k)))
    (case [false] (simp only [hc Bool.not_false]))
    (case [true] (have z := (hs _ hc)) (simp only [z Bool.not_true] at d) (cases d))))
;; tclosed is monotone in both lists
(a/theorem tclosed-k-mono [sks :- (List I8ClosedScopeKey), sks2 :- (List I8ClosedScopeKey),
                           hs :- (forall [x :- Nat] (=> (= (sclosed sks2 x) true) (= (sclosed sks x) true))), t :- Nat, k :- I8ClosedTaskKey]
  (=> (= (tclosed-k sks2 t k) true) (= (tclosed-k sks t k) true))
  (intro h) (simp only [tclosed-k Bool.and_eq_true] at h) (simp only [tclosed-k Bool.and_eq_true])
  (exact (And.intro (And.left h) (hs _ (And.right h)))))
(a/theorem tclosed-mono [tks :- (List I8ClosedTaskKey), sks :- (List I8ClosedScopeKey), tks2 :- (List I8ClosedTaskKey), sks2 :- (List I8ClosedScopeKey),
                         hts :- (forall [p :- (=> I8ClosedTaskKey Bool)] (=> (= (tbl-any p tks2) true) (= (tbl-any p tks) true))),
                         hs :- (forall [x :- Nat] (=> (= (sclosed sks2 x) true) (= (sclosed sks x) true))), t :- Nat]
  (=> (= (tclosed tks2 sks2 t) true) (= (tclosed tks sks t) true))
  (intro h)
  (simp only [tclosed] at h)
  (have a1 (= (tbl-any (tclosed-k sks t) tks2) true))
  (exact (tbl-any-mono I8ClosedTaskKey (tclosed-k sks2 t) (tclosed-k sks t) (tclosed-k-mono sks sks2 hs t) tks2 h))
  (simp only [tclosed]) (exact (hts _ a1)))

;; ===========================================================================
;; Part C. The primitive edits
;; ===========================================================================

;; ---- frames: the keys stay
(a/theorem i8-closed-run-upd [x8s :- (List Nat), w :- World, x :- Nat, f :- (=> RunRow RunRow),
                       hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                       hk :- (forall [r :- RunRow] (= (run-key (f r)) (run-key r)))]
  (=> (= (i8-closed x8s w) true) (= (i8-closed x8s (run-upd w x f)) true))
  (intro h)
  (have e (= (i8-closed-view (run-upd w x f)) (i8-closed-view w))) (simp only [i8-closed-view run-upd set-runs (run-keys-upd x f hk (:runs w))])
  (exact (i8-closed-of-view x8s w _ (well-formed-run-upd w x f hf (i8-closed-well-formed x8s w h)) e h)))
(a/theorem i8-closed-task-upd [x8s :- (List Nat), w :- World, x :- Nat, f :- (=> TaskRow TaskRow),
                        hf :- (forall [t :- TaskRow] (= (task-id (f t)) (task-id t))),
                        hk :- (forall [t :- TaskRow] (= (i8-closed-task-key (f t)) (i8-closed-task-key t)))]
  (=> (= (i8-closed x8s w) true) (= (i8-closed x8s (task-upd w x f)) true))
  (intro h)
  (have e (= (i8-closed-view (task-upd w x f)) (i8-closed-view w))) (simp only [i8-closed-view task-upd set-tasks (toks-upd x f hk (:tasks w))])
  (exact (i8-closed-of-view x8s w _ (well-formed-task-upd w x f hf (i8-closed-well-formed x8s w h)) e h)))
(a/theorem i8-closed-scope-upd [x8s :- (List Nat), w :- World, x :- Nat, f :- (=> ScopeRow ScopeRow),
                         hf :- (forall [s :- ScopeRow] (= (scope-id (f s)) (scope-id s))),
                         hk :- (forall [s :- ScopeRow] (= (i8-closed-scope-key (f s)) (i8-closed-scope-key s)))]
  (=> (= (i8-closed x8s w) true) (= (i8-closed x8s (scope-upd w x f)) true))
  (intro h)
  (have e (= (i8-closed-view (scope-upd w x f)) (i8-closed-view w))) (simp only [i8-closed-view scope-upd set-scopes (soks-upd x f hk (:scopes w))])
  (exact (i8-closed-of-view x8s w _ (well-formed-scope-upd w x f hf (i8-closed-well-formed x8s w h)) e h)))
(a/theorem i8-closed-source-upd [x8s :- (List Nat), w :- World, x :- Nat, f :- (=> SourceRow SourceRow),
                          hf :- (forall [s :- SourceRow] (= (source-id (f s)) (source-id s))),
                          hk :- (forall [s :- SourceRow] (= (i8-closed-source-key (f s)) (i8-closed-source-key s)))]
  (=> (= (i8-closed x8s w) true) (= (i8-closed x8s (source-upd w x f)) true))
  (intro h)
  (have e (= (i8-closed-view (source-upd w x f)) (i8-closed-view w))) (simp only [i8-closed-view source-upd set-sources (xoks-upd x f hk (:sources w))])
  (exact (i8-closed-of-view x8s w _ (well-formed-source-upd w x f hf (i8-closed-well-formed x8s w h)) e h)))

;; ---- a run made done, a source closed: the predicate only gets weaker demands
(a/theorem i8-closed-run-ok-down [xs :- (List Nat), tks :- (List I8ClosedTaskKey), sks :- (List I8ClosedScopeKey), k :- RunKey] (= (i8-closed-run-ok xs tks sks (run-key-down k)) true)
  (simp only [i8-closed-run-ok run-key-down Bool.not_false Bool.true_or]))
(a/defn xk-shut [k :- I8ClosedSourceKey] I8ClosedSourceKey (I8ClosedSourceKey.mk (:id k) (:owner k) false))
(a/theorem i8-closed-source-ok-shut [sks :- (List I8ClosedScopeKey), k :- I8ClosedSourceKey] (= (i8-closed-source-ok sks (xk-shut k)) true)
  (simp only [i8-closed-source-ok xk-shut Bool.not_false Bool.true_or]))
(a/defn xk-orphan [k :- I8ClosedSourceKey] I8ClosedSourceKey (I8ClosedSourceKey.mk (:id k) 0 false))
(a/theorem i8-closed-source-ok-orphan [sks :- (List I8ClosedScopeKey), k :- I8ClosedSourceKey] (= (i8-closed-source-ok sks (xk-orphan k)) true)
  (simp only [i8-closed-source-ok xk-orphan Bool.not_false Bool.true_or]))

(a/theorem i8-closed-run-kill [x8s :- (List Nat), w :- World, x :- Nat, f :- (=> RunRow RunRow),
                        hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                        hk :- (forall [r :- RunRow] (= (run-key (f r)) (run-key-down (run-key r))))]
  (=> (= (i8-closed x8s w) true) (= (i8-closed x8s (run-upd w x f)) true))
  (intro h)
  (have r := (i8-closed-rest-of x8s w h)) (simp only [i8-closed-rest i8-closed-keys-ok Bool.and_eq_true] at r)
  (have e := (run-keys-upd-g x f run-key-down hk (:runs w)))
  (have a1 (= (tbl-all (i8-closed-run-ok x8s (i8-closed-task-keys (:tasks w)) (i8-closed-scope-keys (:scopes w))) (tbl-upd run-key-id x run-key-down (run-keys (:runs w)))) true))
  (exact (tbl-all-upd RunKey run-key-id x run-key-down (i8-closed-run-ok x8s (i8-closed-task-keys (:tasks w)) (i8-closed-scope-keys (:scopes w))) (i8-closed-run-ok x8s (i8-closed-task-keys (:tasks w)) (i8-closed-scope-keys (:scopes w)))
           (fn [k :- RunKey, p :- (= (i8-closed-run-ok x8s (i8-closed-task-keys (:tasks w)) (i8-closed-scope-keys (:scopes w)) k) true), q :- (= (Nat.beq (run-key-id k) x) true)]
             (i8-closed-run-ok-down x8s (i8-closed-task-keys (:tasks w)) (i8-closed-scope-keys (:scopes w)) k))
           (fn [k :- RunKey, p :- (= (i8-closed-run-ok x8s (i8-closed-task-keys (:tasks w)) (i8-closed-scope-keys (:scopes w)) k) true), q :- (= (Nat.beq (run-key-id k) x) false)] p)
           (run-keys (:runs w)) (And.left r)))
  (have hr (= (i8-closed-rest x8s (run-upd w x f)) true))
  (simp only [i8-closed-rest i8-closed-keys-ok run-upd set-runs e a1 (And.right r) Bool.and_self])
  (exact (i8-closed-intro x8s _ (well-formed-run-upd w x f hf (i8-closed-well-formed x8s w h)) hr)))

(a/theorem i8-closed-source-shut [x8s :- (List Nat), w :- World, x :- Nat, f :- (=> SourceRow SourceRow), g :- (=> I8ClosedSourceKey I8ClosedSourceKey),
                           hf :- (forall [s :- SourceRow] (= (source-id (f s)) (source-id s))),
                           hk :- (forall [s :- SourceRow] (= (i8-closed-source-key (f s)) (g (i8-closed-source-key s)))),
                           hg :- (forall [sks :- (List I8ClosedScopeKey), k :- I8ClosedSourceKey] (= (i8-closed-source-ok sks (g k)) true))]
  (=> (= (i8-closed x8s w) true) (= (i8-closed x8s (source-upd w x f)) true))
  (intro h)
  (have r := (i8-closed-rest-of x8s w h)) (simp only [i8-closed-rest i8-closed-keys-ok Bool.and_eq_true] at r)
  (have e := (xoks-upd-g x f g hk (:sources w)))
  (have a1 (= (tbl-all (i8-closed-source-ok (i8-closed-scope-keys (:scopes w))) (tbl-upd i8-closed-source-key-id x g (i8-closed-source-keys (:sources w)))) true))
  (exact (tbl-all-upd I8ClosedSourceKey i8-closed-source-key-id x g (i8-closed-source-ok (i8-closed-scope-keys (:scopes w))) (i8-closed-source-ok (i8-closed-scope-keys (:scopes w)))
           (fn [k :- I8ClosedSourceKey, p :- (= (i8-closed-source-ok (i8-closed-scope-keys (:scopes w)) k) true), q :- (= (Nat.beq (i8-closed-source-key-id k) x) true)] (hg (i8-closed-scope-keys (:scopes w)) k))
           (fn [k :- I8ClosedSourceKey, p :- (= (i8-closed-source-ok (i8-closed-scope-keys (:scopes w)) k) true), q :- (= (Nat.beq (i8-closed-source-key-id k) x) false)] p)
           (i8-closed-source-keys (:sources w)) (And.right r)))
  (have hr (= (i8-closed-rest x8s (source-upd w x f)) true))
  (simp only [i8-closed-rest i8-closed-keys-ok source-upd set-sources e a1 (And.left r) Bool.and_self])
  (exact (i8-closed-intro x8s _ (well-formed-source-upd w x f hf (i8-closed-well-formed x8s w h)) hr)))
(a/theorem xok-close [s :- SourceRow] (= (i8-closed-source-key (source-close-row s)) (xk-shut (i8-closed-source-key s))) (rfl))
(a/theorem xok-detach [s :- SourceRow] (= (i8-closed-source-key (source-detach-row s)) (xk-orphan (i8-closed-source-key s))) (rfl))
(a/theorem i8-closed-source-close [x8s :- (List Nat), w :- World, x :- Nat]
  (=> (= (i8-closed x8s w) true) (= (i8-closed x8s (source-upd w x source-close-row)) true))
  (intro h) (exact (i8-closed-source-shut x8s w x source-close-row xk-shut source-close-row-id xok-close i8-closed-source-ok-shut h)))
(a/theorem i8-closed-source-detach [x8s :- (List Nat), w :- World, x :- Nat]
  (=> (= (i8-closed x8s w) true) (= (i8-closed x8s (source-upd w x source-detach-row)) true))
  (intro h) (exact (i8-closed-source-shut x8s w x source-detach-row xk-orphan source-detach-row-id xok-detach i8-closed-source-ok-orphan h)))

;; ---- deletions and the filter: closedness only shrinks
(a/theorem any8-sub-i8-closed-run-ok [xs :- (List Nat), tks :- (List I8ClosedTaskKey), sks :- (List I8ClosedScopeKey), tks2 :- (List I8ClosedTaskKey), sks2 :- (List I8ClosedScopeKey), rks :- (List RunKey),
                        hts :- (forall [p :- (=> I8ClosedTaskKey Bool)] (=> (= (tbl-any p tks2) true) (= (tbl-any p tks) true))),
                        hss :- (forall [p :- (=> I8ClosedScopeKey Bool)] (=> (= (tbl-any p sks2) true) (= (tbl-any p sks) true)))]
  (=> (= (tbl-all (i8-closed-run-ok xs tks sks) rks) true) (= (tbl-all (i8-closed-run-ok xs tks2 sks2) rks) true))
  (intro h)
  (have hs (forall [x :- Nat] (=> (= (sclosed sks2 x) true) (= (sclosed sks x) true))))
  (intros x q) (simp only [sclosed] at q) (simp only [sclosed]) (exact (hss _ q))
  (exact (tbl-all-mono RunKey (i8-closed-run-ok xs tks sks) (i8-closed-run-ok xs tks2 sks2)
           (i8-closed-run-ok-mono xs xs tks sks tks2 sks2 (tclosed-mono tks sks tks2 sks2 hts hs) (fn [x :- Nat, q :- (= (reach-mem x xs) true)] q))
           rks h)))
(a/theorem any8-sub-i8-closed-source-ok [sks :- (List I8ClosedScopeKey), sks2 :- (List I8ClosedScopeKey), xks :- (List I8ClosedSourceKey),
                        hss :- (forall [p :- (=> I8ClosedScopeKey Bool)] (=> (= (tbl-any p sks2) true) (= (tbl-any p sks) true)))]
  (=> (= (tbl-all (i8-closed-source-ok sks) xks) true) (= (tbl-all (i8-closed-source-ok sks2) xks) true))
  (intro h)
  (have hs (forall [x :- Nat] (=> (= (sclosed sks2 x) true) (= (sclosed sks x) true))))
  (intros x q) (simp only [sclosed] at q) (simp only [sclosed]) (exact (hss _ q))
  (exact (tbl-all-mono I8ClosedSourceKey (i8-closed-source-ok sks) (i8-closed-source-ok sks2) (i8-closed-source-ok-mono sks sks2 hs) xks h)))
(a/theorem any8-refl [A :- Type, xs :- (List A)] (forall [p :- (=> A Bool)] (=> (= (tbl-any p xs) true) (= (tbl-any p xs) true)))
  (intros p h) (exact h))

(a/theorem i8-closed-rest-run-del [x8s :- (List Nat), w :- World, x :- Nat] (=> (= (i8-closed-rest x8s w) true) (= (i8-closed-rest x8s (run-del w x)) true))
  (intro h) (simp only [i8-closed-rest i8-closed-keys-ok Bool.and_eq_true] at h)
  (have a1 (= (tbl-all (i8-closed-run-ok x8s (i8-closed-task-keys (:tasks w)) (i8-closed-scope-keys (:scopes w))) (tbl-del run-key-id x (run-keys (:runs w)))) true))
  (exact (tbl-all-del RunKey run-key-id x _ _ (fn [k :- RunKey, p :- (= (i8-closed-run-ok x8s (i8-closed-task-keys (:tasks w)) (i8-closed-scope-keys (:scopes w)) k) true), q :- (= (Nat.beq (run-key-id k) x) false)] p) _ (And.left h)))
  (simp only [i8-closed-rest i8-closed-keys-ok run-del set-runs run-keys-del a1 (And.right h) Bool.and_self]))
(a/theorem i8-closed-rest-scope-del [x8s :- (List Nat), w :- World, x :- Nat] (=> (= (i8-closed-rest x8s w) true) (= (i8-closed-rest x8s (scope-del w x)) true))
  (intro h) (simp only [i8-closed-rest i8-closed-keys-ok Bool.and_eq_true] at h)
  (have hss (forall [p :- (=> I8ClosedScopeKey Bool)] (=> (= (tbl-any p (tbl-del i8-closed-scope-key-id x (i8-closed-scope-keys (:scopes w)))) true) (= (tbl-any p (i8-closed-scope-keys (:scopes w))) true))))
  (intros p q) (exact (any8-del I8ClosedScopeKey i8-closed-scope-key-id x p _ q))
  (have a1 := (any8-sub-i8-closed-run-ok x8s (i8-closed-task-keys (:tasks w)) (i8-closed-scope-keys (:scopes w)) (i8-closed-task-keys (:tasks w)) _ (run-keys (:runs w)) (any8-refl I8ClosedTaskKey _) hss (And.left h)))
  (have a2 := (any8-sub-i8-closed-source-ok (i8-closed-scope-keys (:scopes w)) _ (i8-closed-source-keys (:sources w)) hss (And.right h)))
  (simp only [i8-closed-rest i8-closed-keys-ok scope-del set-scopes soks-del a1 a2 Bool.and_self]))
(a/theorem i8-closed-rest-filter [x8s :- (List Nat), w :- World, K :- (=> Nat Bool)] (=> (= (i8-closed-rest x8s w) true) (= (i8-closed-rest x8s (filter-world K w)) true))
  (intro h) (simp only [i8-closed-rest i8-closed-keys-ok Bool.and_eq_true] at h)
  (have hss (forall [p :- (=> I8ClosedScopeKey Bool)] (=> (= (tbl-any p (tbl-keep K i8-closed-scope-key-id (i8-closed-scope-keys (:scopes w)))) true) (= (tbl-any p (i8-closed-scope-keys (:scopes w))) true))))
  (intros p q) (exact (any8-keep I8ClosedScopeKey K i8-closed-scope-key-id p _ q))
  (have hts (forall [p :- (=> I8ClosedTaskKey Bool)] (=> (= (tbl-any p (tbl-keep K i8-closed-task-key-id (i8-closed-task-keys (:tasks w)))) true) (= (tbl-any p (i8-closed-task-keys (:tasks w))) true))))
  (intros p q) (exact (any8-keep I8ClosedTaskKey K i8-closed-task-key-id p _ q))
  (have a1 := (any8-sub-i8-closed-run-ok x8s (i8-closed-task-keys (:tasks w)) (i8-closed-scope-keys (:scopes w)) _ _ (run-keys (:runs w)) hts hss (And.left h)))
  (have a1k (= (tbl-all (i8-closed-run-ok x8s (tbl-keep K i8-closed-task-key-id (i8-closed-task-keys (:tasks w))) (tbl-keep K i8-closed-scope-key-id (i8-closed-scope-keys (:scopes w)))) (tbl-keep K run-key-id (run-keys (:runs w)))) true))
  (exact (tbl-all-keep-same RunKey K run-key-id _ _ a1))
  (have a2 := (any8-sub-i8-closed-source-ok (i8-closed-scope-keys (:scopes w)) _ (i8-closed-source-keys (:sources w)) hss (And.right h)))
  (have a2k (= (tbl-all (i8-closed-source-ok (tbl-keep K i8-closed-scope-key-id (i8-closed-scope-keys (:scopes w)))) (tbl-keep K i8-closed-source-key-id (i8-closed-source-keys (:sources w)))) true))
  (exact (tbl-all-keep-same I8ClosedSourceKey K i8-closed-source-key-id _ _ a2))
  (simp only [i8-closed-rest i8-closed-keys-ok filter-world run-keys-keep toks-keep soks-keep xoks-keep a1k a2k Bool.and_self]))
(a/theorem i8-closed-filter-world [x8s :- (List Nat), w :- World, K :- (=> Nat Bool)]
  (=> (= (i8-closed x8s w) true) (= (filter-safe-for K w) true) (= (i8-closed x8s (filter-world K w)) true))
  (intros h hf)
  (exact (i8-closed-intro x8s _ (well-formed-filter-world w K (i8-closed-well-formed x8s w h) hf) (i8-closed-rest-filter x8s w K (i8-closed-rest-of x8s w h)))))

;; ---- the allocator and insertions
(a/theorem i8-closed-run-ok-all-mono [xs :- (List Nat), tks :- (List I8ClosedTaskKey), sks :- (List I8ClosedScopeKey), tks2 :- (List I8ClosedTaskKey), sks2 :- (List I8ClosedScopeKey),
                        ht :- (forall [t :- Nat] (=> (= (tclosed tks2 sks2 t) true) (= (tclosed tks sks t) true))), rks :- (List RunKey)]
  (=> (= (tbl-all (i8-closed-run-ok xs tks sks) rks) true) (= (tbl-all (i8-closed-run-ok xs tks2 sks2) rks) true))
  (intro h)
  (exact (tbl-all-mono RunKey (i8-closed-run-ok xs tks sks) (i8-closed-run-ok xs tks2 sks2)
           (i8-closed-run-ok-mono xs xs tks sks tks2 sks2 ht (fn [x :- Nat, q :- (= (reach-mem x xs) true)] q)) rks h)))
(a/theorem i8-closed-source-ok-all-mono [sks :- (List I8ClosedScopeKey), sks2 :- (List I8ClosedScopeKey),
                        hs :- (forall [x :- Nat] (=> (= (sclosed sks2 x) true) (= (sclosed sks x) true))), xks :- (List I8ClosedSourceKey)]
  (=> (= (tbl-all (i8-closed-source-ok sks) xks) true) (= (tbl-all (i8-closed-source-ok sks2) xks) true))
  (intro h) (exact (tbl-all-mono I8ClosedSourceKey (i8-closed-source-ok sks) (i8-closed-source-ok sks2) (i8-closed-source-ok-mono sks sks2 hs) xks h)))
(a/theorem i8-closed-run-ok-esc-all [xs :- (List Nat), ys :- (List Nat), tks :- (List I8ClosedTaskKey), sks :- (List I8ClosedScopeKey),
                       hx :- (forall [x :- Nat] (=> (= (reach-mem x xs) true) (= (reach-mem x ys) true))), rks :- (List RunKey)]
  (=> (= (tbl-all (i8-closed-run-ok xs tks sks) rks) true) (= (tbl-all (i8-closed-run-ok ys tks sks) rks) true))
  (intro h)
  (exact (tbl-all-mono RunKey (i8-closed-run-ok xs tks sks) (i8-closed-run-ok ys tks sks)
           (i8-closed-run-ok-mono xs ys tks sks tks sks (fn [t :- Nat, q :- (= (tclosed tks sks t) true)] q) hx) rks h)))
(a/theorem sclosed-cons-open [k :- I8ClosedScopeKey, sks :- (List I8ClosedScopeKey), x :- Nat]
  (=> (= (:open k) true) (= (sclosed (List.cons I8ClosedScopeKey k sks) x) true) (= (sclosed sks x) true))
  (intros ho h) (simp only [sclosed tbl-any sclosed-k ho Bool.not_true Bool.and_false Bool.false_or] at h) (exact h))
(a/theorem tclosed-cons-free [k :- I8ClosedTaskKey, tks :- (List I8ClosedTaskKey), sks :- (List I8ClosedScopeKey), t :- Nat]
  (=> (= (sclosed sks (:owner k)) false) (= (tclosed (List.cons I8ClosedTaskKey k tks) sks t) true) (= (tclosed tks sks t) true))
  (intros ho h) (simp only [tclosed tbl-any tclosed-k ho Bool.and_false Bool.false_or] at h) (exact h))

(a/theorem i8-closed-scope-ins [x8s :- (List Nat), w :- World, r :- ScopeRow, ho :- (= (:open r) true)]
  (=> (= (scope-id r) (:next-id w)) (= (i8-closed x8s w) true) (= (i8-closed x8s (bump (scope-ins w r))) true))
  (intros hr h)
  (have h0 := (i8-closed-rest-of x8s w h)) (simp only [i8-closed-rest i8-closed-keys-ok Bool.and_eq_true] at h0)
  (have hs (forall [x :- Nat] (=> (= (sclosed (List.cons I8ClosedScopeKey (i8-closed-scope-key r) (i8-closed-scope-keys (:scopes w))) x) true) (= (sclosed (i8-closed-scope-keys (:scopes w)) x) true))))
  (intros x q) (exact (sclosed-cons-open (i8-closed-scope-key r) _ x ho q))
  (have ht (forall [t :- Nat] (=> (= (tclosed (i8-closed-task-keys (:tasks w)) (List.cons I8ClosedScopeKey (i8-closed-scope-key r) (i8-closed-scope-keys (:scopes w))) t) true)
                                   (= (tclosed (i8-closed-task-keys (:tasks w)) (i8-closed-scope-keys (:scopes w)) t) true))))
  (exact (tclosed-mono (i8-closed-task-keys (:tasks w)) (i8-closed-scope-keys (:scopes w)) (i8-closed-task-keys (:tasks w)) _ (any8-refl I8ClosedTaskKey _) hs))
  (have a1 := (i8-closed-run-ok-all-mono x8s _ _ _ _ ht _ (And.left h0)))
  (have a2 := (i8-closed-source-ok-all-mono _ _ hs _ (And.right h0)))
  (have hrest (= (i8-closed-rest x8s (bump (scope-ins w r))) true))
  (simp only [i8-closed-rest i8-closed-keys-ok bump set-next-id scope-ins set-scopes tbl-ins i8-closed-scope-keys a1 a2 Bool.and_self])
  (exact (i8-closed-intro x8s _ (well-formed-scope-ins-fresh w r hr (i8-closed-well-formed x8s w h)) hrest)))

(a/theorem i8-closed-task-ins [x8s :- (List Nat), w :- World, r :- TaskRow]
  (=> (= (task-id r) (:next-id w)) (= (sclosed (i8-closed-scope-keys (:scopes w)) (:owner r)) false) (= (i8-closed x8s w) true)
      (= (i8-closed x8s (bump (task-ins w r))) true))
  (intros hr ho h)
  (have h0 := (i8-closed-rest-of x8s w h)) (simp only [i8-closed-rest i8-closed-keys-ok Bool.and_eq_true] at h0)
  (have ht (forall [t :- Nat] (=> (= (tclosed (List.cons I8ClosedTaskKey (i8-closed-task-key r) (i8-closed-task-keys (:tasks w))) (i8-closed-scope-keys (:scopes w)) t) true)
                                   (= (tclosed (i8-closed-task-keys (:tasks w)) (i8-closed-scope-keys (:scopes w)) t) true))))
  (intros t q) (exact (tclosed-cons-free (i8-closed-task-key r) _ _ t ho q))
  (have a1 := (i8-closed-run-ok-all-mono x8s _ _ _ _ ht _ (And.left h0)))
  (have hrest (= (i8-closed-rest x8s (bump (task-ins w r))) true))
  (simp only [i8-closed-rest i8-closed-keys-ok bump set-next-id task-ins set-tasks tbl-ins i8-closed-task-keys a1 (And.right h0) Bool.and_self])
  (exact (i8-closed-intro x8s _ (well-formed-task-ins-fresh w r hr (i8-closed-well-formed x8s w h)) hrest)))

(a/theorem i8-closed-source-ins [x8s :- (List Nat), w :- World, r :- SourceRow]
  (=> (= (source-id r) (:next-id w)) (= (i8-closed-source-ok (i8-closed-scope-keys (:scopes w)) (i8-closed-source-key r)) true) (= (i8-closed x8s w) true)
      (= (i8-closed x8s (bump (source-ins w r))) true))
  (intros hr ho h)
  (have h0 := (i8-closed-rest-of x8s w h)) (simp only [i8-closed-rest i8-closed-keys-ok Bool.and_eq_true] at h0)
  (have hrest (= (i8-closed-rest x8s (bump (source-ins w r))) true))
  (simp only [i8-closed-rest i8-closed-keys-ok bump set-next-id source-ins set-sources tbl-ins i8-closed-source-keys tbl-all ho (And.left h0) (And.right h0) Bool.and_self])
  (exact (i8-closed-intro x8s _ (well-formed-source-ins-fresh w r hr (i8-closed-well-formed x8s w h)) hrest)))

(a/theorem i8-closed-run-ins [x8s :- (List Nat), w :- World, r :- RunRow]
  (=> (= (run-id r) (:next-id w)) (= (i8-closed-run-ok x8s (i8-closed-task-keys (:tasks w)) (i8-closed-scope-keys (:scopes w)) (run-key r)) true) (= (i8-closed x8s w) true)
      (= (i8-closed x8s (bump (run-ins w r))) true))
  (intros hr ho h)
  (have h0 := (i8-closed-rest-of x8s w h)) (simp only [i8-closed-rest i8-closed-keys-ok Bool.and_eq_true] at h0)
  (have hrest (= (i8-closed-rest x8s (bump (run-ins w r))) true))
  (simp only [i8-closed-rest i8-closed-keys-ok bump set-next-id run-ins set-runs tbl-ins run-keys tbl-all ho (And.left h0) (And.right h0) Bool.and_self])
  (exact (i8-closed-intro x8s _ (well-formed-run-ins-fresh w r hr (i8-closed-well-formed x8s w h)) hrest)))

;; a new run of an entity with no task of closed owner, with its fresh open run scope
(a/theorem i8-closed-add-run-scope-hand [x8s :- (List Nat), w :- World, of :- Nat, epoch :- Nat, parent :- Nat, ei :- Nat]
  (=> (= (tclosed (i8-closed-task-keys (:tasks w)) (i8-closed-scope-keys (:scopes w)) of) false) (= (i8-closed x8s w) true) (= (i8-closed x8s (add-run-scope w of epoch parent ei)) true))
  (intros hc h)
  (have r8n (= (i8-closed-run-ok x8s (i8-closed-task-keys (:tasks w)) (i8-closed-scope-keys (:scopes w)) (run-key (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei))) true))
  (simp only [i8-closed-run-ok run-key new-run-row hc Bool.not_false Bool.or_true])
  (have h1 := (i8-closed-run-ins x8s w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei) (rfl) r8n h))
  (simp only [add-run-scope])
  (have he (= (scope-id (new-scope-row (+ (:next-id w) 1) parent)) (:next-id (bump (run-ins w (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei)))))) (rfl)
  (exact (i8-closed-scope-ins x8s _ (new-scope-row (+ (:next-id w) 1) parent) (rfl) he h1)))

;; ===========================================================================
;; Part D. Closing a subtree (close-local): the closed scopes join, the owned runs escape
;; ===========================================================================

;; ---- frames for the waking and T10 (lit's i10-task-view chain, with the task, scope and source keys)
(a/theorem i8-closed-view-fold [f :- (=> World Nat World), hf :- (forall [w :- World, x :- Nat] (= (i8-closed-view (f w x)) (i8-closed-view w))), xs :- (List Nat)]
  (forall [w :- World] (= (i8-closed-view (nat-fold f w xs)) (i8-closed-view w)))
  (induction xs)
  (case [nil] (intro w) (simp only [nat-fold]))
  (case [cons h t ih] (intro w) (simp only [nat-fold]) (exact (Eq.trans (ih (f w h)) (hf w h)))))

(a/theorem i8-closed-view-finalize-loop [fuel :- (List Nat)]
  (forall [w :- World, ds :- (List Nat)] (= (i8-closed-view (:world (finalize-loop fuel w ds))) (i8-closed-view w)))
  (induction fuel)
  (case [nil] (intros w ds) (simp only [finalize-loop]))
  (case [cons h f ih]
    (intros w ds)
    (cases ds)
    (simp only [finalize-loop])
    (rename_i d t)
    (simp only [finalize-loop])
    (exact (ih (finalize-one w d) _))))

;; Z#53: closing a source wakes its waiters (T9): a fill may wake a parked run (still alive), so
;; the run keys stay
(a/theorem i8-closed-view-resume [w :- World, a :- ActRow] (= (i8-closed-view (resume w a)) (i8-closed-view w))
  (simp only [resume i8-closed-view run-upd set-runs])
  (rw [(run-keys-upd (:run a) run-wake run-key-run-wake (:runs w))]))
(a/theorem i8-closed-view-fill-slot [w :- World, a :- ActRow, y :- Nat, v :- RunResult] (= (i8-closed-view (fill-slot w a y v)) (i8-closed-view w))
  (cases hm (act-ready (act-fill y v a)))
  (simp only [fill-slot hm])
  (simp only [fill-slot hm]) (exact (i8-closed-view-resume w a)))
(a/theorem i8-closed-view-remove-edge [w :- World, y :- Nat] (= (i8-closed-view (remove-edge w y)) (i8-closed-view w))
  (cases hf (edge-find w y)) (case' [some e]) (case' [none])
  (simp only [remove-edge hf])
  (cases hm (:marked e))
  (all_goals (simp only [remove-edge hf hm])))
(a/theorem i8-closed-view-fire-dep [w :- World, e :- EdgeRow] (= (i8-closed-view (fire-dep w e)) (i8-closed-view w))
  (cases ha (act-with-member (:id e) (:acts w))) (case' [some a]) (case' [none])
  (simp only [fire-dep ha invalidate])
  (cases hc (Bool.and (run-current-of w (:run a) (:creditor e)) (deb-avail w (:debtor e))))
  (simp only [fire-dep ha hc invalidate])
  (simp only [fire-dep ha hc deliver-dep])
  (have e1 (= (i8-closed-view (dep-consumed w e)) (i8-closed-view w)))
  (cases hf (deb-final w (:debtor e)))
  (simp only [dep-consumed hf])
  (simp only [dep-consumed hf]) (exact (i8-closed-view-remove-edge w (:id e)))
  (exact (Eq.trans (i8-closed-view-fill-slot _ a _ _) e1)))
(a/theorem i8-closed-view-fire-wait [res :- RunResult, w :- World, e :- EdgeRow] (= (i8-closed-view (fire-wait res w e)) (i8-closed-view w))
  (cases hc (Nat.beq (:creditor e) 0))
  (case [true] (simp only [fire-wait hc]) (exact (i8-closed-view-remove-edge w (:id e))))
  (case [false]
    (simp only [fire-wait hc])
    (cases ha (act-find w (:creditor e))) (case' [some a]) (case' [none])
    (simp only [fire-wait-act ha])
    (cases hr (run-current w (:run a)))
    (simp only [fire-wait-act ha hr])
    (simp only [fire-wait-act ha hr]) (exact (i8-closed-view-fill-slot _ a _ _))))
(a/theorem i8-closed-view-fire-edge [res :- RunResult, w :- World, y :- Nat] (= (i8-closed-view (fire-edge res w y)) (i8-closed-view w))
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
  (simp only [fire-edge hf hp hk1 hk2]) (exact (i8-closed-view-fire-wait res w e))
  (simp only [fire-edge hf hp hk1]) (exact (i8-closed-view-fire-dep w e)))
(a/theorem i8-closed-view-wake-closed [w :- World, x :- Nat] (= (i8-closed-view (wake-closed w x)) (i8-closed-view w))
  (simp only [wake-closed])
  (exact (i8-closed-view-fold (fire-edge (deb-result w x)) (i8-closed-view-fire-edge (deb-result w x)) _ w)))


;; ---- closing a source and a scope, on the keys
(a/defn sk-shut [k :- I8ClosedScopeKey] I8ClosedScopeKey (I8ClosedScopeKey.mk (:id k) false))
(a/theorem slice-holder-ok-close [s :- ScopeRow] (= (i8-closed-scope-key (scope-close s)) (sk-shut (i8-closed-scope-key s))) (rfl))
;; C0: realizing a link keeps every key (deliver-res writes the value, the link stays open)
(a/theorem i8-closed-view-source-upd-k [w :- World, x :- Nat, f :- (=> SourceRow SourceRow), hk :- (forall [s :- SourceRow] (= (i8-closed-source-key (f s)) (i8-closed-source-key s)))]
  (= (i8-closed-view (source-upd w x f)) (i8-closed-view w))
  (simp only [i8-closed-view source-upd set-sources (xoks-upd x f hk (:sources w))]))
(a/theorem i8-closed-view-deliver-res [w :- World, x :- Nat, v :- Nat, rr :- RunResult] (= (i8-closed-view (deliver-res w x v rr)) (i8-closed-view w))
  (simp only [deliver-res t10-finalize-debtor])
  (exact (Eq.trans (i8-closed-view-finalize-loop _ _ _)
           (Eq.trans (i8-closed-view-fold (fire-edge rr) (i8-closed-view-fire-edge rr) _ _)
             (Eq.trans (i8-closed-view-fold (fire-edge rr) (i8-closed-view-fire-edge rr) _ _)
               (i8-closed-view-source-upd-k w x (source-write v) (fn [s :- SourceRow] (Eq.refl (i8-closed-source-key s)))))))))
(a/theorem i8-closed-view-end-link [w :- World, x :- Nat, fl :- Bool, v :- Nat] (= (i8-closed-view (end-link w x fl v)) (i8-closed-view w))
  (cases hp (link-pending w x))
  (simp only [end-link hp])
  (simp only [end-link hp realize-link])
  (exact (Eq.trans (i8-closed-view-deliver-res _ x _ _) (i8-closed-view-source-upd-k w x (link-done-row fl 0) (fn [s :- SourceRow] (Eq.refl (i8-closed-source-key s)))))))
(a/theorem i8-closed-view-end-stream [w :- World, x :- Nat] (= (i8-closed-view (end-stream w x)) (i8-closed-view w))
  (cases hf (source-find w x)) (case' [some s]) (case' [none])
  (simp only [end-stream hf])
  (cases hk (Nat.beq (:kind s) sk-stream))
  (simp only [end-stream hf hk])
  (simp only [end-stream hf hk]) (exact (i8-closed-view-end-link w _ false 0)))
(a/theorem i8-closed-view-clear-rtasks [w :- World, k :- Nat] (= (i8-closed-view (clear-rtasks w k)) (i8-closed-view w))
  (simp only [clear-rtasks])
  (exact (i8-closed-view-fold clear-rtask (fn [w2 :- World, y :- Nat] (i8-closed-view-source-upd-k w2 y (link-set-rtask 0) (fn [s :- SourceRow] (Eq.refl (i8-closed-source-key s))))) _ w)))
(a/theorem i8-closed-view-close-source-ended [w :- World, x :- Nat]
  (= (i8-closed-view (close-source-ended w x))
     (I8ClosedView.mk (run-keys (:runs w)) (i8-closed-task-keys (:tasks w)) (i8-closed-scope-keys (:scopes w)) (tbl-upd i8-closed-source-key-id x xk-shut (i8-closed-source-keys (:sources w)))))
  (simp only [close-source-ended t10-finalize-debtor])
  (have e1 := (i8-closed-view-finalize-loop (finalize-fuel (wake-closed (source-upd w x source-close-row) x)) (wake-closed (source-upd w x source-close-row) x) (List.cons Nat x (List.nil Nat))))
  (have e2 := (i8-closed-view-wake-closed (source-upd w x source-close-row) x))
  (have e3 (= (i8-closed-view (source-upd w x source-close-row))
              (I8ClosedView.mk (run-keys (:runs w)) (i8-closed-task-keys (:tasks w)) (i8-closed-scope-keys (:scopes w)) (tbl-upd i8-closed-source-key-id x xk-shut (i8-closed-source-keys (:sources w))))))
  (simp only [i8-closed-view source-upd set-sources (xoks-upd-g x source-close-row xk-shut xok-close (:sources w))])
  (exact (Eq.trans e1 (Eq.trans e2 e3))))
(a/theorem i8-closed-view-close-source [w :- World, x :- Nat]
  (= (i8-closed-view (close-source w x))
     (I8ClosedView.mk (run-keys (:runs w)) (i8-closed-task-keys (:tasks w)) (i8-closed-scope-keys (:scopes w)) (tbl-upd i8-closed-source-key-id x xk-shut (i8-closed-source-keys (:sources w)))))
  (simp only [close-source])
  (have e := (i8-closed-view-end-stream w x))
  (have e1 (= (run-keys (:runs (end-stream w x))) (run-keys (:runs w)))) (exact (congrArg (fn [k :- I8ClosedView] (:rks k)) e))
  (have e2 (= (i8-closed-task-keys (:tasks (end-stream w x))) (i8-closed-task-keys (:tasks w)))) (exact (congrArg (fn [k :- I8ClosedView] (:tks k)) e))
  (have e3 (= (i8-closed-scope-keys (:scopes (end-stream w x))) (i8-closed-scope-keys (:scopes w)))) (exact (congrArg (fn [k :- I8ClosedView] (:sks k)) e))
  (have e4 (= (i8-closed-source-keys (:sources (end-stream w x))) (i8-closed-source-keys (:sources w)))) (exact (congrArg (fn [k :- I8ClosedView] (:xks k)) e))
  (rw [(i8-closed-view-close-source-ended (end-stream w x) x) e1 e2 e3 e4]))
(a/theorem i8-closed-view-close-scope-id [w :- World, x :- Nat]
  (= (i8-closed-view (close-scope-id w x))
     (I8ClosedView.mk (run-keys (:runs w)) (i8-closed-task-keys (:tasks w)) (tbl-upd i8-closed-scope-key-id x sk-shut (i8-closed-scope-keys (:scopes w))) (i8-closed-source-keys (:sources w))))
  (simp only [close-scope-id i8-closed-view scope-upd set-scopes (soks-upd-g x scope-close sk-shut slice-holder-ok-close (:scopes w))]))

(a/defn xk-fold [ks :- (List I8ClosedSourceKey), xs :- (List Nat)] (List I8ClosedSourceKey)
  (match xs nil ks (cons x t) (xk-fold (tbl-upd i8-closed-source-key-id x xk-shut ks) t)))
(a/defn sk-fold [ks :- (List I8ClosedScopeKey), xs :- (List Nat)] (List I8ClosedScopeKey)
  (match xs nil ks (cons x t) (sk-fold (tbl-upd i8-closed-scope-key-id x sk-shut ks) t)))
(a/defn i8-closed-view-xs [k :- I8ClosedView, xs :- (List Nat)] I8ClosedView (I8ClosedView.mk (:rks k) (:tks k) (:sks k) (xk-fold (:xks k) xs)))
(a/defn i8-closed-view-ss [k :- I8ClosedView, xs :- (List Nat)] I8ClosedView (I8ClosedView.mk (:rks k) (:tks k) (sk-fold (:sks k) xs) (:xks k)))

(a/theorem i8-closed-view-source-fold [xs :- (List Nat)] (forall [w :- World] (= (i8-closed-view (nat-fold close-source w xs)) (i8-closed-view-xs (i8-closed-view w) xs)))
  (induction xs)
  (case [nil] (intro w) (simp only [nat-fold i8-closed-view-xs xk-fold i8-closed-view]))
  (case [cons x t ih]
    (intro w)
    (simp only [nat-fold])
    (rw [(ih (close-source w x))])
    (rw [(i8-closed-view-close-source w x)])))
(a/theorem i8-closed-view-scope-fold [xs :- (List Nat)] (forall [w :- World] (= (i8-closed-view (nat-fold close-scope-id w xs)) (i8-closed-view-ss (i8-closed-view w) xs)))
  (induction xs)
  (case [nil] (intro w) (simp only [nat-fold i8-closed-view-ss sk-fold i8-closed-view]))
  (case [cons x t ih]
    (intro w)
    (simp only [nat-fold])
    (rw [(ih (close-scope-id w x))])
    (rw [(i8-closed-view-close-scope-id w x)])))
(a/theorem fold8-field [B :- Type, P :- (=> World B), f :- (=> World Nat World), hf :- (forall [q :- World, y :- Nat] (= (P (f q y)) (P q))),
                        xs :- (List Nat)]
  (forall [w :- World] (= (P (nat-fold f w xs)) (P w)))
  (induction xs)
  (case [nil] (intro w) (simp only [nat-fold]))
  (case [cons h t ih] (intro w) (simp only [nat-fold]) (exact (Eq.trans (ih (f w h)) (hf w h)))))
(a/theorem i8-closed-view-close-local [w :- World, sub :- (List Nat)]
  (= (i8-closed-view (close-local w sub))
     (I8ClosedView.mk (run-keys (:runs w)) (i8-closed-task-keys (:tasks w)) (sk-fold (i8-closed-scope-keys (:scopes w)) sub)
             (xk-fold (i8-closed-source-keys (:sources w)) (tbl-scan source-id (source-owned-in sub) (:sources w)))))
  (simp only [close-local])
  (rw [(i8-closed-view-source-fold (tbl-scan source-id (source-owned-in sub) (:sources w)) (nat-fold close-scope-id w sub))])
  (exact (congrArg (fn [k :- I8ClosedView] (i8-closed-view-xs k (tbl-scan source-id (source-owned-in sub) (:sources w)))) (i8-closed-view-scope-fold sub w))))

;; ---- closedness after the folds
(a/theorem sclosed-upd-shut [y :- Nat, x :- Nat, sks :- (List I8ClosedScopeKey)]
  (=> (= (sclosed (tbl-upd i8-closed-scope-key-id x sk-shut sks) y) true) (Or (= (sclosed sks y) true) (= (Nat.beq y x) true)))
  (induction sks)
  (case [nil] (intro h) (simp only [tbl-upd] at h) (exact (Or.inl h)))
  (case [cons k t ih]
    (intro h)
    (cases hx (Nat.beq (i8-closed-scope-key-id k) x))
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
  (forall [sks :- (List I8ClosedScopeKey), y :- Nat]
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
(a/defn towned-k [sub :- (List Nat), t :- Nat, k :- I8ClosedTaskKey] Bool (Bool.and (Nat.beq (:id k) t) (reach-mem (:owner k) sub)))
(a/defn cov8 [ys :- (List Nat), sub :- (List Nat), tks :- (List I8ClosedTaskKey), k :- RunKey] Bool
  (Bool.or (Bool.not (:alive k)) (Bool.or (reach-mem (:id k) ys) (Bool.not (tbl-any (towned-k sub (:of k)) tks)))))
(a/defn lcov8 [L :- (List Nat), sub :- (List Nat), k :- I8ClosedSourceKey] Bool
  (Bool.or (Bool.not (reach-mem (:owner k) sub)) (reach-mem (:id k) L)))

(a/theorem tclosed-skfold [sub :- (List Nat), sks :- (List I8ClosedScopeKey), t :- Nat, tks :- (List I8ClosedTaskKey)]
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

(a/theorem i8-closed-run-ok-close [xs :- (List Nat), ys :- (List Nat), sub :- (List Nat), tks :- (List I8ClosedTaskKey), sks :- (List I8ClosedScopeKey), k :- RunKey]
  (=> (= (i8-closed-run-ok xs tks sks k) true) (= (cov8 ys sub tks k) true) (= (i8-closed-run-ok (List.append Nat xs ys) tks (sk-fold sks sub) k) true))
  (intros h c)
  (cases ha (:alive k))
  (case [false] (simp only [i8-closed-run-ok ha Bool.not_false Bool.true_or]))
  (case [true]
    (cases hx (reach-mem (:id k) xs))
    (case [true] (simp only [i8-closed-run-ok ha reach-mem-append hx Bool.true_or Bool.or_true]))
    (case [false]
      (cases hy (reach-mem (:id k) ys))
      (case [true] (simp only [i8-closed-run-ok ha reach-mem-append hy Bool.true_or Bool.or_true]))
      (case [false]
        (simp only [i8-closed-run-ok ha hx Bool.not_true Bool.false_or] at h)
        (simp only [cov8 ha hy Bool.not_true Bool.false_or] at c)
        (simp only [i8-closed-run-ok ha reach-mem-append hx hy Bool.not_true Bool.false_or Bool.or_false])
        (cases hc (tclosed tks (sk-fold sks sub) (:of k)))
        (case [false] (simp only [hc Bool.not_false]))
        (case [true]
          (have q := (tclosed-skfold sub sks (:of k) tks hc))
          (cases q)
          (case [inl a] (simp only [a Bool.not_true] at h) (cases h))
          (case [inr b] (simp only [b Bool.not_true] at c) (cases c)))))))

(a/defn j8 [L :- (List Nat), sub :- (List Nat), sks :- (List I8ClosedScopeKey), k :- I8ClosedSourceKey] Bool
  (Bool.or (Bool.not (:open k))
   (Bool.or (reach-mem (:id k) L) (Bool.and (Bool.not (reach-mem (:owner k) sub)) (i8-closed-source-ok sks k)))))
(a/theorem j8-step [x :- Nat, t :- (List Nat), sub :- (List Nat), sks :- (List I8ClosedScopeKey), ks :- (List I8ClosedSourceKey)]
  (=> (= (tbl-all (j8 (List.cons Nat x t) sub sks) ks) true) (= (tbl-all (j8 t sub sks) (tbl-upd i8-closed-source-key-id x xk-shut ks)) true))
  (intro h)
  (apply (tbl-all-upd I8ClosedSourceKey i8-closed-source-key-id x xk-shut (j8 (List.cons Nat x t) sub sks) (j8 t sub sks) _ _ ks h))
  (intros k p q) (simp only [j8 xk-shut Bool.not_false Bool.true_or])
  (intros k p q)
  (have q2 (= (Nat.beq (:id k) x) false)) (exact q)
  (simp only [j8 reach-mem-cons q2 Bool.false_or] at p) (exact p))
(a/theorem j8-fold [sub :- (List Nat), sks :- (List I8ClosedScopeKey), L :- (List Nat)]
  (forall [ks :- (List I8ClosedSourceKey)] (=> (= (tbl-all (j8 L sub sks) ks) true) (= (tbl-all (j8 (List.nil Nat) sub sks) (xk-fold ks L)) true)))
  (induction L)
  (case [nil] (intros ks h) (simp only [xk-fold]) (exact h))
  (case [cons x t ih] (intros ks h) (simp only [xk-fold]) (exact (ih _ (j8-step x t sub sks ks h)))))
(a/theorem i8-closed-source-ok-close [L :- (List Nat), sub :- (List Nat), sks :- (List I8ClosedScopeKey), xks :- (List I8ClosedSourceKey)]
  (=> (= (tbl-all (i8-closed-source-ok sks) xks) true) (= (tbl-all (lcov8 L sub) xks) true)
      (= (tbl-all (i8-closed-source-ok (sk-fold sks sub)) (xk-fold xks L)) true))
  (intros h c)
  (have j0 (= (tbl-all (j8 L sub sks) xks) true))
  (apply (tbl-all-mono2 I8ClosedSourceKey (i8-closed-source-ok sks) (lcov8 L sub) (j8 L sub sks) _ xks h c))
  (intros k p q)
  (cases ho (reach-mem (:owner k) sub))
  (case [true] (simp only [lcov8 ho Bool.not_true Bool.false_or] at q) (simp only [j8 q Bool.true_or Bool.or_true]))
  (case [false] (simp only [j8 ho p Bool.not_false Bool.true_and Bool.or_true]))
  (have j1 := (j8-fold sub sks L xks j0))
  (apply (tbl-all-mono I8ClosedSourceKey (j8 (List.nil Nat) sub sks) (i8-closed-source-ok (sk-fold sks sub)) _ _ j1))
  (intros k p)
  (cases hk (:open k))
  (case [false] (simp only [i8-closed-source-ok hk Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [j8 hk reach-mem Bool.not_true Bool.false_or Bool.and_eq_true] at p)
    (have p1 := (bnot-true _ (And.left p)))
    (have p2 := (And.right p))
    (simp only [i8-closed-source-ok hk Bool.not_true Bool.false_or] at p2)
    (have p3 := (bnot-true _ p2))
    (simp only [i8-closed-source-ok hk Bool.not_true Bool.false_or])
    (cases hc (sclosed (sk-fold sks sub) (:owner k)))
    (case [false] (simp only [hc Bool.not_false]))
    (case [true]
      (have q := (sclosed-skfold sub sks (:owner k) hc))
      (cases q)
      (case [inl a] (simp only [a] at p3) (cases p3))
      (case [inr b] (simp only [b] at p1) (cases p1)))))

(a/theorem i8-closed-keys-ok-close [xs :- (List Nat), ys :- (List Nat), sub :- (List Nat), L :- (List Nat),
                      rks :- (List RunKey), tks :- (List I8ClosedTaskKey), sks :- (List I8ClosedScopeKey), xks :- (List I8ClosedSourceKey)]
  (=> (= (i8-closed-keys-ok xs rks tks sks xks) true) (= (tbl-all (cov8 ys sub tks) rks) true) (= (tbl-all (lcov8 L sub) xks) true)
      (= (i8-closed-keys-ok (List.append Nat xs ys) rks tks (sk-fold sks sub) (xk-fold xks L)) true))
  (intros h c l)
  (simp only [i8-closed-keys-ok Bool.and_eq_true] at h)
  (have a1 (= (tbl-all (i8-closed-run-ok (List.append Nat xs ys) tks (sk-fold sks sub)) rks) true))
  (apply (tbl-all-mono2 RunKey (i8-closed-run-ok xs tks sks) (cov8 ys sub tks) _ _ rks (And.left h) c))
  (intros k p q) (exact (i8-closed-run-ok-close xs ys sub tks sks k p q))
  (have a2 := (i8-closed-source-ok-close L sub sks xks (And.right h) l))
  (simp only [i8-closed-keys-ok a1 a2 Bool.and_self]))

;; ---- coverage in a world: the owned runs, the owned sources
(a/defn on-xok [P :- (=> I8ClosedSourceKey Bool), s :- SourceRow] Bool (P (i8-closed-source-key s)))
(a/theorem all-xoks [P :- (=> I8ClosedSourceKey Bool), ss :- (List SourceRow)] (= (tbl-all P (i8-closed-source-keys ss)) (tbl-all (on-xok P) ss))
  (induction ss) (case [nil] (simp only [i8-closed-source-keys tbl-all])) (case [cons h t ih] (simp only [i8-closed-source-keys tbl-all on-xok ih])))
(a/theorem towned-scan [sub :- (List Nat), t :- Nat, ts :- (List TaskRow)]
  (=> (= (tbl-any (towned-k sub t) (i8-closed-task-keys ts)) true) (= (reach-mem t (tbl-scan task-id (task-owned-in sub) ts)) true))
  (induction ts)
  (case [nil] (intro h) (simp only [i8-closed-task-keys tbl-any] at h) (cases h))
  (case [cons k tl ih]
    (intro h)
    (simp only [i8-closed-task-keys tbl-any Bool.or_eq_true] at h)
    (cases h)
    (case [inl a]
      (simp only [towned-k i8-closed-task-key Bool.and_eq_true] at a)
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
  (=> (= (well-formed w) true) (= (tbl-all (cov8 (owned-runs w sub) sub (i8-closed-task-keys (:tasks w))) (run-keys (:runs w))) true))
  (intro hs)
  (rw [all-run-keys])
  (apply (all-of-mem RunRow _ (:runs w)))
  (intros r hm)
  (simp only [on-rkey])
  (cases ha (run-alive r))
  (case [false] (simp only [cov8 run-key ha Bool.not_false Bool.true_or]))
  (case [true]
    (cases ht (tbl-any (towned-k sub (:of r)) (i8-closed-task-keys (:tasks w))))
    (case [false] (simp only [cov8 run-key ht Bool.not_false Bool.or_true]))
    (case [true]
      (have f := (scan-mem-find TaskRow task-id (task-owned-in sub) (:of r) (:tasks w) (towned-scan sub (:of r) (:tasks w) ht) (tasks-nodup w hs)))
      (have p (= (run-owned-by w sub r) true)) (simp only [run-owned-by ha task-find f Bool.true_and])
      (have m := (scan-mem RunRow run-id (run-owned-by w sub) r (:runs w) hm p))
      (have m2 (= (reach-mem (:id (run-key r)) (owned-runs w sub)) true)) (exact m)
      (simp only [cov8 m2 Bool.true_or Bool.or_true]))))
(a/theorem lcov-owned [w :- World, sub :- (List Nat)]
  (= (tbl-all (lcov8 (tbl-scan source-id (source-owned-in sub) (:sources w)) sub) (i8-closed-source-keys (:sources w))) true)
  (rw [all-xoks])
  (apply (all-of-mem SourceRow _ (:sources w)))
  (intros s hm)
  (simp only [on-xok])
  (cases ho (reach-mem (:owner s) sub))
  (case [false] (simp only [lcov8 i8-closed-source-key ho Bool.not_false Bool.true_or]))
  (case [true]
    (have p (= (source-owned-in sub s) true)) (simp only [source-owned-in]) (exact ho)
    (have m := (scan-mem SourceRow source-id (source-owned-in sub) s (:sources w) hm p))
    (have m2 (= (reach-mem (:id (i8-closed-source-key s)) (tbl-scan source-id (source-owned-in sub) (:sources w))) true)) (exact m)
    (simp only [lcov8 m2 Bool.or_true])))

(a/theorem i8-closed-rest-mk [x8s :- (List Nat), w :- World, a :- (List RunKey), b :- (List I8ClosedTaskKey), c :- (List I8ClosedScopeKey), d :- (List I8ClosedSourceKey)]
  (=> (= (i8-closed-view w) (I8ClosedView.mk a b c d)) (= (i8-closed-rest x8s w) (i8-closed-keys-ok x8s a b c d)))
  (intro e)
  (have e1 (= (run-keys (:runs w)) a)) (exact (congrArg (fn [k :- I8ClosedView] (:rks k)) e))
  (have e2 (= (i8-closed-task-keys (:tasks w)) b)) (exact (congrArg (fn [k :- I8ClosedView] (:tks k)) e))
  (have e3 (= (i8-closed-scope-keys (:scopes w)) c)) (exact (congrArg (fn [k :- I8ClosedView] (:sks k)) e))
  (have e4 (= (i8-closed-source-keys (:sources w)) d)) (exact (congrArg (fn [k :- I8ClosedView] (:xks k)) e))
  (simp only [i8-closed-rest e1 e2 e3 e4]))

;; Closing a subtree: the runs of the tasks it owns join the escape list
(a/theorem i8-closed-close-local-cov [x8s :- (List Nat), ys :- (List Nat), w :- World, sub :- (List Nat)]
  (=> (= (i8-closed x8s w) true) (= (tbl-all (cov8 ys sub (i8-closed-task-keys (:tasks w))) (run-keys (:runs w))) true)
      (= (i8-closed (List.append Nat x8s ys) (close-local w sub)) true))
  (intros h hc)
  (have hs := (i8-closed-well-formed x8s w h))
  (have r := (i8-closed-rest-of x8s w h)) (simp only [i8-closed-rest] at r)
  (have c := (i8-closed-keys-ok-close x8s ys sub (tbl-scan source-id (source-owned-in sub) (:sources w))
               _ _ _ _ r hc (lcov-owned w sub)))
  (exact (i8-closed-intro _ _ (well-formed-close-local w sub hs) (Eq.trans (i8-closed-rest-mk _ _ _ _ _ _ (i8-closed-view-close-local w sub)) c))))
(a/theorem i8-closed-close-local [x8s :- (List Nat), w :- World, sub :- (List Nat)]
  (=> (= (i8-closed x8s w) true) (= (i8-closed (List.append Nat x8s (owned-runs w sub)) (close-local w sub)) true))
  (intro h) (exact (i8-closed-close-local-cov x8s (owned-runs w sub) w sub h (cov-owned w sub (i8-closed-well-formed x8s w h)))))

;; ===========================================================================
;; Part E. The copy over the raw transition and Rule R
;; ===========================================================================

;; a run row made alive that was alive already (every row with that id is alive)
(a/theorem run-keys-upd-al [x :- Nat, f :- (=> RunRow RunRow), rs :- (List RunRow)]
  (=> (= (tbl-all (run-ok-for x) rs) true) (forall [r :- RunRow] (=> (= (run-alive r) true) (= (run-key (f r)) (run-key r))))
      (= (run-keys (tbl-upd run-id x f rs)) (run-keys rs)))
  (induction rs)
  (case [nil] (intros h1 h2) (simp only [tbl-upd run-keys]))
  (case [cons h t ih]
    (intros h1 h2)
    (simp only [tbl-all Bool.and_eq_true] at h1)
    (cases hx (Nat.beq (run-id h) x))
    (case [false] (simp only [tbl-upd hx run-keys (ih (And.right h1) h2)]))
    (case [true]
      (have a (= (run-alive h) true))
      (have q := (And.left h1)) (have hx2 (= (Nat.beq (:id h) x) true)) (exact hx)
      (simp only [run-ok-for hx2 Bool.not_true Bool.false_or] at q) (exact q)
      (simp only [tbl-upd hx run-keys (ih (And.right h1) h2) (h2 h a)]))))
(a/theorem i8-closed-run-upd-up [x8s :- (List Nat), w :- World, x :- Nat, f :- (=> RunRow RunRow),
                          hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                          hk :- (forall [r :- RunRow] (= (run-alive (f r)) true)),
                          ho :- (forall [r :- RunRow] (= (:of (f r)) (:of r)))]
  (=> (= (tbl-all (run-ok-for x) (:runs w)) true) (= (i8-closed x8s w) true) (= (i8-closed x8s (run-upd w x f)) true))
  (intros hal h)
  (have e (= (run-keys (tbl-upd run-id x f (:runs w))) (run-keys (:runs w))))
  (apply (run-keys-upd-al x f (:runs w) hal))
  (intros r q) (have i (= (:id (f r)) (:id r))) (exact (hf r)) (simp only [run-key i (hk r) (ho r) q])
  (have e2 (= (i8-closed-view (run-upd w x f)) (i8-closed-view w))) (simp only [i8-closed-view run-upd set-runs e])
  (exact (i8-closed-of-view x8s w _ (well-formed-run-upd w x f hf (i8-closed-well-formed x8s w h)) e2 h)))

;; ---------------------------------------------------------------------------
;; The part i8-closed: I8, closed scopes (spec §6 I8; formal/notes/proof-layout.md §4.6)
;;
;; 1. In words: a closed scope owns no alive run (of its tasks) and no open source; `i8-closed-rest x8s`
;;    allows the alive runs in the escape list x8s (Part A, over the key lists `i8-closed-view`).
;; 2. View: runs, tasks, scopes, sources (`g8-rest-frame-<field>` for every other field, from
;;    `defpart`). Finer, column level: `i8-closed-view` = run keys (id, of, alive), task (id, owner), scope
;;    (id, open), source (id, owner, open), frame `i8-closed-of-view`.
;; 3. Exempt form: the bundle parameter x8s, run ids (`i8-closed []` is the part; `defexempt 'i8-closed` at the
;;    end of Part F gives the uniform names `g8-exempt-<role>`). Break `i8-closed-close-local` (closing a
;;    subtree adds the alive runs of its tasks: the cancel jobs the cascade queues next); repair: a
;;    cancel job kills its run (`i8-closed-job-cancel`); loop invariant `i8-closed-cascade` (the escape list is
;;    base ++ the runs of the pending cancel jobs, `cj`); exit `i8-closed-cascade-done` (the worklist is
;;    empty: P4, `cascade-done-acts-parked`).
;; 4. Cells, the edits that write the view: updates that keep the keys (`i8-closed-run-upd`, `i8-closed-task-upd`,
;;    `i8-closed-scope-upd`, `i8-closed-source-upd`; the key equation `rfl` at every site not in the table), a new
;;    scope is open (`i8-closed-scope-ins`), deletes (`i8-closed-rest-run-del`, `i8-closed-rest-scope-del`), Rule R's filter
;;    (`i8-closed-filter-world`); new tasks, sources and runs (`i8-closed-task-ins`, `i8-closed-source-ins`, `i8-closed-run-ins`,
;;    Part G: the owner is not closed). Every other primitive is a frame. Sites (Part H): the row
;;    functions that change a key (a run dies, is made parked, a task's owner changes, a source
;;    closes or is orphaned, `serve-or`'s `keep`).
;; 5. Deferred within a step: the cascade (`well-formed-run-cascade`: break inside the close and retire
;;    jobs, repair by the cancel jobs, ghost `cj`, exit by P4), i8-closed's own proof in the table. The facts
;;    i8-closed takes from the path are its table's `:ctx`, `:own` and `:pass` (Part H): owners of new tasks
;;    and sources are open (the guards `cur-closed`, which is P10, `root-open-if`, `scope-open-at`), a
;;    run made parked was alive (`awaiting-run-alive` through the await), and the companion `acts-parked` to the cascades.
;; 6. Companions: `acts-parked` (P4 at every cascade; `step-i8-closed`: acts-alive for Rule R), `awaiting-run-alive` (the awaiting
;;    run stays alive through the await's wiring).

(def G8 (mk-bundle 'i8-closed '[x8s :- (List Nat)] "i8-closed-"
          {'well-formed-run-upd ['(fn [r :- RunRow] (Eq.refl (run-key r))) 4]
           'well-formed-task-upd ['(fn [t :- TaskRow] (Eq.refl (i8-closed-task-key t))) 4]
           'well-formed-scope-upd ['(fn [s :- ScopeRow] (Eq.refl (i8-closed-scope-key s))) 4]
           'well-formed-source-upd ['(fn [s :- SourceRow] (Eq.refl (i8-closed-source-key s))) 4]
           'well-formed-scope-ins-fresh ['(Eq.refl true) 2]}))
(swap! (:renames G8) assoc 'well-formed-parts 'i8-closed-parts)
(defpart G8
  :reads '[runs tasks scopes sources]
  :cells '{well-formed-run-upd i8-closed-run-upd                       ; keeps the run key
           well-formed-task-upd i8-closed-task-upd                     ; keeps (id, owner)
           well-formed-scope-upd i8-closed-scope-upd                   ; keeps (id, open)
           well-formed-source-upd i8-closed-source-upd                 ; keeps (id, owner, open)
           well-formed-scope-ins-fresh i8-closed-scope-ins             ; a new scope is open
           well-formed-filter-world i8-closed-filter-world             ; Rule R's filter only drops rows
           well-formed-run-del (i8-closed-rest-run-del x8s w x R)      ; a deleted run escapes nothing
           well-formed-scope-del (i8-closed-rest-scope-del x8s w x R)}); a deleted scope closes nothing
;; the per-edit frame lemmas of the edge edits, now from the view
(frames/frame-theorem! 'i8-closed-rest-mark-edge 'i8-closed-rest 'well-formed-mark-edge)
(frames/frame-theorem! 'i8-closed-rest-unmark-edge 'i8-closed-rest 'well-formed-unmark-edge)
(frames/frame-theorem! 'i8-closed-rest-remove-edge 'i8-closed-rest 'well-formed-remove-edge)

;; ===========================================================================
;; Part F. The cascade: the escape list is the list of pending cancel jobs
;; ===========================================================================

;; ---- keys through T14's local part: only the cancelled run's key goes down
(a/theorem tok-cancel-result [t :- TaskRow] (= (i8-closed-task-key (task-cancel-result t)) (i8-closed-task-key t))
  (cases hn (Nat.beq (:tag (:result t)) res-none))
  (case [true] (simp only [task-cancel-result hn i8-closed-task-key]))
  (case [false] (simp only [task-cancel-result hn])))
(a/theorem i8-closed-view-invalidate [w :- World, e :- EdgeRow] (= (i8-closed-view (invalidate w e)) (i8-closed-view w)) (rfl))
(a/theorem i8-closed-view-invalidate-id [w :- World, x :- Nat] (= (i8-closed-view (invalidate-id w x)) (i8-closed-view w))
  (cases hf (edge-find w x))
  (case [none] (simp only [invalidate-id hf]))
  (case [some e] (cases hp (Nat.beq (:phase e) ph-armed)) (all_goals (simp only [invalidate-id hf hp i8-closed-view-invalidate]))))
(a/theorem i8-closed-view-debtor-side [w :- World, r :- RunRow] (= (i8-closed-view (debtor-side w r)) (i8-closed-view w))
  (cases hc (comp-find w (:of r)))
  (case [none]
    (simp only [debtor-side hc fire-task-cancelled])
    (rw [(i8-closed-view-clear-rtasks _ (:of r))])
    (simp only [t10-finalize-debtor])
    (have e1 := (i8-closed-view-finalize-loop (finalize-fuel (nat-fold (fire-edge res-cancelled) (task-upd w (:of r) task-cancel-result)
                                           (tbl-scan edge-id (on-task (:of r)) (:edges (task-upd w (:of r) task-cancel-result)))))
                              (nat-fold (fire-edge res-cancelled) (task-upd w (:of r) task-cancel-result)
                                  (tbl-scan edge-id (on-task (:of r)) (:edges (task-upd w (:of r) task-cancel-result))))
                              (List.cons Nat (:of r) (List.nil Nat))))
    (have e2 := (i8-closed-view-fold (fire-edge res-cancelled) (i8-closed-view-fire-edge res-cancelled)
                          (tbl-scan edge-id (on-task (:of r)) (:edges (task-upd w (:of r) task-cancel-result)))
                          (task-upd w (:of r) task-cancel-result)))
    (have e3 (= (i8-closed-view (task-upd w (:of r) task-cancel-result)) (i8-closed-view w)))
    (simp only [i8-closed-view task-upd set-tasks (toks-upd (:of r) task-cancel-result tok-cancel-result (:tasks w))])
    (exact (Eq.trans e1 (Eq.trans e2 e3))))
  (case [some c]
    (cases he (Nat.beq (:epoch r) (:epoch c)))
    (case [false] (simp only [debtor-side hc he]))
    (case [true]
      (simp only [debtor-side hc he invalidate-dependents fire-waits-cancelled])
      (exact (Eq.trans (i8-closed-view-fold invalidate-id i8-closed-view-invalidate-id _ _)
                       (i8-closed-view-fold (fire-edge res-cancelled) (i8-closed-view-fire-edge res-cancelled) _ w))))))
(a/theorem i8-closed-view-cancel-debtor [rep :- Bool, w :- World, r :- RunRow] (= (i8-closed-view (cancel-debtor rep w r)) (i8-closed-view w))
  (cases hc (Bool.and rep (comp-has w (:of r))))
  (case [true] (simp only [cancel-debtor hc]))
  (case [false] (simp only [cancel-debtor hc]) (exact (i8-closed-view-debtor-side w r))))
(a/theorem i8-closed-view-drop-act [w :- World, x :- Nat] (= (i8-closed-view (drop-act w x)) (i8-closed-view w)) (rfl))
(a/theorem i8-closed-view-res-cancel [w :- World, x :- Nat] (= (i8-closed-view (res-cancel w x)) (i8-closed-view w)) (rfl))
(a/theorem i8-closed-view-cancel-run-local [w :- World, r :- RunRow, rep :- Bool]
  (= (i8-closed-view (cancel-run-local w r rep))
     (I8ClosedView.mk (tbl-upd run-key-id (:id r) run-key-down (run-keys (:runs w))) (i8-closed-task-keys (:tasks w)) (i8-closed-scope-keys (:scopes w)) (i8-closed-source-keys (:sources w))))
  (simp only [cancel-run-local])
  (have e1 := (i8-closed-view-cancel-debtor rep (cleanup-set (cancel-res (cancel-acts (run-upd w (:id r) run-cancel-row) (:id r)) r) (:id r) (cleanup-rows-of w r)) r))
  (have e2 (= (i8-closed-view (cleanup-set (cancel-res (cancel-acts (run-upd w (:id r) run-cancel-row) (:id r)) r) (:id r) (cleanup-rows-of w r)))
              (i8-closed-view (cancel-res (cancel-acts (run-upd w (:id r) run-cancel-row) (:id r)) r))))
  (rfl)
  (have e3 := (i8-closed-view-fold res-cancel i8-closed-view-res-cancel (:resources r) (cancel-acts (run-upd w (:id r) run-cancel-row) (:id r))))
  (have e4 (= (i8-closed-view (cancel-acts (run-upd w (:id r) run-cancel-row) (:id r))) (i8-closed-view (run-upd w (:id r) run-cancel-row))))
  (simp only [cancel-acts]) (exact (i8-closed-view-fold drop-act i8-closed-view-drop-act _ _))
  (have e5 (= (i8-closed-view (run-upd w (:id r) run-cancel-row))
              (I8ClosedView.mk (tbl-upd run-key-id (:id r) run-key-down (run-keys (:runs w))) (i8-closed-task-keys (:tasks w)) (i8-closed-scope-keys (:scopes w)) (i8-closed-source-keys (:sources w)))))
  (simp only [i8-closed-view run-upd set-runs (run-keys-upd-g (:id r) run-cancel-row run-key-down (fn [q :- RunRow] (Eq.refl (run-key-down (run-key q)))) (:runs w))])
  (exact (Eq.trans e1 (Eq.trans e2 (Eq.trans e3 (Eq.trans e4 e5))))))

;; ---- the escape list
(a/defn job-cid [j :- Job] (List Nat)
  (match j (jcancel r rep) (List.cons Nat r (List.nil Nat)) (jretire r) (List.nil Nat) (jclose s) (List.nil Nat)))
(a/defn cj [js :- (List Job)] (List Nat) (match js nil (List.nil Nat) (cons j t) (List.append Nat (job-cid j) (cj t))))
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

(a/theorem i8-closed-esc-mono [xs :- (List Nat), ys :- (List Nat), w :- World,
                        hx :- (forall [x :- Nat] (=> (= (reach-mem x xs) true) (= (reach-mem x ys) true)))]
  (=> (= (i8-closed xs w) true) (= (i8-closed ys w) true))
  (intro h)
  (have r := (i8-closed-rest-of xs w h)) (simp only [i8-closed-rest i8-closed-keys-ok Bool.and_eq_true] at r)
  (have a1 := (i8-closed-run-ok-esc-all xs ys (i8-closed-task-keys (:tasks w)) (i8-closed-scope-keys (:scopes w)) hx (run-keys (:runs w)) (And.left r)))
  (have hr (= (i8-closed-rest ys w) true)) (simp only [i8-closed-rest i8-closed-keys-ok a1 (And.right r) Bool.and_self])
  (exact (i8-closed-intro ys w (i8-closed-well-formed xs w h) hr)))

;; discharge: a run id whose rows are all dead (or absent) leaves the escape list
(a/defn dead-k [x :- Nat, k :- RunKey] Bool (Bool.or (Bool.not (Nat.beq (:id k) x)) (Bool.not (:alive k))))
(a/theorem i8-closed-disch [x :- Nat, xs :- (List Nat), w :- World]
  (=> (= (i8-closed (List.cons Nat x xs) w) true) (= (tbl-all (dead-k x) (run-keys (:runs w))) true) (= (i8-closed xs w) true))
  (intros h hd)
  (have r := (i8-closed-rest-of _ w h)) (simp only [i8-closed-rest i8-closed-keys-ok Bool.and_eq_true] at r)
  (have a1 (= (tbl-all (i8-closed-run-ok xs (i8-closed-task-keys (:tasks w)) (i8-closed-scope-keys (:scopes w))) (run-keys (:runs w))) true))
  (apply (tbl-all-mono2 RunKey (i8-closed-run-ok (List.cons Nat x xs) (i8-closed-task-keys (:tasks w)) (i8-closed-scope-keys (:scopes w))) (dead-k x) _ _ _ (And.left r) hd))
  (intros k p q)
  (cases ha (:alive k))
  (case [false] (simp only [i8-closed-run-ok ha Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [dead-k ha Bool.not_true Bool.or_false] at q)
    (have q2 := (bnot-true _ q))
    (simp only [i8-closed-run-ok ha reach-mem-cons q2 Bool.false_or] at p)
    (simp only [i8-closed-run-ok ha]) (exact p))
  (have hr (= (i8-closed-rest xs w) true)) (simp only [i8-closed-rest i8-closed-keys-ok a1 (And.right r) Bool.and_self])
  (exact (i8-closed-intro xs w (i8-closed-well-formed _ w h) hr)))

(a/theorem dead-upd-down [x :- Nat, ks :- (List RunKey)] (= (tbl-all (dead-k x) (tbl-upd run-key-id x run-key-down ks)) true)
  (induction ks)
  (case [nil] (simp only [tbl-upd tbl-all]))
  (case [cons k t ih]
    (cases hx (Nat.beq (run-key-id k) x))
    (case [true] (simp only [tbl-upd hx tbl-all dead-k run-key-down ih Bool.not_false Bool.or_true Bool.and_self]))
    (case [false]
      (have hx2 (= (Nat.beq (:id k) x) false)) (exact hx)
      (simp only [tbl-upd hx tbl-all dead-k hx2 ih Bool.not_false Bool.true_or Bool.and_self]))))
(a/theorem i8-closed-keys-ok-kill [xs :- (List Nat), x :- Nat, rks :- (List RunKey), tks :- (List I8ClosedTaskKey), sks :- (List I8ClosedScopeKey), xks :- (List I8ClosedSourceKey)]
  (=> (= (i8-closed-keys-ok xs rks tks sks xks) true) (= (i8-closed-keys-ok xs (tbl-upd run-key-id x run-key-down rks) tks sks xks) true))
  (intro h) (simp only [i8-closed-keys-ok Bool.and_eq_true] at h)
  (have a1 (= (tbl-all (i8-closed-run-ok xs tks sks) (tbl-upd run-key-id x run-key-down rks)) true))
  (exact (tbl-all-upd RunKey run-key-id x run-key-down (i8-closed-run-ok xs tks sks) (i8-closed-run-ok xs tks sks)
           (fn [k :- RunKey, p :- (= (i8-closed-run-ok xs tks sks k) true), q :- (= (Nat.beq (run-key-id k) x) true)] (i8-closed-run-ok-down xs tks sks k))
           (fn [k :- RunKey, p :- (= (i8-closed-run-ok xs tks sks k) true), q :- (= (Nat.beq (run-key-id k) x) false)] p)
           rks (And.left h)))
  (simp only [i8-closed-keys-ok a1 (And.right h) Bool.and_self]))

;; T14's local part, then the cancelled id leaves the escape list
(a/theorem i8-closed-cancel-run-local-x [x :- Nat, xs :- (List Nat), w :- World, r :- RunRow, rep :- Bool]
  (=> (= (i8-closed (List.cons Nat (:id r) xs) w) true) (= (i8-closed xs (cancel-run-local w r rep)) true))
  (intro h)
  (have hs := (i8-closed-well-formed _ w h))
  (have r0 := (i8-closed-rest-of _ w h)) (simp only [i8-closed-rest] at r0)
  (have e := (i8-closed-rest-mk (List.cons Nat (:id r) xs) _ _ _ _ _ (i8-closed-view-cancel-run-local w r rep)))
  (have h1 := (i8-closed-intro _ _ (well-formed-cancel-run-local w r rep hs) (Eq.trans e (i8-closed-keys-ok-kill _ (:id r) _ _ _ _ r0))))
  (have er (= (run-keys (:runs (cancel-run-local w r rep))) (tbl-upd run-key-id (:id r) run-key-down (run-keys (:runs w)))))
  (exact (congrArg (fn [k :- I8ClosedView] (:rks k)) (i8-closed-view-cancel-run-local w r rep)))
  (have hd (= (tbl-all (dead-k (:id r)) (run-keys (:runs (cancel-run-local w r rep)))) true))
  (rw [er]) (exact (dead-upd-down (:id r) _))
  (exact (i8-closed-disch (:id r) xs _ h1 hd)))

;; T13 (t13-retire-with-subtree) and T16 (t16-close-with-subtree): the subtree's owned runs join the escape list
(a/theorem i8-closed-view-clear-comp-run [w :- World, r :- RunRow] (= (i8-closed-view (clear-comp-run w r)) (i8-closed-view w))
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
        (simp only [clear-task-run ht hr i8-closed-view task-upd set-tasks
                    (toks-upd (:of r) task-clear-run (fn [q :- TaskRow] (Eq.refl (i8-closed-task-key q))) (:tasks w))])))))
(a/theorem i8-closed-scope-del-fold [xs :- (List Nat), sub :- (List Nat)]
  (forall [w :- World] (=> (= (i8-closed xs w) true) (= (i8-closed xs (nat-fold scope-del w sub)) true)))
  (induction sub)
  (case [nil] (intros w h) (simp only [nat-fold]) (exact h))
  (case [cons x t ih]
    (intros w h) (simp only [nat-fold])
    (exact (ih _ (i8-closed-intro xs _ (well-formed-scope-del w x (i8-closed-well-formed xs w h)) (i8-closed-rest-scope-del xs w x (i8-closed-rest-of xs w h)))))))
(a/theorem i8-closed-remove-if-empty-x [xs :- (List Nat), w :- World, sub :- (List Nat)]
  (=> (= (i8-closed xs w) true) (= (i8-closed xs (remove-if-empty w sub)) true))
  (intro h)
  (cases he (subtree-empty w sub))
  (case [false] (simp only [remove-if-empty he]) (exact h))
  (case [true] (simp only [remove-if-empty he]) (exact (i8-closed-scope-del-fold xs sub w h))))
(a/theorem i8-closed-t13-retire-with-subtree-x [xs :- (List Nat), w :- World, r :- RunRow, sub :- (List Nat)]
  (=> (= (i8-closed xs w) true) (= (i8-closed (List.append Nat xs (owned-runs w sub)) (t13-retire-with-subtree w r sub)) true))
  (intro h)
  (have hs := (i8-closed-well-formed xs w h))
  (have e := (i8-closed-view-clear-comp-run w r))
  (have h1 := (i8-closed-of-view xs w _ (well-formed-clear-comp-run w r hs) e h))
  (have er (= (run-keys (:runs (clear-comp-run w r))) (run-keys (:runs w)))) (exact (congrArg (fn [k :- I8ClosedView] (:rks k)) e))
  (have et (= (i8-closed-task-keys (:tasks (clear-comp-run w r))) (i8-closed-task-keys (:tasks w)))) (exact (congrArg (fn [k :- I8ClosedView] (:tks k)) e))
  (have cv (= (tbl-all (cov8 (owned-runs w sub) sub (i8-closed-task-keys (:tasks (clear-comp-run w r)))) (run-keys (:runs (clear-comp-run w r)))) true))
  (rw [er, et]) (exact (cov-owned w sub hs))
  (have h2 := (i8-closed-close-local-cov xs (owned-runs w sub) _ sub h1 cv))
  (have h3 := (i8-closed-intro _ _ (well-formed-run-del _ (:id r) (i8-closed-well-formed _ _ h2)) (i8-closed-rest-run-del _ _ (:id r) (i8-closed-rest-of _ _ h2))))
  (have h4 := (i8-closed-intro _ _ (well-formed-cleanup-del _ (:id r) (i8-closed-well-formed _ _ h3)) (i8-closed-rest-of _ _ h3)))
  (simp only [t13-retire-with-subtree])
  (exact (i8-closed-remove-if-empty-x _ _ sub h4)))
(a/theorem i8-closed-t16-close-with-subtree-x [xs :- (List Nat), w :- World, sub :- (List Nat)]
  (=> (= (i8-closed xs w) true) (= (i8-closed (List.append Nat xs (owned-runs w sub)) (t16-close-with-subtree w sub)) true))
  (intro h) (simp only [t16-close-with-subtree]) (exact (i8-closed-remove-if-empty-x _ _ sub (i8-closed-close-local xs w sub h))))

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
  (=> (= (run-find w rid) (Option.none RunRow)) (= (tbl-all (dead-k rid) (run-keys (:runs w))) true))
  (intro hf)
  (have n := (ne-of-none w rid hf)) (simp only [run-gone-rest] at n)
  (rw [all-run-keys])
  (apply (tbl-all-mono RunRow (ne-ok rid) (on-rkey (dead-k rid)) _ (:runs w) n))
  (intros q p) (simp only [ne-ok] at p) (simp only [on-rkey dead-k run-key p Bool.true_or]))
(a/theorem dead-of-find [w :- World, rid :- Nat, r :- RunRow]
  (=> (= (well-formed w) true) (= (run-find w rid) (Option.some RunRow r)) (= (run-alive r) false)
      (= (tbl-all (dead-k rid) (run-keys (:runs w))) true))
  (intros hs hf ha)
  (have m := (tbl-find-mem RunRow run-id rid r (:runs w) hf))
  (have i (= (run-id r) rid)) (exact (tbl-find-id RunRow run-id rid r (:runs w) hf))
  (have nd (= (Bool.not (run-alive r)) true)) (simp only [ha Bool.not_false])
  (have u := (uniq-all RunRow run-id (fn [q :- RunRow] (Bool.not (run-alive q))) r (:runs w) (lit-runs-nodup w hs) m nd))
  (rw [i] at u)
  (rw [all-run-keys])
  (apply (tbl-all-mono RunRow _ (on-rkey (dead-k rid)) _ (:runs w) u))
  (intros q p) (simp only [same-id-then] at p) (simp only [on-rkey dead-k run-key]) (exact p))
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

(a/theorem i8-closed-job-cancel [base :- (List Nat), w :- World, rid :- Nat, rep :- Bool, t :- (List Job)]
  (=> (= (i8-closed (List.append Nat base (cj (List.cons Job (Job.jcancel rid rep) t))) w) true)
      (= (i8-closed (esc8 base w (Job.jcancel rid rep) t) (job-apply w (Job.jcancel rid rep))) true))
  (intro h)
  (have hs := (i8-closed-well-formed _ w h))
  (have h0 := (i8-closed-esc-mono (List.append Nat base (cj (List.cons Job (Job.jcancel rid rep) t))) (List.cons Nat rid (List.append Nat base (cj t))) w
                (fn [x :- Nat, q :- (= (reach-mem x (List.append Nat base (cj (List.cons Job (Job.jcancel rid rep) t)))) true)]
                  (cancel-esc x rid rep base t q)) h))
  (apply (i8-closed-esc-mono (List.append Nat base (cj t)) (esc8 base w (Job.jcancel rid rep) t) (job-apply w (Job.jcancel rid rep))
           (fn [x :- Nat, q :- (= (reach-mem x (List.append Nat base (cj t))) true)] (esc-tail x base w (Job.jcancel rid rep) t q))))
  (cases hf (run-find w rid))
  (case [none]
    (simp only [job-apply hf])
    (exact (i8-closed-disch rid (List.append Nat base (cj t)) w h0 (dead-of-none w rid hf))))
  (case [some r]
    (cases ha (run-alive r))
    (case [false]
      (simp only [job-apply hf ha])
      (exact (i8-closed-disch rid (List.append Nat base (cj t)) w h0 (dead-of-find w rid r hs hf ha))))
    (case [true]
      (have i (= (:id r) rid)) (exact (tbl-find-id RunRow run-id rid r (:runs w) hf))
      (simp only [job-apply hf ha])
      (rw [← i] at h0)
      (exact (i8-closed-cancel-run-local-x rid (List.append Nat base (cj t)) w r rep h0)))))

(a/theorem i8-closed-job-retire [base :- (List Nat), w :- World, rid :- Nat, t :- (List Job)]
  (=> (= (i8-closed (List.append Nat base (cj (List.cons Job (Job.jretire rid) t))) w) true)
      (= (i8-closed (esc8 base w (Job.jretire rid) t) (job-apply w (Job.jretire rid))) true))
  (intro h)
  (have h0 (= (i8-closed (List.append Nat base (cj t)) w) true)) (exact h)
  (cases hf (run-find w rid))
  (case [none]
    (simp only [job-apply hf])
    (exact (i8-closed-esc-mono (List.append Nat base (cj t)) (esc8 base w (Job.jretire rid) t) w
             (fn [x :- Nat, q :- (= (reach-mem x (List.append Nat base (cj t))) true)] (esc-tail x base w (Job.jretire rid) t q)) h0)))
  (case [some r]
    (cases hr (retirable r))
    (case [false]
      (simp only [job-apply hf hr])
      (exact (i8-closed-esc-mono (List.append Nat base (cj t)) (esc8 base w (Job.jretire rid) t) w
               (fn [x :- Nat, q :- (= (reach-mem x (List.append Nat base (cj t))) true)] (esc-tail x base w (Job.jretire rid) t q)) h0)))
    (case [true]
      (have e (= (job-next w (Job.jretire rid)) (cancel-jobs (owned-runs w (scope-subtree w (:scope r)))))) (simp only [job-next hf hr])
      (have h1 := (i8-closed-t13-retire-with-subtree-x (List.append Nat base (cj t)) w r (scope-subtree w (:scope r)) h0))
      (simp only [job-apply hf hr retire-run])
      (exact (i8-closed-esc-mono _ (esc8 base w (Job.jretire rid) t) (t13-retire-with-subtree w r (scope-subtree w (:scope r)))
               (fn [x :- Nat, q :- (= (reach-mem x (List.append Nat (List.append Nat base (cj t)) (owned-runs w (scope-subtree w (:scope r))))) true)]
                 (esc-owned x base w (Job.jretire rid) t _ e q)) h1)))))

(a/theorem i8-closed-job-close [base :- (List Nat), w :- World, s :- Nat, t :- (List Job)]
  (=> (= (i8-closed (List.append Nat base (cj (List.cons Job (Job.jclose s) t))) w) true)
      (= (i8-closed (esc8 base w (Job.jclose s) t) (job-apply w (Job.jclose s))) true))
  (intro h)
  (have h0 (= (i8-closed (List.append Nat base (cj t)) w) true)) (exact h)
  (cases hc (scope-has w s))
  (case [false]
    (simp only [job-apply hc])
    (exact (i8-closed-esc-mono (List.append Nat base (cj t)) (esc8 base w (Job.jclose s) t) w
             (fn [x :- Nat, q :- (= (reach-mem x (List.append Nat base (cj t))) true)] (esc-tail x base w (Job.jclose s) t q)) h0)))
  (case [true]
    (have e (= (job-next w (Job.jclose s)) (cancel-jobs (owned-runs w (scope-subtree w s))))) (simp only [job-next hc])
    (have h1 := (i8-closed-t16-close-with-subtree-x (List.append Nat base (cj t)) w (scope-subtree w s) h0))
    (simp only [job-apply hc close-scope-local])
    (exact (i8-closed-esc-mono _ (esc8 base w (Job.jclose s) t) (t16-close-with-subtree w (scope-subtree w s))
             (fn [x :- Nat, q :- (= (reach-mem x (List.append Nat (List.append Nat base (cj t)) (owned-runs w (scope-subtree w s)))) true)]
               (esc-owned x base w (Job.jclose s) t _ e q)) h1))))

(a/theorem i8-closed-job [base :- (List Nat), w :- World, j :- Job, t :- (List Job)]
  (=> (= (i8-closed (List.append Nat base (cj (List.cons Job j t))) w) true)
      (= (i8-closed (List.append Nat base (cj (List.append Job t (job-next w j)))) (job-apply w j)) true))
  (intro h)
  (cases j)
  (case [jcancel rid rep] (exact (i8-closed-job-cancel base w rid rep t h)))
  (case [jretire rid] (exact (i8-closed-job-retire base w rid t h)))
  (case [jclose s] (exact (i8-closed-job-close base w s t h))))

(a/theorem i8-closed-cascade [base :- (List Nat), fuel :- (List Nat)]
  (forall [w :- World, js :- (List Job)]
    (=> (= (i8-closed (List.append Nat base (cj js)) w) true)
        (= (i8-closed (List.append Nat base (cj (:rest (cascade fuel w js)))) (:world (cascade fuel w js))) true)))
  (induction fuel)
  (case [nil] (intros w js h) (simp only [cascade]) (exact h))
  (case [cons u f ih]
    (intros w js h)
    (cases js)
    (case [nil] (simp only [cascade]) (exact h))
    (case [cons j t] (simp only [cascade]) (exact (ih _ _ (i8-closed-job base w j t h))))))

(a/theorem esc-base [x :- Nat, base :- (List Nat), js :- (List Job)]
  (=> (= (reach-mem x base) true) (= (reach-mem x (List.append Nat base (cj js))) true))
  (intro h) (simp only [reach-mem-append h Bool.true_or]))
(a/theorem esc-done [x :- Nat, base :- (List Nat)]
  (=> (= (reach-mem x (List.append Nat base (cj (List.nil Job)))) true) (= (reach-mem x base) true))
  (intro h) (simp only [reach-mem-append cj reach-mem Bool.or_false] at h) (exact h))
;; a cascade whose worklist empties keeps i8-closed (the escape list of pending cancels is then empty)
(a/theorem i8-closed-cascade-done [x8s :- (List Nat), w :- World, js :- (List Job)]
  (=> (= (cascade-done w js) true) (= (i8-closed x8s w) true) (= (i8-closed x8s (run-cascade w js)) true))
  (intros hd h)
  (have h0 := (i8-closed-esc-mono x8s (List.append Nat x8s (cj js)) w (fn [x :- Nat, q :- (= (reach-mem x x8s) true)] (esc-base x x8s js q)) h))
  (have c := (i8-closed-cascade x8s (cascade-fuel w js) w js h0))
  (have d := (jobs-nil (:rest (cascade-run w js)) hd))
  (have d2 (= (:rest (cascade (cascade-fuel w js) w js)) (List.nil Job))) (exact d)
  (rw [d2] at c)
  (exact (i8-closed-esc-mono _ x8s _ (fn [x :- Nat, q :- (= (reach-mem x (List.append Nat x8s (cj (List.nil Job)))) true)] (esc-done x x8s q)) c)))
(a/theorem i8-closed-run-cascade-aa [x8s :- (List Nat), w :- World, js :- (List Job)]
  (=> (= (acts-alive w) true) (= (i8-closed x8s w) true) (= (i8-closed x8s (run-cascade w js)) true))
  (intros ha h) (exact (i8-closed-cascade-done x8s w js (cascade-done-ok w js (i8-closed-well-formed x8s w h) ha) h)))
(a/theorem i8-closed-run-cascade-acts-parked [x8s :- (List Nat), w :- World, js :- (List Job)]
  (=> (= (acts-parked w) true) (= (i8-closed x8s w) true) (= (i8-closed x8s (run-cascade w js)) true))
  (intros hga h) (exact (i8-closed-cascade-done x8s w js (cascade-done-acts-parked w js hga) h)))
;; ---- i8-closed's exempt form, uniform names (spindel.v2.pres.exempt): the escape list x8s holds the
;; deferred violations of I8; `inv` uses i8-closed [] (chain-to-i8-closed)
(exempt/defexempt 'i8-closed
  :form "i8-closed x8s w" :ids "run ids: alive runs of tasks owned by a closed scope" :commit "i8-closed [] (chain-to-i8-closed)"
  :mono 'i8-closed-esc-mono                           ; a longer escape list is weaker
  :break '{close-local i8-closed-close-local}         ; closing a subtree: its tasks' alive runs escape
  :repair '{cancel-job i8-closed-job-cancel}          ; a cancel job kills its run (one loop step)
  :loop 'i8-closed-cascade                            ; escape list = base ++ runs of the pending cancel jobs
  :exit 'i8-closed-cascade-done)                      ; the worklist is empty at the end (P4)

;; ===========================================================================
;; Part G. Owners of new tasks and sources; task owners that change
;; ===========================================================================

(a/theorem scopes-nodup8 [w :- World] (=> (= (well-formed w) true) (= (nat-nodup (tbl-ids scope-id (:scopes w))) true))
  (intro h) (have u := (ids-unique-of w h)) (simp only [all-ids] at u) (exact (nat-nodup-app-left _ _ u)))
(a/theorem sclosed-has [x :- Nat, ss :- (List ScopeRow)] (=> (= (sclosed (i8-closed-scope-keys ss) x) true) (= (tbl-has scope-id x ss) true))
  (induction ss)
  (case [nil] (intro h) (simp only [i8-closed-scope-keys sclosed tbl-any] at h) (cases h))
  (case [cons s t ih]
    (intro h)
    (simp only [i8-closed-scope-keys sclosed tbl-any Bool.or_eq_true] at h)
    (cases h)
    (case [inl a]
      (simp only [sclosed-k i8-closed-scope-key Bool.and_eq_true] at a)
      (have e (= (Nat.beq (scope-id s) x) true)) (exact (And.left a))
      (simp only [tbl-has e]))
    (case [inr b]
      (have q := (ih b))
      (cases e (Nat.beq (scope-id s) x))
      (case [true] (simp only [tbl-has e]))
      (case [false] (simp only [tbl-has e]) (exact q)))))
(a/theorem sclosed-zero [w :- World] (=> (= (well-formed w) true) (= (sclosed (i8-closed-scope-keys (:scopes w)) 0) false))
  (intro h)
  (cases hc (sclosed (i8-closed-scope-keys (:scopes w)) 0))
  (case [false] (rfl))
  (case [true] (have p := (scope-pos w 0 h (sclosed-has 0 (:scopes w) hc))) (simp only [Nat.beq_refl] at p) (cases p)))
(a/theorem no-closed-of [x :- Nat, ss :- (List ScopeRow)]
  (=> (= (tbl-all (same-id-then scope-id x (fn [q :- ScopeRow] (:open q))) ss) true) (= (sclosed (i8-closed-scope-keys ss) x) false))
  (induction ss)
  (case [nil] (intro h) (simp only [i8-closed-scope-keys sclosed tbl-any]))
  (case [cons s t ih]
    (intro h)
    (simp only [tbl-all Bool.and_eq_true] at h)
    (have r := (ih (And.right h)))
    (simp only [sclosed] at r)
    (have a := (And.left h))
    (simp only [same-id-then Bool.or_eq_true] at a)
    (have k (= (sclosed-k x (i8-closed-scope-key s)) false))
    (cases a)
    (case [inl b] (have b2 := (bnot-true _ b)) (have b3 (= (Nat.beq (:id s) x) false)) (exact b2) (simp only [sclosed-k i8-closed-scope-key b3 Bool.false_and]))
    (case [inr c] (simp only [sclosed-k i8-closed-scope-key c Bool.not_true Bool.and_false]))
    (simp only [i8-closed-scope-keys sclosed tbl-any k r Bool.or_self])))
(a/theorem tclosed-absent [c :- Nat, ts :- (List TaskRow), sks :- (List I8ClosedScopeKey)]
  (=> (= (nat-mem c (tbl-ids task-id ts)) false) (= (tclosed (i8-closed-task-keys ts) sks c) false))
  (induction ts)
  (case [nil] (intro h) (simp only [i8-closed-task-keys tclosed tbl-any]))
  (case [cons t tl ih]
    (intro h)
    (cases hb (Nat.beq (task-id t) c))
    (case [true] (simp [tbl-ids nat-mem hb] at h))
    (case [false]
      (simp only [tbl-ids nat-mem hb] at h)
      (have r := (ih h)) (simp only [tclosed] at r)
      (have e (= (Nat.beq (:id t) c) false)) (exact hb)
      (simp only [i8-closed-task-keys tclosed tbl-any tclosed-k i8-closed-task-key e r Bool.false_and Bool.or_self]))))
(a/theorem open-not-closed [w :- World, s :- Nat] (=> (= (well-formed w) true) (= (scope-open-at w s) true) (= (sclosed (i8-closed-scope-keys (:scopes w)) s) false))
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
(a/theorem comp-not-tclosed [w :- World, c :- Nat, sks :- (List I8ClosedScopeKey)]
  (=> (= (well-formed w) true) (= (comp-has w c) true) (= (tclosed (i8-closed-task-keys (:tasks w)) sks c) false))
  (intros h hc)
  (have n := (comp-not-task w c h hc))
  (exact (tclosed-absent c (:tasks w) sks n)))
(a/theorem tasks-below8 [w :- World] (=> (= (well-formed w) true) (= (tbl-all (id-in-range (:next-id w)) (tbl-ids task-id (:tasks w))) true))
  (intro h) (have b := (ids-below-of w h)) (simp only [all-ids tbl-all-nat-app Bool.and_eq_true] at b) (exact (And.left (And.right (And.right b)))))
(a/theorem tclosed-fresh [w :- World, sks :- (List I8ClosedScopeKey)] (=> (= (well-formed w) true) (= (tclosed (i8-closed-task-keys (:tasks w)) sks (:next-id w)) false))
  (intro h) (exact (tclosed-absent _ _ sks (range-not-mem _ _ (tasks-below8 w h)))))
(a/theorem comp-not-sclosed [w :- World, c :- Nat] (=> (= (well-formed w) true) (= (comp-has w c) true) (= (sclosed (i8-closed-scope-keys (:scopes w)) c) false))
  (intros h hc)
  (cases hs (sclosed (i8-closed-scope-keys (:scopes w)) c))
  (case [false] (rfl))
  (case [true]
    (have u := (ids-unique-of w h)) (simp only [all-ids] at u)
    (have hm (= (nat-mem c (tbl-ids scope-id (:scopes w))) true)) (rw [nat-mem-ids]) (exact (sclosed-has c (:scopes w) hs))
    (have hm2 (= (nat-mem c (tbl-ids comp-id (:comps w))) true)) (rw [nat-mem-ids]) (exact hc)
    (have d := (nodup-app-disj c _ _ u hm))
    (simp only [nat-mem-app Bool.or_eq_false_iff] at d)
    (have d1 := (And.left d)) (rw [hm2] at d1) (cases d1)))

;; ---- T4: spawn rows with an owner that is not a closed scope
(a/theorem i8-closed-spawn-rows-hand [x8s :- (List Nat), w :- World, owner :- Nat, inputs :- (List Nat), loc :- Bool]
  (=> (= (sclosed (i8-closed-scope-keys (:scopes w)) owner) false) (= (i8-closed x8s w) true) (= (i8-closed x8s (spawn-rows w owner inputs loc)) true))
  (intros ho h)
  (have hs := (i8-closed-well-formed x8s w h))
  (have h1 := (i8-closed-task-ins x8s w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs loc) (rfl) ho h))
  (have tf := (tclosed-fresh w (i8-closed-scope-keys (:scopes w)) hs))
  (have tc (= (tclosed (i8-closed-task-keys (:tasks (bump (task-ins w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs loc)))))
                       (i8-closed-scope-keys (:scopes (bump (task-ins w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs loc))))) (:next-id w)) false))
  (simp only [tclosed] at tf)
  (simp only [bump set-next-id task-ins set-tasks tbl-ins i8-closed-task-keys tclosed tbl-any tclosed-k i8-closed-task-key new-task-row ho tf Bool.and_false Bool.false_or])
  (simp only [spawn-rows])
  (exact (i8-closed-add-run-scope-hand x8s _ (:next-id w) 0 _ 0 tc h1)))
(a/theorem owner-ok8 [w :- World, r :- RunRow]
  (=> (= (well-formed w) true) (= (run-cur-closed w r) false) (= (sclosed (i8-closed-scope-keys (:scopes w)) (spawn-owner w r)) false))
  (intros h hc)
  (cases hi (in-comp w r))
  (case [true] (simp only [spawn-owner hi]) (exact (comp-not-sclosed w (:of r) h hi)))
  (case [false]
    (simp only [spawn-owner hi])
    (simp only [run-cur-closed hi Bool.not_false Bool.true_and] at hc)
    (exact (open-not-closed w (cur-scope w r) h (bnot-false _ hc)))))
(a/theorem source-owner-ok8 [w :- World, r :- RunRow]
  (=> (= (well-formed w) true) (= (run-cur-closed w r) false) (= (sclosed (i8-closed-scope-keys (:scopes w)) (source-owner-in-run w r)) false))
  (intros h hc)
  (have e (= (source-owner-in-run w r) (spawn-owner w r))) (rfl)
  (rw [e]) (exact (owner-ok8 w r h hc)))
(a/theorem cur-of-tok [w :- World, st :- Nat, r :- RunRow]
  (=> (= (cur-closed w st) false) (= (tok-run w st) (Option.some RunRow r)) (= (run-cur-closed w r) false))
  (intros h ht) (simp only [cur-closed ht opt-test] at h) (exact h))
(a/theorem bshut-cur [w :- World, st :- Nat] (=> (= (create-in-scope-refused w st) false) (= (cur-closed w st) false))
  (intro h) (simp only [create-in-scope-refused Bool.or_eq_false_iff] at h) (exact (And.right h)))

;; ---- task owners that change: detach (an open scope, Q10) and Rule R's detach (0)
(a/defn tk-own [o :- Nat, k :- I8ClosedTaskKey] I8ClosedTaskKey (I8ClosedTaskKey.mk (:id k) o))
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
(a/theorem i8-closed-task-owner [x8s :- (List Nat), w :- World, x :- Nat, f :- (=> TaskRow TaskRow), o :- Nat,
                          hf :- (forall [t :- TaskRow] (= (task-id (f t)) (task-id t))),
                          hk :- (forall [t :- TaskRow] (= (i8-closed-task-key (f t)) (tk-own o (i8-closed-task-key t))))]
  (=> (= (sclosed (i8-closed-scope-keys (:scopes w)) o) false) (= (i8-closed x8s w) true) (= (i8-closed x8s (task-upd w x f)) true))
  (intros ho h)
  (have r := (i8-closed-rest-of x8s w h)) (simp only [i8-closed-rest i8-closed-keys-ok Bool.and_eq_true] at r)
  (have e := (toks-upd-g x f (tk-own o) hk (:tasks w)))
  (have ht (forall [t :- Nat] (=> (= (tclosed (tbl-upd i8-closed-task-key-id x (tk-own o) (i8-closed-task-keys (:tasks w))) (i8-closed-scope-keys (:scopes w)) t) true)
                                   (= (tclosed (i8-closed-task-keys (:tasks w)) (i8-closed-scope-keys (:scopes w)) t) true))))
  (intros t q)
  (simp only [tclosed] at q) (simp only [tclosed])
  (apply (any8-upd I8ClosedTaskKey i8-closed-task-key-id x (tk-own o) (tclosed-k (i8-closed-scope-keys (:scopes w)) t) _ (i8-closed-task-keys (:tasks w)) q))
  (intros k p) (simp only [tclosed-k tk-own ho Bool.and_false] at p) (cases p)
  (have a1 := (i8-closed-run-ok-all-mono x8s _ _ _ _ ht _ (And.left r)))
  (have hr (= (i8-closed-rest x8s (task-upd w x f)) true)) (simp only [i8-closed-rest i8-closed-keys-ok task-upd set-tasks e a1 (And.right r) Bool.and_self])
  (exact (i8-closed-intro x8s _ (well-formed-task-upd w x f hf (i8-closed-well-formed x8s w h)) hr)))
(a/theorem tok-detach [t :- TaskRow] (= (i8-closed-task-key (task-detach-row t)) (tk-own 0 (i8-closed-task-key t))) (rfl))
(a/theorem tok-set-owner [s :- Nat, t :- TaskRow] (= (i8-closed-task-key (task-set-owner s t)) (tk-own s (i8-closed-task-key t))) (rfl))
(a/theorem i8-closed-task-detach [x8s :- (List Nat), w :- World, x :- Nat]
  (=> (= (i8-closed x8s w) true) (= (i8-closed x8s (task-upd w x task-detach-row)) true))
  (intro h) (exact (i8-closed-task-owner x8s w x task-detach-row 0 task-detach-row-id tok-detach (sclosed-zero w (i8-closed-well-formed x8s w h)) h)))

(swap! (:renames G8) assoc 'well-formed-task-ins-fresh 'i8-closed-task-ins 'well-formed-source-ins-fresh 'i8-closed-source-ins 'well-formed-run-ins-fresh 'i8-closed-run-ins
       'well-formed-close-local 'i8-closed-close-local)

(a/theorem tick-park-alive8 [r :- RunRow] (= (run-alive (run-tick-park r)) true) (simp [run-alive run-tick-park act-parked act-done]))
(a/theorem park-alive8 [r :- RunRow] (= (run-alive (run-park-row r)) true) (simp [run-alive run-park-row act-parked act-done]))

;; ---- KA k: every run row with id k is alive (the awaiting run, through the await's wiring and fills)
(a/defn awaiting-run-alive-rest [k8a :- Nat, w :- World] Bool (tbl-all (run-ok-for k8a) (:runs w)))
(a/defn awaiting-run-alive [k8a :- Nat, w :- World] Bool (Bool.and (well-formed w) (awaiting-run-alive-rest k8a w)))
(a/theorem awaiting-run-alive-well-formed [k8a :- Nat, w :- World] (=> (= (awaiting-run-alive k8a w) true) (= (well-formed w) true))
  (intro h) (simp only [awaiting-run-alive Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem awaiting-run-alive-rest-of [k8a :- Nat, w :- World] (=> (= (awaiting-run-alive k8a w) true) (= (awaiting-run-alive-rest k8a w) true))
  (intro h) (simp only [awaiting-run-alive Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem awaiting-run-alive-intro [k8a :- Nat, w :- World] (=> (= (well-formed w) true) (= (awaiting-run-alive-rest k8a w) true) (= (awaiting-run-alive k8a w) true))
  (intros h1 h2) (simp only [awaiting-run-alive h1 h2 Bool.and_self]))
(a/theorem awaiting-run-alive-parts [k8a :- Nat, w :- World]
  (=> (= (awaiting-run-alive k8a w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (awaiting-run-alive-well-formed k8a w h))))
(a/theorem awaiting-run-alive-run-upd [k8a :- Nat, w :- World, x :- Nat, f :- (=> RunRow RunRow),
                       hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                       hk :- (forall [r :- RunRow] (= (run-alive (f r)) (run-alive r)))]
  (=> (= (awaiting-run-alive k8a w) true) (= (awaiting-run-alive k8a (run-upd w x f)) true))
  (intro h)
  (have r0 := (awaiting-run-alive-rest-of k8a w h)) (simp only [awaiting-run-alive-rest] at r0)
  (have r1 (= (awaiting-run-alive-rest k8a (run-upd w x f)) true))
  (simp only [awaiting-run-alive-rest run-upd set-runs])
  (apply (tbl-all-upd RunRow run-id x f (run-ok-for k8a) (run-ok-for k8a) _ _ (:runs w) r0))
  (intros q p e) (have i (= (:id (f q)) (:id q))) (exact (hf q)) (simp only [run-ok-for i (hk q)]) (simp only [run-ok-for] at p) (exact p)
  (intros q p e) (exact p)
  (exact (awaiting-run-alive-intro k8a _ (well-formed-run-upd w x f hf (awaiting-run-alive-well-formed k8a w h)) r1)))
(def KA (mk-bundle 'awaiting-run-alive '[k8a :- Nat] "awaiting-run-alive-" {'well-formed-run-upd ['(fn [r :- RunRow] (Eq.refl (run-alive r))) 4]}))
(swap! (:renames KA) assoc 'well-formed-parts 'awaiting-run-alive-parts 'well-formed-run-upd 'awaiting-run-alive-run-upd)
(doseq [o '[well-formed-scope-upd well-formed-pub-upd well-formed-source-upd well-formed-resource-upd well-formed-cleanup-upd well-formed-cleanup-del well-formed-cleanup-ins well-formed-set-pins
            well-formed-resource-del well-formed-scope-del well-formed-act-upd well-formed-task-upd well-formed-comp-upd well-formed-bump well-formed-edge-upd well-formed-drop-cred-edges well-formed-drop-act
            well-formed-drop-edges well-formed-comp-del-unref well-formed-act-ins-fresh well-formed-task-ins-fresh well-formed-comp-ins-fresh well-formed-scope-ins-fresh
            well-formed-resource-ins-fresh well-formed-source-ins-fresh well-formed-fork-ins-fresh well-formed-insert-edge-fresh well-formed-fork-del]]
  (prim! KA o nil))
(a/theorem awaiting-run-alive-rest-same [k8a :- Nat, w :- World, w2 :- World] (=> (= (:runs w2) (:runs w)) (= (awaiting-run-alive-rest k8a w2) (awaiting-run-alive-rest k8a w)))
  (intro e) (simp only [awaiting-run-alive-rest e]))
(prim! KA 'well-formed-remove-edge '(Eq.trans (awaiting-run-alive-rest-same k8a w (remove-edge w x) (runs-remove-edge w x)) R))
(prim! KA 'well-formed-mark-edge '(Eq.trans (awaiting-run-alive-rest-same k8a w (mark-edge w x) (runs-mark-edge w x)) R))
(prim! KA 'well-formed-unmark-edge '(Eq.trans (awaiting-run-alive-rest-same k8a w (unmark-edge w x) (runs-unmark-edge w x)) R))
(prim! KA 'well-formed-run-del '(all-sub-del RunRow (run-ok-for k8a) run-id x (:runs w) R))
;; awaiting-run-alive on the generic tree: waking the run keeps it alive (a site); the three lemmas the await needs
(tree/part! KA
  :sites '{[well-formed-run-upd run-wake] (awaiting-run-alive-run-upd k8a w x run-wake hf run-wake-alive h0)})
(tree/restate! KA '[well-formed-await-pre well-formed-await-wire well-formed-fast-fill])

;; ===========================================================================
;; C0: a link owned by the root scope (a stream's first tail, a pull link in a run, the next pull link
;; of a realization, an appended tail) is created only while the root scope is open: transition's `require-root-open`
;; (engine.clj) refuses the item otherwise; the transitions below take the gate's fact
;; ===========================================================================
(a/theorem root-ok-any [b :- Bool, w :- World] (=> (= (root-open-if true w) true) (= (root-open-if b w) true))
  (intro h) (simp only [root-open-if Bool.not_true Bool.false_or] at h) (simp only [root-open-if h Bool.or_true]))
(a/theorem root-ok-true [w :- World] (=> (= (root-open-if true w) true) (= (scope-open-at w root-scope-id) true))
  (intro h) (simp only [root-open-if Bool.not_true Bool.false_or] at h) (exact h))

(a/theorem i8-closed-source-ok-root-link [w :- World, id :- Nat, t :- Nat]
  (=> (= (well-formed w) true) (= (scope-open-at w root-scope-id) true) (= (i8-closed-source-ok (i8-closed-scope-keys (:scopes w)) (i8-closed-source-key (new-link id root-scope-id t))) true))
  (intros h ho)
  (simp only [i8-closed-source-ok i8-closed-source-key new-link (open-not-closed w root-scope-id h ho) Bool.not_false Bool.or_true]))

;; ---- the facts the table passes, from the guards (each a projection of a transition's guard)
(a/theorem root-ok-of-true [b :- Bool, w :- World] (=> (= b true) (= (root-open-if b w) true) (= (scope-open-at w root-scope-id) true))
  (intros hb h) (rw [hb] at h) (exact (root-ok-true w h)))
(a/theorem i8-closed-source-ok-new-source [w :- World, id :- Nat, o :- Nat, kind :- Nat, v :- Nat]
  (=> (= (sclosed (i8-closed-scope-keys (:scopes w)) o) false) (= (i8-closed-source-ok (i8-closed-scope-keys (:scopes w)) (i8-closed-source-key (new-source id o kind v))) true))
  (intro ho) (simp only [i8-closed-source-ok i8-closed-source-key new-source ho Bool.not_false Bool.or_true]))
(a/theorem i8-closed-source-ok-link-open [w :- World, id :- Nat, s :- Nat, t :- Nat]
  (=> (= (well-formed w) true) (= (scope-open-at w s) true) (= (i8-closed-source-ok (i8-closed-scope-keys (:scopes w)) (i8-closed-source-key (new-link id s t))) true))
  (intros h ho) (simp only [i8-closed-source-ok i8-closed-source-key new-link (open-not-closed w s h ho) Bool.not_false Bool.or_true]))
(a/theorem detach-open [w :- World, t :- TaskRow, s :- Nat] (=> (= (detach-ok w t s) true) (= (scope-open-at w s) true))
  (intro hg) (simp only [detach-ok Bool.and_eq_true] at hg) (exact (And.left (And.right (And.right hg)))))
;; take-park's edits before the run update keep the run rows
(a/theorem take-park-ok [w :- World, r :- RunRow, x :- Nat, k :- Nat]
  (=> (= (tbl-all (run-ok-for (:id r)) (:runs w)) true)
      (= (tbl-all (run-ok-for (:id r)) (:runs (insert-edge-checked (bump (act-ins w (take-act w r k))) (take-edge r (:next-id w) x)))) true))
  (intro o) (rw [runs-iec]) (exact o))
;; T-slice-exit: the exiting run has no activation (acts-parked), so its update keeps acts-parked
(a/theorem slice-exit-free [w :- World, rid :- Nat, r :- RunRow]
  (=> (= (run-find w rid) (Option.some RunRow r)) (= (exit-ready r) true) (= (acts-parked w) true)
      (= (tbl-any (act-of-run rid) (:acts w)) false))
  (intros hf hg hga)
  (have p := (find-facts w rid r hf))
  (simp only [exit-ready Bool.and_eq_true] at hg)
  (have hn := (no-act-bad w r hga (And.left p) (done-not-good r (And.left hg))))
  (rw [(And.right p)] at hn)
  (exact hn))

(a/theorem i8-closed-source-key-consume [s :- SourceRow] (= (i8-closed-source-key (source-consume s)) (i8-closed-source-key s))
  (cases ha (source-available s)) (all_goals (cases h (Nat.beq (:kind s) sk-mailbox)))
  (all_goals (simp only [source-consume i8-closed-source-key ha h])))
;; ===========================================================================
;; Part H. i8-closed on the generic tree (spindel.v2.pres.tree): its table, its own proofs, its restatements
;; ===========================================================================

(tree/part! G8
  ;; ---- the part's own proofs (content)
  :over '{well-formed-run-cascade      i8-closed-run-cascade-acts-parked     ; the cascade: break, repair, ghost escape list, exit by P4 (Part F)
          well-formed-add-run-scope    i8-closed-add-run-scope-hand    ; a new run of no task with a closed owner, its open scope
          well-formed-spawn-rows       i8-closed-spawn-rows-hand       ; T4: a task with an open owner, its run
          well-formed-stream-rows      i8-closed-stream-rows        ; a stream (open owner) and its first link (the root scope)
          well-formed-start-raw        i8-closed-start-raw          ; T5: a computation's run (not a task)
          well-formed-new-run-of       i8-closed-new-run-of-comp    ; T11: same
          well-formed-t28-retire-local   i8-closed-t28-retire-local}    ; T13: i8-closed and acts-parked together through the retire fold
  ;; ---- sites: the row functions that change i8-closed's keys
  :sites '{[well-formed-run-upd run-wake]            (i8-closed-run-upd x8s w x run-wake hf run-wake-run-key h0)          ; resume: key kept, by lemma
           [well-formed-run-upd run-complete-row]    (i8-closed-run-kill x8s w x run-complete-row hf                  ; T12: the run dies
                                               (fn [q :- RunRow] (Eq.refl (run-key-down (run-key q)))) h0)
           [well-formed-run-upd run-tick-park]       (i8-closed-run-upd-up x8s w x run-tick-park hf tick-park-alive8   ; take: made parked,
                                               (fn [q :- RunRow] (Eq.refl (:of q))) h0 h1)              ;   it was alive (h0)
           [well-formed-run-upd run-park-row]        (i8-closed-run-upd-up x8s w x run-park-row hf park-alive8         ; await: same
                                               (fn [q :- RunRow] (Eq.refl (:of q))) h0 h1)
           [well-formed-task-upd task-detach-row]    (i8-closed-task-detach x8s w x h0)                               ; Rule R: owner 0
           [well-formed-task-upd task-cancel-result] (i8-closed-task-upd x8s w x task-cancel-result hf tok-cancel-result h0)
           [well-formed-task-upd (task-set-owner s)] (i8-closed-task-owner x8s w x (task-set-owner s) s hf (tok-set-owner s) h0 h1) ; detach (Q10)
           [well-formed-source-upd source-consume]   (i8-closed-source-upd x8s w x source-consume hf i8-closed-source-key-consume h0)  ; key kept, by lemma
           [well-formed-source-upd source-close-row] (i8-closed-source-close x8s w x h0)                              ; a source closes
           [well-formed-source-upd source-detach-row] (i8-closed-source-detach x8s w x h0)                            ; a source is orphaned
           [well-formed-serve-or (source-enqueue v)] (i8-closed-serve-or x8s w x res (source-enqueue v) hk (fn [s :- SourceRow] (Eq.refl (i8-closed-source-key s))) h0)
           [well-formed-serve-or source-permit]      (i8-closed-serve-or x8s w x res source-permit hk (fn [s :- SourceRow] (Eq.refl (i8-closed-source-key s))) h0)}
  ;; ---- facts from the path: what i8-closed's own proofs and cells take ...
  :ctx '{well-formed-run-cascade      [(= (acts-parked w) true)]                                       ; P4 needs acts-parked (cascade-done-acts-parked)
         well-formed-add-run-scope    [(= (tclosed (i8-closed-task-keys (:tasks w)) (i8-closed-scope-keys (:scopes w)) of) false)]
         well-formed-spawn-rows       [(= (sclosed (i8-closed-scope-keys (:scopes w)) owner) false)]
         well-formed-stream-rows      [(= (sclosed (i8-closed-scope-keys (:scopes w)) owner) false) (= (scope-open-at w root-scope-id) true)]
         well-formed-start-raw        [(= (comp-has w (:id c)) true)]
         well-formed-new-run-of       [(= (comp-has w (:id c)) true)]
         well-formed-t28-retire-local   [(= (acts-parked w) true)]
         well-formed-source-ins-fresh [(= (i8-closed-source-ok (i8-closed-scope-keys (:scopes w)) (i8-closed-source-key r)) true)]              ; a new source's owner is not closed
         [well-formed-run-upd run-tick-park]       [(= (tbl-all (run-ok-for x) (:runs w)) true)] ; every row of the run is alive
         [well-formed-run-upd run-park-row]        [(= (tbl-all (run-ok-for x) (:runs w)) true)]
         [well-formed-task-upd (task-set-owner s)] [(= (sclosed (i8-closed-scope-keys (:scopes w)) s) false)]}   ; the new owner is not closed
  ;; ---- ... and the facts nodes take from above them and pass on
  :own '{;; P10, open: transition refuses T1 and T4 when the token's current scope is closed (`create-in-scope-refused`, a
         ;; model-only guard); that an alive run's current scope is open is not proved. Taken here at T4
         ;; and T1, carried in T1 to the source and stream creations.
         well-formed-t4-spawn               [hcc (= (cur-closed w st) false)]
         well-formed-t1-create-source          [hcc (= (cur-closed w st) false) hc0 (= (root-open-if (Nat.beq kind sk-stream) w) true)]
         well-formed-t1-create-nonstream          [hcc (= (cur-closed w st) false)]
         well-formed-t1-create-stream        [hcc (= (cur-closed w st) false) hro (= (scope-open-at w root-scope-id) true)]
         well-formed-t1-create-source-top      [hc0 (= (root-open-if (Nat.beq kind sk-stream) w) true)]          ; C0's gate (transition)
         well-formed-t-create-link    [hc0 (= (root-open-if true w) true)]
         well-formed-link-realize-raw [hc0 (= (root-open-if (Nat.beq tag res-ok) w) true)]
         well-formed-t-append         [hc0 (= (root-open-if true w) true)]
         well-formed-create-source-in-run [hc (= (run-cur-closed w r) false)]
         well-formed-create-stream-in-run [hc (= (run-cur-closed w r) false) ho (= (scope-open-at w root-scope-id) true)]
         well-formed-create-link-in-run  [ho (= (scope-open-at w root-scope-id) true)]
         well-formed-link-next-raw    [ho (= (scope-open-at w root-scope-id) true)]
         well-formed-append-raw       [ho (= (scope-open-at w root-scope-id) true)]
         well-formed-link-demand-raw  [ho (= (scope-open-at w root-scope-id) true)]
         well-formed-take-park        [hm (List.Mem r (:runs w)) hal (= (run-alive r) true)]          ; revival: the run was alive
         well-formed-arm-park         [hm (List.Mem r (:runs w)) hal (= (run-alive r) true)]
         well-formed-await-raw        [hm (List.Mem r (:runs w)) hal (= (run-alive r) true)]
         well-formed-await-post       [hk (= (awaiting-run-alive rid (:world acc)) true)]                           ;   carried by awaiting-run-alive
         well-formed-raw              [hga (= (acts-parked w) true)]   ; the companion acts-parked, from raw to the cascades (host-guarded-transition, transition, T14, T16, ... forward it: inferred)
         well-formed-t15-resource-ack         [hga (= (acts-parked w) true)]
         well-formed-t-slice-exit     [hga (= (acts-parked w) true)]
         well-formed-t21-release-world  [hga (= (acts-parked w) true)]
         well-formed-t12-complete              [hga (= (acts-parked w) true)]
         well-formed-complete-raw     [hn (= (tbl-any (act-of-run (:id r)) (:acts w)) false) hga (= (acts-parked w) true)]
         well-formed-retire-one       [hga (= (acts-parked w) true)]
         well-formed-t11-dispatch              [hga (= (acts-parked w) true)]
         well-formed-dispatch-raw     [hga (= (acts-parked w) true) hc (= (comp-has w (:id c)) true)]}
  :gates '{well-formed-require-root-open hc0}                                                                 ; C0: the root scope is open
  :pass '{;; transition's guards, per item: create-in-scope-refused gives cur-closed (P10); C0's gate gives root-open-if
          well-formed-transition-spawn         {well-formed-t4-spawn [(bshut-cur w st hc)]}
          well-formed-transition-create-source {well-formed-t1-create-source [(bshut-cur w st hc) hc0]}
          well-formed-transition-create-source-top {well-formed-t1-create-source-top [hc0]}
          well-formed-transition-create-link   {well-formed-t-create-link [hc0]}
          well-formed-transition-append        {well-formed-t-append [hc0]}
          well-formed-transition-link-realize  {well-formed-t-link-realize [(root-ok-any (Nat.beq tag res-ok) w hc0)]}
          well-formed-raw              {well-formed-cancel-losers [(acts-parked-host-guarded-transition w it hga)]}
          ;; owners of new tasks and sources
          well-formed-t4-spawn               {well-formed-spawn-rows [(owner-ok8 w r (base-of w h) (cur-of-tok w st r hcc ht))]}
          well-formed-t4-spawn-top           {well-formed-spawn-rows [(open-not-closed w scope (base-of w h) (bool-and-right _ _ hg))]}
          well-formed-link-demand-raw  {well-formed-spawn-rows [(open-not-closed w root-scope-id (base-of w h) ho)]}
          well-formed-t-link-demand    {well-formed-link-demand-raw [(bool-and-right _ _ (bool-and-right _ _ hg))]}
          well-formed-t1-create-nonstream          {well-formed-create-source-in-run [(cur-of-tok w st r hcc ht)]}
          well-formed-t1-create-stream        {well-formed-create-stream-in-run [(cur-of-tok w st r hcc ht) hro]}
          well-formed-t1-create-source          {well-formed-t1-create-stream [hcc (root-ok-of-true _ w hk hc0)]}
          well-formed-t1-create-source-top      {well-formed-stream-rows [(open-not-closed w scope (base-of w h) (bool-and-right _ _ hg)) (root-ok-of-true _ w hk hc0)]}
          well-formed-create-source-in-run {well-formed-source-ins-fresh [(i8-closed-source-ok-new-source w _ _ kind v (source-owner-ok8 w r (base-of w h) hc))]}
          well-formed-create-stream-in-run {well-formed-stream-rows [(source-owner-ok8 w r (base-of w h) hc) ho]}
          well-formed-t1-create-nonstream-top           {well-formed-source-ins-fresh [(i8-closed-source-ok-new-source w _ scope kind v (open-not-closed w scope (base-of w h) (bool-and-right _ _ hg)))]}
          well-formed-create-link-in-run  {well-formed-source-ins-fresh [(i8-closed-source-ok-root-link w _ _ (base-of w h) ho)]}
          well-formed-t-create-link    {well-formed-create-link-in-run [(root-ok-true w hc0)]}
          well-formed-t-create-link-top {well-formed-source-ins-fresh [(i8-closed-source-ok-link-open w _ scope _ (base-of w h) (bool-and-right _ _ hg))]}
          well-formed-link-next-raw    {well-formed-source-ins-fresh [(i8-closed-source-ok-root-link w _ _ (base-of w h) ho)]}
          well-formed-link-realize-raw {well-formed-link-next-raw [(root-ok-of-true _ w h1 hc0)]}
          well-formed-append-raw       {well-formed-source-ins-fresh [(i8-closed-source-ok-root-link w _ _ (base-of w h) ho)]}
          well-formed-t-append         {well-formed-append-raw [(root-ok-true w hc0)]}
          well-formed-t5-start               {well-formed-start-raw [(find-comp-has w cid c hc)]}
          well-formed-t-detach         {[well-formed-task-upd (task-set-owner s)] [(open-not-closed w s (base-of w h) (detach-open w t s hg))]}
          ;; revival: a run made parked was alive
          well-formed-t-take           {well-formed-take-park [(And.left (tok-facts w st r ht)) (normal-alive r (bool-and-left _ _ (bool-and-right _ _ hg)))]}
          well-formed-t17-arm              {well-formed-arm-park [(And.left (tok-facts w st r ht)) (normal-alive r (bool-and-left _ _ (bool-and-right _ _ hg)))]}
          well-formed-arm-park         {well-formed-take-park [(arm-raw-mem w r kind hm) hal]}
          well-formed-take-park        {[well-formed-run-upd run-tick-park] [(take-park-ok w r x k (run-ok-of-mem w r (base-of w h) hm hal))]}
          well-formed-t6-await               {well-formed-await-raw [(And.left (tok-facts w st r ht)) (normal-alive r (await-ok-normal w r ds mode fresh _ hg))]}
          well-formed-await-raw        {well-formed-await-post [(awaiting-run-alive-await-wire (:id r) r (:next-id w) mode k (nat-distinct ds)
                                                  (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true)
                                                  (awaiting-run-alive-await-pre (:id r) w r ds mode k mine
                                                    (awaiting-run-alive-intro (:id r) w (base-of w h) (run-ok-of-mem w r (base-of w h) hm hal))))]}
          well-formed-await-post       {well-formed-park-if [(awaiting-run-alive-rest-of rid _ (awaiting-run-alive-nat-fold rid (fast-fill (:pairs acc)) (awaiting-run-alive-fast-fill rid (:pairs acc)) (nat-distinct ds) _
                                                (awaiting-run-alive-act-upd rid (:world acc) a (act-set-members (mk-members (:pairs acc) 0 ds))
                                                  (act-set-members-id (mk-members (:pairs acc) 0 ds)) hk)))]}
          ;; acts-parked to the cascades, carried by acts-parked's own lemmas
          well-formed-t15-resource-ack         {well-formed-run-cascade [(acts-parked-ack-raw w z (:owner zr) hu hga)]}
          well-formed-t-slice-exit     {well-formed-run-cascade [(acts-parked-run-upd-free w rid run-fin-pop-end run-fin-pop-end-id (slice-exit-free w rid r hf hg hga) hga)]}
          well-formed-t21-release-world  {well-formed-run-cascade [(acts-parked-zero-handles _ (acts-parked-revoke-roots w hga))]}
          well-formed-t12-complete              {well-formed-complete-raw [(acts-parked-free-of-tok w st r hga ht) hga]}
          well-formed-complete-raw     {well-formed-run-cascade [(acts-parked-retire-after _ (:id r) (acts-parked-complete-body _ r res (acts-parked-run-upd-free w (:id r) run-complete-row run-complete-row-id hn hga)))]}
          well-formed-retire-one       {well-formed-complete-raw [(retire-r1-noact w r r1 rid hf hf1) (acts-parked-retire-pre w r hga)]
                                well-formed-run-cascade [(acts-parked-retire-pre w r hga)]}
          well-formed-t11-dispatch              {well-formed-dispatch-raw [hga (find-comp-has w cid c hc)]}}
  ;; T11: the predecessor's cancel takes acts-parked; comp-has (:id c) survives cancel-pred, cut-suffix and
  ;; consume-entry, which keep the computation ids (the copier's bundle `comp-exists`, as i10-task)
  :src '{well-formed-dispatch-raw
         (a/theorem well-formed-dispatch-raw [w :- World, c :- CompRow]
           (=> (= (acts-parked w) true) (= (comp-has w (:id c)) true) (= (well-formed w) true) (= (well-formed (dispatch-raw w c)) true))
           (intros hga hc h)
           (have h1 := (well-formed-cancel-pred w c hga h))
           (have k1 := (comp-exists-cancel-pred (:id c) w c (comp-exists-intro (:id c) w (base-of w h) hc)))
           (cases he (entry-edge w (:id c))) (case' [some e]) (case' [none])
           (simp only [dispatch-raw he])
           (exact (well-formed-new-run-of _ c 0 (comp-exists-rest-of (:id c) _ (comp-exists-cut-suffix (:id c) _ (:id c) false 0 0 k1))
                    (well-formed-cut-suffix _ (:id c) false 0 0 h1)))
           (simp only [dispatch-raw he])
           (exact (well-formed-new-run-of _ c _
                    (comp-exists-rest-of (:id c) _ (comp-exists-consume-entry (:id c) _ e (comp-exists-cut-suffix (:id c) _ (:id c) true (:at e) (:id e) k1)))
                    (well-formed-consume-entry _ e (well-formed-cut-suffix _ (:id c) true (:at e) (:id e) h1)))))})

;; ---- i8-closed's own proofs (the table's :over), over the cells and restated lemmas they use

(tree/restate! G8 '[well-formed-comp-upd well-formed-fire-edge])

(a/theorem i8-closed-serve-or [x8s :- (List Nat), w :- World, x :- Nat, res :- RunResult, keep :- (=> SourceRow SourceRow),
                        hk :- (forall [s :- SourceRow] (= (source-id (keep s)) (source-id s))),
                        hx :- (forall [s :- SourceRow] (= (i8-closed-source-key (keep s)) (i8-closed-source-key s)))]
  (=> (= (i8-closed x8s w) true) (= (i8-closed x8s (serve-or w x res keep)) true))
  (intro h)
  (cases hz (Nat.beq (oldest-waiter w x) 0))
  (simp only [serve-or hz]) (exact (i8-closed-fire-edge x8s res w _ h))
  (simp only [serve-or hz]) (exact (i8-closed-source-upd x8s w x keep hk hx h)))
(a/theorem i8-closed-stream-rows [x8s :- (List Nat), w :- World, owner :- Nat, v :- Nat]
  (=> (= (sclosed (i8-closed-scope-keys (:scopes w)) owner) false) (= (scope-open-at w root-scope-id) true) (= (i8-closed x8s w) true)
      (= (i8-closed x8s (stream-rows w owner v)) true))
  (intros hc ho h)
  (have hx (= (i8-closed-source-ok (i8-closed-scope-keys (:scopes w)) (i8-closed-source-key (new-stream (:next-id w) owner v))) true))
  (simp only [i8-closed-source-ok i8-closed-source-key new-stream hc Bool.not_false Bool.or_true])
  (have h1 := (i8-closed-source-ins x8s w (new-stream (:next-id w) owner v) (rfl) hx h))
  (simp only [stream-rows])
  (exact (i8-closed-source-ins x8s (bump (source-ins w (new-stream (:next-id w) owner v))) (new-link (+ (:next-id w) 1) root-scope-id (:next-id w)) (rfl)
           (i8-closed-source-ok-root-link w _ _ (i8-closed-well-formed x8s w h) ho) h1)))
(a/theorem i8-closed-start-raw [x8s :- (List Nat), w :- World, c :- CompRow]
  (=> (= (comp-has w (:id c)) true) (= (i8-closed x8s w) true) (= (i8-closed x8s (start-raw w c)) true))
  (intros hc h)
  (simp only [start-raw])
  (exact (i8-closed-comp-upd x8s _ (:id c) (comp-start-row (:next-id w)) (comp-start-row-id (:next-id w)) (comp-start-row-pending (:next-id w))
           (i8-closed-add-run-scope-hand x8s w (:id c) (start-epoch c) 0 0 (comp-not-tclosed w (:id c) (i8-closed-scope-keys (:scopes w)) (i8-closed-well-formed x8s w h) hc) h))))
(a/theorem i8-closed-new-run-of [x8s :- (List Nat), w :- World, c :- CompRow, ei :- Nat]
  (=> (= (tclosed (i8-closed-task-keys (:tasks w)) (i8-closed-scope-keys (:scopes w)) (:id c)) false) (= (i8-closed x8s w) true) (= (i8-closed x8s (new-run-of w c ei)) true))
  (intros hc h)
  (simp only [new-run-of])
  (exact (i8-closed-comp-upd x8s _ (:id c) (comp-set-run (:next-id w)) (comp-set-run-id (:next-id w))
           (comp-set-run-pending (:next-id w)) (i8-closed-add-run-scope-hand x8s w (:id c) (:epoch c) 0 ei hc h))))
(a/theorem i8-closed-new-run-of-comp [x8s :- (List Nat), w :- World, c :- CompRow, ei :- Nat]
  (=> (= (comp-has w (:id c)) true) (= (i8-closed x8s w) true) (= (i8-closed x8s (new-run-of w c ei)) true))
  (intros hc h) (exact (i8-closed-new-run-of x8s w c ei (comp-not-tclosed w (:id c) (i8-closed-scope-keys (:scopes w)) (i8-closed-well-formed x8s w h) hc) h)))

(tree/restate! G8 '[well-formed-retire-one])

(a/theorem i8-closed-t28-retire-local [x8s :- (List Nat), w :- World, v :- Nat]
  (=> (= (acts-parked w) true) (= (i8-closed x8s w) true) (= (i8-closed x8s (:world (t28-retire-local w v))) true))
  (intros hga h)
  (cases hm (tbl-any (run-of-local w) (:runs w)))
  (case [false] (simp only [t28-retire-local hm refuse]) (exact h))
  (case [true] (simp only [t28-retire-local hm accept])
    (exact (nat-fold-pres2 acts-parked (i8-closed x8s) (retire-one v) (acts-parked-retire-one v) (i8-closed-retire-one x8s v) (local-order w) w hga h))))

;; ---- the raw step

(tree/restate! G8 '[well-formed-raw])

;; ===========================================================================
;; Part I. Rule R (normalization with acts-alive: demote's and the strays' cascades), the step
;; ===========================================================================

(tree/restate! G8 '[well-formed-detach well-formed-demote-epoch well-formed-demote-finish well-formed-end-basis well-formed-drop-edges])

(a/theorem i8-closed-demote-aa [x8s :- (List Nat), w :- World, cid :- Nat]
  (=> (= (acts-alive w) true) (= (i8-closed x8s w) true) (= (i8-closed x8s (demote w cid)) true))
  (intros ha h)
  (cases hf (comp-find w cid))
  (case [none] (simp only [demote hf]) (exact h))
  (case [some c]
    (cases hi (:idle c))
    (case [true] (simp only [demote hf hi]) (exact h))
    (case [false]
      (simp only [demote hf hi demote-edges])
      (exact (i8-closed-demote-finish x8s _ cid _ (i8-closed-end-basis x8s _ cid (i8-closed-drop-edges x8s _ (not-dep-of cid)
               (i8-closed-demote-epoch x8s _ cid _ (i8-closed-run-cascade-aa x8s w _ ha h)))))))))
(a/theorem i8-closed-demote-fold [x8s :- (List Nat), a :- Nat, k :- Nat, L :- (List Nat)]
  (forall [W :- World] (=> (= (round-bound a k W) true) (= (i8-closed x8s W) true) (= (i8-closed x8s (nat-fold demote W L)) true)))
  (induction L)
  (case [nil] (intros W hb h) (simp only [nat-fold]) (exact h))
  (case [cons x t ih]
    (intros W hb h)
    (simp only [nat-fold])
    (have p := (round-bound-parts a k W hb))
    (exact (ih (demote W x) (round-bound-demote a k W x hb) (i8-closed-demote-aa x8s W x (And.left (And.right p)) h)))))
(a/theorem i8-closed-normalize-round-aa [x8s :- (List Nat), w :- World]
  (=> (= (acts-alive w) true) (= (i8-closed x8s w) true) (= (i8-closed x8s (normalize-round w)) true))
  (intros ha h)
  (have hs := (i8-closed-well-formed x8s w h))
  (have b0 := (round-bound-intro (alive-cnt w) (act-cnt w) w hs ha (Nat.le_refl _) (Nat.le_refl _)))
  (simp only [normalize-round normalize-round-with-live])
  (exact (i8-closed-detach x8s _ (i8-closed-demote-fold x8s (alive-cnt w) (act-cnt w) _ _
           (round-bound-run-cascade (alive-cnt w) (act-cnt w) w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w))) b0)
           (i8-closed-run-cascade-aa x8s w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w))) ha h)))))
(a/theorem i8-closed-normalize-loop-aa [x8s :- (List Nat), fuel :- (List Nat)]
  (forall [w :- World] (=> (= (acts-alive w) true) (= (i8-closed x8s w) true) (= (i8-closed x8s (normalize-loop fuel w)) true)))
  (induction fuel)
  (case [nil] (intros w ha h) (simp only [normalize-loop]) (exact h))
  (case [cons x f ih]
    (intros w ha h)
    (cases hn (normalized w))
    (case [true] (simp only [normalize-loop hn]) (exact h))
    (case [false]
      (have p := (round-bound-round w (i8-closed-well-formed x8s w h) ha))
      (simp only [normalize-loop hn])
      (exact (ih (normalize-round w) (And.right p) (i8-closed-normalize-round-aa x8s w ha h))))))
(a/theorem i8-closed-normalize-aa [x8s :- (List Nat), w :- World]
  (=> (= (acts-alive w) true) (= (i8-closed x8s w) true) (= (i8-closed x8s (normalize w)) true))
  (intros ha h)
  (have hs := (i8-closed-well-formed x8s w h))
  (have p := (round-bound-parts _ _ _ (round-bound-detach (alive-cnt w) (act-cnt w) w (round-bound-intro _ _ w hs ha (Nat.le_refl _) (Nat.le_refl _)))))
  (simp only [normalize])
  (exact (i8-closed-normalize-loop-aa x8s _ (detach w) (And.left (And.right p)) (i8-closed-detach x8s w h))))
(a/theorem i8-closed-rule-r-round [x8s :- (List Nat), w :- World]
  (=> (= (acts-alive w) true) (= (i8-closed x8s w) true) (= (filter-safe (normalize w)) true) (= (i8-closed x8s (rule-r-round w)) true))
  (intros ha h hf)
  (simp only [rule-r-round]) (rw [rule-r-filter-eq])
  (exact (i8-closed-filter-world x8s (normalize w) (keep-fn (normalize w)) (i8-closed-normalize-aa x8s w ha h) hf)))
(a/theorem i8-closed-rule-r-loop [x8s :- (List Nat), fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (acts-alive w0) true) (= (i8-closed x8s w0) true) (= (rounds-safe-loop fuel w0) true)
                            (= (i8-closed x8s (rule-r-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 ha h hs) (simp only [rounds-safe-loop] at hs) (simp only [rule-r-loop]) (exact (i8-closed-rule-r-round x8s w0 ha h hs)))
  (case [cons x f ih]
    (intros w0 ha h hs)
    (have hs0 := (rounds-safe-loop-head x f w0 hs))
    (have h1 := (i8-closed-rule-r-round x8s w0 ha h hs0))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false]
      (rw [(rule-r-loop-f x f (rule-r-round w0) ho)])
      (exact (ih (rule-r-round w0) (acts-alive-round w0 (i8-closed-well-formed x8s w0 h) ha) h1 (And.right (rounds-safe-loop-f x f w0 hs ho)))))
    (case [true] (rw [(rule-r-loop-t x f (rule-r-round w0) ho)]) (exact h1))))
(a/theorem i8-closed-rule-r [x8s :- (List Nat), w :- World]
  (=> (= (acts-alive w) true) (= (i8-closed x8s w) true) (= (rule-r-safe w) true) (= (i8-closed x8s (rule-r w)) true))
  (intros ha h hs)
  (have hs2 (= (rounds-safe-loop (List.cons Nat 0 (all-ids w)) w) true)) (exact hs)
  (rw [rule-r-eq5])
  (exact (i8-closed-rule-r-loop x8s (List.cons Nat 0 (all-ids w)) w ha h hs2)))
(a/theorem step-i8-closed [x8s :- (List Nat), w :- World, it :- Item]
  (=> (= (acts-parked w) true) (= (i8-closed x8s w) true) (= (rule-r-safe (:world (raw w it))) true) (= (i8-closed x8s (:world (world-step w it))) true))
  (intros hg h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true] (have e2 := (step-accepted w it ha)) (rw [e2])
    (exact (i8-closed-rule-r x8s (:world (raw w it)) (raw-acts-alive w it hg) (i8-closed-raw x8s w it hg h) hs))))
(a/theorem i8-closed-empty [] (= (i8-closed (List.nil Nat) empty-world) true) (rfl))

;; ---- literal I8 from i8-closed []
(a/theorem any-i8-closed-task-keys [p :- (=> I8ClosedTaskKey Bool), t :- TaskRow, ts :- (List TaskRow)]
  (=> (List.Mem t ts) (= (p (i8-closed-task-key t)) true) (= (tbl-any p (i8-closed-task-keys ts)) true))
  (induction ts)
  (case [nil] (intros hm hp) (cases hm))
  (case [cons h tl ih]
    (intros hm hp)
    (cases hm)
    (case [head] (simp only [i8-closed-task-keys tbl-any hp Bool.true_or]))
    (case [tail] (rename_i hm2) (simp only [i8-closed-task-keys tbl-any (ih hm2 hp) Bool.or_true]))))
(a/theorem any-i8-closed-scope-keys [p :- (=> I8ClosedScopeKey Bool), s :- ScopeRow, ss :- (List ScopeRow)]
  (=> (List.Mem s ss) (= (p (i8-closed-scope-key s)) true) (= (tbl-any p (i8-closed-scope-keys ss)) true))
  (induction ss)
  (case [nil] (intros hm hp) (cases hm))
  (case [cons h tl ih]
    (intros hm hp)
    (cases hm)
    (case [head] (simp only [i8-closed-scope-keys tbl-any hp Bool.true_or]))
    (case [tail] (rename_i hm2) (simp only [i8-closed-scope-keys tbl-any (ih hm2 hp) Bool.or_true]))))
(a/theorem sclosed-of-row [s :- ScopeRow, ss :- (List ScopeRow)]
  (=> (List.Mem s ss) (= (:open s) false) (= (sclosed (i8-closed-scope-keys ss) (:id s)) true))
  (intros hm ho)
  (simp only [sclosed])
  (exact (any-i8-closed-scope-keys (sclosed-k (:id s)) s ss hm (Eq.trans (congrArg (fn [b :- Bool] (Bool.and (Nat.beq (:id s) (:id s)) (Bool.not b))) ho)
                                                        (Eq.trans (congrArg (fn [b :- Bool] (Bool.and b true)) (Nat.beq_refl (:id s))) (rfl))))))
(a/theorem i8-runs-of [w :- World] (=> (= (i8-closed (List.nil Nat) w) true) (= (lit-i8-runs w) true))
  (intro h)
  (have r := (i8-closed-rest-of _ w h)) (simp only [i8-closed-rest i8-closed-keys-ok Bool.and_eq_true] at r)
  (have rr := (And.left r)) (rw [all-run-keys] at rr)
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
      (have k := (tbl-all-mem RunRow (on-rkey (i8-closed-run-ok (List.nil Nat) (i8-closed-task-keys (:tasks w)) (i8-closed-scope-keys (:scopes w)))) q (:runs w) rr hq))
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
        (have tc (= (tclosed (i8-closed-task-keys (:tasks w)) (i8-closed-scope-keys (:scopes w)) (:of q)) true))
        (simp only [tclosed])
        (exact (any-i8-closed-task-keys (tclosed-k (i8-closed-scope-keys (:scopes w)) (:of q)) t (:tasks w) tm (Eq.trans (congrArg (fn [b :- Bool] (Bool.and b (sclosed (i8-closed-scope-keys (:scopes w)) (:owner t)))) ti) (Eq.trans (congrArg (fn [b :- Bool] (Bool.and true b)) sc) (rfl)))))
        (simp only [on-rkey i8-closed-run-ok run-key (And.left hx) tc reach-mem Bool.not_true Bool.false_or] at k)
        (cases k)))))
(a/theorem i8-sources-of [w :- World] (=> (= (i8-closed (List.nil Nat) w) true) (= (lit-i8-sources w) true))
  (intro h)
  (have r := (i8-closed-rest-of _ w h)) (simp only [i8-closed-rest i8-closed-keys-ok Bool.and_eq_true] at r)
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
      (have k := (tbl-all-mem SourceRow (on-xok (i8-closed-source-ok (i8-closed-scope-keys (:scopes w)))) x (:sources w) rx hx))
      (simp only [open-source-of Bool.and_eq_true] at hy)
      (have eo (= (:owner x) (:id s))) (exact (Nat.eq_of_beq_eq_true (And.right hy)))
      (have sc := (sclosed-of-row s (:scopes w) hm ho))
      (rw [← eo] at sc)
      (simp only [on-xok i8-closed-source-ok i8-closed-source-key (And.left hy) sc Bool.not_true Bool.false_or] at k)
      (cases k))))

;; ---- the combined bundle
(a/defn chain-to-i8-closed [w :- World] Bool (Bool.and (chain-to-i1-runs w) (i8-closed (List.nil Nat) w)))
(a/theorem chain-to-i8-closed-parts [w :- World] (=> (= (chain-to-i8-closed w) true) (And (= (chain-to-i1-runs w) true) (= (i8-closed (List.nil Nat) w) true)))
  (intro h) (simp only [chain-to-i8-closed Bool.and_eq_true] at h) (exact h))
(a/theorem chain-to-i8-closed-empty [] (= (chain-to-i8-closed empty-world) true) (rfl))
(a/theorem chain-to-i8-closed-acts-parked [w :- World] (=> (= (chain-to-i1-runs w) true) (= (chain-start w) true))
  (intro h)
  (have pg := (chain-to-i1-detached-closed-parts w (And.left (chain-to-i1-runs-parts w h))))
  (have pf := (chain-to-i5-dep-final-parts w (And.left pg)))
  (have pe := (chain-to-i1-scopes-parts w (And.left pf)))
  (have pd := (chain-to-i11a-parts w (And.left pe)))
  (exact (And.left (chain-to-i10-current-parts w (And.left pd)))))
(a/theorem step-chain-to-i8-closed [w :- World, it :- Item] (=> (= (chain-to-i8-closed w) true) (= (chain-to-i8-closed (:world (world-step w it))) true))
  (intro h)
  (have p := (chain-to-i8-closed-parts w h))
  (have pb := (chain-to-i8-closed-acts-parked w (And.left p)))
  (have a1 := (step-chain-to-i1-runs w it (And.left p)))
  (have a2 := (step-i8-closed (List.nil Nat) w it (And.left (chain-start-parts w pb)) (And.right p) (step-rule-r-safe w it pb)))
  (simp only [chain-to-i8-closed a1 a2 Bool.and_self]))
;; Theorem: literal I8 (a closed scope owns no alive run of a task and no open source), through every step
(a/theorem step-lit-i8-total [w :- World, it :- Item]
  (=> (= (chain-to-i8-closed w) true) (And (= (lit-i8-runs (:world (world-step w it))) true) (= (lit-i8-sources (:world (world-step w it))) true)))
  (intro h)
  (have g := (And.right (chain-to-i8-closed-parts _ (step-chain-to-i8-closed w it h))))
  (exact (And.intro (i8-runs-of _ g) (i8-sources-of _ g))))
