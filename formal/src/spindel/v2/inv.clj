(ns spindel.v2.inv
  "Layer-1 safety invariants of spec v1.5.1 §6 over the model's step `world-step`
  (spindel.v2.engine), kernel-checked (Init only).

  Part A: one executable Bool predicate per invariant (the tripwire the random drivers and the
  oracle run after every commit; names `inv-iN-*`). The predicates are the ones that HOLD on the
  model; the spec's literal readings that the model falsifies are kept as `lit-*` predicates
  and their counterexamples are tests (test/spindel/v2/inv_test.clj, notes/PLAN.md findings).
  Part B: I13 as transition guards (A#5) and L1 as the corollary of I3 (A#3).
  Part C: I10's D0 half (`inv-i10-slice`) preserved by every step.
  Part D: I9 (an unwinding run has no activation) preserved by every step.
  Part E: I5's wait half (no wait edge without its activation) from I2 (inv-sample).

  Proof architecture (Parts C, D): one lemma per World function on the path of `world-step`
  (`sl-<f>` for I10, `s9-<f>` for I9), mirroring the inv-sample proofs of step/rule/engine: a
  frame lemma (rfl) per primitive edit of a table the predicate does not read, a specific lemma
  per edit of the tables it reads, and the composites by their case structure. The `s9-` chain
  was generated from the `sl-` chain by renaming (scratch script; only the edits of runs and
  acts needed new proofs), so a further invariant costs its primitive lemmas plus the composites
  where it is not preserved edit by edit (I9: `s9-cancel-acts`, T14 sets `unwinding` and removes
  the run's activations in one transition).

  Theorems:
    i13-fire-dep-live, i13-fire-dep-stale, i13-fire-wait-stale, i13-complete-stale,
    i13-complete-raw-stale      I13 as guards of T9 (delivery) and T12 (result)
    step-l1, step-l1-comp, step-l1-run   L1: after an accepted step a row outside live is in a
                                cleanup entry, admitted or in storage; a computation outside live is
                                idle, a run outside live is done (honest flags of step-i3/-i4)
    step-i10-slice              inv-i10-slice w -> inv-i10-slice (world-step w it) (no hypothesis)
    i10-slice-count, step-d0    with unique run ids: at most one run holds the slice
    step-i9                     inv-sample w, inv-i9 w -> inv-i9 (world-step w it)
    step-i5-wait                inv-sample w, rule-r-safe -> every wait edge has its activation

  Readings (the literal `lit-*` predicates were falsified by the counterexamples of
  test/spindel/v2/inv_test.clj; the alignment pass, spec Z#38-Z#42, resolved every one, and
  the literal readings now run as a second tripwire in the random drivers and in the oracle):
    I1   scopes: non-root -> parent 0 (Z#26 computation run scope), existing, or the scope is
         held by a cleanup entry (the literal `lit-i1-scope` without the exemption holds since
         Z#52: cleanup retains the CURRENT parent chain, inv_test literal-i1-reparent-resolved, and
         is proved through the step in spindel.v2.i1, `step-lit-i1-scope-total`); tasks: owner 0 (detached) or an existing
         scope/computation; resources: an existing run; sources: detached (owner 0) and
         closed, or an existing scope/computation owner; computations (Z#23): owner 0 or
         existing; runs: the entity (computation or task) exists, and so does the run scope.
    I5   a wait edge's creditor is the host (0) or an existing activation; an observe edge's
         `seen` never exceeds its debtor's version. Literal `lit-i5-dep-final` (no armed dep
         edge on a final debtor): T14 makes a cancelled task final and fires its dep creditors
         (Z#39), T9/T11 remove a consumed edge on a final debtor, T7 on a closed source consumes
         its edge in the same commit (Z#48).
    I7   an idle computation: no run, no adoption basis/baselines, no dep edge as creditor,
         pending 0. Literal `lit-i7-basis` (empty basis): T1 is refused in a cleanup slice (Z#40).
    I8   only the literal forms (`lit-i8-runs`: detach re-parents the run scope, Z#41;
         `lit-i8-sources`: no T1 in a cleanup slice, Z#40); tripwire only.
    I9   an unwinding run has no activation (hence no savepoint edge: their creditor is an
         activation). Literal `lit-i9-res` (its resources cancelling or fired): no arm in a
         cleanup slice (Z#40).
    I10  `inv-i10-slice` (D0: at most one run holds the slice, given unique ids), every run of a
         computation that is not done is C.run (`inv-i10-comp`; so at most one), every run of a
         task K is K.run and a task without result has its run, not done (`inv-i10-task`).
         Literal `lit-i10-current` (at most one run with R.epoch = C.epoch): demotion steps the
         epoch of a computation whose C.run is current (Z#42).
    I11a every id is the root scope or the world record, in storage, or reachable through §3.2
         from the obligations (open explicit scopes, non-done runs, outstanding resources,
         observe edges and host waits, pins, rows with handles > 0, pending-activation), the
         cleanup rows or §3.4 admissions (`inv-i11a`, tripwire only)."
  (:require [ansatz.core :as a]
            [spindel.v2.state :refer :all]
            [spindel.v2.edits :refer :all]
            [spindel.v2.reach :refer :all]
            [spindel.v2.retain :refer :all]
            [spindel.v2.step :refer :all]
            [spindel.v2.rule :refer :all]
            [spindel.v2.engine :refer :all]))

;; ===========================================================================
;; Part A. The predicates
;; ===========================================================================

(a/defn in-cleanup-rows [w :- World, x :- Nat] Bool (reach-mem x (cleanup-rows w)))
(a/defn owner-exists [w :- World, o :- Nat] Bool (Bool.or (scope-has w o) (comp-has w o)))

;; ---- I1
(a/defn scope-parent-ok [w :- World, s :- ScopeRow] Bool
  (Bool.or (Nat.beq (:kind s) scope-root)
   (Bool.or (Nat.beq (:parent s) 0) (Bool.or (scope-has w (:parent s)) (in-cleanup-rows w (:id s))))))
(a/defn task-owner-ok [w :- World, t :- TaskRow] Bool
  (Bool.or (Nat.beq (:owner t) 0) (owner-exists w (:owner t))))
(a/defn res-owner-ok [w :- World, z :- ResRow] Bool (run-has w (:owner z)))
(a/defn source-owner-ok [w :- World, x :- SourceRow] Bool
  (if (Nat.beq (:owner x) 0) (Bool.not (:open x)) (owner-exists w (:owner x))))
(a/defn comp-owner-ok [w :- World, c :- CompRow] Bool
  (Bool.or (Nat.beq (:owner c) 0) (owner-exists w (:owner c))))
(a/defn run-entity-ok [w :- World, r :- RunRow] Bool
  (Bool.and (Bool.or (comp-has w (:of r)) (task-has w (:of r))) (scope-has w (:scope r))))
(a/defn inv-i1 [w :- World] Bool
  (Bool.and (tbl-all (scope-parent-ok w) (:scopes w))
  (Bool.and (tbl-all (task-owner-ok w) (:tasks w))
  (Bool.and (tbl-all (res-owner-ok w) (:res w))
  (Bool.and (tbl-all (source-owner-ok w) (:sources w))
  (Bool.and (tbl-all (comp-owner-ok w) (:comps w))
            (tbl-all (run-entity-ok w) (:runs w))))))))
;; literal: every non-root scope has an existing parent (0 for a computation run scope, Z#26)
(a/defn lit-scope-parent [w :- World, s :- ScopeRow] Bool
  (Bool.or (Nat.beq (:kind s) scope-root) (Bool.or (Nat.beq (:parent s) 0) (scope-has w (:parent s)))))
(a/defn lit-i1-scope [w :- World] Bool (tbl-all (lit-scope-parent w) (:scopes w)))

;; ---- I5
(a/defn wait-cred-ok [w :- World, e :- EdgeRow] Bool
  (Bool.or (Bool.not (Nat.beq (:kind e) ek-wait)) (Bool.or (Nat.beq (:creditor e) 0) (act-has w (:creditor e)))))
(a/defn seen-ok [w :- World, e :- EdgeRow] Bool
  (Bool.or (Bool.not (Nat.beq (:kind e) ek-observe))
           (Bool.or (Bool.not (:has-seen e)) (Nat.ble (:seen e) (deb-version w (:debtor e))))))
(a/defn inv-i5 [w :- World] Bool
  (Bool.and (tbl-all (wait-cred-ok w) (:edges w)) (tbl-all (seen-ok w) (:edges w))))
(a/defn dep-final-ok [w :- World, e :- EdgeRow] Bool
  (Bool.or (Bool.not (Nat.beq (:kind e) ek-dep))
           (Bool.or (Bool.not (Nat.beq (:phase e) ph-armed)) (Bool.not (deb-final w (:debtor e))))))
(a/defn lit-i5-dep-final [w :- World] Bool (tbl-all (dep-final-ok w) (:edges w)))

;; ---- I7
(a/defn created-empty [xs :- (List Created)] Bool (match xs [nil true] [(cons h t) false]))
(a/defn bases-empty [xs :- (List AdoptBase)] Bool (match xs [nil true] [(cons h t) false]))
(a/defn idle-shape [w :- World, c :- CompRow] Bool
  (Bool.or (Bool.not (:idle c))
   (Bool.and (Nat.beq (:run c) 0)
   (Bool.and (created-empty (:adopt-basis c))
   (Bool.and (bases-empty (:adopt-baselines c))
   (Bool.and (Nat.beq (:pending c) 0)
             (Bool.not (tbl-any (dep-of (:id c)) (:edges w)))))))))
(a/defn inv-i7 [w :- World] Bool (tbl-all (idle-shape w) (:comps w)))
(a/defn idle-basis-ok [c :- CompRow] Bool (Bool.or (Bool.not (:idle c)) (created-empty (:basis c))))
(a/defn lit-i7-basis [w :- World] Bool (tbl-all idle-basis-ok (:comps w)))

;; ---- I8 (literal only)
(a/defn run-of-owned-task [w :- World, s :- Nat, r :- RunRow] Bool
  (Bool.and (run-alive r) (opt-test (fn [t :- TaskRow] (Nat.beq (:owner t) s)) (task-find w (:of r)))))
(a/defn open-source-of [s :- Nat, x :- SourceRow] Bool (Bool.and (:open x) (Nat.beq (:owner x) s)))
(a/defn closed-scope-runs-ok [w :- World, s :- ScopeRow] Bool
  (Bool.or (:open s) (Bool.not (tbl-any (run-of-owned-task w (:id s)) (:runs w)))))
(a/defn closed-scope-sources-ok [w :- World, s :- ScopeRow] Bool
  (Bool.or (:open s) (Bool.not (tbl-any (open-source-of (:id s)) (:sources w)))))
(a/defn lit-i8-runs [w :- World] Bool (tbl-all (closed-scope-runs-ok w) (:scopes w)))
(a/defn lit-i8-sources [w :- World] Bool (tbl-all (closed-scope-sources-ok w) (:scopes w)))

;; ---- I9
(a/defn unwinding-acts-ok [as :- (List ActRow), r :- RunRow] Bool
  (Bool.or (Bool.not (Nat.beq (:mode r) mode-unwinding)) (Bool.not (tbl-any (act-of-run (:id r)) as))))
(a/defn inv-i9 [w :- World] Bool (tbl-all (unwinding-acts-ok (:acts w)) (:runs w)))
(a/defn res-quiet [z :- ResRow] Bool (Bool.or (Nat.beq (:phase z) rp-cancelling) (Nat.beq (:phase z) rp-fired)))
(a/defn res-of-quiet [x :- Nat, z :- ResRow] Bool (Bool.or (Bool.not (Nat.beq (:owner z) x)) (res-quiet z)))
(a/defn unwinding-res-ok [w :- World, r :- RunRow] Bool
  (Bool.or (Bool.not (Nat.beq (:mode r) mode-unwinding)) (tbl-all (res-of-quiet (:id r)) (:res w))))
(a/defn lit-i9-res [w :- World] Bool (tbl-all (unwinding-res-ok w) (:runs w)))

;; ---- I10
(a/defn slice-only [x :- Nat, r :- RunRow] Bool (Bool.or (Bool.not (:slice r)) (Nat.beq (:id r) x)))
(a/defn slice-holder [rs :- (List RunRow)] Nat
  (match rs [nil 0] [(cons h t) (if (:slice h) (:id h) (slice-holder t))]))
;; every run holding the slice has id x
(a/defn i10-slice-at [x :- Nat, w :- World] Bool (tbl-all (slice-only x) (:runs w)))
(a/defn inv-i10-slice [w :- World] Bool (i10-slice-at (slice-holder (:runs w)) w))
(a/defn comp-run-is [w :- World, r :- RunRow] Bool
  (Bool.or (Bool.not (run-alive r))
           (match (comp-find w (:of r)) [none true] [(some c) (Nat.beq (:run c) (:id r))])))
(a/defn inv-i10-comp [w :- World] Bool (tbl-all (comp-run-is w) (:runs w)))
(a/defn task-run-is [w :- World, r :- RunRow] Bool
  (match (task-find w (:of r)) [none true] [(some t) (Nat.beq (:run t) (:id r))]))
(a/defn task-has-run [w :- World, t :- TaskRow] Bool
  (Bool.or (Bool.not (Nat.beq (:tag (:result t)) res-none))
           (match (run-find w (:run t)) [none false]
                  [(some r) (Bool.and (Nat.beq (:of r) (:id t)) (run-alive r))])))
(a/defn inv-i10-task [w :- World] Bool
  (Bool.and (tbl-all (task-run-is w) (:runs w)) (tbl-all (task-has-run w) (:tasks w))))
(a/defn inv-i10 [w :- World] Bool
  (Bool.and (inv-i10-slice w) (Bool.and (inv-i10-comp w) (inv-i10-task w))))
(a/defn current-of [c :- CompRow, r :- RunRow] Bool
  (Bool.and (Nat.beq (:of r) (:id c)) (Nat.beq (:epoch r) (:epoch c))))
(a/defn one-current [w :- World, c :- CompRow] Bool (Nat.ble (tbl-count (current-of c) (:runs w)) 1))
(a/defn lit-i10-current [w :- World] Bool (tbl-all (one-current w) (:comps w)))

;; ---- I11a: obligations (§6) and their §3.2 closure
(a/defn handled-ids [w :- World] (List Nat)
  (nat-app (tbl-scan comp-id (fn [c :- CompRow] (Nat.blt 0 (:handles c))) (:comps w))
  (nat-app (tbl-scan task-id (fn [t :- TaskRow] (Nat.blt 0 (:handles t))) (:tasks w))
  (nat-app (tbl-scan source-id (fn [x :- SourceRow] (Nat.blt 0 (:handles x))) (:sources w))
           (tbl-scan pub-id (fn [p :- PubRow] (Nat.blt 0 (:handles p))) (:pubs w))))))
(a/defn obligations [w :- World] (List Nat)
  (nat-app (tbl-scan scope-id is-open-explicit (:scopes w))
  (nat-app (tbl-scan run-id run-alive (:runs w))
  (nat-app (tbl-ids resource-id (:res w))
  (nat-app (tbl-scan edge-id is-observe (:edges w))
  (nat-app (:pins w)
  (nat-app (handled-ids w)
  (nat-app (nz (:pending-act w))
           (cleanup-rows w)))))))))
(a/defn obl-reach [w :- World] ReachResult
  (reach-run-l (List.cons Nat 0 (List.append Nat (obligations w) (succ-all w (all-ids w))))
               (retain-succ w) (obligations w)))
(a/defn obl-ok [w :- World, lv :- (List Nat), y :- Nat] Bool
  (Bool.or (Nat.beq y (root-scope-id)) (Bool.or (Nat.beq y (world-record-id))
  (Bool.or (reach-mem y lv) (Bool.or (admitted w y) (reach-mem y (storage-with w lv)))))))
(a/defn inv-i11a [w :- World] Bool
  (Bool.and (:converged (obl-reach w)) (tbl-all (obl-ok w (:visited (obl-reach w))) (all-ids w))))

;; the tripwire: every predicate above that holds on the model
(a/defn inv-all [w :- World] Bool
  (Bool.and (inv-i1 w) (Bool.and (inv-i5 w) (Bool.and (inv-i7 w) (Bool.and (inv-i9 w)
  (Bool.and (inv-i10 w) (inv-i11a w)))))))

;; ===========================================================================
;; Part B. I13 as transition guards (A#5, W#1) and L1 (A#3)
;; ===========================================================================

;; T9 fills a slot from a computation only while it is live: a dep fire whose debtor is a
;; computation that is not live is an invalidation (epoch step), never a delivery
(a/theorem i13-fire-dep-live [w :- World, e :- EdgeRow, c :- CompRow]
  (=> (= (comp-find w (:debtor e)) (Option.some CompRow c)) (= (comp-live c) false)
      (= (fire-dep w e) (invalidate w e)))
  (intros hc hl)
  (have ha (= (deb-avail w (:debtor e)) false)) (simp only [deb-avail hc hl])
  (cases hm (act-with-member (:id e) (:acts w))) (case' [some a]) (case' [none])
  (simp only [fire-dep hm])
  (simp only [fire-dep hm ha Bool.and_false]))

;; a fire into an activation of a stale run is not delivered (§4.5.4): dep edges ...
(a/theorem i13-fire-dep-stale [w :- World, e :- EdgeRow, a :- ActRow]
  (=> (= (act-with-member (:id e) (:acts w)) (Option.some ActRow a))
      (= (run-current-of w (:run a) (:creditor e)) false)
      (= (fire-dep w e) (invalidate w e)))
  (intros hm hs)
  (simp only [fire-dep hm hs Bool.false_and]))

;; ... and wait edges: the edge is only marked fired, no slot is filled
(a/theorem i13-fire-wait-stale [res :- RunResult, w :- World, e :- EdgeRow, a :- ActRow]
  (=> (= (act-find w (:creditor e)) (Option.some ActRow a)) (= (run-current w (:run a)) false)
      (= (fire-wait-act res w e) (edge-upd w (:id e) (edge-set-phase ph-fired))))
  (intros hm hs)
  (simp only [fire-wait-act hm hs]))

;; T12 sets a result only for a current run: a stale computation run's completion leaves the
;; computation (and every other row) as it is
(a/theorem i13-complete-stale [w :- World, r :- RunRow, res :- RunResult, c :- CompRow]
  (=> (= (comp-find w (:of r)) (Option.some CompRow c)) (= (Nat.beq (:epoch r) (:epoch c)) false)
      (= (complete-body w r res) (Casc.mk w (List.nil Job))))
  (intros hc he)
  (simp only [complete-body hc he]))

;; the computation complete-raw looks up is the one before the run's own row update
(a/theorem comp-find-run-upd [w :- World, x :- Nat, f :- (=> RunRow RunRow), d :- Nat]
  (= (comp-find (run-upd w x f) d) (comp-find w d)) (rfl))

(a/theorem i13-complete-raw-stale [w :- World, r :- RunRow, res :- RunResult, c :- CompRow]
  (=> (= (comp-find w (:of r)) (Option.some CompRow c)) (= (Nat.beq (:epoch r) (:epoch c)) false)
      (= (complete-raw w r res)
         (fin-if-final (run-cascade (retire-after (run-upd w (:id r) run-complete-row) (:id r))
                                    (List.cons Job (Job.jretire (:id r)) (List.nil Job)))
                       (:of r))))
  (intros hc he)
  (have hc2 (= (comp-find (run-upd w (:id r) run-complete-row) (:of r)) (Option.some CompRow c)))
  (rw [comp-find-run-upd]) (exact hc)
  (simp only [complete-raw (i13-complete-stale (run-upd w (:id r) run-complete-row) r res c hc2 he)]))

;; L1 (prompt reclamation) as the corollary of I3: after an accepted step every row that is not
;; in live(W) is in a cleanup entry, admitted by §3.4 or in storage; a computation outside live
;; is idle (demoted) and a run outside live is done
(a/theorem step-l1 [w :- World, it :- Item, y :- Nat]
  (=> (= (:accepted (raw w it)) true)
      (= (live-converged (normalize (rule-r-pre (:world (raw w it))))) true)
      (= (live-converged (rule-r (:world (raw w it)))) true)
      (List.Mem y (all-ids (:world (world-step w it))))
      (= (in-live (:world (world-step w it)) y) false)
      (= (Bool.or (in-cleanup-rows (:world (world-step w it)) y)
                  (Bool.or (admitted (:world (world-step w it)) y)
                           (reach-mem y (storage (:world (world-step w it)))))) true))
  (intros ha hc hc2 hm hl)
  (have hi := (step-i3 w it ha hc hc2))
  (have hk := (tbl-all-mem Nat (keep-fn (:world (world-step w it))) y (all-ids (:world (world-step w it))) hi hm))
  (simp only [in-live] at hl)
  (simp only [keep-fn keep-with hl Bool.false_or] at hk)
  (simp only [in-cleanup-rows])
  (exact hk))

(a/theorem step-l1-comp [w :- World, it :- Item, c :- CompRow]
  (=> (= (:accepted (raw w it)) true)
      (= (live-converged (normalize (rule-r-pre (:world (raw w it))))) true)
      (= (live-converged (rule-r (:world (raw w it)))) true)
      (= (normalized (normalize (rule-r-pre (:world (raw w it))))) true)
      (List.Mem c (:comps (:world (world-step w it))))
      (= (in-live (:world (world-step w it)) (:id c)) false)
      (= (:idle c) true))
  (intros ha hc hc2 hn hm hl)
  (cases hi (:idle c))
  (have hl2 := (normalized-comps (:world (world-step w it)) c (step-normalized w it ha hc hc2 hn) hm hi))
  (rw [hl] at hl2) (exact hl2)
  (rfl))

(a/theorem step-l1-run [w :- World, it :- Item, r :- RunRow]
  (=> (= (:accepted (raw w it)) true)
      (= (live-converged (normalize (rule-r-pre (:world (raw w it))))) true)
      (= (live-converged (rule-r (:world (raw w it)))) true)
      (= (normalized (normalize (rule-r-pre (:world (raw w it))))) true)
      (List.Mem r (:runs (:world (world-step w it))))
      (= (in-live (:world (world-step w it)) (:id r)) false)
      (= (run-alive r) false))
  (intros ha hc hc2 hn hm hl)
  (cases hr (run-alive r))
  (rfl)
  (have hl2 := (step-i4 w it r ha hc hc2 hn hm hr))
  (rw [hl] at hl2) (simp at hl2))

;; ===========================================================================
;; Part C. I10, D0 half: at most one run holds the slice
;;
;; `i10-slice-at x w`: every run holding the slice has id x. Every edit except the two
;; scheduling choices (`schedule`, `finalize`: run-enter-row, guarded by "no run holds the
;; slice") preserves it for EVERY x: no other row function sets `slice`. `sl-<f>` lemmas:
;; i10-slice-at x w -> i10-slice-at x (f w ...). With unique run ids (ids-ok, in inv-sample)
;; `inv-i10-slice` = at most one run holds the slice.
;; ===========================================================================

;; a generic fold lemma for any Bool world predicate
(a/theorem nat-fold-pres [P :- (=> World Bool), f :- (=> World Nat World),
                          hf :- (forall [w :- World, x :- Nat] (=> (= (P w) true) (= (P (f w x)) true))),
                          xs :- (List Nat)]
  (forall [w :- World] (=> (= (P w) true) (= (P (nat-fold f w xs)) true)))
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (intros w hw) (simp only [nat-fold]) (exact hw)
  (intros w hw) (simp only [nat-fold]) (exact (ih _ (hf w h hw))))

(defmacro ^:private defsl-frames
  "sl-<name>: (= (i10-slice-at x <edit>) (i10-slice-at x w)) by rfl, for edits that leave `runs`."
  [& edits]
  `(do ~@(for [[nm params app] (partition 3 edits)]
           `(a/theorem ~(symbol (str "sl-" nm)) [~'x :- ~'Nat, ~'w :- ~'World ~@params]
              (~'= (~'i10-slice-at ~'x ~app) (~'i10-slice-at ~'x ~'w)) (~'rfl)))))

(defmacro ^:private sl-table-edits [& specs]
  (vec (mapcat (fn [[prefix row]]
                 [(symbol (str prefix "-ins")) ['r :- row] (list (symbol (str prefix "-ins")) 'w 'r)
                  (symbol (str prefix "-del")) ['y :- 'Nat] (list (symbol (str prefix "-del")) 'w 'y)
                  (symbol (str prefix "-upd")) ['y :- 'Nat 'f :- (list '=> row row)]
                  (list (symbol (str prefix "-upd")) 'w 'y 'f)])
               (partition 2 specs))))

(defmacro ^:private defsl-tables [& specs]
  `(defsl-frames ~@(macroexpand `(sl-table-edits ~@specs))))

(defsl-tables scope ScopeRow comp CompRow task TaskRow source SourceRow edge EdgeRow act ActRow
  resource ResRow cleanup CleanupRow pub PubRow fork ForkRow)
(defsl-frames
  set-pins [v :- (List Nat)] (set-pins w v)
  set-pending-act [v :- Nat] (set-pending-act w v)
  set-released [v :- Bool] (set-released w v)
  set-edges [v :- (List EdgeRow)] (set-edges w v)
  set-comps [v :- (List CompRow)] (set-comps w v)
  set-next-id [v :- Nat] (set-next-id w v)
  bump [] (bump w)
  insert-edge [e :- EdgeRow] (insert-edge w e)
  insert-edge-fresh [e :- EdgeRow] (insert-edge-fresh w e)
  drop-cred-edges [a :- Nat] (drop-cred-edges w a)
  drop-act [a :- Nat] (drop-act w a)
  drop-edges [p :- (=> EdgeRow Bool)] (drop-edges w p)
  cleanup-set [rid :- Nat, rows :- (List Nat)] (cleanup-set w rid rows)
  close-scope-id [s :- Nat] (close-scope-id w s)
  res-cancel [z :- Nat] (res-cancel w z)
  finalize-one [d :- Nat] (finalize-one w d))

;; run edits: a row function that sets no slice keeps i10-slice-at
(a/defn keeps-slice [x :- Nat, f :- (=> RunRow RunRow)] Prop
  (forall [r :- RunRow] (=> (= (slice-only x r) true) (= (slice-only x (f r)) true))))

(a/theorem sl-run-upd [x :- Nat, w :- World, y :- Nat, f :- (=> RunRow RunRow), hf :- (keeps-slice x f)]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (run-upd w y f)) true))
  (intro h)
  (simp only [i10-slice-at run-upd set-runs] at h)
  (simp only [i10-slice-at run-upd set-runs])
  (have hin (forall [r :- RunRow] (=> (= (slice-only x r) true) (= (Nat.beq (run-id r) y) true) (= (slice-only x (f r)) true))))
  (intros r hr hy) (exact (hf r hr))
  (have hout (forall [r :- RunRow] (=> (= (slice-only x r) true) (= (Nat.beq (run-id r) y) false) (= (slice-only x r) true))))
  (intros r hr hy) (exact hr)
  (exact (tbl-all-upd RunRow run-id y f (slice-only x) (slice-only x) hin hout (:runs w) h)))

(a/theorem sl-run-del [x :- Nat, w :- World, y :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (run-del w y)) true))
  (intro h)
  (simp only [i10-slice-at run-del set-runs] at h)
  (simp only [i10-slice-at run-del set-runs])
  (have hout (forall [r :- RunRow] (=> (= (slice-only x r) true) (= (Nat.beq (run-id r) y) false) (= (slice-only x r) true))))
  (intros r hr hy) (exact hr)
  (exact (tbl-all-del RunRow run-id y (slice-only x) (slice-only x) hout (:runs w) h)))

(a/theorem sl-run-ins [x :- Nat, w :- World, r :- RunRow]
  (=> (= (:slice r) false) (= (i10-slice-at x w) true) (= (i10-slice-at x (run-ins w r)) true))
  (intros hr h)
  (simp only [i10-slice-at run-ins set-runs tbl-ins] at h)
  (simp only [i10-slice-at run-ins set-runs tbl-ins tbl-all slice-only hr Bool.not_false Bool.true_or Bool.true_and])
  (exact h))

(a/theorem sl-filter-world [x :- Nat, K :- (=> Nat Bool), w :- World]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (filter-world K w)) true))
  (intro h)
  (simp only [i10-slice-at filter-world] at h)
  (simp only [i10-slice-at filter-world])
  (exact (tbl-all-keep-same RunRow K run-id (slice-only x) (:runs w) h)))

;; the run row functions other than run-enter-row
(defmacro ^:private defkeeps [& specs]
  `(do ~@(for [[f params] (partition 2 specs)]
           `(a/theorem ~(symbol (str "keeps-" f)) [~'x :- ~'Nat ~@params]
              (~'keeps-slice ~'x ~(if (seq params) (cons f (map first (partition 3 params))) f))
              (~'unfold ~'keeps-slice) (~'intros ~'r ~'h)
              (~'simp ~'only [~f ~'slice-only] ~'at ~'h)
              (~'simp ~'only [~f ~'slice-only ~'h])))))

(defkeeps run-tick [] run-arm [z :- Nat] run-unres [z :- Nat] run-set-act [n :- Nat] run-wake []
  run-cancel-row [] run-fin-push [fz :- Finalizer] run-fin-pop [])

(defmacro ^:private defkeeps-off [& specs]
  `(do ~@(for [f specs]
           `(a/theorem ~(symbol (str "keeps-" f)) [~'x :- ~'Nat]
              (~'keeps-slice ~'x ~f)
              (~'unfold ~'keeps-slice) (~'intros ~'r ~'h)
              (~'simp ~'only [~f ~'slice-only ~'Bool.not_false ~'Bool.true_or])))))

(defkeeps-off run-complete-row run-park-row run-tick-park run-fin-pop-end)

;; the slice holder: if every run with the slice has id x, inv-i10-slice holds
(a/theorem slice-holder-of [x :- Nat, rs :- (List RunRow)]
  (=> (= (tbl-all (slice-only x) rs) true) (= (tbl-any run-slice rs) true) (= (slice-holder rs) x))
  (induction rs)
  (case' [cons h t ih])
  (case' [nil])
  (intros ha hb) (simp [tbl-any] at hb)
  (intros ha hb)
  (simp only [tbl-all Bool.and_eq_true] at ha)
  (cases hs (:slice h))
  (simp only [tbl-any run-slice hs Bool.false_or] at hb)
  (simp only [slice-holder hs]) (exact (ih (And.right ha) hb))
  (have h1 := (And.left ha))
  (simp only [slice-only hs Bool.not_true Bool.false_or] at h1)
  (simp only [slice-holder hs]) (exact (Nat.eq_of_beq_eq_true h1)))

(a/theorem slice-none [y :- Nat, rs :- (List RunRow)]
  (=> (= (tbl-any run-slice rs) false) (= (tbl-all (slice-only y) rs) true))
  (induction rs)
  (case' [cons h t ih])
  (case' [nil])
  (intro hb) (simp [tbl-all])
  (intro hb)
  (simp only [tbl-any run-slice Bool.or_eq_false_iff] at hb)
  (simp only [tbl-all slice-only (And.left hb) Bool.not_false Bool.true_or Bool.true_and])
  (exact (ih (And.right hb))))

(a/theorem i10-slice-intro [x :- Nat, w :- World]
  (=> (= (i10-slice-at x w) true) (= (inv-i10-slice w) true))
  (intro h)
  (simp only [inv-i10-slice i10-slice-at] at h)
  (simp only [inv-i10-slice i10-slice-at])
  (cases hb (tbl-any run-slice (:runs w)))
  (exact (slice-none _ (:runs w) hb))
  (rw [(slice-holder-of x (:runs w) h hb)]) (exact h))

(a/theorem i10-slice-elim [w :- World]
  (=> (= (inv-i10-slice w) true) (= (i10-slice-at (slice-holder (:runs w)) w) true))
  (intro h) (simp only [inv-i10-slice] at h) (exact h))

;; ---- step.clj: T9 fire and the raw transitions

(a/theorem sl-resume [x :- Nat, w :- World, a :- ActRow]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (resume w a)) true))
  (intro h) (simp only [resume])
  (exact (sl-run-upd x _ _ _ (keeps-run-wake x) (Eq.trans (sl-drop-act x w (:id a)) h))))

(a/theorem sl-fill-slot [x :- Nat, w :- World, a :- ActRow, y :- Nat, v :- RunResult]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (fill-slot w a y v)) true))
  (intro h)
  (cases hm (act-ready (act-fill y v a)))
  (simp only [fill-slot hm sl-act-upd]) (exact h)
  (simp only [fill-slot hm]) (exact (sl-resume x w a h)))

(a/theorem sl-invalidate [x :- Nat, w :- World, e :- EdgeRow]
  (= (i10-slice-at x (invalidate w e)) (i10-slice-at x w))
  (simp only [invalidate sl-comp-upd sl-edge-upd]))

(a/theorem sl-remove-edge [x :- Nat, w :- World, y :- Nat]
  (= (i10-slice-at x (remove-edge w y)) (i10-slice-at x w))
  (cases hf (edge-find w y)) (case' [some e]) (case' [none])
  (simp only [remove-edge hf])
  (cases hm (:marked e))
  (all_goals (simp only [remove-edge hf hm sl-comp-upd sl-edge-del])))

(a/theorem sl-dep-consumed [x :- Nat, w :- World, e :- EdgeRow]
  (= (i10-slice-at x (dep-consumed w e)) (i10-slice-at x w))
  (cases hf (deb-final w (:debtor e)))
  (all_goals (simp only [dep-consumed hf sl-edge-upd sl-remove-edge])))

(a/theorem sl-fire-dep [x :- Nat, w :- World, e :- EdgeRow]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (fire-dep w e)) true))
  (intro h)
  (cases ha (act-with-member (:id e) (:acts w))) (case' [some a]) (case' [none])
  (simp only [fire-dep ha sl-invalidate]) (exact h)
  (cases hc (Bool.and (run-current-of w (:run a) (:creditor e)) (deb-avail w (:debtor e))))
  (simp only [fire-dep ha hc sl-invalidate]) (exact h)
  (simp only [fire-dep ha hc deliver-dep])
  (exact (sl-fill-slot x _ a _ _ (Eq.trans (sl-dep-consumed x w e) h))))

(a/theorem sl-fire-wait-act [x :- Nat, res :- RunResult, w :- World, e :- EdgeRow]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (fire-wait-act res w e)) true))
  (intro h)
  (cases ha (act-find w (:creditor e))) (case' [some a]) (case' [none])
  (simp only [fire-wait-act ha sl-edge-upd]) (exact h)
  (cases hc (run-current w (:run a)))
  (simp only [fire-wait-act ha hc sl-edge-upd]) (exact h)
  (simp only [fire-wait-act ha hc]) (exact (sl-fill-slot x _ a _ _ (Eq.trans (sl-edge-upd x w _ _) h))))

(a/theorem sl-mark-edge [x :- Nat, w :- World, y :- Nat]
  (= (i10-slice-at x (mark-edge w y)) (i10-slice-at x w))
  (cases hf (edge-find w y)) (case' [some e]) (case' [none])
  (simp only [mark-edge hf])
  (cases hm (:marked e))
  (all_goals (simp only [mark-edge hf hm sl-comp-upd sl-edge-upd])))

(a/theorem sl-unmark-edge [x :- Nat, w :- World, y :- Nat]
  (= (i10-slice-at x (unmark-edge w y)) (i10-slice-at x w))
  (cases hf (edge-find w y)) (case' [some e]) (case' [none])
  (simp only [unmark-edge hf])
  (cases hm (:marked e))
  (all_goals (simp only [unmark-edge hf hm sl-comp-upd sl-edge-upd])))

(a/theorem sl-fire-wait [x :- Nat, res :- RunResult, w :- World, e :- EdgeRow]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (fire-wait res w e)) true))
  (intro h)
  (cases hc (Nat.beq (:creditor e) 0))
  (simp only [fire-wait hc]) (exact (sl-fire-wait-act x res w e h))
  (simp only [fire-wait hc sl-remove-edge]) (exact h))

(a/theorem sl-fire-observe [x :- Nat, w :- World, e :- EdgeRow]
  (= (i10-slice-at x (fire-observe w e)) (i10-slice-at x w))
  (cases hs (observe-new e (deb-version w (:debtor e))))
  (all_goals (simp only [fire-observe hs sl-edge-upd])))

(a/theorem sl-fire-edge [x :- Nat, res :- RunResult, w :- World, y :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (fire-edge res w y)) true))
  (intro h)
  (cases hf (edge-find w y)) (case' [some e]) (case' [none])
  (simp only [fire-edge hf]) (exact h)
  (cases hp (Nat.beq (:phase e) ph-armed))
  (simp only [fire-edge hf hp]) (exact h)
  (cases hk1 (Nat.beq (:kind e) ek-dep))
  (cases hk2 (Nat.beq (:kind e) ek-wait))
  (cases hk3 (Nat.beq (:kind e) ek-observe))
  (simp only [fire-edge hf hp hk1 hk2 hk3 fire-savepoint-todo]) (exact h)
  (simp only [fire-edge hf hp hk1 hk2 hk3 sl-fire-observe]) (exact h)
  (simp only [fire-edge hf hp hk1 hk2]) (exact (sl-fire-wait x res w e h))
  (simp only [fire-edge hf hp hk1]) (exact (sl-fire-dep x w e h)))

(a/theorem sl-fold-fire [x :- Nat, res :- RunResult, w :- World, ys :- (List Nat)]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (nat-fold (fire-edge res) w ys)) true))
  (exact (nat-fold-pres (i10-slice-at x) (fire-edge res) (fn [w2 :- World, y :- Nat] (sl-fire-edge x res w2 y)) ys w)))

(a/theorem sl-fold-frame [x :- Nat, f :- (=> World Nat World),
                          hf :- (forall [w :- World, y :- Nat] (= (i10-slice-at x (f w y)) (i10-slice-at x w))),
                          w :- World, ys :- (List Nat)]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (nat-fold f w ys)) true))
  (have hf2 (forall [w2 :- World, y :- Nat] (=> (= (i10-slice-at x w2) true) (= (i10-slice-at x (f w2 y)) true))))
  (intros w2 y hw) (rw [(hf w2 y)]) (exact hw)
  (exact (nat-fold-pres (i10-slice-at x) f hf2 ys w)))

(a/theorem sl-record-basis [x :- Nat, w :- World, r :- RunRow, y :- Nat]
  (= (i10-slice-at x (record-basis w r y)) (i10-slice-at x w))
  (cases hc (in-comp w r))
  (all_goals (simp only [record-basis hc sl-comp-upd])))

(a/theorem sl-t1-top [x :- Nat, w :- World, sc :- Nat, kind :- Nat, v :- Nat, fresh :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t1-create-source-top w sc kind v fresh))) true))
  (intro h)
  (cases hg (Bool.and (Bool.and (Nat.beq fresh (:next-id w)) (src-kind-ok kind)) (scope-open-at w sc)))
  (simp only [t1-create-source-top hg refuse]) (exact h)
  (simp only [t1-create-source-top hg accept sl-bump sl-source-ins]) (exact h))

(a/theorem sl-write-raw [x :- Nat, w :- World, s :- Nat, v :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (write-raw w s v)) true))
  (intro h) (simp only [write-raw])
  (exact (sl-fold-frame x mark-edge (sl-mark-edge x) _ _
           (sl-fold-fire x _ _ _ (Eq.trans (sl-source-upd x w s _) h)))))

(a/theorem sl-t2 [x :- Nat, w :- World, s :- Nat, v :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t2-write w s v))) true))
  (intro h)
  (cases hf (source-find w s)) (case' [some sr]) (case' [none])
  (simp only [t2-write hf refuse]) (exact h)
  (cases hw (writable sr))
  (simp only [t2-write hf hw refuse]) (exact h)
  (simp only [t2-write hf hw accept]) (exact (sl-write-raw x w s v h)))

(a/theorem sl-track-fin [x :- Nat, sr :- SourceRow, y :- Nat, w :- World]
  (= (i10-slice-at x (track-fin sr y w)) (i10-slice-at x w))
  (cases ho (:open sr))
  (case [true] (simp only [track-fin ho]))
  (case [false] (simp only [track-fin ho sl-remove-edge])))

(a/theorem sl-track-raw [x :- Nat, w :- World, r :- RunRow, s :- Nat, sr :- SourceRow, k :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (track-raw w r s sr k)) true))
  (intro h)
  (cases hs (site-edge (:edges w) (:of r) (:effect-index r) s)) (case' [some e]) (case' [none])
  (simp only [track-raw hs track-new])
  (exact (sl-run-upd x _ _ _ (keeps-run-tick x) (Eq.trans (sl-comp-upd x _ _ _) (Eq.trans (sl-track-fin x _ _ _) (Eq.trans (sl-insert-edge-fresh x w _) h)))))
  (simp only [track-raw hs])
  (exact (sl-run-upd x _ _ _ (keeps-run-tick x) (Eq.trans (sl-comp-upd x _ _ _) (Eq.trans (sl-track-fin x _ _ _) (Eq.trans (sl-edge-upd x w _ _) h))))))

(a/theorem sl-t7 [x :- Nat, w :- World, st :- Nat, s :- Nat, k :- Nat, fresh :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t7-track w st s k fresh))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t7-track ht refuse]) (exact h)
  (cases hs (source-find w s)) (case' [some sr]) (case' [none])
  (simp only [t7-track ht hs refuse]) (exact h)
  (cases hk (trackable sr))
  (simp only [t7-track ht hs hk refuse]) (exact h)
  (cases hc (comp-has w (:of r)))
  (cases hta (task-has w (:of r)))
  (simp only [t7-track ht hs hk hc hta refuse]) (exact h)
  (simp only [t7-track ht hs hk hc hta accept]) (exact (sl-run-upd x w _ _ (keeps-run-tick x) h))
  (cases hg (Bool.or (Nat.beq fresh (:next-id w)) (opt-some (site-edge (:edges w) (:of r) (:effect-index r) s))))
  (simp only [t7-track ht hs hk hc hg refuse]) (exact h)
  (simp only [t7-track ht hs hk hc hg accept]) (exact (sl-track-raw x w r s sr k h)))

(a/theorem sl-t8-unobserve [x :- Nat, w :- World, y :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t8-unobserve w y))) true))
  (intro h)
  (cases hf (edge-find w y)) (case' [some e]) (case' [none])
  (simp only [t8-unobserve hf refuse]) (exact h)
  (cases hk (Nat.beq (:kind e) ek-observe))
  (simp only [t8-unobserve hf hk refuse]) (exact h)
  (simp only [t8-unobserve hf hk accept sl-remove-edge]) (exact h))

(a/theorem sl-t9 [x :- Nat, w :- World, y :- Nat, tag :- Nat, v :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t9-fire w y tag v))) true))
  (intro h)
  (cases hg (fire-tok-ok w y))
  (simp only [t9-fire hg refuse]) (exact h)
  (simp only [t9-fire hg accept]) (exact (sl-fire-edge x _ w y h)))

(a/theorem sl-ack-raw [x :- Nat, w :- World, z :- Nat, o :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (ack-raw w z o)) true))
  (intro h) (simp only [ack-raw sl-cleanup-upd])
  (exact (sl-run-upd x _ _ _ (keeps-run-unres x z) (Eq.trans (sl-resource-del x w z) h))))

(a/theorem sl-t18 [x :- Nat, w :- World, z :- Nat, tag :- Nat, v :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t18-resource-fire w z tag v))) true))
  (intro h)
  (cases hf (resource-find w z)) (case' [some zr]) (case' [none])
  (simp only [t18-resource-fire hf refuse]) (exact h)
  (cases hp (Nat.beq (:phase zr) rp-armed))
  (simp only [t18-resource-fire hf hp refuse]) (exact h)
  (simp only [t18-resource-fire hf hp accept])
  (exact (sl-fold-fire x _ _ _ (Eq.trans (sl-resource-upd x w z _) h))))

(a/theorem sl-drop-pub-handle [x :- Nat, w :- World, y :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (drop-pub-handle w y))) true))
  (intro h)
  (cases hp (pub-find w y)) (case' [some p]) (case' [none])
  (simp only [drop-pub-handle hp refuse]) (exact h)
  (cases hh (Nat.blt 0 (:handles p)))
  (all_goals (simp only [drop-pub-handle hp hh refuse accept sl-pub-upd]))
  (all_goals (exact h)))

(a/theorem sl-drop-source-handle [x :- Nat, w :- World, y :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (drop-source-handle w y))) true))
  (intro h)
  (cases hs (source-find w y)) (case' [some s]) (case' [none])
  (simp only [drop-source-handle hs]) (exact (sl-drop-pub-handle x w y h))
  (cases hh (Nat.blt 0 (:handles s)))
  (all_goals (simp only [drop-source-handle hs hh refuse accept sl-source-upd]))
  (all_goals (exact h)))

(a/theorem sl-drop-task-handle [x :- Nat, w :- World, y :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (drop-task-handle w y))) true))
  (intro h)
  (cases ht (task-find w y)) (case' [some t]) (case' [none])
  (simp only [drop-task-handle ht]) (exact (sl-drop-source-handle x w y h))
  (cases hh (Nat.blt 0 (:handles t)))
  (all_goals (simp only [drop-task-handle ht hh refuse accept sl-task-upd]))
  (all_goals (exact h)))

(a/theorem sl-t19 [x :- Nat, w :- World, y :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t19-handle-drop w y))) true))
  (intro h)
  (cases hc (comp-find w y)) (case' [some c]) (case' [none])
  (simp only [t19-handle-drop hc]) (exact (sl-drop-task-handle x w y h))
  (cases hh (Nat.blt 0 (:handles c)))
  (all_goals (simp only [t19-handle-drop hc hh refuse accept sl-comp-upd]))
  (all_goals (exact h)))

(a/theorem sl-t20-pin [x :- Nat, w :- World, y :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t20-pin w y))) true))
  (intro h)
  (cases hg (Bool.or (comp-has w y) (source-has w y)))
  (all_goals (simp only [t20-pin hg refuse accept sl-set-pins]))
  (all_goals (exact h)))

(a/theorem sl-t20-unpin [x :- Nat, w :- World, y :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t20-unpin w y))) true))
  (intro h)
  (cases hg (nat-mem y (:pins w)))
  (all_goals (simp only [t20-unpin hg refuse accept sl-set-pins]))
  (all_goals (exact h)))

;; ---- rule.clj: T10, T13, T14, T16, the cascade, Rule R

(a/theorem sl-fin-loop [x :- Nat, fuel :- (List Nat)]
  (forall [w :- World, ds :- (List Nat)]
    (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (fin-loop fuel w ds))) true)))
  (induction fuel)
  (case' [cons h f ih])
  (case' [nil])
  (intros w ds hw) (simp only [fin-loop]) (exact hw)
  (intros w ds hw)
  (cases ds)
  (simp only [fin-loop]) (exact hw)
  (rename_i d t)
  (simp only [fin-loop])
  (exact (ih _ _ (Eq.trans (sl-finalize-one x w d) hw))))

(a/theorem sl-finalize-debtor [x :- Nat, w :- World, d :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (finalize-debtor w d)) true))
  (intro h) (simp only [finalize-debtor]) (exact (sl-fin-loop x _ w _ h)))

(a/theorem sl-close-source [x :- Nat, w :- World, s :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (close-source w s)) true))
  (intro h) (simp only [close-source wake-closed])
  (exact (sl-finalize-debtor x _ s (sl-fold-fire x _ _ _ (Eq.trans (sl-source-upd x w s _) h)))))

(a/theorem sl-close-local [x :- Nat, w :- World, sub :- (List Nat)]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (close-local w sub)) true))
  (intro h) (simp only [close-local])
  (exact (nat-fold-pres (i10-slice-at x) close-source (sl-close-source x) _ _
           (sl-fold-frame x close-scope-id (sl-close-scope-id x) w sub h))))

(a/theorem sl-remove-if-empty [x :- Nat, w :- World, sub :- (List Nat)]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (remove-if-empty w sub)) true))
  (intro h)
  (cases he (subtree-empty w sub))
  (simp only [remove-if-empty he]) (exact h)
  (simp only [remove-if-empty he]) (exact (sl-fold-frame x scope-del (sl-scope-del x) w sub h)))

(a/theorem sl-invalidate-id [x :- Nat, w :- World, y :- Nat]
  (= (i10-slice-at x (invalidate-id w y)) (i10-slice-at x w))
  (cases hf (edge-find w y)) (case' [some e]) (case' [none])
  (simp only [invalidate-id hf])
  (cases hp (Nat.beq (:phase e) ph-armed))
  (all_goals (simp only [invalidate-id hf hp sl-invalidate])))

(a/theorem sl-debtor-side [x :- Nat, w :- World, r :- RunRow]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (debtor-side w r)) true))
  (intro h)
  (cases hc (comp-find w (:of r))) (case' [some c]) (case' [none])
  (simp only [debtor-side hc fire-task-cancelled])
  (exact (sl-finalize-debtor x _ _ (sl-fold-fire x _ _ _ (Eq.trans (sl-task-upd x w _ _) h))))
  (cases he (Nat.beq (:epoch r) (:epoch c)))
  (simp only [debtor-side hc he]) (exact h)
  (simp only [debtor-side hc he invalidate-dependents fire-waits-cancelled])
  (exact (sl-fold-frame x invalidate-id (sl-invalidate-id x) _ _ (sl-fold-fire x _ _ _ h))))

(a/theorem sl-cancel-run-local [x :- Nat, w :- World, r :- RunRow, rep :- Bool]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (cancel-run-local w r rep)) true))
  (intro h)
  (have h1 (= (i10-slice-at x (cleanup-set (cancel-res (cancel-acts (run-upd w (:id r) run-cancel-row) (:id r)) r)
                                           (:id r) (cleanup-rows-of w r))) true))
  (rw [sl-cleanup-set]) (simp only [cancel-res cancel-acts])
  (exact (sl-fold-frame x res-cancel (sl-res-cancel x) _ _
           (sl-fold-frame x drop-act (sl-drop-act x) _ _ (sl-run-upd x w _ _ (keeps-run-cancel-row x) h))))
  (cases hr (Bool.and rep (comp-has (cleanup-set (cancel-res (cancel-acts (run-upd w (:id r) run-cancel-row) (:id r)) r) (:id r) (cleanup-rows-of w r)) (:of r))))
  (simp only [cancel-run-local cancel-debtor hr]) (exact (sl-debtor-side x _ r h1))
  (simp only [cancel-run-local cancel-debtor hr]) (exact h1))

(a/theorem sl-clear-task-run [x :- Nat, w :- World, r :- RunRow]
  (= (i10-slice-at x (clear-task-run w r)) (i10-slice-at x w))
  (cases ht (task-find w (:of r))) (case' [some t]) (case' [none])
  (simp only [clear-task-run ht])
  (cases hb (Nat.beq (:run t) (:id r)))
  (all_goals (simp only [clear-task-run ht hb sl-task-upd])))

(a/theorem sl-clear-comp-run [x :- Nat, w :- World, r :- RunRow]
  (= (i10-slice-at x (clear-comp-run w r)) (i10-slice-at x w))
  (cases hc (comp-find w (:of r))) (case' [some c]) (case' [none])
  (simp only [clear-comp-run hc sl-clear-task-run])
  (cases hb (Nat.beq (:run c) (:id r)))
  (all_goals (simp only [clear-comp-run hc hb sl-comp-upd])))

(a/theorem sl-retire-local [x :- Nat, w :- World, r :- RunRow]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (retire-local w r)) true))
  (intro h) (simp only [retire-local retire-with])
  (exact (sl-remove-if-empty x _ _
           (Eq.trans (sl-cleanup-del x _ _)
             (sl-run-del x _ _ (sl-close-local x _ _ (Eq.trans (sl-clear-comp-run x w r) h)))))))

(a/theorem sl-close-scope-local [x :- Nat, w :- World, s :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (close-scope-local w s)) true))
  (intro h) (simp only [close-scope-local close-with])
  (exact (sl-remove-if-empty x _ _ (sl-close-local x w _ h))))

(a/theorem sl-job-apply [x :- Nat, w :- World, j :- Job]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (job-apply w j)) true))
  (intro h)
  (cases j)
  (rename_i rid rep)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [job-apply hf]) (exact h)
  (cases ha (run-alive r))
  (simp only [job-apply hf ha]) (exact h)
  (simp only [job-apply hf ha]) (exact (sl-cancel-run-local x w r rep h))
  (rename_i rid)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [job-apply hf]) (exact h)
  (cases ha (retirable r))
  (simp only [job-apply hf ha]) (exact h)
  (simp only [job-apply hf ha]) (exact (sl-retire-local x w r h))
  (rename_i s)
  (cases hs (scope-has w s))
  (simp only [job-apply hs]) (exact h)
  (simp only [job-apply hs]) (exact (sl-close-scope-local x w s h)))

(a/theorem sl-cascade [x :- Nat, fuel :- (List Nat)]
  (forall [w :- World, js :- (List Job)]
    (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (cascade fuel w js))) true)))
  (induction fuel)
  (case' [cons h f ih])
  (case' [nil])
  (intros w js hw) (simp only [cascade]) (exact hw)
  (intros w js hw)
  (cases js)
  (simp only [cascade]) (exact hw)
  (rename_i j t)
  (simp only [cascade])
  (exact (ih (job-apply w j) (List.append Job t (job-next w j)) (sl-job-apply x w j hw))))

(a/theorem sl-run-cascade [x :- Nat, w :- World, js :- (List Job)]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (run-cascade w js)) true))
  (intro h) (simp only [run-cascade cascade-run]) (exact (sl-cascade x _ w js h)))

(a/theorem sl-t14 [x :- Nat, w :- World, rid :- Nat, rep :- Bool]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t14-cancel w rid rep))) true))
  (intro h)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [t14-cancel hf refuse]) (exact h)
  (cases ha (run-alive r))
  (simp only [t14-cancel hf ha refuse]) (exact h)
  (simp only [t14-cancel hf ha accept]) (exact (sl-run-cascade x w _ h)))

(a/theorem sl-t16 [x :- Nat, w :- World, s :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t16-close-scope w s))) true))
  (intro h)
  (cases hs (scope-has w s))
  (simp only [t16-close-scope hs refuse]) (exact h)
  (simp only [t16-close-scope hs accept]) (exact (sl-run-cascade x w _ h)))

(a/theorem sl-retire-full [x :- Nat, w :- World, rid :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (retire-full w rid)) true))
  (intro h) (simp only [retire-full]) (exact (sl-run-cascade x w _ h)))

(a/theorem sl-t15 [x :- Nat, w :- World, z :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t15-full w z))) true))
  (intro h)
  (cases hg (ack-tok-ok w z))
  (simp only [t15-full hg refuse]) (exact h)
  (cases hf (resource-find w z)) (case' [some zr]) (case' [none])
  (simp only [t15-full hg hf refuse]) (exact h)
  (simp only [t15-full hg hf accept]) (exact (sl-retire-full x _ _ (sl-ack-raw x w z _ h))))

(a/theorem sl-demote-epoch [x :- Nat, w :- World, cid :- Nat, b :- Bool]
  (= (i10-slice-at x (demote-epoch w cid b)) (i10-slice-at x w))
  (cases b) (all_goals (simp only [demote-epoch sl-comp-upd])))

(a/theorem sl-demote [x :- Nat, w :- World, cid :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (demote w cid)) true))
  (intro h)
  (cases hc (comp-find w cid)) (case' [some c]) (case' [none])
  (simp only [demote hc]) (exact h)
  (cases hi (:idle c))
  (simp only [demote hc hi demote-edges])
  (have h1 := (Eq.trans (sl-demote-epoch x _ cid (demote-cur w c)) (sl-run-cascade x w (cancel-jobs (demote-cancels w c)) h)))
  (have h2 := (Eq.trans (sl-drop-edges x _ (not-dep-of cid)) h1))
  (cases hf (comp-find (drop-edges (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) cid (demote-cur w c)) (not-dep-of cid)) cid))
  (case' [some c2]) (case' [none])
  (simp only [demote-finish hf]) (exact h2)
  (cases hk (demote-keep (drop-edges (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) cid (demote-cur w c)) (not-dep-of cid)) c2))
  (simp only [demote-finish hf hk sl-comp-del sl-drop-edges]) (exact h2)
  (simp only [demote-finish hf hk sl-comp-upd]) (exact h2)
  (simp only [demote hc hi]) (exact h))

(a/theorem sl-detach [x :- Nat, w :- World]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (detach w)) true))
  (intro h) (simp only [detach])
  (have hs (forall [w2 :- World, y :- Nat] (=> (= (i10-slice-at x w2) true) (= (i10-slice-at x (detach-source w2 y)) true))))
  (intros w2 y hw) (simp only [detach-source wake-closed])
  (exact (sl-finalize-debtor x _ y (sl-fold-fire x _ _ _ (Eq.trans (sl-source-upd x w2 y _) hw))))
  (have ht (forall [w2 :- World, y :- Nat] (= (i10-slice-at x (detach-task w2 y)) (i10-slice-at x w2))))
  (intros w2 y) (simp only [detach-task sl-task-upd])
  (have hc (forall [w2 :- World, y :- Nat] (= (i10-slice-at x (detach-comp w2 y)) (i10-slice-at x w2))))
  (intros w2 y) (simp only [detach-comp sl-comp-upd])
  (exact (sl-fold-frame x detach-comp hc _ _ (sl-fold-frame x detach-task ht _ _
           (nat-fold-pres (i10-slice-at x) detach-source hs _ w h)))))

(a/theorem sl-norm-round [x :- Nat, w :- World]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (norm-round w)) true))
  (intro h) (simp only [norm-round norm-round-lv])
  (exact (sl-detach x _ (nat-fold-pres (i10-slice-at x) demote (sl-demote x) _ _ (sl-run-cascade x w _ h)))))

(a/theorem sl-norm-loop [x :- Nat, fuel :- (List Nat)]
  (forall [w :- World] (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (norm-loop fuel w)) true)))
  (induction fuel)
  (case' [cons h f ih])
  (case' [nil])
  (intros w hw) (simp only [norm-loop]) (exact hw)
  (intros w hw)
  (cases hn (normalized w))
  (simp only [norm-loop hn]) (exact (ih _ (sl-norm-round x w hw)))
  (simp only [norm-loop hn]) (exact hw))

(a/theorem sl-normalize [x :- Nat, w :- World]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (normalize w)) true))
  (intro h) (simp only [normalize]) (exact (sl-norm-loop x _ _ (sl-detach x w h))))

(a/theorem sl-rule-r-round [x :- Nat, w :- World]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (rule-r-round w)) true))
  (intro h) (simp only [rule-r-round rule-r-filter rule-r-filter-lv])
  (exact (sl-filter-world x _ _ (sl-normalize x w h))))

(a/theorem sl-rr-loop [x :- Nat, fuel :- (List Nat)]
  (forall [w :- World] (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (rr-loop fuel w)) true)))
  (induction fuel)
  (case' [cons h f ih])
  (case' [nil])
  (intros w hw) (simp only [rr-loop]) (exact hw)
  (intros w hw)
  (cases hn (no-orphans w))
  (simp only [rr-loop hn]) (exact (ih _ (sl-rule-r-round x w hw)))
  (simp only [rr-loop hn]) (exact hw))

(a/theorem sl-rule-r [x :- Nat, w :- World]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (rule-r w)) true))
  (intro h) (simp only [rule-r]) (exact (sl-rr-loop x _ _ (sl-rule-r-round x w h))))

;; ---- engine.clj Parts A-E

(a/theorem sl-insert-edge-checked [x :- Nat, w :- World, e :- EdgeRow]
  (= (i10-slice-at x (insert-edge-checked w e)) (i10-slice-at x w))
  (cases hk (edge-ok-in w e))
  (all_goals (simp only [insert-edge-checked hk sl-insert-edge-fresh])))

(a/theorem new-run-row-slice [id :- Nat, of :- Nat, ep :- Nat, sc :- Nat, ei :- Nat]
  (= (:slice (new-run-row id of ep sc ei)) false) (rfl))

(a/theorem sl-add-run-scope [x :- Nat, w :- World, of :- Nat, ep :- Nat, par :- Nat, ei :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (add-run-scope w of ep par ei)) true))
  (intro h) (simp only [add-run-scope sl-bump sl-scope-ins])
  (exact (sl-run-ins x w _ (new-run-row-slice _ _ _ _ _) h)))

(a/theorem sl-raise-loop [x :- Nat, fuel :- (List Nat)]
  (forall [d :- Nat, w :- World, todo :- (List RJ)]
    (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (raise-loop fuel d w todo))) true)))
  (induction fuel)
  (case [nil] (intros d w todo h) (cases todo) (all_goals (simp only [raise-loop])) (all_goals (exact h)))
  (case [cons u f ih]
    (intros d w todo h)
    (cases todo)
    (case [nil] (simp only [raise-loop]) (exact h))
    (case [cons j t]
      (cases hd (Nat.beq (:node j) d))
      (case [true] (simp only [raise-loop hd]) (exact h))
      (case [false]
        (cases hn (Nat.ble (:need j) (comp-rank w (:node j))))
        (case [true] (simp only [raise-loop hd hn]) (exact (ih d w t h)))
        (case [false]
          (simp only [raise-loop hd hn])
          (exact (ih d _ _ (Eq.trans (sl-comp-upd x w _ _) h))))))))

(a/theorem sl-raise-run [x :- Nat, w :- World, c :- Nat, d :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (raise-run w c d))) true))
  (intro h)
  (cases hd (comp-has w d))
  (simp only [raise-run hd]) (exact h)
  (simp only [raise-run hd]) (exact (sl-raise-loop x (raise-fuel w) d w _ h)))

(a/theorem sl-react-add [x :- Nat, w :- World, c :- Nat, v :- Valid]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (react-add w c v)) true))
  (intro h)
  (cases hk (react-ok w c v))
  (simp only [react-add hk]) (exact h)
  (simp only [react-add hk])
  (exact (sl-raise-run x _ c (:debtor v) (Eq.trans (sl-insert-edge-checked x w _) h))))

(a/theorem sl-react-edges [x :- Nat, vs :- (List Valid)]
  (forall [w :- World, c :- Nat] (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (react-edges w c vs)) true)))
  (induction vs)
  (case' [cons h t ih])
  (case' [nil])
  (intros w c hw) (simp only [react-edges]) (exact hw)
  (intros w c hw) (simp only [react-edges]) (exact (ih _ c (sl-react-add x w c h hw))))

(a/theorem sl-react-loop [x :- Nat, fuel :- (List Nat)]
  (forall [w :- World, q :- (List Nat)] (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (react-loop fuel w q)) true)))
  (induction fuel)
  (case' [cons h f ih])
  (case' [nil])
  (intros w q hw) (simp only [react-loop]) (exact hw)
  (intros w q hw)
  (cases q)
  (simp only [react-loop]) (exact hw)
  (rename_i y t)
  (cases hc (comp-find w y)) (case' [some c]) (case' [none])
  (simp only [react-loop hc]) (exact (ih w t hw))
  (cases hi (:idle c))
  (simp only [react-loop hc hi]) (exact (ih w t hw))
  (simp only [react-loop hc hi react-one])
  (exact (ih _ _ (sl-react-edges x (:validity c) _ (:id c) (Eq.trans (sl-comp-upd x w _ _) hw)))))

(a/theorem sl-demand-reactive [x :- Nat, w :- World, d :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (demand-reactive w d)) true))
  (intro h)
  (cases hc (comp-find w d)) (case' [some c]) (case' [none])
  (simp only [demand-reactive hc]) (exact h)
  (cases hi (:idle c))
  (simp only [demand-reactive hc hi]) (exact h)
  (cases hv (valid-idle w c))
  (simp only [demand-reactive hc hi hv sl-comp-upd]) (exact h)
  (simp only [demand-reactive hc hi hv]) (exact (sl-react-loop x (react-fuel w) w _ h)))

(a/theorem sl-spawn-rows [x :- Nat, w :- World, owner :- Nat, ins :- (List Nat)]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (spawn-rows w owner ins)) true))
  (intro h) (simp only [spawn-rows])
  (exact (sl-add-run-scope x _ _ _ _ _ (Eq.trans (sl-bump x _) (Eq.trans (sl-task-ins x w _) h)))))

(a/theorem sl-respawn-raw [x :- Nat, w :- World, r :- RunRow, y :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (respawn-raw w r y)) true))
  (intro h) (simp only [respawn-raw])
  (exact (sl-run-upd x _ _ _ (keeps-run-tick x) (Eq.trans (sl-comp-upd x w _ _) h))))

(a/theorem sl-t4 [x :- Nat, w :- World, st :- Nat, body :- Nat, fresh :- Nat, ins :- (List Nat)]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t4-spawn w st body fresh ins))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t4-spawn ht refuse]) (exact h)
  (cases hr (respawn-target w r fresh)) (case' [some t]) (case' [none])
  (cases hf (Nat.beq fresh (:next-id w)))
  (simp only [t4-spawn ht hr hf refuse]) (exact h)
  (simp only [t4-spawn ht hr hf accept])
  (exact (sl-run-upd x _ _ _ (keeps-run-tick x) (Eq.trans (sl-record-basis x _ r fresh) (sl-spawn-rows x w _ ins h))))
  (cases hi (nat-list-eq ins (:inputs t)))
  (simp only [t4-spawn ht hr hi refuse]) (exact h)
  (simp only [t4-spawn ht hr hi accept]) (exact (sl-respawn-raw x w r fresh h)))

(a/theorem sl-t4-top [x :- Nat, w :- World, sc :- Nat, body :- Nat, fresh :- Nat, ins :- (List Nat)]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t4-spawn-top w sc body fresh ins))) true))
  (intro h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (scope-open-at w sc)))
  (simp only [t4-spawn-top hg refuse]) (exact h)
  (simp only [t4-spawn-top hg accept]) (exact (sl-spawn-rows x w sc ins h)))

(a/theorem sl-t5 [x :- Nat, w :- World, cid :- Nat, fresh :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t5-start w cid fresh))) true))
  (intro h)
  (cases hc (comp-find w cid)) (case' [some c]) (case' [none])
  (simp only [t5-start hc refuse]) (exact h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (startable w c)))
  (simp only [t5-start hc hg refuse]) (exact h)
  (simp only [t5-start hc hg accept start-raw sl-comp-upd]) (exact (sl-add-run-scope x w _ _ _ _ h)))

(a/theorem sl-mark-from [x :- Nat, w :- World, c :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (mark-from w c)) true))
  (intro h) (simp only [mark-from]) (exact (sl-fold-frame x mark-edge (sl-mark-edge x) w _ h)))

(a/theorem sl-create-comp-raw [x :- Nat, w :- World, c :- Nat, owner :- Nat, ins :- (List Nat), body :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (create-comp-raw w c owner ins body)) true))
  (intro h)
  (cases hf (comp-find w c)) (case' [some row]) (case' [none])
  (simp only [create-comp-raw hf sl-bump sl-comp-ins]) (exact h)
  (cases he (nat-list-eq (:inputs row) ins))
  (simp only [create-comp-raw hf he]) (exact (sl-mark-from x _ c (Eq.trans (sl-comp-upd x w _ _) h)))
  (simp only [create-comp-raw hf he sl-comp-upd]) (exact h))

(a/theorem sl-t3 [x :- Nat, w :- World, st :- Nat, c :- Nat, ins :- (List Nat), body :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t3-create w st c ins body))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t3-create ht refuse]) (exact h)
  (cases hg (create-ok w c))
  (simp only [t3-create ht hg refuse]) (exact h)
  (simp only [t3-create ht hg accept])
  (exact (sl-run-upd x _ _ _ (keeps-run-tick x) (Eq.trans (sl-record-basis x _ r c) (sl-create-comp-raw x w c _ ins body h)))))

(a/theorem sl-t3-top [x :- Nat, w :- World, sc :- Nat, c :- Nat, ins :- (List Nat), body :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t3-create-top w sc c ins body))) true))
  (intro h)
  (cases hg (Bool.and (create-ok w c) (scope-open-at w sc)))
  (simp only [t3-create-top hg refuse]) (exact h)
  (simp only [t3-create-top hg accept]) (exact (sl-create-comp-raw x w c sc ins body h)))

(a/theorem sl-consume-entry [x :- Nat, w :- World, e :- EdgeRow]
  (= (i10-slice-at x (consume-entry w e)) (i10-slice-at x w))
  (cases hf (deb-final w (:debtor e)))
  (all_goals (cases hc (Nat.beq (:cont e) cont-restart)))
  (all_goals (simp only [consume-entry hc hf sl-edge-upd sl-remove-edge])))

(a/theorem sl-cancel-pred [x :- Nat, w :- World, c :- CompRow]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (cancel-pred w c)) true))
  (intro h)
  (cases hf (run-find w (:run c))) (case' [some r]) (case' [none])
  (simp only [cancel-pred hf]) (exact h)
  (cases ha (run-alive r))
  (simp only [cancel-pred hf ha]) (exact h)
  (simp only [cancel-pred hf ha]) (exact (sl-run-cascade x w _ h)))

(a/theorem sl-cut-suffix [x :- Nat, w :- World, c :- Nat, has :- Bool, cut :- Nat, cid :- Nat]
  (= (i10-slice-at x (cut-suffix w c has cut cid)) (i10-slice-at x w))
  (simp only [cut-suffix sl-comp-upd sl-drop-edges]))

(a/theorem sl-new-run-of [x :- Nat, w :- World, c :- CompRow, ei :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (new-run-of w c ei)) true))
  (intro h) (simp only [new-run-of sl-comp-upd]) (exact (sl-add-run-scope x w _ _ _ _ h)))

(a/theorem sl-t11 [x :- Nat, w :- World, cid :- Nat, fresh :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t11-dispatch w cid fresh))) true))
  (intro h)
  (cases hc (comp-find w cid)) (case' [some c]) (case' [none])
  (simp only [t11-dispatch hc refuse]) (exact h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (Bool.not (:idle c)) (Bool.and (needs-run w c) (eligible w c)))))
  (simp only [t11-dispatch hc hg refuse]) (exact h)
  (simp only [t11-dispatch hc hg accept])
  (have h1 := (sl-cancel-pred x w c h))
  (cases he (entry-edge w (:id c))) (case' [some e]) (case' [none])
  (simp only [dispatch-raw he]) (exact (sl-new-run-of x _ c _ (Eq.trans (sl-cut-suffix x _ _ _ _ _) h1)))
  (simp only [dispatch-raw he])
  (exact (sl-new-run-of x _ c _ (Eq.trans (sl-consume-entry x _ e) (Eq.trans (sl-cut-suffix x _ _ _ _ _) h1)))))

(a/theorem sl-settle-edge [x :- Nat, changed :- Bool, ver :- Nat, w :- World, y :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (settle-edge changed ver w y)) true))
  (intro h)
  (cases hf (edge-find w y)) (case' [some e]) (case' [none])
  (simp only [settle-edge hf]) (exact h)
  (simp only [settle-edge hf sl-unmark-edge])
  (cases hp (Nat.beq (:phase e) ph-armed))
  (simp only [hp]) (exact h)
  (cases hc (Bool.or (edge-behind ver e) (member-current w e)))
  (simp only [hp hc]) (exact h)
  (simp only [hp hc]) (exact (sl-fire-dep x w e h)))

(a/theorem sl-settle-one [x :- Nat, w :- World, d :- Nat, changed :- Bool]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (settle-one w d changed)) true))
  (intro h) (simp only [settle-one settle-host])
  (exact (sl-fold-fire x _ _ _ (nat-fold-pres (i10-slice-at x) (settle-edge changed (deb-version w d))
                                  (sl-settle-edge x changed (deb-version w d)) _ w h))))

(a/theorem sl-settle-loop [x :- Nat, fuel :- (List Nat)]
  (forall [w :- World, q :- (List Nat)] (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (settle-loop fuel w q))) true)))
  (induction fuel)
  (case' [cons h f ih])
  (case' [nil])
  (intros w q hw) (simp only [settle-loop]) (exact hw)
  (intros w q hw)
  (cases q)
  (simp only [settle-loop]) (exact hw)
  (rename_i d t)
  (simp only [settle-loop])
  (exact (ih _ _ (sl-settle-one x w d false hw))))

(a/theorem sl-settle [x :- Nat, w :- World, d :- Nat, changed :- Bool]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (settle w d changed)) true))
  (intro h)
  (cases hr (ready-id w d))
  (simp only [settle hr]) (exact h)
  (simp only [settle hr settle-res])
  (exact (sl-settle-loop x (settle-fuel w) _ _ (sl-settle-one x w d changed h))))

(a/theorem sl-fin-if-final [x :- Nat, w :- World, d :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (fin-if-final w d)) true))
  (intro h)
  (cases hf (deb-final w d))
  (simp only [fin-if-final hf]) (exact h)
  (simp only [fin-if-final hf]) (exact (sl-finalize-debtor x w d h)))

(a/theorem sl-complete-body [x :- Nat, w :- World, r :- RunRow, res :- RunResult]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (complete-body w r res))) true))
  (intro h)
  (cases hc (comp-find w (:of r)))
  (case [none]
    (cases ht (task-find w (:of r)))
    (case [none] (simp only [complete-body hc ht]) (exact h))
    (case [some k]
      (simp only [complete-body hc ht complete-task])
      (exact (sl-fold-fire x _ _ _ (sl-fold-frame x res-cancel (sl-res-cancel x) _ _ (Eq.trans (sl-task-upd x w _ _) h))))))
  (case [some c]
    (cases he (Nat.beq (:epoch r) (:epoch c)))
    (case [false] (simp only [complete-body hc he]) (exact h))
    (case [true]
      (simp only [complete-body hc he complete-comp cancel-res])
      (exact (sl-settle x _ _ _ (sl-fold-frame x res-cancel (sl-res-cancel x) _ _ (Eq.trans (sl-comp-upd x w _ _) h)))))))

(a/theorem sl-retire-after [x :- Nat, w :- World, rid :- Nat]
  (= (i10-slice-at x (retire-after w rid)) (i10-slice-at x w))
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [retire-after hf])
  (cases hr (retirable r))
  (all_goals (simp only [retire-after hf hr sl-cleanup-set])))

(a/theorem sl-t12 [x :- Nat, w :- World, st :- Nat, tag :- Nat, v :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t12-complete w st tag v))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t12-complete ht refuse]) (exact h)
  (cases hn (run-normal r))
  (simp only [t12-complete ht hn refuse]) (exact h)
  (simp only [t12-complete ht hn accept complete-raw])
  (have h1 := (sl-run-upd x w (:id r) run-complete-row (keeps-run-complete-row x) h))
  (have h2 := (sl-complete-body x _ r (RunResult.mk tag v) h1))
  (exact (sl-fin-if-final x _ _ (sl-run-cascade x _ _ (Eq.trans (sl-retire-after x _ _) h2)))))

;; ---- engine.clj Parts F, F2

(a/theorem sl-await-step [x :- Nat, r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, acc :- AwAcc, d :- Nat]
  (=> (= (i10-slice-at x (:world acc)) true) (= (i10-slice-at x (:world (await-step r a mode k acc d))) true))
  (intro h)
  (cases hd (as-dep (:world acc) r d))
  (case [false]
    (simp only [await-step hd sl-insert-edge-checked]) (exact h))
  (case [true]
    (cases hs (site-edge (:edges (:world acc)) (:of r) (:effect-index r) d))
    (case [none]
      (simp only [await-step hd hs await-new-dep sl-comp-upd])
      (exact (sl-raise-run x _ (:of r) d (Eq.trans (sl-insert-edge-checked x _ _) h))))
    (case [some e]
      (simp only [await-step hd hs sl-comp-upd sl-edge-upd]) (exact h))))

(a/theorem sl-await-wire [x :- Nat, r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, ds :- (List Nat)]
  (forall [acc :- AwAcc] (=> (= (i10-slice-at x (:world acc)) true) (= (i10-slice-at x (:world (await-wire r a mode k acc ds))) true)))
  (induction ds)
  (case' [cons d t ih])
  (case' [nil])
  (intros acc h) (simp only [await-wire]) (exact h)
  (intros acc h) (simp only [await-wire]) (exact (ih _ (sl-await-step x r a mode k acc d h))))

(a/theorem sl-fast-fill [x :- Nat, ps :- (List DE), w :- World, d :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (fast-fill ps w d)) true))
  (intro h)
  (cases hr (fast-ready w d))
  (simp only [fast-fill hr]) (exact h)
  (simp only [fast-fill hr]) (exact (sl-fire-edge x _ w _ h)))

(a/theorem sl-park-if [x :- Nat, w :- World, a :- Nat, rid :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (park-if w a rid)) true))
  (intro h)
  (cases ha (act-has w a))
  (simp only [park-if ha]) (exact h)
  (simp only [park-if ha]) (exact (sl-run-upd x w rid run-park-row (keeps-run-park-row x) h)))

(a/theorem sl-await-raw [x :- Nat, w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (await-raw w r ds mode k mine)) true))
  (intro h)
  (have h0 (= (i10-slice-at x (await-pre w r ds mode k mine)) true))
  (simp only [await-pre])
  (exact (nat-fold-pres (i10-slice-at x) demand-reactive (sl-demand-reactive x) _ _
           (Eq.trans (sl-bump x _) (Eq.trans (sl-act-ins x _ _) (sl-run-upd x w _ _ (keeps-run-tick x) h)))))
  (have h1 (= (i10-slice-at x (:world (await-acc w r ds mode k mine))) true))
  (exact (sl-await-wire x r (:next-id w) mode k (nat-distinct ds)
           (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) h0))
  (simp only [await-raw await-post])
  (exact (nat-fold-pres (i10-slice-at x) fin-if-final (sl-fin-if-final x) _ _
           (sl-park-if x _ _ _ (nat-fold-pres (i10-slice-at x) (fast-fill (:pairs (await-acc w r ds mode k mine)))
                                  (sl-fast-fill x (:pairs (await-acc w r ds mode k mine))) _ _
                                  (Eq.trans (sl-act-upd x _ _ _) h1))))))

(a/theorem sl-t6 [x :- Nat, w :- World, st :- Nat, ds :- (List Nat), mode :- Nat, k :- Nat, fresh :- Nat, mine :- (List Nat)]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t6-await w st ds mode k fresh mine))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t6-await ht refuse]) (exact h)
  (cases hg (Bool.and (await-ok w r ds mode fresh) (:ok (await-acc w r ds mode k mine))))
  (simp only [t6-await ht hg refuse]) (exact h)
  (simp only [t6-await ht hg accept]) (exact (sl-await-raw x w r ds mode k mine h)))

(a/theorem sl-host-await-dem [x :- Nat, w :- World, d :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (host-await-dem w d)) true))
  (intro h) (simp only [host-await-dem])
  (exact (sl-demand-reactive x _ d (Eq.trans (sl-insert-edge-checked x w _) h))))

(a/theorem sl-t22 [x :- Nat, w :- World, d :- Nat, fresh :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t22-host-await w d fresh))) true))
  (intro h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (deb-exists w d)))
  (simp only [t22-host-await hg refuse]) (exact h)
  (simp only [t22-host-await hg accept])
  (have h1 := (sl-host-await-dem x w d h))
  (cases hr (fast-ready (host-await-dem w d) d))
  (simp only [host-await-raw hr]) (exact h1)
  (simp only [host-await-raw hr]) (exact (sl-fire-edge x _ _ _ h1)))

(a/theorem sl-t22-un [x :- Nat, w :- World, y :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t22-host-unawait w y))) true))
  (intro h)
  (cases hf (edge-find w y)) (case' [some e]) (case' [none])
  (simp only [t22-host-unawait hf refuse]) (exact h)
  (cases hg (Bool.and (Nat.beq (:kind e) ek-wait) (Nat.beq (:creditor e) 0)))
  (simp only [t22-host-unawait hf hg refuse]) (exact h)
  (simp only [t22-host-unawait hf hg accept sl-remove-edge]) (exact h))

(a/theorem sl-t8-full [x :- Nat, w :- World, d :- Nat, cb :- Nat, fresh :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t8-full w d cb fresh))) true))
  (intro h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (edge-ok-in w (observe-edge w d cb))))
  (simp only [t8-full hg refuse]) (exact h)
  (simp only [t8-full hg accept])
  (have h1 := (sl-demand-reactive x _ d (Eq.trans (sl-insert-edge-fresh x w (observe-edge w d cb)) h)))
  (cases hr (deb-ready (demand-reactive (insert-edge-fresh w (observe-edge w d cb)) d) d))
  (simp only [observe-raw hr]) (exact h1)
  (simp only [observe-raw hr]) (exact (sl-fire-edge x _ _ _ h1)))

(a/theorem sl-new-pub-handle [x :- Nat, w :- World, y :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (new-pub-handle w y))) true))
  (intro h)
  (cases hp (pub-find w y)) (case' [some p]) (case' [none])
  (simp only [new-pub-handle hp refuse]) (exact h)
  (cases hh (Nat.beq (:handles p) 0))
  (all_goals (simp only [new-pub-handle hp hh refuse accept sl-pub-upd]))
  (all_goals (exact h)))

(a/theorem sl-new-source-handle [x :- Nat, w :- World, y :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (new-source-handle w y))) true))
  (intro h)
  (cases hs (source-find w y)) (case' [some s]) (case' [none])
  (simp only [new-source-handle hs]) (exact (sl-new-pub-handle x w y h))
  (cases hh (Nat.beq (:handles s) 0))
  (all_goals (simp only [new-source-handle hs hh refuse accept sl-source-upd]))
  (all_goals (exact h)))

(a/theorem sl-new-task-handle [x :- Nat, w :- World, y :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (new-task-handle w y))) true))
  (intro h)
  (cases ht (task-find w y)) (case' [some t]) (case' [none])
  (simp only [new-task-handle ht]) (exact (sl-new-source-handle x w y h))
  (cases hh (Nat.beq (:handles t) 0))
  (all_goals (simp only [new-task-handle ht hh refuse accept sl-task-upd]))
  (all_goals (exact h)))

(a/theorem sl-t-handle-new [x :- Nat, w :- World, y :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t-handle-new w y))) true))
  (intro h)
  (cases hc (comp-find w y)) (case' [some c]) (case' [none])
  (simp only [t-handle-new hc]) (exact (sl-new-task-handle x w y h))
  (cases hh (Nat.beq (:handles c) 0))
  (all_goals (simp only [t-handle-new hc hh refuse accept sl-comp-upd]))
  (all_goals (exact h)))

(a/theorem sl-t-deliver [x :- Nat, w :- World, s :- Nat, v :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t-deliver w s v))) true))
  (intro h)
  (cases hf (source-find w s)) (case' [some sr]) (case' [none])
  (simp only [t-deliver hf refuse]) (exact h)
  (cases hd (deliverable sr))
  (simp only [t-deliver hf hd refuse]) (exact h)
  (simp only [t-deliver hf hd accept deliver-raw deliver-fire])
  (exact (sl-finalize-debtor x _ s (sl-fold-fire x _ _ _ (sl-fold-fire x _ _ _ (Eq.trans (sl-source-upd x w s _) h))))))

(a/theorem sl-serve-or [x :- Nat, w :- World, s :- Nat, res :- RunResult, keep :- (=> SourceRow SourceRow)]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (serve-or w s res keep)) true))
  (intro h)
  (cases hw (Nat.beq (oldest-waiter w s) 0))
  (simp only [serve-or hw]) (exact (sl-fire-edge x _ w _ h))
  (simp only [serve-or hw sl-source-upd]) (exact h))

(a/theorem sl-t-post [x :- Nat, w :- World, s :- Nat, v :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t-post w s v))) true))
  (intro h)
  (cases hf (source-find w s)) (case' [some sr]) (case' [none])
  (simp only [t-post hf refuse]) (exact h)
  (cases hk (open-kind sk-mailbox sr))
  (simp only [t-post hf hk refuse]) (exact h)
  (simp only [t-post hf hk accept post-raw]) (exact (sl-serve-or x _ s _ _ (Eq.trans (sl-source-upd x w s _) h))))

(a/theorem sl-t-release [x :- Nat, w :- World, s :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t-release w s))) true))
  (intro h)
  (cases hf (source-find w s)) (case' [some sr]) (case' [none])
  (simp only [t-release hf refuse]) (exact h)
  (cases hk (open-kind sk-semaphore sr))
  (simp only [t-release hf hk refuse]) (exact h)
  (simp only [t-release hf hk accept release-raw]) (exact (sl-serve-or x _ s _ _ (Eq.trans (sl-source-upd x w s _) h))))

(a/theorem sl-t-take [x :- Nat, w :- World, st :- Nat, s :- Nat, k :- Nat, fresh :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t-take w st s k fresh))) true))
  (intro h)
  (cases ht (tok-run w st))
  (case [none] (simp only [t-take ht refuse]) (exact h))
  (case [some r]
    (cases hf (source-find w s))
    (case [none] (simp only [t-take ht hf refuse]) (exact h))
    (case [some sr]
      (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (run-normal r) (takeable sr))))
      (case [false] (simp only [t-take ht hf hg refuse]) (exact h))
      (case [true]
        (cases ha (take-ready sr))
        (case [false]
          (simp only [t-take ht hf hg ha accept take-park])
          (exact (sl-run-upd x _ _ _ (keeps-run-tick-park x)
                   (Eq.trans (sl-insert-edge-checked x _ _) (Eq.trans (sl-bump x _) (Eq.trans (sl-act-ins x w _) h))))))
        (case [true]
          (simp only [t-take ht hf hg ha accept take-now sl-bump])
          (exact (sl-run-upd x _ _ _ (keeps-run-tick x) (Eq.trans (sl-source-upd x w s _) h))))))))

;; Z#55: arm = the resource (arm-raw), then the park on its wait edge (take-park)
(a/theorem sl-t17 [x :- Nat, w :- World, st :- Nat, kind :- Nat, k :- Nat, fresh :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t17-arm w st kind k fresh))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t17-arm ht refuse]) (exact h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (run-normal r) (arm-kind-ok kind))))
  (simp only [t17-arm ht hg refuse]) (exact h)
  (have h1 (= (i10-slice-at x (arm-raw w r kind)) true))
  (simp only [arm-raw])
  (exact (sl-run-upd x _ _ _ (keeps-run-arm x _) (Eq.trans (sl-bump x _) (Eq.trans (sl-resource-ins x w _) h))))
  (simp only [t17-arm ht hg accept arm-park take-park])
  (exact (sl-run-upd x _ _ _ (keeps-run-tick-park x)
           (Eq.trans (sl-insert-edge-checked x _ _) (Eq.trans (sl-bump x _) (Eq.trans (sl-act-ins x _ _) h1))))))

(a/theorem sl-t-finally-enter [x :- Nat, w :- World, st :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t-finally-enter w st))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t-finally-enter ht refuse]) (exact h)
  (cases hg (run-normal r))
  (simp only [t-finally-enter ht hg refuse]) (exact h)
  (simp only [t-finally-enter ht hg accept]) (exact (sl-run-upd x w _ _ (keeps-run-fin-push x _) h)))

(a/theorem sl-t-finally-exit [x :- Nat, w :- World, st :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t-finally-exit w st))) true))
  (intro h)
  (cases ht (tok-run w st))
  (case [none] (simp only [t-finally-exit ht refuse]) (exact h))
  (case [some r]
    (cases he (fins-empty (:finalizers r)))
    (case [true] (simp only [t-finally-exit ht he refuse]) (exact h))
    (case [false] (simp only [t-finally-exit ht he accept]) (exact (sl-run-upd x w _ _ (keeps-run-fin-pop x) h)))))

(a/theorem sl-t-slice-exit [x :- Nat, w :- World, rid :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t-slice-exit w rid))) true))
  (intro h)
  (cases hf (run-find w rid))
  (case [none] (simp only [t-slice-exit hf refuse]) (exact h))
  (case [some r]
    (cases hg (exit-ready r))
    (case [false] (simp only [t-slice-exit hf hg refuse]) (exact h))
    (case [true]
      (simp only [t-slice-exit hf hg accept])
      (exact (sl-retire-full x _ _ (sl-run-upd x w _ _ (keeps-run-fin-pop-end x) h))))))

(a/theorem sl-t-cancel [x :- Nat, w :- World, rid :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t-cancel w rid))) true))
  (intro h)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [t-cancel hf refuse]) (exact h)
  (cases hg (host-cancel-ok w r))
  (simp only [t-cancel hf hg refuse]) (exact h)
  (simp only [t-cancel hf hg]) (exact (sl-t14 x w rid false h)))

(a/theorem sl-t-open-scope [x :- Nat, w :- World, st :- Nat, s :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t-open-scope w st s))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t-open-scope ht refuse]) (exact h)
  (cases hg (Bool.and (Nat.beq s (:next-id w)) (open-ok w r)))
  (all_goals (simp only [t-open-scope ht hg refuse accept sl-bump sl-scope-ins]))
  (all_goals (exact h)))

(a/theorem sl-t-close-scope [x :- Nat, w :- World, s :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t-close-scope w s))) true))
  (intro h)
  (cases hg (scope-explicit-at w s))
  (simp only [t-close-scope hg refuse]) (exact h)
  (simp only [t-close-scope hg]) (exact (sl-t16 x w s h)))

(a/theorem sl-t-detach [x :- Nat, w :- World, k :- Nat, s :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t-detach w k s))) true))
  (intro h)
  (cases hf (task-find w k)) (case' [some t]) (case' [none])
  (simp only [t-detach hf refuse]) (exact h)
  (cases hg (detach-ok w t s))
  (simp only [t-detach hf hg refuse]) (exact h)
  (simp only [t-detach hf hg accept remove-empty-at detach-move])
  (exact (sl-remove-if-empty x _ _ (Eq.trans (sl-scope-upd x _ _ _) (Eq.trans (sl-task-upd x w _ _) h)))))

(a/theorem sl-zero-handles [x :- Nat, w :- World]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (zero-handles w)) true))
  (intro h) (simp only [zero-handles])
  (have hc (forall [w2 :- World, y :- Nat] (= (i10-slice-at x (comp-h0-at w2 y)) (i10-slice-at x w2))))
  (intros w2 y) (simp only [comp-h0-at sl-comp-upd])
  (have ht (forall [w2 :- World, y :- Nat] (= (i10-slice-at x (task-h0-at w2 y)) (i10-slice-at x w2))))
  (intros w2 y) (simp only [task-h0-at sl-task-upd])
  (have hs (forall [w2 :- World, y :- Nat] (= (i10-slice-at x (source-h0-at w2 y)) (i10-slice-at x w2))))
  (intros w2 y) (simp only [source-h0-at sl-source-upd])
  (have hp (forall [w2 :- World, y :- Nat] (= (i10-slice-at x (pub-h0-at w2 y)) (i10-slice-at x w2))))
  (intros w2 y) (simp only [pub-h0-at sl-pub-upd])
  (exact (sl-fold-frame x pub-h0-at hp _ _ (sl-fold-frame x source-h0-at hs _ _
           (sl-fold-frame x task-h0-at ht _ _ (sl-fold-frame x comp-h0-at hc w _ h))))))

(a/theorem sl-t-release-world [x :- Nat, w :- World]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t-release-world w))) true))
  (intro h)
  (cases hr (:released w))
  (simp only [t-release-world hr accept release-world-raw])
  (exact (sl-run-cascade x _ _ (sl-zero-handles x _
           (Eq.trans (sl-set-pending-act x _ _) (Eq.trans (sl-set-pins x _ _)
             (Eq.trans (sl-drop-edges x _ _) (Eq.trans (sl-set-released x w _) h)))))))
  (simp only [t-release-world hr refuse]) (exact h))

(a/theorem sl-t1-full [x :- Nat, w :- World, st :- Nat, kind :- Nat, v :- Nat, fresh :- Nat]
  (=> (= (i10-slice-at x w) true) (= (i10-slice-at x (:world (t1-full w st kind v fresh))) true))
  (intro h)
  (cases ht (tok-run w st))
  (case [none] (simp only [t1-full ht refuse]) (exact h))
  (case [some r]
    (cases ho (readopt-source w r fresh))
    (case [none]
      (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (src-kind-ok kind)))
      (case [false] (simp only [t1-full ht ho hg refuse]) (exact h))
      (case [true]
        (simp only [t1-full ht ho hg accept create-source-cur])
        (exact (sl-run-upd x _ _ _ (keeps-run-tick x)
                 (Eq.trans (sl-record-basis x _ r _) (Eq.trans (sl-bump x _) (Eq.trans (sl-source-ins x w _) h)))))))
    (case [some sx]
      (cases hk (Nat.beq (:kind sx) kind))
      (case [false] (simp only [t1-full ht ho hk refuse]) (exact h))
      (case [true] (simp only [t1-full ht ho hk accept]) (exact (sl-respawn-raw x w r fresh h))))))

;; ---- the two scheduling choices: the slice goes to a run only when no run holds one

(a/theorem sl-enter [w :- World, y :- Nat]
  (=> (= (tbl-any run-slice (:runs w)) false) (= (i10-slice-at y (run-upd w y run-enter-row)) true))
  (intro hb)
  (have h := (slice-none y (:runs w) hb))
  (simp only [i10-slice-at run-upd set-runs])
  (have hin (forall [r :- RunRow] (=> (= (slice-only y r) true) (= (Nat.beq (run-id r) y) true) (= (slice-only y (run-enter-row r)) true))))
  (intros r hr hy) (simp only [run-id] at hy) (simp only [slice-only run-enter-row hy Bool.or_true])
  (have hout (forall [r :- RunRow] (=> (= (slice-only y r) true) (= (Nat.beq (run-id r) y) false) (= (slice-only y r) true))))
  (intros r hr hy) (exact hr)
  (exact (tbl-all-upd RunRow run-id y run-enter-row (slice-only y) (slice-only y) hin hout (:runs w) h)))

(a/theorem i10-t-schedule [w :- World, rid :- Nat]
  (=> (= (inv-i10-slice w) true) (= (inv-i10-slice (:world (t-schedule w rid))) true))
  (intro h)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [t-schedule hf refuse]) (exact h)
  (cases hg (sched-ok w r))
  (simp only [t-schedule hf hg refuse]) (exact h)
  (have hg2 := hg)
  (simp only [sched-ok Bool.and_eq_true] at hg2)
  (have hb (= (tbl-any run-slice (:runs w)) false)) (exact (bnot-true _ (And.right (And.right (And.right hg2)))))
  (simp only [t-schedule hf hg accept])
  (exact (i10-slice-intro rid _ (sl-enter w rid hb))))

(a/theorem i10-t-finalize [w :- World, rid :- Nat]
  (=> (= (inv-i10-slice w) true) (= (inv-i10-slice (:world (t-finalize w rid))) true))
  (intro h)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [t-finalize hf refuse]) (exact h)
  (cases hg (cleanup-ready w r))
  (simp only [t-finalize hf hg refuse]) (exact h)
  (have hg2 := hg)
  (simp only [cleanup-ready Bool.and_eq_true] at hg2)
  (have hb (= (tbl-any run-slice (:runs w)) false))
  (exact (bnot-true _ (And.right (And.right (And.right (And.right hg2))))))
  (simp only [t-finalize hf hg accept])
  (exact (i10-slice-intro rid _ (sl-enter w rid hb))))

;; ---- every item, then the loser cancel, then Rule R

(a/theorem i10-raw0 [w :- World, it :- Item]
  (=> (= (inv-i10-slice w) true) (= (inv-i10-slice (:world (raw0 w it))) true))
  (intro h)
  (have hx := (i10-slice-elim w h))
  (cases it)
  (all_goals (simp only [raw0]))
  (rename_i st kind v fresh) (cases hc (body-shut w st))
  (simp only [hc]) (exact (i10-slice-intro _ _ (sl-t1-full _ w _ _ _ _ hx)))
  (simp only [hc refuse]) (exact h)
  (exact (i10-slice-intro _ _ (sl-t1-top _ w _ _ _ _ hx)))
  (exact (i10-slice-intro _ _ (sl-t2 _ w _ _ hx)))
  (rename_i st s k fresh) (cases hc (in-cleanup w st))
  (simp only [hc]) (exact (i10-slice-intro _ _ (sl-t7 _ w _ _ _ _ hx)))
  (simp only [hc refuse]) (exact h)
  (exact (i10-slice-intro _ _ (sl-t8-full _ w _ _ _ hx)))
  (exact (i10-slice-intro _ _ (sl-t8-unobserve _ w _ hx)))
  (exact (i10-slice-intro _ _ (sl-t9 _ w _ _ _ hx)))
  (exact (i10-slice-intro _ _ (sl-t15 _ w _ hx)))
  (rename_i st kind k fresh) (cases hc (in-cleanup w st))
  (simp only [hc]) (exact (i10-slice-intro _ _ (sl-t17 _ w _ _ _ _ hx)))
  (simp only [hc refuse]) (exact h)
  (exact (i10-slice-intro _ _ (sl-t18 _ w _ _ _ hx)))
  (exact (i10-slice-intro _ _ (sl-t19 _ w _ hx)))
  (exact (i10-slice-intro _ _ (sl-t20-pin _ w _ hx)))
  (exact (i10-slice-intro _ _ (sl-t20-unpin _ w _ hx)))
  (rename_i st c i b) (cases hc (in-cleanup w st))
  (simp only [hc]) (exact (i10-slice-intro _ _ (sl-t3 _ w _ _ _ _ hx)))
  (simp only [hc refuse]) (exact h)
  (exact (i10-slice-intro _ _ (sl-t3-top _ w _ _ _ _ hx)))
  (rename_i st b fresh ins) (cases hc (body-shut w st))
  (simp only [hc]) (exact (i10-slice-intro _ _ (sl-t4 _ w _ _ _ _ hx)))
  (simp only [hc refuse]) (exact h)
  (exact (i10-slice-intro _ _ (sl-t4-top _ w _ _ _ _ hx)))
  (exact (i10-slice-intro _ _ (sl-t5 _ w _ _ hx)))
  (rename_i st ds m k fresh mine) (cases hc (await-kind-bad w ds))
  (simp only [hc]) (exact (i10-slice-intro _ _ (sl-t6 _ w _ _ _ _ _ _ hx)))
  (simp only [hc refuse]) (exact h)
  (exact (i10-slice-intro _ _ (sl-t11 _ w _ _ hx)))
  (rename_i st tag v) (cases hc (complete-refused w st tag))
  (simp only [hc]) (exact (i10-slice-intro _ _ (sl-t12 _ w _ _ _ hx)))
  (simp only [hc refuse]) (exact h)
  (exact (i10-t-schedule w _ h))
  (rename_i d fresh) (cases hc (deb-consuming w d))
  (simp only [hc]) (exact (i10-slice-intro _ _ (sl-t22 _ w _ _ hx)))
  (simp only [hc refuse]) (exact h)
  (exact (i10-slice-intro _ _ (sl-t22-un _ w _ hx)))
  (exact (i10-slice-intro _ _ (sl-t-handle-new _ w _ hx)))
  (exact (i10-slice-intro _ _ (sl-t-deliver _ w _ _ hx)))
  (exact (i10-slice-intro _ _ (sl-t-post _ w _ _ hx)))
  (exact (i10-slice-intro _ _ (sl-t-take _ w _ _ _ _ hx)))
  (exact (i10-slice-intro _ _ (sl-t-release _ w _ hx)))
  (exact (i10-t-finalize w _ h))
  (exact (i10-slice-intro _ _ (sl-t-cancel _ w _ hx)))
  (exact (i10-slice-intro _ _ (sl-t-release-world _ w hx)))
  (exact (i10-slice-intro _ _ (sl-t-open-scope _ w _ _ hx)))
  (exact (i10-slice-intro _ _ (sl-t-close-scope _ w _ hx)))
  (exact (i10-slice-intro _ _ (sl-t-detach _ w _ _ hx)))
  (exact (i10-slice-intro _ _ (sl-t-finally-enter _ w _ hx)))
  (exact (i10-slice-intro _ _ (sl-t-finally-exit _ w _ hx)))
  (exact (i10-slice-intro _ _ (sl-t-slice-exit _ w _ hx))))

(a/theorem i10-raw [w :- World, it :- Item]
  (=> (= (inv-i10-slice w) true) (= (inv-i10-slice (:world (raw w it))) true))
  (intro h)
  (have h00 := (i10-raw0 w it h))
  (have h0 (= (inv-i10-slice (:world (raw0g w it))) true))
  (cases hs (host-shut w it))
  (simp only [raw0g hs]) (exact h00)
  (simp only [raw0g hs refuse]) (exact h)
  (cases ha (:accepted (raw0g w it)))
  (simp only [raw post ha]) (exact h0)
  (simp only [raw post ha accept cancel-losers])
  (exact (i10-slice-intro _ _ (sl-run-cascade _ _ _ (i10-slice-elim _ h0)))))

;; I10 (D0 half) for the step: no honest hypothesis is needed (Rule R sets no slice)
(a/theorem step-i10-slice [w :- World, it :- Item]
  (=> (= (inv-i10-slice w) true) (= (inv-i10-slice (:world (world-step w it))) true))
  (intro h)
  (have h0 := (i10-raw w it h))
  (cases ha (:accepted (raw w it)))
  (simp only [world-step finish ha]) (exact h0)
  (simp only [world-step finish ha accept])
  (exact (i10-slice-intro _ _ (sl-rule-r _ _ (i10-slice-elim _ h0)))))

(a/theorem i10-slice-empty [] (= (inv-i10-slice empty-world) true) (rfl))

;; with unique run ids (inv-sample's ids-ok), inv-i10-slice is "at most one run holds the slice"
(a/theorem slice-count-zero [x :- Nat, rs :- (List RunRow)]
  (=> (= (tbl-all (slice-only x) rs) true) (= (nat-mem x (tbl-ids run-id rs)) false)
      (= (tbl-count run-slice rs) 0))
  (induction rs)
  (case' [cons h t ih])
  (case' [nil])
  (intros ha hm) (simp [tbl-count])
  (intros ha hm)
  (simp only [tbl-all Bool.and_eq_true] at ha)
  (simp only [tbl-ids nat-mem] at hm)
  (cases hx (Nat.beq (run-id h) x))
  (simp only [hx] at hm)
  (have h1 := (And.left ha))
  (have hs (= (:slice h) false))
  (cases hs2 (:slice h)) (rfl)
  (simp only [slice-only hs2 Bool.not_true Bool.false_or] at h1)
  (simp only [run-id] at hx) (rw [hx] at h1) (simp at h1)
  (simp only [tbl-count run-slice hs])
  (exact (ih (And.right ha) hm))
  (simp [hx] at hm))

(a/theorem slice-count-le [x :- Nat, rs :- (List RunRow)]
  (=> (= (tbl-all (slice-only x) rs) true) (= (nat-nodup (tbl-ids run-id rs)) true)
      (= (Nat.ble (tbl-count run-slice rs) 1) true))
  (induction rs)
  (case' [cons h t ih])
  (case' [nil])
  (intros ha hn) (simp [tbl-count])
  (intros ha hn)
  (simp only [tbl-all Bool.and_eq_true] at ha)
  (simp only [tbl-ids nat-nodup Bool.and_eq_true] at hn)
  (cases hs (:slice h))
  (simp only [tbl-count run-slice hs]) (exact (ih (And.right ha) (And.right hn)))
  (have h1 := (And.left ha))
  (simp only [slice-only hs Bool.not_true Bool.false_or] at h1)
  (have hid (= (run-id h) x)) (exact (Nat.eq_of_beq_eq_true h1))
  (have hm (= (nat-mem x (tbl-ids run-id t)) false))
  (rw [← hid]) (exact (bnot-true _ (And.left hn)))
  (have h0 := (slice-count-zero x t (And.right ha) hm))
  (simp only [tbl-count run-slice hs h0]))

(a/theorem run-ids-nodup [w :- World]
  (=> (= (ids-ok w) true) (= (nat-nodup (tbl-ids run-id (:runs w))) true))
  (intro h)
  (simp only [ids-ok ids-unique all-ids Bool.and_eq_true] at h)
  (have h1 := (nat-nodup-app-right _ _ (And.left h)))
  (have h2 := (nat-nodup-app-right _ _ h1))
  (have h3 := (nat-nodup-app-right _ _ h2))
  (exact (nat-nodup-app-left _ _ h3)))

(a/theorem i10-slice-count [w :- World]
  (=> (= (inv-sample w) true) (= (inv-i10-slice w) true)
      (= (Nat.ble (tbl-count run-slice (:runs w)) 1) true))
  (intros hs h)
  (have hp := (inv-parts w hs))
  (exact (slice-count-le _ (:runs w) (i10-slice-elim w h) (run-ids-nodup w (And.right (And.right hp))))))

;; D0 after every step: at most one run holds the slice (Rule R's honest flag as in step-inv)
(a/theorem step-d0 [w :- World, it :- Item]
  (=> (= (inv-sample w) true) (= (rule-r-safe (:world (raw w it))) true) (= (inv-i10-slice w) true)
      (= (Nat.ble (tbl-count run-slice (:runs (:world (world-step w it)))) 1) true))
  (intros hs hr h)
  (exact (i10-slice-count _ (step-inv w it hs hr) (step-i10-slice w it h))))

;; ===========================================================================
;; Part D. I9: an unwinding run has no activation (hence no savepoint edge)
;;
;; `inv-i9 w`: every run with mode unwinding has no activation in `acts`. Only T14's local
;; part makes a run unwinding (`run-cancel-row`), and it removes the run's activations in the
;; same edit (`cancel-acts`); activations are inserted only for a normal run (T6, take), whose
;; id is unique (inv-sample's ids-ok). The `s9-` chain below is the `sl-` chain of Part C with
;; the predicate replaced: tables other than runs and acts are frames.
;; ===========================================================================

(a/theorem tbl-any-del [A :- Type, p :- (=> A Bool), idf :- (=> A Nat), y :- Nat, xs :- (List A)]
  (=> (= (tbl-any p (tbl-del idf y xs)) true) (= (tbl-any p xs) true))
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (intro hp) (simp [tbl-del tbl-any] at hp)
  (intro hp)
  (cases hy (Nat.beq (idf h) y))
  (simp only [tbl-del hy tbl-any Bool.or_eq_true] at hp)
  (simp only [tbl-any Bool.or_eq_true])
  (cases hp) (rename_i h1) (exact (Or.inl h1)) (rename_i h1) (exact (Or.inr (ih h1)))
  (simp only [tbl-del hy] at hp)
  (simp only [tbl-any Bool.or_eq_true]) (exact (Or.inr (ih hp))))

(a/theorem tbl-any-keep [A :- Type, p :- (=> A Bool), K :- (=> Nat Bool), idf :- (=> A Nat), xs :- (List A)]
  (=> (= (tbl-any p (tbl-keep K idf xs)) true) (= (tbl-any p xs) true))
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (intro hp) (simp [tbl-keep tbl-any] at hp)
  (intro hp)
  (cases hk (K (idf h)))
  (simp only [tbl-keep hk] at hp)
  (simp only [tbl-any Bool.or_eq_true]) (exact (Or.inr (ih hp)))
  (simp only [tbl-keep hk tbl-any Bool.or_eq_true] at hp)
  (simp only [tbl-any Bool.or_eq_true])
  (cases hp) (rename_i h1) (exact (Or.inl h1)) (rename_i h1) (exact (Or.inr (ih h1))))

(a/theorem tbl-any-upd-same [A :- Type, p :- (=> A Bool), idf :- (=> A Nat), y :- Nat, f :- (=> A A),
                             hf :- (forall [a :- A] (= (p (f a)) (p a))), xs :- (List A)]
  (= (tbl-any p (tbl-upd idf y f xs)) (tbl-any p xs))
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (simp [tbl-upd tbl-any])
  (cases hy (Nat.beq (idf h) y))
  (all_goals (simp only [tbl-upd hy tbl-any hf ih])))

;; frames: everything but runs and acts
(defmacro ^:private defs9-frames [& edits]
  `(do ~@(for [[nm params app] (partition 3 edits)]
           `(a/theorem ~(symbol (str "s9-" nm)) [~'w :- ~'World ~@params]
              (~'= (~'inv-i9 ~app) (~'inv-i9 ~'w)) (~'rfl)))))

(defmacro ^:private defs9-tables [& specs]
  `(defs9-frames ~@(macroexpand `(sl-table-edits ~@specs))))

(defs9-tables scope ScopeRow comp CompRow task TaskRow source SourceRow edge EdgeRow
  resource ResRow cleanup CleanupRow pub PubRow fork ForkRow)
(defs9-frames
  set-pins [v :- (List Nat)] (set-pins w v)
  set-pending-act [v :- Nat] (set-pending-act w v)
  set-released [v :- Bool] (set-released w v)
  set-edges [v :- (List EdgeRow)] (set-edges w v)
  set-comps [v :- (List CompRow)] (set-comps w v)
  set-next-id [v :- Nat] (set-next-id w v)
  bump [] (bump w)
  insert-edge [e :- EdgeRow] (insert-edge w e)
  insert-edge-fresh [e :- EdgeRow] (insert-edge-fresh w e)
  drop-cred-edges [a :- Nat] (drop-cred-edges w a)
  drop-edges [p :- (=> EdgeRow Bool)] (drop-edges w p)
  cleanup-set [rid :- Nat, rows :- (List Nat)] (cleanup-set w rid rows)
  close-scope-id [s :- Nat] (close-scope-id w s)
  res-cancel [z :- Nat] (res-cancel w z)
  finalize-one [d :- Nat] (finalize-one w d))

;; acts: deletion keeps it; an update that keeps each row's run is a frame; an insertion needs
;; its run to be no unwinding run
(a/theorem s9-act-del [w :- World, y :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (act-del w y)) true))
  (intro h)
  (simp only [inv-i9 act-del set-acts] at h)
  (simp only [inv-i9 act-del set-acts])
  (have hpq (forall [r :- RunRow] (=> (= (unwinding-acts-ok (:acts w) r) true)
                                      (= (unwinding-acts-ok (tbl-del act-id y (:acts w)) r) true))))
  (intros r hr)
  (simp only [unwinding-acts-ok Bool.or_eq_true] at hr)
  (simp only [unwinding-acts-ok Bool.or_eq_true])
  (cases hr) (rename_i h1) (exact (Or.inl h1))
  (rename_i h1) (apply Or.inr)
  (cases ha (tbl-any (act-of-run (:id r)) (tbl-del act-id y (:acts w))))
  (rfl)
  (have h2 := (tbl-any-del ActRow (act-of-run (:id r)) act-id y (:acts w) ha))
  (rw [h2] at h1) (simp at h1)
  (exact (tbl-all-mono RunRow _ _ hpq (:runs w) h)))

(a/theorem s9-drop-act [w :- World, a :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (drop-act w a)) true))
  (intro h) (simp only [drop-act]) (exact (s9-act-del _ a (Eq.trans (s9-drop-cred-edges w a) h))))

(a/theorem s9-ok-upd [as :- (List ActRow), y :- Nat, f :- (=> ActRow ActRow),
                     hf :- (forall [a :- ActRow] (= (:run (f a)) (:run a))), r :- RunRow]
  (= (unwinding-acts-ok (tbl-upd act-id y f as) r) (unwinding-acts-ok as r))
  (have hp (forall [a :- ActRow] (= (act-of-run (:id r) (f a)) (act-of-run (:id r) a))))
  (intro a) (simp only [act-of-run hf])
  (simp only [unwinding-acts-ok (tbl-any-upd-same ActRow (act-of-run (:id r)) act-id y f hp as)]))

(a/theorem s9-act-upd [w :- World, y :- Nat, f :- (=> ActRow ActRow), hf :- (forall [a :- ActRow] (= (:run (f a)) (:run a)))]
  (= (inv-i9 (act-upd w y f)) (inv-i9 w))
  (simp only [inv-i9 act-upd set-acts])
  (exact (tbl-all-congr RunRow _ _ (s9-ok-upd (:acts w) y f hf) (:runs w))))

(a/defn run-not-of [x :- Nat, r :- RunRow] Bool
  (Bool.or (Bool.not (Nat.beq (:mode r) mode-unwinding)) (Bool.not (Nat.beq (:id r) x))))

(a/theorem s9-act-ins [w :- World, a :- ActRow]
  (=> (= (tbl-all (run-not-of (:run a)) (:runs w)) true) (= (inv-i9 w) true) (= (inv-i9 (act-ins w a)) true))
  (intros ha h)
  (simp only [inv-i9] at h)
  (simp only [inv-i9 act-ins set-acts tbl-ins])
  (have hpq (forall [r :- RunRow] (=> (= (unwinding-acts-ok (:acts w) r) true) (= (run-not-of (:run a) r) true)
                                      (= (unwinding-acts-ok (List.cons ActRow a (:acts w)) r) true))))
  (intros r h1 h2)
  (cases hm (Nat.beq (:mode r) mode-unwinding))
  (simp only [unwinding-acts-ok hm Bool.not_false Bool.true_or])
  (simp only [unwinding-acts-ok hm Bool.not_true Bool.false_or] at h1)
  (simp only [run-not-of hm Bool.not_true Bool.false_or] at h2)
  (simp only [unwinding-acts-ok hm Bool.not_true Bool.false_or tbl-any act-of-run])
  (have h3 (= (Nat.beq (:run a) (:id r)) false)) (rw [beq-comm]) (exact (bnot-true _ h2))
  (simp only [h3 Bool.false_or])
  (exact h1)
  (exact (tbl-all-mono2 RunRow _ _ _ hpq (:runs w) h ha)))

;; runs: a row function that keeps mode and id is a frame-like update
(a/defn keeps9 [f :- (=> RunRow RunRow)] Prop
  (forall [r :- RunRow] (And (= (:mode (f r)) (:mode r)) (= (:id (f r)) (:id r)))))

(a/theorem s9-run-upd [w :- World, y :- Nat, f :- (=> RunRow RunRow), hf :- (keeps9 f)]
  (=> (= (inv-i9 w) true) (= (inv-i9 (run-upd w y f)) true))
  (intro h)
  (simp only [inv-i9] at h)
  (simp only [inv-i9 run-upd set-runs])
  (have hin (forall [r :- RunRow] (=> (= (unwinding-acts-ok (:acts w) r) true) (= (Nat.beq (run-id r) y) true)
                                      (= (unwinding-acts-ok (:acts w) (f r)) true))))
  (intros r hr hy)
  (have hk := (hf r))
  (simp only [unwinding-acts-ok (And.left hk) (And.right hk)]) (exact hr)
  (have hout (forall [r :- RunRow] (=> (= (unwinding-acts-ok (:acts w) r) true) (= (Nat.beq (run-id r) y) false)
                                       (= (unwinding-acts-ok (:acts w) r) true))))
  (intros r hr hy) (exact hr)
  (exact (tbl-all-upd RunRow run-id y f _ _ hin hout (:runs w) h)))

(a/theorem s9-run-del [w :- World, y :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (run-del w y)) true))
  (intro h)
  (simp only [inv-i9] at h)
  (simp only [inv-i9 run-del set-runs])
  (have hout (forall [r :- RunRow] (=> (= (unwinding-acts-ok (:acts w) r) true) (= (Nat.beq (run-id r) y) false)
                                       (= (unwinding-acts-ok (:acts w) r) true))))
  (intros r hr hy) (exact hr)
  (exact (tbl-all-del RunRow run-id y _ _ hout (:runs w) h)))

(a/theorem s9-run-ins [w :- World, r :- RunRow]
  (=> (= (:mode r) mode-normal) (= (inv-i9 w) true) (= (inv-i9 (run-ins w r)) true))
  (intros hr h)
  (simp only [inv-i9] at h)
  (simp only [inv-i9 run-ins set-runs tbl-ins tbl-all Bool.and_eq_true])
  (apply And.intro) (simp only [unwinding-acts-ok hr mode-normal mode-unwinding]) (simp) (exact h))

(a/theorem s9-filter-world [K :- (=> Nat Bool), w :- World]
  (=> (= (inv-i9 w) true) (= (inv-i9 (filter-world K w)) true))
  (intro h)
  (simp only [inv-i9] at h)
  (simp only [inv-i9 filter-world])
  (have hpq (forall [r :- RunRow] (=> (= (unwinding-acts-ok (:acts w) r) true) (= (K (run-id r)) true)
                                      (= (unwinding-acts-ok (tbl-keep K act-id (:acts w)) r) true))))
  (intros r hr hk)
  (simp only [unwinding-acts-ok Bool.or_eq_true] at hr)
  (simp only [unwinding-acts-ok Bool.or_eq_true])
  (cases hr) (rename_i h1) (exact (Or.inl h1))
  (rename_i h1) (apply Or.inr)
  (cases ha (tbl-any (act-of-run (:id r)) (tbl-keep K act-id (:acts w))))
  (rfl)
  (have h2 := (tbl-any-keep ActRow (act-of-run (:id r)) K act-id (:acts w) ha))
  (rw [h2] at h1) (simp at h1)
  (exact (tbl-all-keep RunRow K run-id _ _ hpq (:runs w) h)))

(defmacro ^:private defkeeps9 [& specs]
  `(do ~@(for [[f params] (partition 2 specs)]
           `(a/theorem ~(symbol (str "keeps9-" f)) [~@params]
              (~'keeps9 ~(if (seq params) (cons f (map first (partition 3 params))) f))
              (~'unfold ~'keeps9) (~'intro ~'r)
              (~'exact (~'And.intro (~'rfl) (~'rfl)))))))

(defkeeps9 run-tick [] run-arm [z :- Nat] run-unres [z :- Nat] run-set-act [n :- Nat] run-wake []
  run-fin-push [fz :- Finalizer] run-fin-pop [] run-complete-row [] run-park-row [] run-tick-park []
  run-fin-pop-end [] run-enter-row [])

(a/theorem new-run-row-mode [id :- Nat, of :- Nat, ep :- Nat, sc :- Nat, ei :- Nat]
  (= (:mode (new-run-row id of ep sc ei)) mode-normal) (rfl))

;; T14's local part: cancel-acts removes every activation of the run
(a/defn act-covered [rid :- Nat, ids :- (List Nat), a :- ActRow] Bool
  (Bool.or (Bool.not (act-of-run rid a)) (reach-mem (:id a) ids)))

(a/theorem act-covered-drop [rid :- Nat, ids :- (List Nat), i :- Nat, a :- ActRow]
  (=> (= (act-covered rid (List.cons Nat i ids) a) true) (= (Nat.beq (act-id a) i) false)
      (= (act-covered rid ids a) true))
  (intros h hi)
  (simp only [act-covered reach-mem-cons Bool.or_eq_true] at h)
  (simp only [act-covered Bool.or_eq_true])
  (cases h) (rename_i h1) (exact (Or.inl h1))
  (rename_i h1) (cases h1) (rename_i h2)
  (simp only [act-id] at hi) (rw [hi] at h2) (simp at h2)
  (rename_i h2) (exact (Or.inr h2)))

(a/theorem covered-nil-any [rid :- Nat, xs :- (List ActRow)]
  (=> (= (tbl-all (act-covered rid (List.nil Nat)) xs) true) (= (tbl-any (act-of-run rid) xs) false))
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (intro hp) (simp [tbl-any])
  (intro hp)
  (simp only [tbl-all Bool.and_eq_true] at hp)
  (have h1 := (And.left hp))
  (simp only [act-covered reach-mem Bool.or_false] at h1)
  (simp only [tbl-any (bnot-true _ h1) Bool.false_or])
  (exact (ih (And.right hp))))

(a/theorem fold-drop-act-clears [rid :- Nat, ids :- (List Nat)]
  (forall [w :- World] (=> (= (tbl-all (act-covered rid ids) (:acts w)) true)
                           (= (tbl-any (act-of-run rid) (:acts (nat-fold drop-act w ids))) false)))
  (induction ids)
  (case' [cons i t ih])
  (case' [nil])
  (intros w h) (simp only [nat-fold]) (exact (covered-nil-any rid (:acts w) h))
  (intros w h) (simp only [nat-fold])
  (apply (ih (drop-act w i)))
  (have hout (forall [a :- ActRow] (=> (= (act-covered rid (List.cons Nat i t) a) true) (= (Nat.beq (act-id a) i) false)
                                       (= (act-covered rid t a) true))))
  (intros a h1 h2) (exact (act-covered-drop rid t i a h1 h2))
  (exact (tbl-all-del ActRow act-id i _ _ hout (:acts w) h)))

;; the scan of a run's activations covers them
(a/theorem scan-covers [rid :- Nat, xs :- (List ActRow), ys :- (List ActRow)]
  (=> (forall [a :- ActRow] (=> (List.Mem a xs) (List.Mem a ys)))
      (= (tbl-all (act-covered rid (tbl-scan act-id (act-of-run rid) ys)) xs) true))
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (intro hs) (simp [tbl-all])
  (intro hs)
  (simp only [tbl-all Bool.and_eq_true])
  (apply And.intro)
  (simp only [act-covered Bool.or_eq_true])
  (cases ho (act-of-run rid h))
  (exact (Or.inl (rfl)))
  (exact (Or.inr (scan-mem ActRow act-id (act-of-run rid) h ys (hs h (List.Mem.head t)) ho)))
  (exact (ih (fn [a :- ActRow, m :- (List.Mem a t)] (hs a (List.Mem.tail h m))))))

(a/theorem runs-fold-drop-act [ids :- (List Nat)]
  (forall [w :- World] (= (:runs (nat-fold drop-act w ids)) (:runs w)))
  (induction ids)
  (case' [cons i t ih])
  (case' [nil])
  (intro w) (simp only [nat-fold])
  (intro w) (simp only [nat-fold]) (rw [(ih (drop-act w i))]))

(a/theorem any-fold-drop-act [p :- (=> ActRow Bool), ids :- (List Nat)]
  (forall [w :- World] (=> (= (tbl-any p (:acts (nat-fold drop-act w ids))) true) (= (tbl-any p (:acts w)) true)))
  (induction ids)
  (case' [cons i t ih])
  (case' [nil])
  (intros w h) (simp only [nat-fold] at h) (exact h)
  (intros w h) (simp only [nat-fold] at h)
  (have h1 := (ih (drop-act w i) h))
  (simp only [drop-act act-del set-acts drop-cred-edges comp-upd set-comps set-edges] at h1)
  (exact (tbl-any-del ActRow p act-id i (:acts w) h1)))

(a/theorem s9-cancel-acts [w :- World, rid :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (cancel-acts (run-upd w rid run-cancel-row) rid)) true))
  (intro h)
  (simp only [inv-i9] at h)
  (have hcl (= (tbl-any (act-of-run rid) (:acts (cancel-acts (run-upd w rid run-cancel-row) rid))) false))
  (simp only [cancel-acts])
  (apply (fold-drop-act-clears rid _ (run-upd w rid run-cancel-row)))
  (exact (scan-covers rid _ _ (fn [a :- ActRow, m :- (List.Mem a (:acts (run-upd w rid run-cancel-row)))] m)))
  (have hru (= (:runs (cancel-acts (run-upd w rid run-cancel-row) rid)) (tbl-upd run-id rid run-cancel-row (:runs w))))
  (simp only [cancel-acts]) (rw [runs-fold-drop-act])
  (simp only [inv-i9 hru])
  (have hin (forall [r :- RunRow] (=> (= (unwinding-acts-ok (:acts w) r) true) (= (Nat.beq (run-id r) rid) true)
              (= (unwinding-acts-ok (:acts (cancel-acts (run-upd w rid run-cancel-row) rid)) (run-cancel-row r)) true))))
  (intros r hr hy)
  (have he (= (:id (run-cancel-row r)) rid)) (simp only [run-cancel-row]) (exact (Nat.eq_of_beq_eq_true hy))
  (simp only [unwinding-acts-ok he hcl Bool.not_false Bool.or_true])
  (have hout (forall [r :- RunRow] (=> (= (unwinding-acts-ok (:acts w) r) true) (= (Nat.beq (run-id r) rid) false)
               (= (unwinding-acts-ok (:acts (cancel-acts (run-upd w rid run-cancel-row) rid)) r) true))))
  (intros r hr hy)
  (simp only [unwinding-acts-ok Bool.or_eq_true] at hr)
  (simp only [unwinding-acts-ok Bool.or_eq_true])
  (cases hr) (rename_i h1) (exact (Or.inl h1))
  (rename_i h1) (apply Or.inr)
  (cases ha (tbl-any (act-of-run (:id r)) (:acts (cancel-acts (run-upd w rid run-cancel-row) rid))))
  (rfl)
  (have h2 (= (tbl-any (act-of-run (:id r)) (:acts w)) true))
  (simp only [cancel-acts] at ha)
  (exact (any-fold-drop-act (act-of-run (:id r)) _ (run-upd w rid run-cancel-row) ha))
  (rw [h2] at h1) (simp at h1)
  (exact (tbl-all-upd RunRow run-id rid run-cancel-row _ _ hin hout (:runs w) h)))

;; an activation is inserted only for the token run r (normal): with unique run ids no run with
;; r's id is unwinding
(a/theorem not-of-unique [i :- Nat, rs :- (List RunRow)]
  (=> (= (nat-mem i (tbl-ids run-id rs)) false) (= (tbl-all (run-not-of i) rs) true))
  (induction rs)
  (case' [cons h t ih])
  (case' [nil])
  (intro hm) (simp [tbl-all])
  (intro hm)
  (simp only [tbl-ids nat-mem] at hm)
  (cases hx (Nat.beq (run-id h) i))
  (simp only [hx] at hm)
  (simp only [tbl-all Bool.and_eq_true])
  (apply And.intro)
  (simp only [run-not-of Bool.or_eq_true])
  (apply Or.inr) (simp only [run-id] at hx) (simp only [hx Bool.not_false])
  (exact (ih hm))
  (simp [hx] at hm))

(a/theorem has-of-mem [A :- Type, idf :- (=> A Nat), r :- A, xs :- (List A)]
  (=> (List.Mem r xs) (= (tbl-has idf (idf r) xs) true))
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (intro hm) (cases hm)
  (intro hm)
  (cases hm)
  (simp [tbl-has Nat.beq_refl])
  (rename_i hm2)
  (cases hx (Nat.beq (idf h) (idf r)))
  (all_goals (simp only [tbl-has hx]))
  (exact (ih hm2)))

(a/theorem not-of-mem [r :- RunRow, rs :- (List RunRow)]
  (=> (= (nat-nodup (tbl-ids run-id rs)) true) (List.Mem r rs) (= (Nat.beq (:mode r) mode-unwinding) false)
      (= (tbl-all (run-not-of (:id r)) rs) true))
  (induction rs)
  (case' [cons h t ih])
  (case' [nil])
  (intros hn hm hu) (cases hm)
  (intros hn hm hu)
  (simp only [tbl-ids nat-nodup Bool.and_eq_true] at hn)
  (have hnm := (bnot-true _ (And.left hn)))
  (cases hm)
  (simp only [tbl-all Bool.and_eq_true])
  (apply And.intro)
  (simp only [run-not-of hu Bool.not_false Bool.true_or])
  (simp only [run-id] at hnm)
  (exact (not-of-unique _ t hnm))
  (rename_i hm2)
  (simp only [tbl-all Bool.and_eq_true])
  (apply And.intro)
  (have hin := (has-of-mem RunRow run-id r t hm2))
  (rw [← nat-mem-ids] at hin)
  (cases hx (Nat.beq (:id h) (:id r)))
  (simp only [run-not-of hx Bool.not_false Bool.or_true])
  (have he (= (run-id h) (run-id r))) (exact (Nat.eq_of_beq_eq_true hx))
  (rw [he] at hnm) (rw [hin] at hnm) (simp at hnm)
  (exact (ih (And.right hn) hm2 hu)))

(a/theorem tok-run-mem [w :- World, st :- Nat, r :- RunRow]
  (=> (= (tok-run w st) (Option.some RunRow r)) (List.Mem r (:runs w)))
  (intro ht)
  (cases hf (tbl-find run-stamp st (:runs w))) (case' [some r2]) (case' [none])
  (simp [tok-run hf] at ht)
  (cases hv (run-valid r2))
  (simp [tok-run hf hv] at ht)
  (simp only [tok-run hf hv Option.some.injEq] at ht)
  (rw [← ht]) (exact (tbl-find-mem RunRow run-stamp st r2 (:runs w) hf)))

(a/theorem tok-not-of [w :- World, st :- Nat, r :- RunRow]
  (=> (= (inv-sample w) true) (= (tok-run w st) (Option.some RunRow r)) (= (run-normal r) true)
      (= (tbl-all (run-not-of (:id r)) (:runs w)) true))
  (intros hs ht hn)
  (have hp := (inv-parts w hs))
  (simp only [run-normal Bool.and_eq_true] at hn)
  (have hu (= (Nat.beq (:mode r) mode-unwinding) false))
  (have hm (= (:mode r) mode-normal)) (exact (Nat.eq_of_beq_eq_true (And.right hn)))
  (rw [hm])
  (exact (not-of-mem r (:runs w) (run-ids-nodup w (And.right (And.right hp))) (tok-run-mem w st r ht) hu)))

(a/theorem not-of-tick [w :- World, i :- Nat, hn :- (= (tbl-all (run-not-of i) (:runs w)) true)]
  (= (tbl-all (run-not-of i) (:runs (run-upd w i run-tick))) true)
  (simp only [run-upd set-runs])
  (have hin (forall [r :- RunRow] (=> (= (run-not-of i r) true) (= (Nat.beq (run-id r) i) true) (= (run-not-of i (run-tick r)) true))))
  (intros r hr hy) (simp only [run-not-of run-tick] at hr) (simp only [run-not-of run-tick]) (exact hr)
  (have hout (forall [r :- RunRow] (=> (= (run-not-of i r) true) (= (Nat.beq (run-id r) i) false) (= (run-not-of i r) true))))
  (intros r hr hy) (exact hr)
  (exact (tbl-all-upd RunRow run-id i run-tick _ _ hin hout (:runs w) hn)))

(a/theorem act-fill-run [y :- Nat, v :- RunResult] (forall [a :- ActRow] (= (:run (act-fill y v a)) (:run a)))
  (intro a) (rfl))
(a/theorem act-set-members-run [ms :- (List Member)] (forall [a :- ActRow] (= (:run (act-set-members ms a)) (:run a)))
  (intro a) (rfl))
;; ---- the s9- chain (generated from the sl- chain: predicate inv-i9, no x)

(a/theorem s9-resume [w :- World, a :- ActRow]
  (=> (= (inv-i9 w) true) (= (inv-i9 (resume w a)) true))
  (intro h) (simp only [resume])
  (exact (s9-run-upd _ _ _ keeps9-run-wake (s9-drop-act w (:id a) h))))

(a/theorem s9-fill-slot [w :- World, a :- ActRow, y :- Nat, v :- RunResult]
  (=> (= (inv-i9 w) true) (= (inv-i9 (fill-slot w a y v)) true))
  (intro h)
  (cases hm (act-ready (act-fill y v a)))
  (simp only [fill-slot hm]) (rw [(s9-act-upd w (:id a) (act-fill y v) (act-fill-run y v))]) (exact h)
  (simp only [fill-slot hm]) (exact (s9-resume w a h)))

(a/theorem s9-invalidate [w :- World, e :- EdgeRow]
  (= (inv-i9 (invalidate w e)) (inv-i9 w))
  (simp only [invalidate s9-comp-upd s9-edge-upd]))

(a/theorem s9-remove-edge [w :- World, y :- Nat]
  (= (inv-i9 (remove-edge w y)) (inv-i9 w))
  (cases hf (edge-find w y)) (case' [some e]) (case' [none])
  (simp only [remove-edge hf])
  (cases hm (:marked e))
  (all_goals (simp only [remove-edge hf hm s9-comp-upd s9-edge-del])))

(a/theorem s9-dep-consumed [w :- World, e :- EdgeRow]
  (= (inv-i9 (dep-consumed w e)) (inv-i9 w))
  (cases hf (deb-final w (:debtor e)))
  (all_goals (simp only [dep-consumed hf s9-edge-upd s9-remove-edge])))

(a/theorem s9-fire-dep [w :- World, e :- EdgeRow]
  (=> (= (inv-i9 w) true) (= (inv-i9 (fire-dep w e)) true))
  (intro h)
  (cases ha (act-with-member (:id e) (:acts w))) (case' [some a]) (case' [none])
  (simp only [fire-dep ha s9-invalidate]) (exact h)
  (cases hc (Bool.and (run-current-of w (:run a) (:creditor e)) (deb-avail w (:debtor e))))
  (simp only [fire-dep ha hc s9-invalidate]) (exact h)
  (simp only [fire-dep ha hc deliver-dep])
  (exact (s9-fill-slot _ a _ _ (Eq.trans (s9-dep-consumed w e) h))))

(a/theorem s9-fire-wait-act [res :- RunResult, w :- World, e :- EdgeRow]
  (=> (= (inv-i9 w) true) (= (inv-i9 (fire-wait-act res w e)) true))
  (intro h)
  (cases ha (act-find w (:creditor e))) (case' [some a]) (case' [none])
  (simp only [fire-wait-act ha s9-edge-upd]) (exact h)
  (cases hc (run-current w (:run a)))
  (simp only [fire-wait-act ha hc s9-edge-upd]) (exact h)
  (simp only [fire-wait-act ha hc]) (exact (s9-fill-slot _ a _ _ (Eq.trans (s9-edge-upd w _ _) h))))

(a/theorem s9-mark-edge [w :- World, y :- Nat]
  (= (inv-i9 (mark-edge w y)) (inv-i9 w))
  (cases hf (edge-find w y)) (case' [some e]) (case' [none])
  (simp only [mark-edge hf])
  (cases hm (:marked e))
  (all_goals (simp only [mark-edge hf hm s9-comp-upd s9-edge-upd])))

(a/theorem s9-unmark-edge [w :- World, y :- Nat]
  (= (inv-i9 (unmark-edge w y)) (inv-i9 w))
  (cases hf (edge-find w y)) (case' [some e]) (case' [none])
  (simp only [unmark-edge hf])
  (cases hm (:marked e))
  (all_goals (simp only [unmark-edge hf hm s9-comp-upd s9-edge-upd])))

(a/theorem s9-fire-wait [res :- RunResult, w :- World, e :- EdgeRow]
  (=> (= (inv-i9 w) true) (= (inv-i9 (fire-wait res w e)) true))
  (intro h)
  (cases hc (Nat.beq (:creditor e) 0))
  (simp only [fire-wait hc]) (exact (s9-fire-wait-act res w e h))
  (simp only [fire-wait hc s9-remove-edge]) (exact h))

(a/theorem s9-fire-observe [w :- World, e :- EdgeRow]
  (= (inv-i9 (fire-observe w e)) (inv-i9 w))
  (cases hs (observe-new e (deb-version w (:debtor e))))
  (all_goals (simp only [fire-observe hs s9-edge-upd])))

(a/theorem s9-fire-edge [res :- RunResult, w :- World, y :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (fire-edge res w y)) true))
  (intro h)
  (cases hf (edge-find w y)) (case' [some e]) (case' [none])
  (simp only [fire-edge hf]) (exact h)
  (cases hp (Nat.beq (:phase e) ph-armed))
  (simp only [fire-edge hf hp]) (exact h)
  (cases hk1 (Nat.beq (:kind e) ek-dep))
  (cases hk2 (Nat.beq (:kind e) ek-wait))
  (cases hk3 (Nat.beq (:kind e) ek-observe))
  (simp only [fire-edge hf hp hk1 hk2 hk3 fire-savepoint-todo]) (exact h)
  (simp only [fire-edge hf hp hk1 hk2 hk3 s9-fire-observe]) (exact h)
  (simp only [fire-edge hf hp hk1 hk2]) (exact (s9-fire-wait res w e h))
  (simp only [fire-edge hf hp hk1]) (exact (s9-fire-dep w e h)))

(a/theorem s9-fold-fire [res :- RunResult, w :- World, ys :- (List Nat)]
  (=> (= (inv-i9 w) true) (= (inv-i9 (nat-fold (fire-edge res) w ys)) true))
  (exact (nat-fold-pres inv-i9 (fire-edge res) (fn [w2 :- World, y :- Nat] (s9-fire-edge res w2 y)) ys w)))

(a/theorem s9-fold-frame [f :- (=> World Nat World),
                          hf :- (forall [w :- World, y :- Nat] (= (inv-i9 (f w y)) (inv-i9 w))),
                          w :- World, ys :- (List Nat)]
  (=> (= (inv-i9 w) true) (= (inv-i9 (nat-fold f w ys)) true))
  (have hf2 (forall [w2 :- World, y :- Nat] (=> (= (inv-i9 w2) true) (= (inv-i9 (f w2 y)) true))))
  (intros w2 y hw) (rw [(hf w2 y)]) (exact hw)
  (exact (nat-fold-pres inv-i9 f hf2 ys w)))

(a/theorem s9-record-basis [w :- World, r :- RunRow, y :- Nat]
  (= (inv-i9 (record-basis w r y)) (inv-i9 w))
  (cases hc (in-comp w r))
  (all_goals (simp only [record-basis hc s9-comp-upd])))

(a/theorem s9-t1-top [w :- World, sc :- Nat, kind :- Nat, v :- Nat, fresh :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t1-create-source-top w sc kind v fresh))) true))
  (intro h)
  (cases hg (Bool.and (Bool.and (Nat.beq fresh (:next-id w)) (src-kind-ok kind)) (scope-open-at w sc)))
  (simp only [t1-create-source-top hg refuse]) (exact h)
  (simp only [t1-create-source-top hg accept s9-bump s9-source-ins]) (exact h))

(a/theorem s9-write-raw [w :- World, s :- Nat, v :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (write-raw w s v)) true))
  (intro h) (simp only [write-raw])
  (exact (s9-fold-frame mark-edge s9-mark-edge _ _
           (s9-fold-fire _ _ _ (Eq.trans (s9-source-upd w s _) h)))))

(a/theorem s9-t2 [w :- World, s :- Nat, v :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t2-write w s v))) true))
  (intro h)
  (cases hf (source-find w s)) (case' [some sr]) (case' [none])
  (simp only [t2-write hf refuse]) (exact h)
  (cases hw (writable sr))
  (simp only [t2-write hf hw refuse]) (exact h)
  (simp only [t2-write hf hw accept]) (exact (s9-write-raw w s v h)))

(a/theorem s9-track-fin [sr :- SourceRow, y :- Nat, w :- World]
  (= (inv-i9 (track-fin sr y w)) (inv-i9 w))
  (cases ho (:open sr))
  (case [true] (simp only [track-fin ho]))
  (case [false] (simp only [track-fin ho s9-remove-edge])))

(a/theorem s9-track-raw [w :- World, r :- RunRow, s :- Nat, sr :- SourceRow, k :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (track-raw w r s sr k)) true))
  (intro h)
  (cases hs (site-edge (:edges w) (:of r) (:effect-index r) s)) (case' [some e]) (case' [none])
  (simp only [track-raw hs track-new])
  (exact (s9-run-upd _ _ _ keeps9-run-tick (Eq.trans (s9-comp-upd _ _ _) (Eq.trans (s9-track-fin _ _ _) (Eq.trans (s9-insert-edge-fresh w _) h)))))
  (simp only [track-raw hs])
  (exact (s9-run-upd _ _ _ keeps9-run-tick (Eq.trans (s9-comp-upd _ _ _) (Eq.trans (s9-track-fin _ _ _) (Eq.trans (s9-edge-upd w _ _) h))))))

(a/theorem s9-t7 [w :- World, st :- Nat, s :- Nat, k :- Nat, fresh :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t7-track w st s k fresh))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t7-track ht refuse]) (exact h)
  (cases hs (source-find w s)) (case' [some sr]) (case' [none])
  (simp only [t7-track ht hs refuse]) (exact h)
  (cases hk (trackable sr))
  (simp only [t7-track ht hs hk refuse]) (exact h)
  (cases hc (comp-has w (:of r)))
  (cases hta (task-has w (:of r)))
  (simp only [t7-track ht hs hk hc hta refuse]) (exact h)
  (simp only [t7-track ht hs hk hc hta accept]) (exact (s9-run-upd w _ _ keeps9-run-tick h))
  (cases hg (Bool.or (Nat.beq fresh (:next-id w)) (opt-some (site-edge (:edges w) (:of r) (:effect-index r) s))))
  (simp only [t7-track ht hs hk hc hg refuse]) (exact h)
  (simp only [t7-track ht hs hk hc hg accept]) (exact (s9-track-raw w r s sr k h)))

(a/theorem s9-t8-unobserve [w :- World, y :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t8-unobserve w y))) true))
  (intro h)
  (cases hf (edge-find w y)) (case' [some e]) (case' [none])
  (simp only [t8-unobserve hf refuse]) (exact h)
  (cases hk (Nat.beq (:kind e) ek-observe))
  (simp only [t8-unobserve hf hk refuse]) (exact h)
  (simp only [t8-unobserve hf hk accept s9-remove-edge]) (exact h))

(a/theorem s9-t9 [w :- World, y :- Nat, tag :- Nat, v :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t9-fire w y tag v))) true))
  (intro h)
  (cases hg (fire-tok-ok w y))
  (simp only [t9-fire hg refuse]) (exact h)
  (simp only [t9-fire hg accept]) (exact (s9-fire-edge _ w y h)))

(a/theorem s9-ack-raw [w :- World, z :- Nat, o :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (ack-raw w z o)) true))
  (intro h) (simp only [ack-raw s9-cleanup-upd])
  (exact (s9-run-upd _ _ _ (keeps9-run-unres z) (Eq.trans (s9-resource-del w z) h))))

(a/theorem s9-t18 [w :- World, z :- Nat, tag :- Nat, v :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t18-resource-fire w z tag v))) true))
  (intro h)
  (cases hf (resource-find w z)) (case' [some zr]) (case' [none])
  (simp only [t18-resource-fire hf refuse]) (exact h)
  (cases hp (Nat.beq (:phase zr) rp-armed))
  (simp only [t18-resource-fire hf hp refuse]) (exact h)
  (simp only [t18-resource-fire hf hp accept])
  (exact (s9-fold-fire _ _ _ (Eq.trans (s9-resource-upd w z _) h))))

(a/theorem s9-drop-pub-handle [w :- World, y :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (drop-pub-handle w y))) true))
  (intro h)
  (cases hp (pub-find w y)) (case' [some p]) (case' [none])
  (simp only [drop-pub-handle hp refuse]) (exact h)
  (cases hh (Nat.blt 0 (:handles p)))
  (all_goals (simp only [drop-pub-handle hp hh refuse accept s9-pub-upd]))
  (all_goals (exact h)))

(a/theorem s9-drop-source-handle [w :- World, y :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (drop-source-handle w y))) true))
  (intro h)
  (cases hs (source-find w y)) (case' [some s]) (case' [none])
  (simp only [drop-source-handle hs]) (exact (s9-drop-pub-handle w y h))
  (cases hh (Nat.blt 0 (:handles s)))
  (all_goals (simp only [drop-source-handle hs hh refuse accept s9-source-upd]))
  (all_goals (exact h)))

(a/theorem s9-drop-task-handle [w :- World, y :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (drop-task-handle w y))) true))
  (intro h)
  (cases ht (task-find w y)) (case' [some t]) (case' [none])
  (simp only [drop-task-handle ht]) (exact (s9-drop-source-handle w y h))
  (cases hh (Nat.blt 0 (:handles t)))
  (all_goals (simp only [drop-task-handle ht hh refuse accept s9-task-upd]))
  (all_goals (exact h)))

(a/theorem s9-t19 [w :- World, y :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t19-handle-drop w y))) true))
  (intro h)
  (cases hc (comp-find w y)) (case' [some c]) (case' [none])
  (simp only [t19-handle-drop hc]) (exact (s9-drop-task-handle w y h))
  (cases hh (Nat.blt 0 (:handles c)))
  (all_goals (simp only [t19-handle-drop hc hh refuse accept s9-comp-upd]))
  (all_goals (exact h)))

(a/theorem s9-t20-pin [w :- World, y :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t20-pin w y))) true))
  (intro h)
  (cases hg (Bool.or (comp-has w y) (source-has w y)))
  (all_goals (simp only [t20-pin hg refuse accept s9-set-pins]))
  (all_goals (exact h)))

(a/theorem s9-t20-unpin [w :- World, y :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t20-unpin w y))) true))
  (intro h)
  (cases hg (nat-mem y (:pins w)))
  (all_goals (simp only [t20-unpin hg refuse accept s9-set-pins]))
  (all_goals (exact h)))

;; ---- rule.clj: T10, T13, T14, T16, the cascade, Rule R

(a/theorem s9-fin-loop [fuel :- (List Nat)]
  (forall [w :- World, ds :- (List Nat)]
    (=> (= (inv-i9 w) true) (= (inv-i9 (:world (fin-loop fuel w ds))) true)))
  (induction fuel)
  (case' [cons h f ih])
  (case' [nil])
  (intros w ds hw) (simp only [fin-loop]) (exact hw)
  (intros w ds hw)
  (cases ds)
  (simp only [fin-loop]) (exact hw)
  (rename_i d t)
  (simp only [fin-loop])
  (exact (ih _ _ (Eq.trans (s9-finalize-one w d) hw))))

(a/theorem s9-finalize-debtor [w :- World, d :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (finalize-debtor w d)) true))
  (intro h) (simp only [finalize-debtor]) (exact (s9-fin-loop _ w _ h)))

(a/theorem s9-close-source [w :- World, s :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (close-source w s)) true))
  (intro h) (simp only [close-source wake-closed])
  (exact (s9-finalize-debtor _ s (s9-fold-fire _ _ _ (Eq.trans (s9-source-upd w s _) h)))))

(a/theorem s9-close-local [w :- World, sub :- (List Nat)]
  (=> (= (inv-i9 w) true) (= (inv-i9 (close-local w sub)) true))
  (intro h) (simp only [close-local])
  (exact (nat-fold-pres inv-i9 close-source s9-close-source _ _
           (s9-fold-frame close-scope-id s9-close-scope-id w sub h))))

(a/theorem s9-remove-if-empty [w :- World, sub :- (List Nat)]
  (=> (= (inv-i9 w) true) (= (inv-i9 (remove-if-empty w sub)) true))
  (intro h)
  (cases he (subtree-empty w sub))
  (simp only [remove-if-empty he]) (exact h)
  (simp only [remove-if-empty he]) (exact (s9-fold-frame scope-del s9-scope-del w sub h)))

(a/theorem s9-invalidate-id [w :- World, y :- Nat]
  (= (inv-i9 (invalidate-id w y)) (inv-i9 w))
  (cases hf (edge-find w y)) (case' [some e]) (case' [none])
  (simp only [invalidate-id hf])
  (cases hp (Nat.beq (:phase e) ph-armed))
  (all_goals (simp only [invalidate-id hf hp s9-invalidate])))

(a/theorem s9-debtor-side [w :- World, r :- RunRow]
  (=> (= (inv-i9 w) true) (= (inv-i9 (debtor-side w r)) true))
  (intro h)
  (cases hc (comp-find w (:of r))) (case' [some c]) (case' [none])
  (simp only [debtor-side hc fire-task-cancelled])
  (exact (s9-finalize-debtor _ _ (s9-fold-fire _ _ _ (Eq.trans (s9-task-upd w _ _) h))))
  (cases he (Nat.beq (:epoch r) (:epoch c)))
  (simp only [debtor-side hc he]) (exact h)
  (simp only [debtor-side hc he invalidate-dependents fire-waits-cancelled])
  (exact (s9-fold-frame invalidate-id s9-invalidate-id _ _ (s9-fold-fire _ _ _ h))))

(a/theorem s9-cancel-run-local [w :- World, r :- RunRow, rep :- Bool]
  (=> (= (inv-i9 w) true) (= (inv-i9 (cancel-run-local w r rep)) true))
  (intro h)
  (have h1 (= (inv-i9 (cleanup-set (cancel-res (cancel-acts (run-upd w (:id r) run-cancel-row) (:id r)) r)
                                   (:id r) (cleanup-rows-of w r))) true))
  (rw [s9-cleanup-set]) (simp only [cancel-res])
  (exact (s9-fold-frame res-cancel s9-res-cancel _ _ (s9-cancel-acts w (:id r) h)))
  (cases hr (Bool.and rep (comp-has (cleanup-set (cancel-res (cancel-acts (run-upd w (:id r) run-cancel-row) (:id r)) r) (:id r) (cleanup-rows-of w r)) (:of r))))
  (simp only [cancel-run-local cancel-debtor hr]) (exact (s9-debtor-side _ r h1))
  (simp only [cancel-run-local cancel-debtor hr]) (exact h1))

(a/theorem s9-clear-task-run [w :- World, r :- RunRow]
  (= (inv-i9 (clear-task-run w r)) (inv-i9 w))
  (cases ht (task-find w (:of r))) (case' [some t]) (case' [none])
  (simp only [clear-task-run ht])
  (cases hb (Nat.beq (:run t) (:id r)))
  (all_goals (simp only [clear-task-run ht hb s9-task-upd])))

(a/theorem s9-clear-comp-run [w :- World, r :- RunRow]
  (= (inv-i9 (clear-comp-run w r)) (inv-i9 w))
  (cases hc (comp-find w (:of r))) (case' [some c]) (case' [none])
  (simp only [clear-comp-run hc s9-clear-task-run])
  (cases hb (Nat.beq (:run c) (:id r)))
  (all_goals (simp only [clear-comp-run hc hb s9-comp-upd])))

(a/theorem s9-retire-local [w :- World, r :- RunRow]
  (=> (= (inv-i9 w) true) (= (inv-i9 (retire-local w r)) true))
  (intro h) (simp only [retire-local retire-with])
  (exact (s9-remove-if-empty _ _
           (Eq.trans (s9-cleanup-del _ _)
             (s9-run-del _ _ (s9-close-local _ _ (Eq.trans (s9-clear-comp-run w r) h)))))))

(a/theorem s9-close-scope-local [w :- World, s :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (close-scope-local w s)) true))
  (intro h) (simp only [close-scope-local close-with])
  (exact (s9-remove-if-empty _ _ (s9-close-local w _ h))))

(a/theorem s9-job-apply [w :- World, j :- Job]
  (=> (= (inv-i9 w) true) (= (inv-i9 (job-apply w j)) true))
  (intro h)
  (cases j)
  (rename_i rid rep)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [job-apply hf]) (exact h)
  (cases ha (run-alive r))
  (simp only [job-apply hf ha]) (exact h)
  (simp only [job-apply hf ha]) (exact (s9-cancel-run-local w r rep h))
  (rename_i rid)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [job-apply hf]) (exact h)
  (cases ha (retirable r))
  (simp only [job-apply hf ha]) (exact h)
  (simp only [job-apply hf ha]) (exact (s9-retire-local w r h))
  (rename_i s)
  (cases hs (scope-has w s))
  (simp only [job-apply hs]) (exact h)
  (simp only [job-apply hs]) (exact (s9-close-scope-local w s h)))

(a/theorem s9-cascade [fuel :- (List Nat)]
  (forall [w :- World, js :- (List Job)]
    (=> (= (inv-i9 w) true) (= (inv-i9 (:world (cascade fuel w js))) true)))
  (induction fuel)
  (case' [cons h f ih])
  (case' [nil])
  (intros w js hw) (simp only [cascade]) (exact hw)
  (intros w js hw)
  (cases js)
  (simp only [cascade]) (exact hw)
  (rename_i j t)
  (simp only [cascade])
  (exact (ih (job-apply w j) (List.append Job t (job-next w j)) (s9-job-apply w j hw))))

(a/theorem s9-run-cascade [w :- World, js :- (List Job)]
  (=> (= (inv-i9 w) true) (= (inv-i9 (run-cascade w js)) true))
  (intro h) (simp only [run-cascade cascade-run]) (exact (s9-cascade _ w js h)))

(a/theorem s9-t14 [w :- World, rid :- Nat, rep :- Bool]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t14-cancel w rid rep))) true))
  (intro h)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [t14-cancel hf refuse]) (exact h)
  (cases ha (run-alive r))
  (simp only [t14-cancel hf ha refuse]) (exact h)
  (simp only [t14-cancel hf ha accept]) (exact (s9-run-cascade w _ h)))

(a/theorem s9-t16 [w :- World, s :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t16-close-scope w s))) true))
  (intro h)
  (cases hs (scope-has w s))
  (simp only [t16-close-scope hs refuse]) (exact h)
  (simp only [t16-close-scope hs accept]) (exact (s9-run-cascade w _ h)))

(a/theorem s9-retire-full [w :- World, rid :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (retire-full w rid)) true))
  (intro h) (simp only [retire-full]) (exact (s9-run-cascade w _ h)))

(a/theorem s9-t15 [w :- World, z :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t15-full w z))) true))
  (intro h)
  (cases hg (ack-tok-ok w z))
  (simp only [t15-full hg refuse]) (exact h)
  (cases hf (resource-find w z)) (case' [some zr]) (case' [none])
  (simp only [t15-full hg hf refuse]) (exact h)
  (simp only [t15-full hg hf accept]) (exact (s9-retire-full _ _ (s9-ack-raw w z _ h))))

(a/theorem s9-demote-epoch [w :- World, cid :- Nat, b :- Bool]
  (= (inv-i9 (demote-epoch w cid b)) (inv-i9 w))
  (cases b) (all_goals (simp only [demote-epoch s9-comp-upd])))

(a/theorem s9-demote [w :- World, cid :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (demote w cid)) true))
  (intro h)
  (cases hc (comp-find w cid)) (case' [some c]) (case' [none])
  (simp only [demote hc]) (exact h)
  (cases hi (:idle c))
  (simp only [demote hc hi demote-edges])
  (have h1 := (Eq.trans (s9-demote-epoch _ cid (demote-cur w c)) (s9-run-cascade w (cancel-jobs (demote-cancels w c)) h)))
  (have h2 := (Eq.trans (s9-drop-edges _ (not-dep-of cid)) h1))
  (cases hf (comp-find (drop-edges (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) cid (demote-cur w c)) (not-dep-of cid)) cid))
  (case' [some c2]) (case' [none])
  (simp only [demote-finish hf]) (exact h2)
  (cases hk (demote-keep (drop-edges (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) cid (demote-cur w c)) (not-dep-of cid)) c2))
  (simp only [demote-finish hf hk s9-comp-del s9-drop-edges]) (exact h2)
  (simp only [demote-finish hf hk s9-comp-upd]) (exact h2)
  (simp only [demote hc hi]) (exact h))

(a/theorem s9-detach [w :- World]
  (=> (= (inv-i9 w) true) (= (inv-i9 (detach w)) true))
  (intro h) (simp only [detach])
  (have hs (forall [w2 :- World, y :- Nat] (=> (= (inv-i9 w2) true) (= (inv-i9 (detach-source w2 y)) true))))
  (intros w2 y hw) (simp only [detach-source wake-closed])
  (exact (s9-finalize-debtor _ y (s9-fold-fire _ _ _ (Eq.trans (s9-source-upd w2 y _) hw))))
  (have ht (forall [w2 :- World, y :- Nat] (= (inv-i9 (detach-task w2 y)) (inv-i9 w2))))
  (intros w2 y) (simp only [detach-task s9-task-upd])
  (have hc (forall [w2 :- World, y :- Nat] (= (inv-i9 (detach-comp w2 y)) (inv-i9 w2))))
  (intros w2 y) (simp only [detach-comp s9-comp-upd])
  (exact (s9-fold-frame detach-comp hc _ _ (s9-fold-frame detach-task ht _ _
           (nat-fold-pres inv-i9 detach-source hs _ w h)))))

(a/theorem s9-norm-round [w :- World]
  (=> (= (inv-i9 w) true) (= (inv-i9 (norm-round w)) true))
  (intro h) (simp only [norm-round norm-round-lv])
  (exact (s9-detach _ (nat-fold-pres inv-i9 demote s9-demote _ _ (s9-run-cascade w _ h)))))

(a/theorem s9-norm-loop [fuel :- (List Nat)]
  (forall [w :- World] (=> (= (inv-i9 w) true) (= (inv-i9 (norm-loop fuel w)) true)))
  (induction fuel)
  (case' [cons h f ih])
  (case' [nil])
  (intros w hw) (simp only [norm-loop]) (exact hw)
  (intros w hw)
  (cases hn (normalized w))
  (simp only [norm-loop hn]) (exact (ih _ (s9-norm-round w hw)))
  (simp only [norm-loop hn]) (exact hw))

(a/theorem s9-normalize [w :- World]
  (=> (= (inv-i9 w) true) (= (inv-i9 (normalize w)) true))
  (intro h) (simp only [normalize]) (exact (s9-norm-loop _ _ (s9-detach w h))))

(a/theorem s9-rule-r-round [w :- World]
  (=> (= (inv-i9 w) true) (= (inv-i9 (rule-r-round w)) true))
  (intro h) (simp only [rule-r-round rule-r-filter rule-r-filter-lv])
  (exact (s9-filter-world _ _ (s9-normalize w h))))

(a/theorem s9-rr-loop [fuel :- (List Nat)]
  (forall [w :- World] (=> (= (inv-i9 w) true) (= (inv-i9 (rr-loop fuel w)) true)))
  (induction fuel)
  (case' [cons h f ih])
  (case' [nil])
  (intros w hw) (simp only [rr-loop]) (exact hw)
  (intros w hw)
  (cases hn (no-orphans w))
  (simp only [rr-loop hn]) (exact (ih _ (s9-rule-r-round w hw)))
  (simp only [rr-loop hn]) (exact hw))

(a/theorem s9-rule-r [w :- World]
  (=> (= (inv-i9 w) true) (= (inv-i9 (rule-r w)) true))
  (intro h) (simp only [rule-r]) (exact (s9-rr-loop _ _ (s9-rule-r-round w h))))

;; ---- engine.clj Parts A-E

(a/theorem s9-insert-edge-checked [w :- World, e :- EdgeRow]
  (= (inv-i9 (insert-edge-checked w e)) (inv-i9 w))
  (cases hk (edge-ok-in w e))
  (all_goals (simp only [insert-edge-checked hk s9-insert-edge-fresh])))


(a/theorem s9-add-run-scope [w :- World, of :- Nat, ep :- Nat, par :- Nat, ei :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (add-run-scope w of ep par ei)) true))
  (intro h) (simp only [add-run-scope s9-bump s9-scope-ins])
  (exact (s9-run-ins w _ (new-run-row-mode _ _ _ _ _) h)))

(a/theorem s9-raise-loop [fuel :- (List Nat)]
  (forall [d :- Nat, w :- World, todo :- (List RJ)]
    (=> (= (inv-i9 w) true) (= (inv-i9 (:world (raise-loop fuel d w todo))) true)))
  (induction fuel)
  (case [nil] (intros d w todo h) (cases todo) (all_goals (simp only [raise-loop])) (all_goals (exact h)))
  (case [cons u f ih]
    (intros d w todo h)
    (cases todo)
    (case [nil] (simp only [raise-loop]) (exact h))
    (case [cons j t]
      (cases hd (Nat.beq (:node j) d))
      (case [true] (simp only [raise-loop hd]) (exact h))
      (case [false]
        (cases hn (Nat.ble (:need j) (comp-rank w (:node j))))
        (case [true] (simp only [raise-loop hd hn]) (exact (ih d w t h)))
        (case [false]
          (simp only [raise-loop hd hn])
          (exact (ih d _ _ (Eq.trans (s9-comp-upd w _ _) h))))))))

(a/theorem s9-raise-run [w :- World, c :- Nat, d :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (raise-run w c d))) true))
  (intro h)
  (cases hd (comp-has w d))
  (simp only [raise-run hd]) (exact h)
  (simp only [raise-run hd]) (exact (s9-raise-loop (raise-fuel w) d w _ h)))

(a/theorem s9-react-add [w :- World, c :- Nat, v :- Valid]
  (=> (= (inv-i9 w) true) (= (inv-i9 (react-add w c v)) true))
  (intro h)
  (cases hk (react-ok w c v))
  (simp only [react-add hk]) (exact h)
  (simp only [react-add hk])
  (exact (s9-raise-run _ c (:debtor v) (Eq.trans (s9-insert-edge-checked w _) h))))

(a/theorem s9-react-edges [vs :- (List Valid)]
  (forall [w :- World, c :- Nat] (=> (= (inv-i9 w) true) (= (inv-i9 (react-edges w c vs)) true)))
  (induction vs)
  (case' [cons h t ih])
  (case' [nil])
  (intros w c hw) (simp only [react-edges]) (exact hw)
  (intros w c hw) (simp only [react-edges]) (exact (ih _ c (s9-react-add w c h hw))))

(a/theorem s9-react-loop [fuel :- (List Nat)]
  (forall [w :- World, q :- (List Nat)] (=> (= (inv-i9 w) true) (= (inv-i9 (react-loop fuel w q)) true)))
  (induction fuel)
  (case' [cons h f ih])
  (case' [nil])
  (intros w q hw) (simp only [react-loop]) (exact hw)
  (intros w q hw)
  (cases q)
  (simp only [react-loop]) (exact hw)
  (rename_i y t)
  (cases hc (comp-find w y)) (case' [some c]) (case' [none])
  (simp only [react-loop hc]) (exact (ih w t hw))
  (cases hi (:idle c))
  (simp only [react-loop hc hi]) (exact (ih w t hw))
  (simp only [react-loop hc hi react-one])
  (exact (ih _ _ (s9-react-edges (:validity c) _ (:id c) (Eq.trans (s9-comp-upd w _ _) hw)))))

(a/theorem s9-demand-reactive [w :- World, d :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (demand-reactive w d)) true))
  (intro h)
  (cases hc (comp-find w d)) (case' [some c]) (case' [none])
  (simp only [demand-reactive hc]) (exact h)
  (cases hi (:idle c))
  (simp only [demand-reactive hc hi]) (exact h)
  (cases hv (valid-idle w c))
  (simp only [demand-reactive hc hi hv s9-comp-upd]) (exact h)
  (simp only [demand-reactive hc hi hv]) (exact (s9-react-loop (react-fuel w) w _ h)))

(a/theorem s9-spawn-rows [w :- World, owner :- Nat, ins :- (List Nat)]
  (=> (= (inv-i9 w) true) (= (inv-i9 (spawn-rows w owner ins)) true))
  (intro h) (simp only [spawn-rows])
  (exact (s9-add-run-scope _ _ _ _ _ (Eq.trans (s9-bump _) (Eq.trans (s9-task-ins w _) h)))))

(a/theorem s9-respawn-raw [w :- World, r :- RunRow, y :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (respawn-raw w r y)) true))
  (intro h) (simp only [respawn-raw])
  (exact (s9-run-upd _ _ _ keeps9-run-tick (Eq.trans (s9-comp-upd w _ _) h))))

(a/theorem s9-t4 [w :- World, st :- Nat, body :- Nat, fresh :- Nat, ins :- (List Nat)]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t4-spawn w st body fresh ins))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t4-spawn ht refuse]) (exact h)
  (cases hr (respawn-target w r fresh)) (case' [some t]) (case' [none])
  (cases hf (Nat.beq fresh (:next-id w)))
  (simp only [t4-spawn ht hr hf refuse]) (exact h)
  (simp only [t4-spawn ht hr hf accept])
  (exact (s9-run-upd _ _ _ keeps9-run-tick (Eq.trans (s9-record-basis _ r fresh) (s9-spawn-rows w _ ins h))))
  (cases hi (nat-list-eq ins (:inputs t)))
  (simp only [t4-spawn ht hr hi refuse]) (exact h)
  (simp only [t4-spawn ht hr hi accept]) (exact (s9-respawn-raw w r fresh h)))

(a/theorem s9-t4-top [w :- World, sc :- Nat, body :- Nat, fresh :- Nat, ins :- (List Nat)]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t4-spawn-top w sc body fresh ins))) true))
  (intro h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (scope-open-at w sc)))
  (simp only [t4-spawn-top hg refuse]) (exact h)
  (simp only [t4-spawn-top hg accept]) (exact (s9-spawn-rows w sc ins h)))

(a/theorem s9-t5 [w :- World, cid :- Nat, fresh :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t5-start w cid fresh))) true))
  (intro h)
  (cases hc (comp-find w cid)) (case' [some c]) (case' [none])
  (simp only [t5-start hc refuse]) (exact h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (startable w c)))
  (simp only [t5-start hc hg refuse]) (exact h)
  (simp only [t5-start hc hg accept start-raw s9-comp-upd]) (exact (s9-add-run-scope w _ _ _ _ h)))

(a/theorem s9-mark-from [w :- World, c :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (mark-from w c)) true))
  (intro h) (simp only [mark-from]) (exact (s9-fold-frame mark-edge s9-mark-edge w _ h)))

(a/theorem s9-create-comp-raw [w :- World, c :- Nat, owner :- Nat, ins :- (List Nat), body :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (create-comp-raw w c owner ins body)) true))
  (intro h)
  (cases hf (comp-find w c)) (case' [some row]) (case' [none])
  (simp only [create-comp-raw hf s9-bump s9-comp-ins]) (exact h)
  (cases he (nat-list-eq (:inputs row) ins))
  (simp only [create-comp-raw hf he]) (exact (s9-mark-from _ c (Eq.trans (s9-comp-upd w _ _) h)))
  (simp only [create-comp-raw hf he s9-comp-upd]) (exact h))

(a/theorem s9-t3 [w :- World, st :- Nat, c :- Nat, ins :- (List Nat), body :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t3-create w st c ins body))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t3-create ht refuse]) (exact h)
  (cases hg (create-ok w c))
  (simp only [t3-create ht hg refuse]) (exact h)
  (simp only [t3-create ht hg accept])
  (exact (s9-run-upd _ _ _ keeps9-run-tick (Eq.trans (s9-record-basis _ r c) (s9-create-comp-raw w c _ ins body h)))))

(a/theorem s9-t3-top [w :- World, sc :- Nat, c :- Nat, ins :- (List Nat), body :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t3-create-top w sc c ins body))) true))
  (intro h)
  (cases hg (Bool.and (create-ok w c) (scope-open-at w sc)))
  (simp only [t3-create-top hg refuse]) (exact h)
  (simp only [t3-create-top hg accept]) (exact (s9-create-comp-raw w c sc ins body h)))

(a/theorem s9-consume-entry [w :- World, e :- EdgeRow]
  (= (inv-i9 (consume-entry w e)) (inv-i9 w))
  (cases hf (deb-final w (:debtor e)))
  (all_goals (cases hc (Nat.beq (:cont e) cont-restart)))
  (all_goals (simp only [consume-entry hc hf s9-edge-upd s9-remove-edge])))

(a/theorem s9-cancel-pred [w :- World, c :- CompRow]
  (=> (= (inv-i9 w) true) (= (inv-i9 (cancel-pred w c)) true))
  (intro h)
  (cases hf (run-find w (:run c))) (case' [some r]) (case' [none])
  (simp only [cancel-pred hf]) (exact h)
  (cases ha (run-alive r))
  (simp only [cancel-pred hf ha]) (exact h)
  (simp only [cancel-pred hf ha]) (exact (s9-run-cascade w _ h)))

(a/theorem s9-cut-suffix [w :- World, c :- Nat, has :- Bool, cut :- Nat, cid :- Nat]
  (= (inv-i9 (cut-suffix w c has cut cid)) (inv-i9 w))
  (simp only [cut-suffix s9-comp-upd s9-drop-edges]))

(a/theorem s9-new-run-of [w :- World, c :- CompRow, ei :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (new-run-of w c ei)) true))
  (intro h) (simp only [new-run-of s9-comp-upd]) (exact (s9-add-run-scope w _ _ _ _ h)))

(a/theorem s9-t11 [w :- World, cid :- Nat, fresh :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t11-dispatch w cid fresh))) true))
  (intro h)
  (cases hc (comp-find w cid)) (case' [some c]) (case' [none])
  (simp only [t11-dispatch hc refuse]) (exact h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (Bool.not (:idle c)) (Bool.and (needs-run w c) (eligible w c)))))
  (simp only [t11-dispatch hc hg refuse]) (exact h)
  (simp only [t11-dispatch hc hg accept])
  (have h1 := (s9-cancel-pred w c h))
  (cases he (entry-edge w (:id c))) (case' [some e]) (case' [none])
  (simp only [dispatch-raw he]) (exact (s9-new-run-of _ c _ (Eq.trans (s9-cut-suffix _ _ _ _ _) h1)))
  (simp only [dispatch-raw he])
  (exact (s9-new-run-of _ c _ (Eq.trans (s9-consume-entry _ e) (Eq.trans (s9-cut-suffix _ _ _ _ _) h1)))))

(a/theorem s9-settle-edge [changed :- Bool, ver :- Nat, w :- World, y :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (settle-edge changed ver w y)) true))
  (intro h)
  (cases hf (edge-find w y)) (case' [some e]) (case' [none])
  (simp only [settle-edge hf]) (exact h)
  (simp only [settle-edge hf s9-unmark-edge])
  (cases hp (Nat.beq (:phase e) ph-armed))
  (simp only [hp]) (exact h)
  (cases hc (Bool.or (edge-behind ver e) (member-current w e)))
  (simp only [hp hc]) (exact h)
  (simp only [hp hc]) (exact (s9-fire-dep w e h)))

(a/theorem s9-settle-one [w :- World, d :- Nat, changed :- Bool]
  (=> (= (inv-i9 w) true) (= (inv-i9 (settle-one w d changed)) true))
  (intro h) (simp only [settle-one settle-host])
  (exact (s9-fold-fire _ _ _ (nat-fold-pres inv-i9 (settle-edge changed (deb-version w d))
                                  (s9-settle-edge changed (deb-version w d)) _ w h))))

(a/theorem s9-settle-loop [fuel :- (List Nat)]
  (forall [w :- World, q :- (List Nat)] (=> (= (inv-i9 w) true) (= (inv-i9 (:world (settle-loop fuel w q))) true)))
  (induction fuel)
  (case' [cons h f ih])
  (case' [nil])
  (intros w q hw) (simp only [settle-loop]) (exact hw)
  (intros w q hw)
  (cases q)
  (simp only [settle-loop]) (exact hw)
  (rename_i d t)
  (simp only [settle-loop])
  (exact (ih _ _ (s9-settle-one w d false hw))))

(a/theorem s9-settle [w :- World, d :- Nat, changed :- Bool]
  (=> (= (inv-i9 w) true) (= (inv-i9 (settle w d changed)) true))
  (intro h)
  (cases hr (ready-id w d))
  (simp only [settle hr]) (exact h)
  (simp only [settle hr settle-res])
  (exact (s9-settle-loop (settle-fuel w) _ _ (s9-settle-one w d changed h))))

(a/theorem s9-fin-if-final [w :- World, d :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (fin-if-final w d)) true))
  (intro h)
  (cases hf (deb-final w d))
  (simp only [fin-if-final hf]) (exact h)
  (simp only [fin-if-final hf]) (exact (s9-finalize-debtor w d h)))

(a/theorem s9-complete-body [w :- World, r :- RunRow, res :- RunResult]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (complete-body w r res))) true))
  (intro h)
  (cases hc (comp-find w (:of r)))
  (case [none]
    (cases ht (task-find w (:of r)))
    (case [none] (simp only [complete-body hc ht]) (exact h))
    (case [some k]
      (simp only [complete-body hc ht complete-task])
      (exact (s9-fold-fire _ _ _ (s9-fold-frame res-cancel s9-res-cancel _ _ (Eq.trans (s9-task-upd w _ _) h))))))
  (case [some c]
    (cases he (Nat.beq (:epoch r) (:epoch c)))
    (case [false] (simp only [complete-body hc he]) (exact h))
    (case [true]
      (simp only [complete-body hc he complete-comp cancel-res])
      (exact (s9-settle _ _ _ (s9-fold-frame res-cancel s9-res-cancel _ _ (Eq.trans (s9-comp-upd w _ _) h)))))))

(a/theorem s9-retire-after [w :- World, rid :- Nat]
  (= (inv-i9 (retire-after w rid)) (inv-i9 w))
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [retire-after hf])
  (cases hr (retirable r))
  (all_goals (simp only [retire-after hf hr s9-cleanup-set])))

(a/theorem s9-t12 [w :- World, st :- Nat, tag :- Nat, v :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t12-complete w st tag v))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t12-complete ht refuse]) (exact h)
  (cases hn (run-normal r))
  (simp only [t12-complete ht hn refuse]) (exact h)
  (simp only [t12-complete ht hn accept complete-raw])
  (have h1 := (s9-run-upd w (:id r) run-complete-row keeps9-run-complete-row h))
  (have h2 := (s9-complete-body _ r (RunResult.mk tag v) h1))
  (exact (s9-fin-if-final _ _ (s9-run-cascade _ _ (Eq.trans (s9-retire-after _ _) h2)))))

;; ---- engine.clj Parts F, F2

(a/theorem s9-await-step [r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, acc :- AwAcc, d :- Nat]
  (=> (= (inv-i9 (:world acc)) true) (= (inv-i9 (:world (await-step r a mode k acc d))) true))
  (intro h)
  (cases hd (as-dep (:world acc) r d))
  (case [false]
    (simp only [await-step hd s9-insert-edge-checked]) (exact h))
  (case [true]
    (cases hs (site-edge (:edges (:world acc)) (:of r) (:effect-index r) d))
    (case [none]
      (simp only [await-step hd hs await-new-dep s9-comp-upd])
      (exact (s9-raise-run _ (:of r) d (Eq.trans (s9-insert-edge-checked _ _) h))))
    (case [some e]
      (simp only [await-step hd hs s9-comp-upd s9-edge-upd]) (exact h))))

(a/theorem s9-await-wire [r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, ds :- (List Nat)]
  (forall [acc :- AwAcc] (=> (= (inv-i9 (:world acc)) true) (= (inv-i9 (:world (await-wire r a mode k acc ds))) true)))
  (induction ds)
  (case' [cons d t ih])
  (case' [nil])
  (intros acc h) (simp only [await-wire]) (exact h)
  (intros acc h) (simp only [await-wire]) (exact (ih _ (s9-await-step r a mode k acc d h))))

(a/theorem s9-fast-fill [ps :- (List DE), w :- World, d :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (fast-fill ps w d)) true))
  (intro h)
  (cases hr (fast-ready w d))
  (simp only [fast-fill hr]) (exact h)
  (simp only [fast-fill hr]) (exact (s9-fire-edge _ w _ h)))

(a/theorem s9-park-if [w :- World, a :- Nat, rid :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (park-if w a rid)) true))
  (intro h)
  (cases ha (act-has w a))
  (simp only [park-if ha]) (exact h)
  (simp only [park-if ha]) (exact (s9-run-upd w rid run-park-row keeps9-run-park-row h)))

(a/theorem s9-await-raw [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (= (tbl-all (run-not-of (:id r)) (:runs w)) true) (= (inv-i9 w) true) (= (inv-i9 (await-raw w r ds mode k mine)) true))
  (intros hn h)
  (have h0 (= (inv-i9 (await-pre w r ds mode k mine)) true))
  (simp only [await-pre])
  (have hc (= (tbl-all (run-not-of (:run (ActRow.mk (:next-id w) (:id r) mode (List.nil Member) (none-slots ds) (nat-len ds) k mine)))
                       (:runs (run-upd w (:id r) run-tick))) true))
  (exact (not-of-tick w (:id r) hn))
  (have ha := (s9-act-ins (run-upd w (:id r) run-tick)
                (ActRow.mk (:next-id w) (:id r) mode (List.nil Member) (none-slots ds) (nat-len ds) k mine)
                hc (s9-run-upd w _ _ keeps9-run-tick h)))
  (exact (nat-fold-pres inv-i9 demand-reactive s9-demand-reactive _ _ (Eq.trans (s9-bump _) ha)))
  (have h1 (= (inv-i9 (:world (await-acc w r ds mode k mine))) true))
  (exact (s9-await-wire r (:next-id w) mode k (nat-distinct ds)
           (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) h0))
  (simp only [await-raw await-post])
  (exact (nat-fold-pres inv-i9 fin-if-final s9-fin-if-final _ _
           (s9-park-if _ _ _ (nat-fold-pres inv-i9 (fast-fill (:pairs (await-acc w r ds mode k mine)))
                                  (s9-fast-fill (:pairs (await-acc w r ds mode k mine))) _ _
                                  (Eq.trans (s9-act-upd _ _ _ (act-set-members-run _)) h1))))))

(a/theorem s9-t6 [w :- World, st :- Nat, ds :- (List Nat), mode :- Nat, k :- Nat, fresh :- Nat, mine :- (List Nat)]
  (=> (= (inv-sample w) true) (= (inv-i9 w) true) (= (inv-i9 (:world (t6-await w st ds mode k fresh mine))) true))
  (intros hs h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t6-await ht refuse]) (exact h)
  (cases hg (Bool.and (await-ok w r ds mode fresh) (:ok (await-acc w r ds mode k mine))))
  (simp only [t6-await ht hg refuse]) (exact h)
  (have hg2 := hg)
  (simp only [await-ok Bool.and_eq_true] at hg2)
  (simp only [t6-await ht hg accept])
  (exact (s9-await-raw w r ds mode k mine (tok-not-of w st r hs ht (And.left (And.right (And.left hg2)))) h)))

(a/theorem s9-host-await-dem [w :- World, d :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (host-await-dem w d)) true))
  (intro h) (simp only [host-await-dem])
  (exact (s9-demand-reactive _ d (Eq.trans (s9-insert-edge-checked w _) h))))

(a/theorem s9-t22 [w :- World, d :- Nat, fresh :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t22-host-await w d fresh))) true))
  (intro h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (deb-exists w d)))
  (simp only [t22-host-await hg refuse]) (exact h)
  (simp only [t22-host-await hg accept])
  (have h1 := (s9-host-await-dem w d h))
  (cases hr (fast-ready (host-await-dem w d) d))
  (simp only [host-await-raw hr]) (exact h1)
  (simp only [host-await-raw hr]) (exact (s9-fire-edge _ _ _ h1)))

(a/theorem s9-t22-un [w :- World, y :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t22-host-unawait w y))) true))
  (intro h)
  (cases hf (edge-find w y)) (case' [some e]) (case' [none])
  (simp only [t22-host-unawait hf refuse]) (exact h)
  (cases hg (Bool.and (Nat.beq (:kind e) ek-wait) (Nat.beq (:creditor e) 0)))
  (simp only [t22-host-unawait hf hg refuse]) (exact h)
  (simp only [t22-host-unawait hf hg accept s9-remove-edge]) (exact h))

(a/theorem s9-t8-full [w :- World, d :- Nat, cb :- Nat, fresh :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t8-full w d cb fresh))) true))
  (intro h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (edge-ok-in w (observe-edge w d cb))))
  (simp only [t8-full hg refuse]) (exact h)
  (simp only [t8-full hg accept])
  (have h1 := (s9-demand-reactive _ d (Eq.trans (s9-insert-edge-fresh w (observe-edge w d cb)) h)))
  (cases hr (deb-ready (demand-reactive (insert-edge-fresh w (observe-edge w d cb)) d) d))
  (simp only [observe-raw hr]) (exact h1)
  (simp only [observe-raw hr]) (exact (s9-fire-edge _ _ _ h1)))

(a/theorem s9-new-pub-handle [w :- World, y :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (new-pub-handle w y))) true))
  (intro h)
  (cases hp (pub-find w y)) (case' [some p]) (case' [none])
  (simp only [new-pub-handle hp refuse]) (exact h)
  (cases hh (Nat.beq (:handles p) 0))
  (all_goals (simp only [new-pub-handle hp hh refuse accept s9-pub-upd]))
  (all_goals (exact h)))

(a/theorem s9-new-source-handle [w :- World, y :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (new-source-handle w y))) true))
  (intro h)
  (cases hs (source-find w y)) (case' [some s]) (case' [none])
  (simp only [new-source-handle hs]) (exact (s9-new-pub-handle w y h))
  (cases hh (Nat.beq (:handles s) 0))
  (all_goals (simp only [new-source-handle hs hh refuse accept s9-source-upd]))
  (all_goals (exact h)))

(a/theorem s9-new-task-handle [w :- World, y :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (new-task-handle w y))) true))
  (intro h)
  (cases ht (task-find w y)) (case' [some t]) (case' [none])
  (simp only [new-task-handle ht]) (exact (s9-new-source-handle w y h))
  (cases hh (Nat.beq (:handles t) 0))
  (all_goals (simp only [new-task-handle ht hh refuse accept s9-task-upd]))
  (all_goals (exact h)))

(a/theorem s9-t-handle-new [w :- World, y :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t-handle-new w y))) true))
  (intro h)
  (cases hc (comp-find w y)) (case' [some c]) (case' [none])
  (simp only [t-handle-new hc]) (exact (s9-new-task-handle w y h))
  (cases hh (Nat.beq (:handles c) 0))
  (all_goals (simp only [t-handle-new hc hh refuse accept s9-comp-upd]))
  (all_goals (exact h)))

(a/theorem s9-t-deliver [w :- World, s :- Nat, v :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t-deliver w s v))) true))
  (intro h)
  (cases hf (source-find w s)) (case' [some sr]) (case' [none])
  (simp only [t-deliver hf refuse]) (exact h)
  (cases hd (deliverable sr))
  (simp only [t-deliver hf hd refuse]) (exact h)
  (simp only [t-deliver hf hd accept deliver-raw deliver-fire])
  (exact (s9-finalize-debtor _ s (s9-fold-fire _ _ _ (s9-fold-fire _ _ _ (Eq.trans (s9-source-upd w s _) h))))))

(a/theorem s9-serve-or [w :- World, s :- Nat, res :- RunResult, keep :- (=> SourceRow SourceRow)]
  (=> (= (inv-i9 w) true) (= (inv-i9 (serve-or w s res keep)) true))
  (intro h)
  (cases hw (Nat.beq (oldest-waiter w s) 0))
  (simp only [serve-or hw]) (exact (s9-fire-edge _ w _ h))
  (simp only [serve-or hw s9-source-upd]) (exact h))

(a/theorem s9-t-post [w :- World, s :- Nat, v :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t-post w s v))) true))
  (intro h)
  (cases hf (source-find w s)) (case' [some sr]) (case' [none])
  (simp only [t-post hf refuse]) (exact h)
  (cases hk (open-kind sk-mailbox sr))
  (simp only [t-post hf hk refuse]) (exact h)
  (simp only [t-post hf hk accept post-raw]) (exact (s9-serve-or _ s _ _ (Eq.trans (s9-source-upd w s _) h))))

(a/theorem s9-t-release [w :- World, s :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t-release w s))) true))
  (intro h)
  (cases hf (source-find w s)) (case' [some sr]) (case' [none])
  (simp only [t-release hf refuse]) (exact h)
  (cases hk (open-kind sk-semaphore sr))
  (simp only [t-release hf hk refuse]) (exact h)
  (simp only [t-release hf hk accept release-raw]) (exact (s9-serve-or _ s _ _ (Eq.trans (s9-source-upd w s _) h))))

(a/theorem s9-t-take [w :- World, st :- Nat, s :- Nat, k :- Nat, fresh :- Nat]
  (=> (= (inv-sample w) true) (= (inv-i9 w) true) (= (inv-i9 (:world (t-take w st s k fresh))) true))
  (intros hs h)
  (cases ht (tok-run w st))
  (case [none] (simp only [t-take ht refuse]) (exact h))
  (case [some r]
    (cases hf (source-find w s))
    (case [none] (simp only [t-take ht hf refuse]) (exact h))
    (case [some sr]
      (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (run-normal r) (takeable sr))))
      (case [false] (simp only [t-take ht hf hg refuse]) (exact h))
      (case [true]
        (have hg2 := hg)
        (simp only [Bool.and_eq_true] at hg2)
        (have hn := (tok-not-of w st r hs ht (And.left (And.right hg2))))
        (cases ha (take-ready sr))
        (case [false]
          (simp only [t-take ht hf hg ha accept take-park])
          (have hc (= (tbl-all (run-not-of (:run (take-act w r k))) (:runs w)) true))
          (simp only [take-act]) (exact hn)
          (exact (s9-run-upd _ _ _ keeps9-run-tick-park
                   (Eq.trans (s9-insert-edge-checked _ _) (Eq.trans (s9-bump _) (s9-act-ins w (take-act w r k) hc h))))))
        (case [true]
          (simp only [t-take ht hf hg ha accept take-now s9-bump])
          (exact (s9-run-upd _ _ _ keeps9-run-tick (Eq.trans (s9-source-upd w s _) h))))))))

;; Z#55: arm = the resource (arm-raw), then the park on its wait edge (take-park, as T6)
(a/theorem s9-t17 [w :- World, st :- Nat, kind :- Nat, k :- Nat, fresh :- Nat]
  (=> (= (inv-sample w) true) (= (inv-i9 w) true) (= (inv-i9 (:world (t17-arm w st kind k fresh))) true))
  (intros hs h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t17-arm ht refuse]) (exact h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (run-normal r) (arm-kind-ok kind))))
  (simp only [t17-arm ht hg refuse]) (exact h)
  (have hg2 := hg)
  (simp only [Bool.and_eq_true] at hg2)
  (have hn := (tok-not-of w st r hs ht (And.left (And.right hg2))))
  (have h1 (= (inv-i9 (arm-raw w r kind)) true))
  (simp only [arm-raw])
  (exact (s9-run-upd _ _ _ (keeps9-run-arm _) (Eq.trans (s9-bump _) (Eq.trans (s9-resource-ins w _) h))))
  (have hc (= (tbl-all (run-not-of (:id r)) (:runs (arm-raw w r kind))) true))
  (exact (tbl-all-upd RunRow run-id (:id r) (run-arm (:next-id w)) (run-not-of (:id r)) (run-not-of (:id r))
           (fn [q :- RunRow, a1 :- (= (run-not-of (:id r) q) true), a2 :- (= (Nat.beq (run-id q) (:id r)) true)] a1)
           (fn [q :- RunRow, a1 :- (= (run-not-of (:id r) q) true), a2 :- (= (Nat.beq (run-id q) (:id r)) false)] a1)
           (:runs w) hn))
  (simp only [t17-arm ht hg accept arm-park take-park])
  (exact (s9-run-upd _ _ _ keeps9-run-tick-park
           (Eq.trans (s9-insert-edge-checked _ _)
             (Eq.trans (s9-bump _) (s9-act-ins _ (take-act (arm-raw w r kind) (run-arm (:next-id w) r) k) hc h1))))))

(a/theorem s9-t-finally-enter [w :- World, st :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t-finally-enter w st))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t-finally-enter ht refuse]) (exact h)
  (cases hg (run-normal r))
  (simp only [t-finally-enter ht hg refuse]) (exact h)
  (simp only [t-finally-enter ht hg accept]) (exact (s9-run-upd w _ _ (keeps9-run-fin-push _) h)))

(a/theorem s9-t-finally-exit [w :- World, st :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t-finally-exit w st))) true))
  (intro h)
  (cases ht (tok-run w st))
  (case [none] (simp only [t-finally-exit ht refuse]) (exact h))
  (case [some r]
    (cases he (fins-empty (:finalizers r)))
    (case [true] (simp only [t-finally-exit ht he refuse]) (exact h))
    (case [false] (simp only [t-finally-exit ht he accept]) (exact (s9-run-upd w _ _ keeps9-run-fin-pop h)))))

(a/theorem s9-t-slice-exit [w :- World, rid :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t-slice-exit w rid))) true))
  (intro h)
  (cases hf (run-find w rid))
  (case [none] (simp only [t-slice-exit hf refuse]) (exact h))
  (case [some r]
    (cases hg (exit-ready r))
    (case [false] (simp only [t-slice-exit hf hg refuse]) (exact h))
    (case [true]
      (simp only [t-slice-exit hf hg accept])
      (exact (s9-retire-full _ _ (s9-run-upd w _ _ keeps9-run-fin-pop-end h))))))

(a/theorem s9-t-cancel [w :- World, rid :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t-cancel w rid))) true))
  (intro h)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [t-cancel hf refuse]) (exact h)
  (cases hg (host-cancel-ok w r))
  (simp only [t-cancel hf hg refuse]) (exact h)
  (simp only [t-cancel hf hg]) (exact (s9-t14 w rid false h)))

(a/theorem s9-t-open-scope [w :- World, st :- Nat, s :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t-open-scope w st s))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t-open-scope ht refuse]) (exact h)
  (cases hg (Bool.and (Nat.beq s (:next-id w)) (open-ok w r)))
  (all_goals (simp only [t-open-scope ht hg refuse accept s9-bump s9-scope-ins]))
  (all_goals (exact h)))

(a/theorem s9-t-close-scope [w :- World, s :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t-close-scope w s))) true))
  (intro h)
  (cases hg (scope-explicit-at w s))
  (simp only [t-close-scope hg refuse]) (exact h)
  (simp only [t-close-scope hg]) (exact (s9-t16 w s h)))

(a/theorem s9-t-detach [w :- World, k :- Nat, s :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t-detach w k s))) true))
  (intro h)
  (cases hf (task-find w k)) (case' [some t]) (case' [none])
  (simp only [t-detach hf refuse]) (exact h)
  (cases hg (detach-ok w t s))
  (simp only [t-detach hf hg refuse]) (exact h)
  (simp only [t-detach hf hg accept remove-empty-at detach-move])
  (exact (s9-remove-if-empty _ _ (Eq.trans (s9-scope-upd _ _ _) (Eq.trans (s9-task-upd w _ _) h)))))

(a/theorem s9-zero-handles [w :- World]
  (=> (= (inv-i9 w) true) (= (inv-i9 (zero-handles w)) true))
  (intro h) (simp only [zero-handles])
  (have hc (forall [w2 :- World, y :- Nat] (= (inv-i9 (comp-h0-at w2 y)) (inv-i9 w2))))
  (intros w2 y) (simp only [comp-h0-at s9-comp-upd])
  (have ht (forall [w2 :- World, y :- Nat] (= (inv-i9 (task-h0-at w2 y)) (inv-i9 w2))))
  (intros w2 y) (simp only [task-h0-at s9-task-upd])
  (have hs (forall [w2 :- World, y :- Nat] (= (inv-i9 (source-h0-at w2 y)) (inv-i9 w2))))
  (intros w2 y) (simp only [source-h0-at s9-source-upd])
  (have hp (forall [w2 :- World, y :- Nat] (= (inv-i9 (pub-h0-at w2 y)) (inv-i9 w2))))
  (intros w2 y) (simp only [pub-h0-at s9-pub-upd])
  (exact (s9-fold-frame pub-h0-at hp _ _ (s9-fold-frame source-h0-at hs _ _
           (s9-fold-frame task-h0-at ht _ _ (s9-fold-frame comp-h0-at hc w _ h))))))

(a/theorem s9-t-release-world [w :- World]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t-release-world w))) true))
  (intro h)
  (cases hr (:released w))
  (simp only [t-release-world hr accept release-world-raw])
  (exact (s9-run-cascade _ _ (s9-zero-handles _
           (Eq.trans (s9-set-pending-act _ _) (Eq.trans (s9-set-pins _ _)
             (Eq.trans (s9-drop-edges _ _) (Eq.trans (s9-set-released w _) h)))))))
  (simp only [t-release-world hr refuse]) (exact h))

(a/theorem s9-t1-full [w :- World, st :- Nat, kind :- Nat, v :- Nat, fresh :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t1-full w st kind v fresh))) true))
  (intro h)
  (cases ht (tok-run w st))
  (case [none] (simp only [t1-full ht refuse]) (exact h))
  (case [some r]
    (cases ho (readopt-source w r fresh))
    (case [none]
      (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (src-kind-ok kind)))
      (case [false] (simp only [t1-full ht ho hg refuse]) (exact h))
      (case [true]
        (simp only [t1-full ht ho hg accept create-source-cur])
        (exact (s9-run-upd _ _ _ keeps9-run-tick
                 (Eq.trans (s9-record-basis _ r _) (Eq.trans (s9-bump _) (Eq.trans (s9-source-ins w _) h)))))))
    (case [some sx]
      (cases hk (Nat.beq (:kind sx) kind))
      (case [false] (simp only [t1-full ht ho hk refuse]) (exact h))
      (case [true] (simp only [t1-full ht ho hk accept]) (exact (s9-respawn-raw w r fresh h))))))


(a/theorem s9-t-schedule [w :- World, rid :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t-schedule w rid))) true))
  (intro h)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [t-schedule hf refuse]) (exact h)
  (cases hg (sched-ok w r))
  (simp only [t-schedule hf hg refuse]) (exact h)
  (simp only [t-schedule hf hg accept]) (exact (s9-run-upd w rid run-enter-row keeps9-run-enter-row h)))

(a/theorem s9-t-finalize [w :- World, rid :- Nat]
  (=> (= (inv-i9 w) true) (= (inv-i9 (:world (t-finalize w rid))) true))
  (intro h)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [t-finalize hf refuse]) (exact h)
  (cases hg (cleanup-ready w r))
  (simp only [t-finalize hf hg refuse]) (exact h)
  (simp only [t-finalize hf hg accept]) (exact (s9-run-upd w rid run-enter-row keeps9-run-enter-row h)))

(a/theorem i9-raw0 [w :- World, it :- Item]
  (=> (= (inv-sample w) true) (= (inv-i9 w) true) (= (inv-i9 (:world (raw0 w it))) true))
  (intros hs h)
  (cases it)
  (all_goals (simp only [raw0]))
  (rename_i st kind v fresh) (cases hc (body-shut w st))
  (simp only [hc]) (exact (s9-t1-full w _ _ _ _ h))
  (simp only [hc refuse]) (exact h)
  (exact (s9-t1-top w _ _ _ _ h))
  (exact (s9-t2 w _ _ h))
  (rename_i st s k fresh) (cases hc (in-cleanup w st))
  (simp only [hc]) (exact (s9-t7 w _ _ _ _ h))
  (simp only [hc refuse]) (exact h)
  (exact (s9-t8-full w _ _ _ h))
  (exact (s9-t8-unobserve w _ h))
  (exact (s9-t9 w _ _ _ h))
  (exact (s9-t15 w _ h))
  (rename_i st kind k fresh) (cases hc (in-cleanup w st))
  (simp only [hc]) (exact (s9-t17 w _ _ _ _ hs h))
  (simp only [hc refuse]) (exact h)
  (exact (s9-t18 w _ _ _ h))
  (exact (s9-t19 w _ h))
  (exact (s9-t20-pin w _ h))
  (exact (s9-t20-unpin w _ h))
  (rename_i st c i b) (cases hc (in-cleanup w st))
  (simp only [hc]) (exact (s9-t3 w _ _ _ _ h))
  (simp only [hc refuse]) (exact h)
  (exact (s9-t3-top w _ _ _ _ h))
  (rename_i st b fresh ins) (cases hc (body-shut w st))
  (simp only [hc]) (exact (s9-t4 w _ _ _ _ h))
  (simp only [hc refuse]) (exact h)
  (exact (s9-t4-top w _ _ _ _ h))
  (exact (s9-t5 w _ _ h))
  (rename_i st ds m k fresh mine) (cases hc (await-kind-bad w ds))
  (simp only [hc]) (exact (s9-t6 w _ _ _ _ _ _ hs h))
  (simp only [hc refuse]) (exact h)
  (exact (s9-t11 w _ _ h))
  (rename_i st tag v) (cases hc (complete-refused w st tag))
  (simp only [hc]) (exact (s9-t12 w _ _ _ h))
  (simp only [hc refuse]) (exact h)
  (exact (s9-t-schedule w _ h))
  (rename_i d fresh) (cases hc (deb-consuming w d))
  (simp only [hc]) (exact (s9-t22 w _ _ h))
  (simp only [hc refuse]) (exact h)
  (exact (s9-t22-un w _ h))
  (exact (s9-t-handle-new w _ h))
  (exact (s9-t-deliver w _ _ h))
  (exact (s9-t-post w _ _ h))
  (exact (s9-t-take w _ _ _ _ hs h))
  (exact (s9-t-release w _ h))
  (exact (s9-t-finalize w _ h))
  (exact (s9-t-cancel w _ h))
  (exact (s9-t-release-world w h))
  (exact (s9-t-open-scope w _ _ h))
  (exact (s9-t-close-scope w _ h))
  (exact (s9-t-detach w _ _ h))
  (exact (s9-t-finally-enter w _ h))
  (exact (s9-t-finally-exit w _ h))
  (exact (s9-t-slice-exit w _ h)))

(a/theorem i9-raw [w :- World, it :- Item]
  (=> (= (inv-sample w) true) (= (inv-i9 w) true) (= (inv-i9 (:world (raw w it))) true))
  (intros hs h)
  (have h00 := (i9-raw0 w it hs h))
  (have h0 (= (inv-i9 (:world (raw0g w it))) true))
  (cases hsh (host-shut w it))
  (simp only [raw0g hsh]) (exact h00)
  (simp only [raw0g hsh refuse]) (exact h)
  (cases ha (:accepted (raw0g w it)))
  (simp only [raw post ha]) (exact h0)
  (simp only [raw post ha accept cancel-losers]) (exact (s9-run-cascade _ _ h0)))

;; I9 for the step (given inv-sample, for the unique run ids at T6/take)
(a/theorem step-i9 [w :- World, it :- Item]
  (=> (= (inv-sample w) true) (= (inv-i9 w) true) (= (inv-i9 (:world (world-step w it))) true))
  (intros hs h)
  (have h0 := (i9-raw w it hs h))
  (cases ha (:accepted (raw w it)))
  (simp only [world-step finish ha]) (exact h0)
  (simp only [world-step finish ha accept]) (exact (s9-rule-r _ h0)))

(a/theorem i9-empty [] (= (inv-i9 empty-world) true) (rfl))

;; ===========================================================================
;; Part E. I5, wait half: no wait edge without its activation (a host wait has creditor 0).
;; It is part of I2 (`edges-ref-ok` in inv-sample), so it holds after every step.
;; ===========================================================================

(a/theorem wait-cred-of-edge-ok [w :- World, e :- EdgeRow]
  (=> (= (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w) e) true) (= (wait-cred-ok w e) true))
  (intro h)
  (simp only [edge-ok Bool.and_eq_true] at h)
  (have hc := (And.left h))
  (cases hk (Nat.beq (:kind e) ek-wait))
  (simp only [wait-cred-ok hk Bool.not_false Bool.true_or])
  (cases h0 (Nat.beq (:creditor e) 0))
  (have hd (= (Nat.beq (:kind e) ek-dep) false))
  (have he (= (:kind e) ek-wait)) (exact (Nat.eq_of_beq_eq_true hk))
  (rw [he])
  (have hh (= (host-cred e) false))
  (simp only [host-cred hk h0 Bool.and_false Bool.or_false])
  (have he (= (:kind e) ek-wait)) (exact (Nat.eq_of_beq_eq_true hk))
  (rw [he])
  (simp only [cred-ok hd hh] at hc)
  (simp only [wait-cred-ok hk h0 act-has Bool.not_true Bool.false_or hc])
  (simp only [wait-cred-ok hk h0 Bool.not_true Bool.false_or Bool.true_or]))

(a/theorem i5-wait-of-sample [w :- World]
  (=> (= (inv-sample w) true) (= (tbl-all (wait-cred-ok w) (:edges w)) true))
  (intro hs)
  (have hp := (inv-parts w hs))
  (have he := (And.left (And.right hp)))
  (simp only [edges-ref-ok edges-ref-ok-in] at he)
  (exact (tbl-all-mono EdgeRow _ _ (wait-cred-of-edge-ok w) (:edges w) he)))

(a/theorem step-i5-wait [w :- World, it :- Item]
  (=> (= (inv-sample w) true) (= (rule-r-safe (:world (raw w it))) true)
      (= (tbl-all (wait-cred-ok (:world (world-step w it))) (:edges (:world (world-step w it)))) true))
  (intros hs hr)
  (exact (i5-wait-of-sample _ (step-inv w it hs hr))))
