(ns spindel.v2.completion.quiet-world
  "C1 completion stability, layer 1, the quiet half (notes/history/PLAN.md C1, `hq`): a quiet world (released,
  no run) holds only scopes, and every item is refused there, so a quiet world stays quiet.

    cleanup-runs-exist w        well-formed w and every cleanup entry's run is a run row (`cleanup-runs-exist-rest`): the cleanup entry
                is written at a run's cancel (T14) or its completion (T12, `retire-after`) for a run
                found by id, and goes with the run (T13 `t13-retire-with-subtree`); Rule R's filter keeps every
                cleanup entry's run (it is in `cleanup-rows`). `step-cleanup-runs-exist`, `cleanup-runs-exist-empty`.
    quiet-world-inv w      chain-to-marks-waiting w, K (`host-roots-revoked-rest`, spindel.v2.completion.quiet), cleanup-runs-exist and I3 (`i3`: the filter keeps every id,
                `step-i3-total`); `step-quiet-world-inv`, `quiet-world-inv-empty`.
    quiet-rows  the closure lemma: in a quiet world with quiet-world-inv, live is scopes only (the roots are scopes:
                no pin, no host edge, no pending activation, no publication; a scope's successors are
                its parent (I1, a scope; the root scope's parent is 0, root-scope-reserved), no running task (no run),
                no fork marker (root-scope-reserved)), nothing is admitted (every handle count is 0), there is no cleanup
                entry (cleanup-runs-exist) and no storage (no run): every computation, task, source, edge, activation
                and resource id would be kept (I3) only by live, a scope id, against unique ids. So the
                world holds no computation (tombstones included), task, run, source, edge, activation,
                resource, cleanup entry or publication.
    quiet-refused  every item is refused in a quiet world with quiet-world-inv: host items by `host-item-refused` (no run
                holds a slice), creations and roots by transition's released guards, token items for want of
                a run, the others for want of their row; so `world-step` leaves a quiet world as it
                is (`quiet-step`).

  The bundle goes through the generic step tree (spindel.v2.pres.tree)."
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
            [spindel.v2.progress.casc :refer :all]
            [spindel.v2.inv.acts :refer :all]
            [spindel.v2.inv :refer :all]
            [spindel.v2.pres.tree :as tree]
            [spindel.v2.pres.part :refer :all]
            [spindel.v2.inv.copier :refer :all]
            [spindel.v2.inv.base :refer :all]
            [spindel.v2.inv.marks-step :refer [chain-to-marks-waiting]]
            [spindel.v2.completion.quiet :refer :all]
            [spindel.v2.inv.i11] [spindel.v2.inv.i1-scopes] [spindel.v2.inv.i5] [spindel.v2.inv.i1-owners] [spindel.v2.inv.i1-runs :refer [i1-runs]] [spindel.v2.inv.i8]
            [spindel.v2.inv.comp-facts] [spindel.v2.inv.i14] [spindel.v2.inv.i10]
            [spindel.v2.completion.open-scopes :refer [open-scopes-have-runs-rest open-scopes-have-runs os-need hw]]
            [spindel.v2.ledger :refer [task-complete task-held task-srow scope-complete]]))

;; ===========================================================================
;; Part A. cleanup-runs-exist: every cleanup entry's run is a run row
;; ===========================================================================

(a/defn cl-run [rs :- (List RunRow), c :- CleanupRow] Bool (tbl-has run-id (:run c) rs))
(a/defn cleanup-runs-exist-rest [w :- World] Bool (tbl-all (cl-run (:runs w)) (:cleanup w)))
(a/defn cleanup-runs-exist [w :- World] Bool (Bool.and (well-formed w) (cleanup-runs-exist-rest w)))

(a/theorem cleanup-runs-exist-well-formed [w :- World] (=> (= (cleanup-runs-exist w) true) (= (well-formed w) true))
  (intro h) (simp only [cleanup-runs-exist Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem cleanup-runs-exist-rest-of [w :- World] (=> (= (cleanup-runs-exist w) true) (= (cleanup-runs-exist-rest w) true))
  (intro h) (simp only [cleanup-runs-exist Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem cleanup-runs-exist-intro [w :- World] (=> (= (well-formed w) true) (= (cleanup-runs-exist-rest w) true) (= (cleanup-runs-exist w) true))
  (intros h1 h2) (simp only [cleanup-runs-exist h1 h2 Bool.and_self]))
(a/theorem cleanup-runs-exist-parts [w :- World]
  (=> (= (cleanup-runs-exist w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (cleanup-runs-exist-well-formed w h))))

;; the runs grow (as a set of ids), the cleanup table is the same
(a/theorem cleanup-runs-exist-rest-runs [w :- World, w2 :- World]
  (=> (= (:cleanup w2) (:cleanup w))
      (forall [y :- Nat] (=> (= (tbl-has run-id y (:runs w)) true) (= (tbl-has run-id y (:runs w2)) true)))
      (= (cleanup-runs-exist-rest w) true) (= (cleanup-runs-exist-rest w2) true))
  (intros e hy h)
  (simp only [cleanup-runs-exist-rest] at h) (simp only [cleanup-runs-exist-rest]) (rw [e])
  (exact (tbl-all-mono CleanupRow (cl-run (:runs w)) (cl-run (:runs w2))
           (fn [c :- CleanupRow, q :- (= (cl-run (:runs w) c) true)] (hy (:run c) q)) (:cleanup w) h)))

(a/theorem cleanup-runs-exist-rest-run-upd [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                            hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r)))]
  (=> (= (cleanup-runs-exist-rest w) true) (= (cleanup-runs-exist-rest (run-upd w x f)) true))
  (intro h)
  (exact (cleanup-runs-exist-rest-runs w (run-upd w x f) (rfl)
           (fn [y :- Nat, q :- (= (tbl-has run-id y (:runs w)) true)]
             (Eq.trans (tbl-has-upd RunRow run-id x y f hf (:runs w)) q)) h)))
(a/theorem cleanup-runs-exist-rest-run-ins [w :- World, r :- RunRow] (=> (= (cleanup-runs-exist-rest w) true) (= (cleanup-runs-exist-rest (bump (run-ins w r))) true))
  (intro h)
  (exact (cleanup-runs-exist-rest-runs w (bump (run-ins w r)) (rfl)
           (fn [y :- Nat, q :- (= (tbl-has run-id y (:runs w)) true)]
             (Eq.trans (tbl-has-ins RunRow run-id y r (:runs w)) (Eq.trans (congrArg (Bool.or (Nat.beq (run-id r) y)) q) (Bool.or_true _)))) h)))
(a/theorem cleanup-runs-exist-rest-cleanup-del [w :- World, x :- Nat] (=> (= (cleanup-runs-exist-rest w) true) (= (cleanup-runs-exist-rest (cleanup-del w x)) true))
  (intro h) (simp only [cleanup-runs-exist-rest] at h) (simp only [cleanup-runs-exist-rest cleanup-del set-cleanup])
  (exact (all-del-keep CleanupRow cleanup-id x (cl-run (:runs w)) (:cleanup w) h)))
(a/theorem cleanup-runs-exist-rest-cleanup-upd [w :- World, x :- Nat, f :- (=> CleanupRow CleanupRow),
                                hr :- (forall [c :- CleanupRow] (= (:run (f c)) (:run c)))]
  (=> (= (cleanup-runs-exist-rest w) true) (= (cleanup-runs-exist-rest (cleanup-upd w x f)) true))
  (intro h) (simp only [cleanup-runs-exist-rest] at h) (simp only [cleanup-runs-exist-rest cleanup-upd set-cleanup])
  (exact (all-upd-keep CleanupRow cleanup-id x f (cl-run (:runs w))
           (fn [c :- CleanupRow, q :- (= (cl-run (:runs w) c) true)] (Eq.trans (congrArg (fn [n :- Nat] (tbl-has run-id n (:runs w))) (hr c)) q))
           (:cleanup w) h)))
;; cleanup[rid] for a run row rid
(a/theorem cleanup-runs-exist-rest-set [w :- World, rid :- Nat, rows :- (List Nat)]
  (=> (= (tbl-has run-id rid (:runs w)) true) (= (cleanup-runs-exist-rest w) true) (= (cleanup-runs-exist-rest (cleanup-set w rid rows)) true))
  (intros hr h) (simp only [cleanup-runs-exist-rest] at h)
  (have t := (all-del-keep CleanupRow cleanup-id rid (cl-run (:runs w)) (:cleanup w) h))
  (simp only [cleanup-runs-exist-rest cleanup-set cleanup-ins cleanup-del set-cleanup tbl-ins tbl-all cl-run hr t Bool.and_self]))
;; T13: the run row and its cleanup entry go together
(a/theorem cleanup-runs-exist-rest-del-both [w :- World, x :- Nat] (=> (= (cleanup-runs-exist-rest w) true) (= (cleanup-runs-exist-rest (cleanup-del (run-del w x) x)) true))
  (intro h) (simp only [cleanup-runs-exist-rest] at h) (simp only [cleanup-runs-exist-rest cleanup-del run-del set-cleanup set-runs])
  (apply (tbl-all-del CleanupRow cleanup-id x (cl-run (:runs w)) (cl-run (tbl-del run-id x (:runs w))) _ (:cleanup w) h))
  (intros c q ne)
  (simp only [cl-run] at q) (simp only [cl-run])
  (have ne2 (= (Nat.beq x (:run c)) false)) (exact (beq-symm-false _ _ ne))
  (rw [(tbl-has-del-ne RunRow run-id x (:run c) (:runs w) ne2)]) (exact q))
;; Rule R's filter keeps every cleanup entry's run (it is in cleanup-rows)
(a/theorem cl-in-rows [v :- World, c :- CleanupRow, cs :- (List CleanupRow)]
  (=> (List.Mem c cs) (= (reach-mem (:run c) (cleanup-rows-in v cs)) true))
  (induction cs)
  (case [nil] (intro m) (cases m))
  (case [cons hd t ih]
    (intro m)
    (cases m)
    (simp only [cleanup-rows-in cleanup-contrib anc-close cleanup-base reach-mem-append reach-mem Nat.beq_refl Bool.true_or])
    (rename_i m2)
    (simp only [cleanup-rows-in reach-mem-append (ih m2) Bool.or_true])))
(a/theorem cleanup-runs-exist-rest-filter-keep [v :- World] (=> (= (cleanup-runs-exist-rest v) true) (= (cleanup-runs-exist-rest (filter-world (keep-fn v) v)) true))
  (intro h) (simp only [cleanup-runs-exist-rest] at h)
  (simp only [cleanup-runs-exist-rest filter-world])
  (apply all-of-mem) (intros c m)
  (have q := (tbl-all-mem CleanupRow _ c _ h m))
  (have k (= (keep-fn v (:run c)) true))
  (simp only [keep-fn keep-with cleanup-rows (cl-in-rows v c (:cleanup v) m) Bool.or_true Bool.true_or])
  (simp only [cl-run] at q)
  (simp only [cl-run (tbl-has-keep RunRow (keep-fn v) run-id (:run c) (:runs v)) k q Bool.and_self]))
(a/theorem cleanup-runs-exist-filter-keep [v :- World]
  (=> (= (cleanup-runs-exist v) true) (= (filter-safe v) true) (= (cleanup-runs-exist (filter-world (keep-fn v) v)) true))
  (intros h hs)
  (exact (cleanup-runs-exist-intro _ (well-formed-filter-world v (keep-fn v) (cleanup-runs-exist-well-formed v h) hs) (cleanup-runs-exist-rest-filter-keep v (cleanup-runs-exist-rest-of v h)))))


;; ---- the GC copy
(def GC (mk-bundle 'cleanup-runs-exist [] "cleanup-runs-exist-" {'well-formed-cleanup-upd ['(fn [c :- CleanupRow] (Eq.refl (:run c))) 3]}))
(swap! (:renames GC) assoc 'well-formed-parts 'cleanup-runs-exist-parts)

(defpart GC :reads '[cleanup runs])
(frames/frame-theorem! 'cleanup-runs-exist-rest-mark-edge 'cleanup-runs-exist-rest 'well-formed-mark-edge)
(frames/frame-theorem! 'cleanup-runs-exist-rest-unmark-edge 'cleanup-runs-exist-rest 'well-formed-unmark-edge)
(frames/frame-theorem! 'cleanup-runs-exist-rest-remove-edge 'cleanup-runs-exist-rest 'well-formed-remove-edge)
(prim! GC 'well-formed-run-upd '(cleanup-runs-exist-rest-run-upd w x f hf R))
(prim! GC 'well-formed-run-ins-fresh '(cleanup-runs-exist-rest-run-ins w r R))
(prim! GC 'well-formed-cleanup-del '(cleanup-runs-exist-rest-cleanup-del w x R))
(a/theorem cleanup-runs-exist-cleanup-upd [w :- World, x :- Nat, f :- (=> CleanupRow CleanupRow),
                           hr :- (forall [c :- CleanupRow] (= (:run (f c)) (:run c)))]
  (=> (= (cleanup-runs-exist w) true) (= (cleanup-runs-exist (cleanup-upd w x f)) true))
  (intro h) (exact (cleanup-runs-exist-intro _ (well-formed-cleanup-upd w x f (cleanup-runs-exist-well-formed w h)) (cleanup-runs-exist-rest-cleanup-upd w x f hr (cleanup-runs-exist-rest-of w h)))))
(swap! (:renames GC) assoc 'well-formed-cleanup-upd 'cleanup-runs-exist-cleanup-upd)

(a/theorem cleanup-runs-exist-cleanup-set [w :- World, rid :- Nat, rows :- (List Nat)]
  (=> (= (tbl-has run-id rid (:runs w)) true) (= (cleanup-runs-exist w) true) (= (cleanup-runs-exist (cleanup-set w rid rows)) true))
  (intros hr h) (exact (cleanup-runs-exist-intro _ (well-formed-cleanup-set w rid rows (cleanup-runs-exist-well-formed w h)) (cleanup-runs-exist-rest-set w rid rows hr (cleanup-runs-exist-rest-of w h)))))
(a/theorem cleanup-runs-exist-del-both [w :- World, x :- Nat] (=> (= (cleanup-runs-exist w) true) (= (cleanup-runs-exist (cleanup-del (run-del w x) x)) true))
  (intro h) (exact (cleanup-runs-exist-intro _ (well-formed-cleanup-del _ x (well-formed-run-del w x (cleanup-runs-exist-well-formed w h))) (cleanup-runs-exist-rest-del-both w x (cleanup-runs-exist-rest-of w h)))))
(a/theorem run-has-of-find [w :- World, rid :- Nat, r :- RunRow]
  (=> (= (run-find w rid) (Option.some RunRow r)) (= (tbl-has run-id (:id r) (:runs w)) true))
  (intro hf)
  (have e (= (run-id r) rid)) (exact (tbl-find-id RunRow run-id rid r (:runs w) hf))
  (have e2 (= (:id r) rid)) (exact e)
  (rw [e2]) (exact (tbl-find-has RunRow run-id rid r (:runs w) hf)))
(a/theorem runs-cancel-res [w :- World, r :- RunRow] (= (:runs (cancel-res w r)) (:runs w))
  (simp only [cancel-res])
  (exact (nat-fold-frame (List RunRow) (fn [v :- World] (:runs v)) res-cancel (fn [v :- World, y :- Nat] (Eq.refl (:runs v))) (:resources r) w)))
(a/theorem runs-cancel-acts [w :- World, x :- Nat] (= (:runs (cancel-acts w x)) (:runs w))
  (simp only [cancel-acts])
  (exact (nat-fold-frame (List RunRow) (fn [v :- World] (:runs v)) drop-act (fn [v :- World, y :- Nat] (Eq.refl (:runs v))) _ w)))

;; cleanup-runs-exist on the generic tree (spindel.v2.pres.tree): its table. Its own proofs follow; the cleanup-set
;; lemma is the hand lemma above.
(swap! (:renames GC) assoc 'well-formed-cleanup-set 'cleanup-runs-exist-cleanup-set)
(tree/part! GC
  :over '{well-formed-retire-after     cleanup-runs-exist-retire-after
          well-formed-cancel-run-local cleanup-runs-exist-cancel-run-local
          well-formed-t13-retire-with-subtree      cleanup-runs-exist-t13-retire-with-subtree
          well-formed-job-apply        cleanup-runs-exist-job-apply}
  ;; ---- facts from the path: the run whose cleanups are set or cancelled is a row
  :ctx '{well-formed-cleanup-set      [(= (tbl-has run-id rid (:runs w)) true)]
         well-formed-cancel-run-local [(= (tbl-has run-id (:id r) (:runs w)) true)]})
(a/theorem cleanup-runs-exist-retire-after [w :- World, rid :- Nat]
  (=> (= (cleanup-runs-exist w) true) (= (cleanup-runs-exist (retire-after w rid)) true))
  (intro h)
  (cases hr (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [retire-after hr]) (exact h)
  (cases ht (retirable r))
  (simp only [retire-after hr ht]) (exact (cleanup-runs-exist-cleanup-set w rid _ (tbl-find-has RunRow run-id rid r (:runs w) hr) h))
  (simp only [retire-after hr ht]) (exact h))
(tree/restate! GC '[well-formed-cancel-debtor well-formed-cancel-res well-formed-cancel-acts])
(a/theorem cleanup-runs-exist-cancel-run-local [w :- World, r :- RunRow, rep :- Bool]
  (=> (= (tbl-has run-id (:id r) (:runs w)) true) (= (cleanup-runs-exist w) true) (= (cleanup-runs-exist (cancel-run-local w r rep)) true))
  (intros hr h)
  (have hr2 (= (tbl-has run-id (:id r) (:runs (cancel-res (cancel-acts (run-upd w (:id r) run-cancel-row) (:id r)) r))) true))
  (rw [runs-cancel-res runs-cancel-acts])
  (simp only [run-upd set-runs (tbl-has-upd RunRow run-id (:id r) (:id r) run-cancel-row run-cancel-row-id (:runs w)) hr])
  (simp only [cancel-run-local])
  (exact (cleanup-runs-exist-cancel-debtor rep _ r (cleanup-runs-exist-cleanup-set _ (:id r) (cleanup-rows-of w r) hr2
           (cleanup-runs-exist-cancel-res _ r (cleanup-runs-exist-cancel-acts _ (:id r) (cleanup-runs-exist-run-upd w (:id r) run-cancel-row run-cancel-row-id h)))))))
(tree/restate! GC '[well-formed-remove-if-empty well-formed-close-local well-formed-clear-comp-run])
(a/theorem cleanup-runs-exist-t13-retire-with-subtree [w :- World, r :- RunRow, sub :- (List Nat)]
  (=> (= (cleanup-runs-exist w) true) (= (cleanup-runs-exist (t13-retire-with-subtree w r sub)) true))
  (intro h) (simp only [t13-retire-with-subtree])
  (exact (cleanup-runs-exist-remove-if-empty _ sub (cleanup-runs-exist-del-both _ (:id r) (cleanup-runs-exist-close-local _ sub (cleanup-runs-exist-clear-comp-run w r h))))))
(tree/restate! GC '[well-formed-retire-run well-formed-close-scope-local])
(a/theorem cleanup-runs-exist-job-apply [w :- World, j :- Job]
  (=> (= (cleanup-runs-exist w) true) (= (cleanup-runs-exist (job-apply w j)) true))
  (intro h)
  (cases j)
  (rename_i rid rep) (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [job-apply hf]) (exact h)
  (cases ha (run-alive r)) (simp only [job-apply hf ha]) (exact h)
  (simp only [job-apply hf ha]) (exact (cleanup-runs-exist-cancel-run-local w r rep (run-has-of-find w rid r hf) h))
  (rename_i rid) (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [job-apply hf]) (exact h)
  (cases ha (retirable r)) (simp only [job-apply hf ha]) (exact h)
  (simp only [job-apply hf ha]) (exact (cleanup-runs-exist-retire-run w r h))
  (rename_i s) (cases hs (scope-has w s)) (simp only [job-apply hs]) (exact h)
  (simp only [job-apply hs]) (exact (cleanup-runs-exist-close-scope-local w s h)))

(tree/restate! GC '[well-formed-raw well-formed-normalize])

(a/theorem cleanup-runs-exist-rule-r-round [w :- World]
  (=> (= (cleanup-runs-exist w) true) (= (filter-safe (normalize w)) true) (= (cleanup-runs-exist (rule-r-round w)) true))
  (intros h hf)
  (simp only [rule-r-round])
  (rw [rule-r-filter-eq])
  (exact (cleanup-runs-exist-filter-keep (normalize w) (cleanup-runs-exist-normalize w h) hf)))

(a/theorem cleanup-runs-exist-rule-r-loop [fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (cleanup-runs-exist w0) true) (= (rounds-safe-loop fuel w0) true) (= (cleanup-runs-exist (rule-r-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 h hs) (simp only [rounds-safe-loop] at hs) (simp only [rule-r-loop]) (exact (cleanup-runs-exist-rule-r-round w0 h hs)))
  (case [cons x f ih]
    (intros w0 h hs)
    (simp only [rounds-safe-loop Bool.and_eq_true] at hs)
    (have h1 := (cleanup-runs-exist-rule-r-round w0 h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false] (simp only [ho] at hs) (simp only [rule-r-loop ho]) (exact (ih (rule-r-round w0) h1 (And.right hs))))
    (case [true] (simp only [rule-r-loop ho]) (exact h1))))

(a/theorem cleanup-runs-exist-rule-r [w :- World]
  (=> (= (cleanup-runs-exist w) true) (= (rule-r-safe w) true) (= (cleanup-runs-exist (rule-r w)) true))
  (intros h hs) (simp only [rule-r-safe] at hs) (simp only [rule-r]) (exact (cleanup-runs-exist-rule-r-loop (rule-r-fuel w) w h hs)))

(a/theorem step-cleanup-runs-exist [w :- World, it :- Item]
  (=> (= (cleanup-runs-exist w) true) (= (rule-r-safe (:world (raw w it))) true) (= (cleanup-runs-exist (:world (world-step w it))) true))
  (intros h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true] (have e2 := (step-accepted w it ha)) (rw [e2]) (exact (cleanup-runs-exist-rule-r (:world (raw w it)) (cleanup-runs-exist-raw w it h) hs))))

;; Theorem: every cleanup entry's run is a run row, through every step from a chain-start world
(a/theorem step-cleanup-runs-exist-rest [w :- World, it :- Item]
  (=> (= (chain-start w) true) (= (cleanup-runs-exist-rest w) true) (= (cleanup-runs-exist-rest (:world (world-step w it))) true))
  (intros h hk)
  (exact (cleanup-runs-exist-rest-of _ (step-cleanup-runs-exist w it (cleanup-runs-exist-intro w (acts-parked-well-formed w (And.left (chain-start-parts w h))) hk) (step-rule-r-safe w it h)))))
(a/theorem cleanup-runs-exist-empty [] (= (cleanup-runs-exist-rest empty-world) true) (rfl))

;; ===========================================================================
;; Part B. The closure lemma: a quiet world holds only scopes
;; ===========================================================================

;; I3 as a state fact: the filter keeps every id (after every accepted step, `step-i3-total`)
(a/defn i3 [w :- World] Bool (tbl-all (keep-fn w) (all-ids w)))
;; C1c (question 10): and every open non-root scope lies in a run's run-scope subtree (spindel.v2.completion.open-scopes `open-scopes-have-runs-rest`)
(a/defn quiet-world-inv [w :- World] Bool (Bool.and (chain-to-marks-waiting w) (Bool.and (host-roots-revoked-rest w) (Bool.and (cleanup-runs-exist-rest w) (Bool.and (i3 w) (open-scopes-have-runs-rest w))))))

;; chain-to-marks-waiting's parts the closure reads
(a/theorem chain-to-marks-waiting-implies-chain-to-i1-scopes [w :- World] (=> (= (chain-to-marks-waiting w) true) (= (chain-to-i1-scopes w) true))
  (intro h)
  (exact (And.left (chain-to-i5-dep-final-parts _ (And.left (chain-to-i1-detached-closed-parts _ (And.left (chain-to-i1-runs-parts _ (And.left (chain-to-i8-closed-parts _
           (And.left (chain-to-comp-facts-parts _ (And.left (chain-to-i14-ordered-parts _ (And.left (chain-to-marks-waiting-parts w h))))))))))))))))
(a/theorem chain-to-marks-waiting-implies-chain-to-i11a [w :- World] (=> (= (chain-to-marks-waiting w) true) (= (chain-to-i11a w) true))
  (intro h) (exact (And.left (chain-to-i1-scopes-parts _ (chain-to-marks-waiting-implies-chain-to-i1-scopes w h)))))
(a/theorem chain-to-marks-waiting-implies-chain-start [w :- World] (=> (= (chain-to-marks-waiting w) true) (= (chain-start w) true))
  (intro h) (exact (And.left (chain-to-i10-current-parts _ (And.left (chain-to-i11a-parts _ (chain-to-marks-waiting-implies-chain-to-i11a w h)))))))
(a/theorem chain-to-marks-waiting-well-formed [w :- World] (=> (= (chain-to-marks-waiting w) true) (= (well-formed w) true))
  (intro h) (exact (acts-parked-well-formed w (And.left (chain-start-parts w (chain-to-marks-waiting-implies-chain-start w h))))))
(a/theorem chain-to-marks-waiting-root-scope-reserved [w :- World] (=> (= (chain-to-marks-waiting w) true) (= (root-scope-reserved-rest w) true))
  (intro h) (exact (root-scope-reserved-rest-of w (And.left (And.right (chain-to-i11a-parts _ (chain-to-marks-waiting-implies-chain-to-i11a w h)))))))
(a/theorem chain-to-marks-waiting-i1 [w :- World] (=> (= (chain-to-marks-waiting w) true) (= (lit-i1-scope w) true))
  (intro h) (exact (i1-scopes-rest-of w (And.right (chain-to-i1-scopes-parts _ (chain-to-marks-waiting-implies-chain-to-i1-scopes w h))))))

(a/theorem quiet-world-inv-parts [w :- World]
  (=> (= (quiet-world-inv w) true) (And (= (chain-to-marks-waiting w) true) (And (= (host-roots-revoked-rest w) true) (And (= (cleanup-runs-exist-rest w) true) (= (i3 w) true)))))
  (intro h) (simp only [quiet-world-inv Bool.and_eq_true] at h)
  (exact (And.intro (And.left h) (And.intro (And.left (And.right h)) (And.intro (And.left (And.right (And.right h)))
           (And.left (And.right (And.right (And.right h)))))))))
(a/theorem quiet-world-inv-open-scopes-have-runs [w :- World] (=> (= (quiet-world-inv w) true) (= (open-scopes-have-runs-rest w) true))
  (intro h) (simp only [quiet-world-inv Bool.and_eq_true] at h) (exact (And.right (And.right (And.right (And.right h))))))
(a/theorem quiet-world-inv-intro [w :- World]
  (=> (= (chain-to-marks-waiting w) true) (= (host-roots-revoked-rest w) true) (= (cleanup-runs-exist-rest w) true) (= (i3 w) true) (= (open-scopes-have-runs-rest w) true) (= (quiet-world-inv w) true))
  (intros h1 h2 h3 h4 h5) (simp only [quiet-world-inv h1 h2 h3 h4 h5 Bool.and_self]))
(a/theorem chain-to-marks-waiting-i1-runs [w :- World] (=> (= (chain-to-marks-waiting w) true) (= (i1-runs w) true))
  (intro h)
  (exact (And.right (chain-to-i1-runs-parts _ (And.left (chain-to-i8-closed-parts _ (And.left (chain-to-comp-facts-parts _ (And.left (chain-to-i14-ordered-parts _ (And.left (chain-to-marks-waiting-parts w h))))))))))))

(a/theorem step-i3-inv [w :- World, it :- Item] (=> (= (i3 w) true) (= (i3 (:world (world-step w it))) true))
  (intro h)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true] (simp only [i3]) (exact (step-i3-total w it ha))))

;; Theorem: quiet-world-inv holds of the empty world and through every step
(a/theorem step-quiet-world-inv [w :- World, it :- Item] (=> (= (quiet-world-inv w) true) (= (quiet-world-inv (:world (world-step w it))) true))
  (intro h)
  (have q := (quiet-world-inv-parts w h))
  (have b := (chain-to-marks-waiting-implies-chain-start w (And.left q)))
  (have g := (step-open-scopes-have-runs w it (And.left (chain-start-parts w b)) (chain-to-marks-waiting-i1-runs w (And.left q))
                (open-scopes-have-runs-intro w (chain-to-marks-waiting-well-formed w (And.left q)) (quiet-world-inv-open-scopes-have-runs w h)) (step-rule-r-safe w it b)))
  (exact (quiet-world-inv-intro _ (step-chain-to-marks-waiting w it (And.left q)) (step-k w it b (And.left (And.right q)))
           (step-cleanup-runs-exist-rest w it b (And.left (And.right (And.right q)))) (step-i3-inv w it (And.right (And.right (And.right q))))
           (open-scopes-have-runs-rest-of _ g))))
(a/theorem quiet-world-inv-empty [] (= (quiet-world-inv empty-world) true) (rfl))

;; ---- uniqueness: a scope id is no other row's id
(a/defn other-has [w :- World, x :- Nat] Bool
  (Bool.or (tbl-has comp-id x (:comps w)) (Bool.or (tbl-has task-id x (:tasks w)) (Bool.or (tbl-has run-id x (:runs w))
  (Bool.or (tbl-has source-id x (:sources w)) (Bool.or (tbl-has edge-id x (:edges w)) (Bool.or (tbl-has act-id x (:acts w))
  (Bool.or (tbl-has resource-id x (:res w)) (tbl-has pub-id x (:pubs w))))))))))
(a/theorem scope-only [w :- World, x :- Nat]
  (=> (= (well-formed w) true) (= (scope-has w x) true) (= (other-has w x) false))
  (intros hs hh)
  (have u := (ids-unique-of w hs))
  (simp only [all-ids] at u)
  (have hm (= (nat-mem x (tbl-ids scope-id (:scopes w))) true)) (rw [nat-mem-ids]) (exact hh)
  (have d := (nodup-app-disj x _ _ u hm))
  (simp only [nat-mem-app Bool.or_eq_false_iff nat-mem-ids] at d)
  (simp only [other-has (And.left d) (And.left (And.right d)) (And.left (And.right (And.right d)))
              (And.left (And.right (And.right (And.right d)))) (And.left (And.right (And.right (And.right (And.right d)))))
              (And.left (And.right (And.right (And.right (And.right (And.right d))))))
              (And.left (And.right (And.right (And.right (And.right (And.right (And.right d)))))))
              (And.left (And.right (And.right (And.right (And.right (And.right (And.right (And.right d))))))))
              Bool.or_self]))

;; ---- the quiet hypotheses: released, no run, no fork marker (C1c stage B), quiet-world-inv
(a/defn qh [w :- World] Bool
  (Bool.and (quiet-world-inv w) (Bool.and (:released w) (Bool.and (nats-empty (tbl-ids run-id (:runs w))) (forks-nil (:forks w))))))
(a/theorem qh-parts [w :- World]
  (=> (= (qh w) true) (And (= (quiet-world-inv w) true) (And (= (:released w) true) (= (:runs w) (List.nil RunRow)))))
  (intro h) (simp only [qh Bool.and_eq_true] at h)
  (have e (= (:runs w) (List.nil RunRow)))
  (have r := (And.left (And.right (And.right h))))
  (cases hr (:runs w)) (case [nil] (rfl)) (case [cons a t] (rw [hr] at r) (simp [tbl-ids nats-empty] at r))
  (exact (And.intro (And.left h) (And.intro (And.left (And.right h)) e))))
(a/theorem qh-forks [w :- World] (=> (= (qh w) true) (= (:forks w) (List.nil ForkRow)))
  (intro h) (simp only [qh Bool.and_eq_true] at h)
  (have f := (And.right (And.right (And.right h))))
  (cases hf (:forks w)) (case [nil] (rfl)) (case [cons a t] (rw [hf] at f) (simp [forks-nil] at f)))
(a/theorem qh-quiet [w :- World] (=> (= (qh w) true) (= (world-quiet w) true))
  (intro h) (have q := (qh-parts w h))
  (simp only [world-quiet world-runs (And.left (And.right q)) (And.right (And.right q)) (qh-forks w h) forks-nil]))
(a/theorem qh-of [w :- World] (=> (= (quiet-world-inv w) true) (= (world-quiet w) true) (= (qh w) true))
  (intros h hq)
  (simp only [world-quiet world-runs Bool.and_eq_true] at hq)
  (have e (= (nats-empty (tbl-ids run-id (:runs w))) true))
  (have z := (Nat.eq_of_beq_eq_true (And.left (And.right hq))))
  (cases hr (:runs w)) (case [nil] (simp only [tbl-ids nats-empty])) (case [cons a t] (rw [hr] at z) (simp at z))
  (simp only [qh h (And.left hq) e (And.right (And.right hq)) Bool.and_self]))

(a/theorem k-parts [w :- World]
  (=> (= (host-roots-revoked-rest w) true) (= (:released w) true)
      (And (= (:pending-act w) 0) (And (= (:pubs w) (List.nil PubRow))
       (And (= (:pins w) (List.nil Nat)) (And (= (tbl-all not-host (:edges w)) true) (= (hz-all w) true))))))
  (intros h hr)
  (have k0 := (host-roots-revoked-rest-k0 w h)) (have g := (host-roots-revoked-rest-gh w h))
  (simp only [host-roots-revoked-pending-rest hr Bool.not_true Bool.false_or Bool.and_eq_true] at k0)
  (simp only [host-roots-revoked-handles-rest hr Bool.not_true Bool.false_or] at g)
  (have ep (= (:pins w) (List.nil Nat)))
  (have pe := (And.left (And.right (And.right k0))))
  (cases hp (:pins w)) (case [nil] (rfl)) (case [cons a t] (rw [hp] at pe) (simp [nats-empty] at pe))
  (exact (And.intro (Nat.eq_of_beq_eq_true (And.left k0)) (And.intro (pa-all _ (And.left (And.right k0)))
           (And.intro ep (And.intro (And.right (And.right (And.right k0))) g))))))

(a/theorem cleanup-nil [w :- World] (=> (= (cleanup-runs-exist-rest w) true) (= (:runs w) (List.nil RunRow)) (= (:cleanup w) (List.nil CleanupRow)))
  (intros h hn)
  (simp only [cleanup-runs-exist-rest hn] at h)
  (cases hc (:cleanup w)) (case [nil] (rfl))
  (case [cons c t] (rw [hc] at h) (simp [tbl-all cl-run tbl-has] at h)))

;; ---- roots: scopes only
(a/theorem scan-scope [w :- World, p :- (=> ScopeRow Bool), y :- Nat]
  (=> (= (reach-mem y (tbl-scan scope-id p (:scopes w))) true) (= (scope-has w y) true))
  (intro h) (have m := (scan-ids-mem ScopeRow scope-id p y (:scopes w) h)) (rw [nat-mem-ids] at m) (exact m))
(a/theorem roots-scope [w :- World, y :- Nat]
  (=> (= (qh w) true) (= (reach-mem y (roots w)) true) (= (scope-has w y) true))
  (intros h hm)
  (have q := (qh-parts w h))
  (have qi := (quiet-world-inv-parts w (And.left q)))
  (have k := (k-parts w (And.left (And.right qi)) (And.left (And.right q))))
  (have ne (= (reach-mem y (tbl-scan edge-id is-observe (:edges w))) false))
  (cases hb (reach-mem y (tbl-scan edge-id is-observe (:edges w)))) (rfl)
  (apply (False.elim (scan-prop EdgeRow edge-id is-observe (fn [z :- Nat] False) (:edges w) _ y hb)))
  (intros e me pe)
  (have t := (tbl-all-mem EdgeRow not-host e (:edges w) (And.left (And.right (And.right (And.right k)))) me))
  (simp only [is-observe] at pe) (simp [not-host pe] at t)
  (simp only [roots reach-mem-append (And.left (And.right (And.right k))) (And.left k) (And.left (And.right k)) ne
              nz Nat.beq_refl tbl-scan reach-mem Bool.or_false Bool.false_or] at hm)
  (cases hm1 (reach-mem y (tbl-scan scope-id is-root-scope (:scopes w))))
  (case [true] (exact (scan-scope w is-root-scope y hm1)))
  (case [false] (simp only [hm1 Bool.false_or] at hm) (exact (scan-scope w is-open-explicit y hm))))

;; ---- a scope's successors: its parent (a scope), no running task (no run), no fork marker
(a/theorem gather-off [A :- Type, idf :- (=> A Nat), x :- Nat, f :- (=> A (List Nat)), xs :- (List A), y :- Nat]
  (=> (= (tbl-has idf x xs) false) (= (reach-mem y (tbl-gather (id-is idf x) f xs)) false))
  (intro hn)
  (cases hc (reach-mem y (tbl-gather (id-is idf x) f xs))) (rfl)
  (have z := (gather-has A idf x f xs y hc)) (rw [z] at hn) (cases hn))
(a/theorem scope-parent-scope [w :- World, s :- ScopeRow]
  (=> (= (qh w) true) (List.Mem s (:scopes w)) (= (Nat.beq (:parent s) 0) false) (= (scope-has w (:parent s)) true))
  (intros h m hp)
  (have qi := (quiet-world-inv-parts w (And.left (qh-parts w h))))
  (have i1 := (tbl-all-mem ScopeRow _ s _ (chain-to-marks-waiting-i1 w (And.left qi)) m))
  (simp only [lit-scope-parent hp Bool.false_or] at i1)
  (cases hk (Nat.beq (:kind s) scope-root))
  (case [false] (simp only [hk Bool.false_or] at i1) (exact i1))
  (case [true]
    (have g := (chain-to-marks-waiting-root-scope-reserved w (And.left qi)))
    (simp only [root-scope-reserved-rest root-scope-reserved-keys-ok Bool.and_eq_true] at g)
    (have ro := (And.left g)) (rw [all-root-scope-reserved-scope-keys] at ro)
    (have r := (tbl-all-mem ScopeRow _ s _ ro m))
    (have hk2 (= (Nat.beq (:kind (root-scope-reserved-scope-key s)) scope-root) true)) (exact hk)
    (simp only [root-ok hk2 Bool.true_or Bool.or_true Bool.not_true Bool.false_or Bool.and_eq_true] at r)
    (have e (= (Nat.beq (:parent (root-scope-reserved-scope-key s)) 0) true)) (exact (And.right (And.right r)))
    (have e2 (= (Nat.beq (:parent s) 0) true)) (exact e)
    (rw [e2] at hp) (cases hp)))
(a/theorem scope-succ-scope [w :- World, s :- ScopeRow, z :- Nat]
  (=> (= (qh w) true) (List.Mem s (:scopes w)) (= (reach-mem z (scope-contrib w s)) true) (= (scope-has w z) true))
  (intros h m hz)
  (have q := (qh-parts w h))
  (have qi := (quiet-world-inv-parts w (And.left q)))
  (have ef := (qh-forks w h))
  (have t0 (= (reach-mem z (tbl-scan task-id (owned-running-task w (:id s)) (:tasks w))) false))
  (cases hb (reach-mem z (tbl-scan task-id (owned-running-task w (:id s)) (:tasks w)))) (rfl)
  (apply (False.elim (scan-prop TaskRow task-id (owned-running-task w (:id s)) (fn [z :- Nat] False) (:tasks w) _ z hb)))
  (intros t mt pt)
  (simp only [owned-running-task task-running run-find (And.right (And.right q)) tbl-find opt-test Bool.and_false] at pt)
  (cases pt)
  (have f0 (= (reach-mem z (tbl-scan fork-id (owned-fork (:id s)) (:forks w))) false))
  (rw [ef]) (simp only [tbl-scan reach-mem])
  (simp only [scope-contrib reach-mem-append t0 f0 Bool.or_false] at hz)
  (cases hp (Nat.beq (:parent s) 0))
  (simp only [nz hp reach-mem] at hz)
  (cases hb (Nat.beq z (:parent s)))
  (simp only [hb] at hz) (simp at hz)
  (have e (= z (:parent s))) (exact (Nat.eq_of_beq_eq_true hb))
  (rw [e]) (exact (scope-parent-scope w s h m hp))
  (simp [nz hp reach-mem] at hz))
(a/theorem succ-scope [w :- World, x :- Nat, y :- Nat]
  (=> (= (qh w) true) (= (scope-has w x) true) (= (reach-mem y (retain-succ w x)) true) (= (scope-has w y) true))
  (intros h hx hm)
  (have qi := (quiet-world-inv-parts w (And.left (qh-parts w h))))
  (have o := (scope-only w x (chain-to-marks-waiting-well-formed w (And.left qi)) hx))
  (simp only [other-has Bool.or_eq_false_iff] at o)
  (simp only [retain-succ reach-mem-append
              (gather-off CompRow comp-id x (comp-contrib w) (:comps w) y (And.left o))
              (gather-off TaskRow task-id x task-contrib (:tasks w) y (And.left (And.right o)))
              (gather-off RunRow run-id x (run-contrib w) (:runs w) y (And.left (And.right (And.right o))))
              (gather-off EdgeRow edge-id x edge-contrib (:edges w) y (And.left (And.right (And.right (And.right (And.right o))))))
              (gather-off ActRow act-id x act-contrib (:acts w) y (And.left (And.right (And.right (And.right (And.right (And.right o)))))))
              (gather-off PubRow pub-id x pub-contrib (:pubs w) y (And.right (And.right (And.right (And.right (And.right (And.right (And.right o))))))))
              Bool.or_false] at hm)
  (exact (gather-prop ScopeRow (id-is scope-id x) (scope-contrib w) (fn [z :- Nat] (= (scope-has w z) true)) (:scopes w)
           (fn [s :- ScopeRow, z :- Nat, m :- (List.Mem s (:scopes w)), p :- (= (id-is scope-id x s) true), hz :- (= (reach-mem z (scope-contrib w s)) true)]
             (scope-succ-scope w s z h m hz))
           y hm)))
(a/theorem reach-scope [w :- World, y :- Nat]
  (=> (= (qh w) true) (Reach (retain-succ w) (roots w) y) (= (scope-has w y) true))
  (intros h hr)
  (induction hr)
  (case [root r hm] (exact (roots-scope w r h (Iff.mpr (reach-mem-iff r (roots w)) hm))))
  (case [step p q hp hq ihp] (exact (succ-scope w p q h ihp (Iff.mpr (reach-mem-iff q (retain-succ w p)) hq)))))

;; ---- keep: live (scopes), no cleanup entry, nothing admitted (every handle count is 0), no storage
(a/theorem any-none [A :- Type, p :- (=> A Bool), q :- (=> A Bool), xs :- (List A),
                     hpq :- (forall [a :- A] (=> (= (p a) true) (= (q a) false)))]
  (=> (= (tbl-all p xs) true) (= (tbl-any q xs) false))
  (induction xs)
  (case [nil] (intro h) (simp only [tbl-any]))
  (case [cons a t ih]
    (intro h) (simp only [tbl-all Bool.and_eq_true] at h)
    (simp only [tbl-any (hpq a (And.left h)) (ih (And.right h)) Bool.or_self])))
(a/theorem adm-comp-h0 [y :- Nat, c :- CompRow] (=> (= (h0-c c) true) (= (adm-comp y c) false))
  (intro z) (have e := (beq0-eq _ z)) (simp [adm-comp e]))
(a/theorem adm-task-h0 [y :- Nat, t :- TaskRow] (=> (= (h0-t t) true) (= (adm-task y t) false))
  (intro z) (have e := (beq0-eq _ z)) (simp [adm-task e]))
(a/theorem adm-source-h0 [y :- Nat, s :- SourceRow] (=> (= (h0-s s) true) (= (adm-source y s) false))
  (intro z) (have e := (beq0-eq _ z)) (simp [adm-source e]))
(a/theorem keep-scope [w :- World, y :- Nat]
  (=> (= (qh w) true) (= (keep-fn w y) true) (= (scope-has w y) true))
  (intros h hk)
  (have q := (qh-parts w h))
  (have qi := (quiet-world-inv-parts w (And.left q)))
  (have k := (k-parts w (And.left (And.right qi)) (And.left (And.right q))))
  (have hz := (And.right (And.right (And.right (And.right k)))))
  (simp only [hz-all Bool.and_eq_true] at hz)
  (have cn := (cleanup-nil w (And.left (And.right (And.right qi))) (And.right (And.right q))))
  (have a1 := (any-none CompRow h0-c (adm-comp y) (:comps w) (adm-comp-h0 y) (And.left hz)))
  (have a2 := (any-none TaskRow h0-t (adm-task y) (:tasks w) (adm-task-h0 y) (And.left (And.right hz))))
  (have a3 := (any-none SourceRow h0-s (adm-source y) (:sources w) (adm-source-h0 y) (And.right (And.right hz))))
  (have rn := (And.right (And.right q)))
  (have pn := (And.left (And.right k)))
  (simp only [keep-fn keep-with Bool.or_eq_true] at hk)
  (cases hk)
  (case [inl a] (exact (reach-scope w y h (Iff.mp (in-live-iff w y (live-converged-all w)) a))))
  (case [inr b]
    (have ef := (qh-forks w h))
    (simp [cleanup-rows cn cleanup-rows-in admitted a1 a2 a3 pn tbl-any storage storage-with storage-gather storage-seeds
           ef fork-keep rn tbl-gather anc-close anc-all reach-mem] at b)))

;; Theorem (closure): a quiet world with quiet-world-inv holds only scopes: no computation (tombstones
;; included), task, run, source, edge, activation, resource, cleanup entry, publication or fork marker
(a/defn only-scopes [w :- World] Prop
  (And (= (:comps w) (List.nil CompRow)) (And (= (:tasks w) (List.nil TaskRow)) (And (= (:runs w) (List.nil RunRow))
  (And (= (:sources w) (List.nil SourceRow)) (And (= (:edges w) (List.nil EdgeRow)) (And (= (:acts w) (List.nil ActRow))
  (And (= (:res w) (List.nil ResRow)) (And (= (:cleanup w) (List.nil CleanupRow))
  (And (= (:pubs w) (List.nil PubRow)) (= (:forks w) (List.nil ForkRow))))))))))))

(a/theorem tbl-empty [A :- Type, idf :- (=> A Nat), xs :- (List A)]
  (=> (forall [x :- Nat] (=> (= (tbl-has idf x xs) true) False)) (= xs (List.nil A)))
  (intro h)
  (cases xs)
  (case [nil] (rfl))
  (case [cons a t]
    (have e (= (tbl-has idf (idf a) (List.cons A a t)) true)) (simp [tbl-has])
    (exact (False.elim (h (idf a) e)))))
;; an id of a row in the world is kept (I3), so it is a scope's
(a/theorem kept-scope [w :- World, y :- Nat]
  (=> (= (qh w) true) (= (nat-mem y (all-ids w)) true) (= (scope-has w y) true))
  (intros h m)
  (have qi := (quiet-world-inv-parts w (And.left (qh-parts w h))))
  (exact (keep-scope w y h (all-nat-mem (keep-fn w) y (all-ids w) (And.right (And.right (And.right qi))) m))))

(a/theorem quiet-rows [w :- World] (=> (= (qh w) true) (only-scopes w))
  (intro h)
  (have q := (qh-parts w h))
  (have qi := (quiet-world-inv-parts w (And.left q)))
  (have k := (k-parts w (And.left (And.right qi)) (And.left (And.right q))))
  (have hs := (chain-to-marks-waiting-well-formed w (And.left qi)))
  (have o (forall [x :- Nat] (=> (= (scope-has w x) true) (= (other-has w x) false))))
  (intros x hx) (exact (scope-only w x hs hx))
  (have mem (forall [x :- Nat] (=> (= (other-has w x) true) (= (nat-mem x (all-ids w)) true))))
  (intros x hx) (simp only [other-has Bool.or_eq_true] at hx)
  (simp only [all-ids nat-mem-app nat-mem-ids Bool.or_eq_true])
  (rcases hx (or a (or b (or c (or d (or e (or f (or g p))))))))
  (exact (Or.inr (Or.inl a))) (exact (Or.inr (Or.inr (Or.inl b)))) (exact (Or.inr (Or.inr (Or.inr (Or.inl c)))))
  (exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl d)))))) (exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e)))))))
  (exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl f))))))))
  (exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl g)))))))))
  (exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl p))))))))))
  (have hk (forall [x :- Nat] (=> (= (other-has w x) true) (= (scope-has w x) true))))
  (intros x hx) (exact (kept-scope w x h (mem x hx)))
  (have nope (forall [x :- Nat] (=> (= (other-has w x) true) False)))
  (intros x hx) (have z := (o x (hk x hx))) (rw [hx] at z) (cases z)
  (have ef := (qh-forks w h))
  (have c1 (= (:comps w) (List.nil CompRow)))
  (apply (tbl-empty CompRow comp-id (:comps w))) (intros x hx) (apply (nope x)) (simp only [other-has hx Bool.true_or])
  (have c2 (= (:tasks w) (List.nil TaskRow)))
  (apply (tbl-empty TaskRow task-id (:tasks w))) (intros x hx) (apply (nope x)) (simp only [other-has hx Bool.true_or Bool.or_true])
  (have c4 (= (:sources w) (List.nil SourceRow)))
  (apply (tbl-empty SourceRow source-id (:sources w))) (intros x hx) (apply (nope x)) (simp only [other-has hx Bool.true_or Bool.or_true])
  (have c5 (= (:edges w) (List.nil EdgeRow)))
  (apply (tbl-empty EdgeRow edge-id (:edges w))) (intros x hx) (apply (nope x)) (simp only [other-has hx Bool.true_or Bool.or_true])
  (have c6 (= (:acts w) (List.nil ActRow)))
  (apply (tbl-empty ActRow act-id (:acts w))) (intros x hx) (apply (nope x)) (simp only [other-has hx Bool.true_or Bool.or_true])
  (have c7 (= (:res w) (List.nil ResRow)))
  (apply (tbl-empty ResRow resource-id (:res w))) (intros x hx) (apply (nope x)) (simp only [other-has hx Bool.true_or Bool.or_true])
  (have cn := (cleanup-nil w (And.left (And.right (And.right qi))) (And.right (And.right q))))
  (exact (And.intro c1 (And.intro c2 (And.intro (And.right (And.right q)) (And.intro c4 (And.intro c5 (And.intro c6
           (And.intro c7 (And.intro cn (And.intro (And.left (And.right k)) ef)))))))))))

;; root-ok: a root-kind scope is scope 2 with parent 0
(a/theorem root-id-2 [s :- ScopeRow] (=> (= (root-ok (root-scope-reserved-scope-key s)) true) (= (is-root-scope s) true) (= (:id s) root-scope-id))
  (intros r k)
  (have hk2 (= (Nat.beq (:kind (root-scope-reserved-scope-key s)) scope-root) true)) (exact k)
  (simp only [root-ok hk2 Bool.true_or Bool.not_true Bool.false_or Bool.and_eq_true] at r)
  (exact (Nat.eq_of_beq_eq_true (And.left r))))
(a/theorem oe-need-false [s :- ScopeRow] (=> (= (is-open-explicit s) true) (= (os-need s) false) False)
  (intros p n)
  (simp only [is-open-explicit Bool.and_eq_true] at p)
  (have e (= (:kind s) scope-explicit)) (exact (Nat.eq_of_beq_eq_true (And.left p)))
  (simp only [os-need e (And.right p)] at n) (cases n))
(a/theorem root-parent-0 [w :- World, s :- ScopeRow, y :- Nat]
  (=> (= (qh w) true) (List.Mem s (:scopes w)) (= (root-ok (root-scope-reserved-scope-key s)) true) (= (id-is scope-id root-scope-id s) true)
      (= (reach-mem y (scope-contrib w s)) true) False)
  (intros h m r p hy)
  (have q := (qh-parts w h))
  (have qi := (quiet-world-inv-parts w (And.left q)))
  (have i2 (= (Nat.beq (:id (root-scope-reserved-scope-key s)) 2) true)) (simp only [id-is scope-id] at p) (exact p)
  (simp only [root-ok i2 Bool.or_true Bool.not_true Bool.false_or Bool.true_and Bool.and_eq_true] at r)
  (have p0 (= (Nat.beq (:parent s) 0) true)) (exact (And.right r))
  (have ef := (qh-forks w h))
  (have t0 (= (reach-mem y (tbl-scan task-id (owned-running-task w (:id s)) (:tasks w))) false))
  (cases hb (reach-mem y (tbl-scan task-id (owned-running-task w (:id s)) (:tasks w)))) (rfl)
  (apply (False.elim (scan-prop TaskRow task-id (owned-running-task w (:id s)) (fn [z :- Nat] False) (:tasks w) _ y hb)))
  (intros t mt pt)
  (simp only [owned-running-task task-running run-find (And.right (And.right q)) tbl-find opt-test Bool.and_false] at pt)
  (cases pt)
  (have f0 (= (reach-mem y (tbl-scan fork-id (owned-fork (:id s)) (:forks w))) false))
  (simp only [ef tbl-scan reach-mem])
  (simp only [scope-contrib reach-mem-append t0 f0 Bool.or_false] at hy)
  (simp only [nz p0] at hy)
  (simp [reach-mem] at hy))

;; ---- C1c (questions 10, 14): a quiet world holds the root scope only
;; no open non-root scope: its witness would be a run (spindel.v2.completion.open-scopes)
(a/theorem quiet-no-open [w :- World, c :- ScopeRow]
  (=> (= (qh w) true) (List.Mem c (:scopes w)) (= (os-need c) false))
  (intros h m)
  (have q := (qh-parts w h))
  (cases hn (os-need c))
  (case [false] (rfl))
  (case [true]
    (have x := (open-scopes-have-runs-rest-mem w c (quiet-world-inv-open-scopes-have-runs w (And.left q)) m hn))
    (simp [hw (And.right (And.right q)) tbl-any] at x)))
;; the roots of a quiet world: the root scope (no open explicit scope)
(a/theorem roots-root [w :- World, y :- Nat]
  (=> (= (qh w) true) (= (reach-mem y (roots w)) true) (= y root-scope-id))
  (intros h hm)
  (have q := (qh-parts w h))
  (have qi := (quiet-world-inv-parts w (And.left q)))
  (have k := (k-parts w (And.left (And.right qi)) (And.left (And.right q))))
  (have ne (= (reach-mem y (tbl-scan edge-id is-observe (:edges w))) false))
  (cases hb (reach-mem y (tbl-scan edge-id is-observe (:edges w)))) (rfl)
  (apply (False.elim (scan-prop EdgeRow edge-id is-observe (fn [z :- Nat] False) (:edges w) _ y hb)))
  (intros e me pe)
  (have t := (tbl-all-mem EdgeRow not-host e (:edges w) (And.left (And.right (And.right (And.right k)))) me))
  (simp only [is-observe] at pe) (simp [not-host pe] at t)
  (simp only [roots reach-mem-append (And.left (And.right (And.right k))) (And.left k) (And.left (And.right k)) ne
              nz Nat.beq_refl tbl-scan reach-mem Bool.or_false Bool.false_or] at hm)
  (have g := (chain-to-marks-waiting-root-scope-reserved w (And.left qi)))
  (simp only [root-scope-reserved-rest root-scope-reserved-keys-ok Bool.and_eq_true] at g)
  (have ro := (And.left g)) (rw [all-root-scope-reserved-scope-keys] at ro)
  (cases hm1 (reach-mem y (tbl-scan scope-id is-root-scope (:scopes w))))
  (case [true]
    (exact (scan-prop ScopeRow scope-id is-root-scope (fn [z :- Nat] (= z root-scope-id)) (:scopes w)
             (fn [s :- ScopeRow, ms :- (List.Mem s (:scopes w)), ps :- (= (is-root-scope s) true)]
               (root-id-2 s (tbl-all-mem ScopeRow _ s _ ro ms) ps))
             y hm1)))
  (case [false]
    (simp only [hm1 Bool.false_or] at hm)
    (exact (False.elim (scan-prop ScopeRow scope-id is-open-explicit (fn [z :- Nat] False) (:scopes w)
             (fn [s :- ScopeRow, ms :- (List.Mem s (:scopes w)), ps :- (= (is-open-explicit s) true)]
               (oe-need-false s ps (quiet-no-open w s h ms)))
             y hm)))))
;; the root scope retains nothing in a quiet world: its parent is 0, no running task, no fork marker
(a/theorem root-succ-none [w :- World, z :- Nat]
  (=> (= (qh w) true) (= (scope-has w root-scope-id) true) (= (reach-mem z (retain-succ w root-scope-id)) true) False)
  (intros h hx hm)
  (have qi := (quiet-world-inv-parts w (And.left (qh-parts w h))))
  (have o := (scope-only w root-scope-id (chain-to-marks-waiting-well-formed w (And.left qi)) hx))
  (simp only [other-has Bool.or_eq_false_iff] at o)
  (simp only [retain-succ reach-mem-append
              (gather-off CompRow comp-id root-scope-id (comp-contrib w) (:comps w) z (And.left o))
              (gather-off TaskRow task-id root-scope-id task-contrib (:tasks w) z (And.left (And.right o)))
              (gather-off RunRow run-id root-scope-id (run-contrib w) (:runs w) z (And.left (And.right (And.right o))))
              (gather-off EdgeRow edge-id root-scope-id edge-contrib (:edges w) z (And.left (And.right (And.right (And.right (And.right o))))))
              (gather-off ActRow act-id root-scope-id act-contrib (:acts w) z (And.left (And.right (And.right (And.right (And.right (And.right o)))))))
              (gather-off PubRow pub-id root-scope-id pub-contrib (:pubs w) z (And.right (And.right (And.right (And.right (And.right (And.right (And.right o))))))))
              Bool.or_false] at hm)
  (have g := (chain-to-marks-waiting-root-scope-reserved w (And.left qi)))
  (simp only [root-scope-reserved-rest root-scope-reserved-keys-ok Bool.and_eq_true] at g)
  (have ro := (And.left g)) (rw [all-root-scope-reserved-scope-keys] at ro)
  (exact (gather-prop ScopeRow (id-is scope-id root-scope-id) (scope-contrib w) (fn [y :- Nat] False) (:scopes w)
           (fn [s :- ScopeRow, y :- Nat, m :- (List.Mem s (:scopes w)), p :- (= (id-is scope-id root-scope-id s) true),
                hy :- (= (reach-mem y (scope-contrib w s)) true)]
             (root-parent-0 w s y h m (tbl-all-mem ScopeRow _ s _ ro m) p hy))
           z hm)))
;; a kept id of a quiet world is live (no cleanup entry, nothing admitted, no storage)
(a/theorem keep-live [w :- World, y :- Nat]
  (=> (= (qh w) true) (= (keep-fn w y) true) (Reach (retain-succ w) (roots w) y))
  (intros h hk)
  (have q := (qh-parts w h))
  (have qi := (quiet-world-inv-parts w (And.left q)))
  (have k := (k-parts w (And.left (And.right qi)) (And.left (And.right q))))
  (have hz := (And.right (And.right (And.right (And.right k)))))
  (simp only [hz-all Bool.and_eq_true] at hz)
  (have cn := (cleanup-nil w (And.left (And.right (And.right qi))) (And.right (And.right q))))
  (have a1 := (any-none CompRow h0-c (adm-comp y) (:comps w) (adm-comp-h0 y) (And.left hz)))
  (have a2 := (any-none TaskRow h0-t (adm-task y) (:tasks w) (adm-task-h0 y) (And.left (And.right hz))))
  (have a3 := (any-none SourceRow h0-s (adm-source y) (:sources w) (adm-source-h0 y) (And.right (And.right hz))))
  (have rn := (And.right (And.right q)))
  (have pn := (And.left (And.right k)))
  (simp only [keep-fn keep-with Bool.or_eq_true] at hk)
  (cases hk)
  (case [inl a] (exact (Iff.mp (in-live-iff w y (live-converged-all w)) a)))
  (case [inr b]
    (have ef := (qh-forks w h))
    (simp [cleanup-rows cn cleanup-rows-in admitted a1 a2 a3 pn tbl-any storage storage-with storage-gather storage-seeds
           ef fork-keep rn tbl-gather anc-close anc-all reach-mem] at b)))
;; live is the root scope
(a/theorem live-root [w :- World, y :- Nat]
  (=> (= (qh w) true) (Reach (retain-succ w) (roots w) y) (= y root-scope-id))
  (intros h r)
  (induction r)
  (case [root x hx] (exact (roots-root w x h (Iff.mpr (reach-mem-iff x (roots w)) hx))))
  (case [step p x hp hx ih]
    (have hp2 := (reach-scope w p h hp))
    (rw [ih] at hp2)
    (rw [ih] at hx)
    (exact (False.elim (root-succ-none w x h hp2 (Iff.mpr (reach-mem-iff x (retain-succ w root-scope-id)) hx))))))
;; Theorem (questions 10, 14): a quiet world with quiet-world-inv holds the root scope only
(a/theorem quiet-root-only [w :- World, y :- Nat]
  (=> (= (qh w) true) (= (scope-has w y) true) (= y root-scope-id))
  (intros h hy)
  (have qi := (quiet-world-inv-parts w (And.left (qh-parts w h))))
  (have hm (= (nat-mem y (tbl-ids scope-id (:scopes w))) true)) (rw [nat-mem-ids]) (exact hy)
  (have m2 (= (nat-mem y (all-ids w)) true)) (simp only [all-ids nat-mem-app hm Bool.true_or])
  (have kk := (all-nat-mem (keep-fn w) y (all-ids w) (And.right (And.right (And.right qi))) m2))
  (exact (live-root w y h (keep-live w y h kk))))

;; Theorem (question 10): in a quiet world with quiet-world-inv every task (id /= 0) and every non-root scope is complete
;; (spindel.v2.ledger): no task row (quiet-rows), and no scope row but the root scope's (quiet-root-only)
(a/theorem quiet-task-complete [w :- World, t :- Nat]
  (=> (= (qh w) true) (= (Nat.beq t 0) false) (= (task-complete w t) true))
  (intros h ht)
  (have o := (quiet-rows w h))
  (simp only [only-scopes] at o)
  (have et := (And.left (And.right o)))
  (have hs (= (scope-has w (+ t 2)) false))
  (cases hb (scope-has w (+ t 2)))
  (case [false] (rfl))
  (case [true] (have e := (quiet-root-only w (+ t 2) h hb)) (simp only [root-scope-id] at e) (have z (= t 0)) (omega) (rw [z] at ht) (cases ht))
  (simp only [task-complete task-held task-srow task-find et tbl-find hs
              Bool.not_false Bool.and_self]))
(a/theorem quiet-scope-complete [w :- World, s :- Nat]
  (=> (= (qh w) true) (= (Nat.beq s root-scope-id) false) (= (scope-complete w s) true))
  (intros h hs)
  (cases hb (scope-has w s))
  (case [false] (simp only [scope-complete hb Bool.not_false]))
  (case [true] (have e := (quiet-root-only w s h hb)) (rw [e] at hs) (simp at hs)))

;; ===========================================================================
;; Part C. The refusal lemma: every item is refused in a quiet world
;; ===========================================================================

;; a non-host item: transition's released guards (creations, roots, link items), a token for want of a
;; run, the rest for want of their row
(a/theorem transition-quiet [w :- World, it :- Item]
  (=> (= (host-item it) false) (= (:runs w) (List.nil RunRow)) (= (:comps w) (List.nil CompRow))
      (= (:edges w) (List.nil EdgeRow)) (= (:res w) (List.nil ResRow)) (= (:sources w) (List.nil SourceRow))
      (= (:released w) true) (= (:forks w) (List.nil ForkRow))
      (= (:accepted (transition w it)) false))
  (intros hh rn cn en zn sn hr fn0)
  (cases it)
  (all_goals (simp only [host-item] at hh))
  (all_goals (simp only [transition create-in-scope-refused create-refused world-released hr Bool.or_true Bool.true_or refuse]))
  (all_goals (simp [t7-track t9-fire fire-tok-ok t15-resource-ack ack-tok-ok t17-arm t18-resource-fire t5-start t6-await t11-dispatch
                    t12-complete t-schedule t-take t-finalize t-open-scope t-finally-enter t-finally-exit t-finally-leave t-slice-exit
                    t21-release-world tok-run run-find comp-find edge-find resource-find resource-has source-find rn cn en zn sn hr
                    tbl-find tbl-has refuse in-cleanup arm-refused in-finally await-refused take-refused complete-refused fins-open opt-test
                    t-own own-ok t-owned-done t-drain t28-retire-local fn0 tbl-any]))
  (all_goals (cases hh)))

;; Theorem (refusal): in a quiet world with quiet-world-inv every item is refused (host items by host-item-refused: no
;; run holds a slice)
(a/theorem quiet-refused [w :- World, it :- Item] (=> (= (qh w) true) (= (:accepted (raw w it)) false))
  (intro h)
  (have q := (qh-parts w h))
  (have o := (quiet-rows w h))
  (have hr := (And.left (And.right q)))
  (have rn := (And.right (And.right q)))
  (have sh (= (slice-held w) false)) (simp only [slice-held rn tbl-any])
  (have e0 (= (:accepted (host-guarded-transition w it)) false))
  (cases hh (host-item it))
  (simp only [host-guarded-transition host-item-refused hr sh hh Bool.and_false])
  (exact (transition-quiet w it hh rn (And.left o) (And.left (And.right (And.right (And.right (And.right o)))))
           (And.left (And.right (And.right (And.right (And.right (And.right (And.right o)))))))
           (And.left (And.right (And.right (And.right o)))) hr (qh-forks w h)))
  (simp only [host-guarded-transition host-item-refused hr sh hh Bool.not_false Bool.and_self refuse])
  (simp only [raw then-cancel-losers e0]))

;; Theorem: a quiet world with quiet-world-inv is left as it is by every step (so it stays quiet)
(a/theorem quiet-step [w :- World, it :- Item] (=> (= (qh w) true) (= (:world (world-step w it)) w))
  (intro h) (simp only [(step-refuse w it (quiet-refused w it h)) refuse]))
(a/theorem quiet-stays [w :- World, it :- Item]
  (=> (= (quiet-world-inv w) true) (= (world-quiet w) true) (= (world-quiet (:world (world-step w it))) true))
  (intros h hq) (rw [(quiet-step w it (qh-of w h hq))]) (exact hq))
