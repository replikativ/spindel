(ns spindel.v2.qworld
  "C1 completion stability, layer 1, the quiet half (notes/PLAN.md C1, `hq`): a quiet world (released,
  no run) holds only scopes, and every item is refused there, so a quiet world stays quiet.

    gc w        inv-sample w and every cleanup entry's run is a run row (`gc-rest`): the cleanup entry
                is written at a run's cancel (T14) or its completion (T12, `retire-after`) for a run
                found by id, and goes with the run (T13 `retire-with`); Rule R's filter keeps every
                cleanup entry's run (it is in `cleanup-rows`). `step-gc`, `gc-empty`.
    qinv w      p3l w, K (`gk-rest`, spindel.v2.quiet), gc and I3 (`i3`: the filter keeps every id,
                `step-i3-total`); `step-qinv`, `qinv-empty`.
    quiet-rows  the closure lemma: in a quiet world with qinv, live is scopes only (the roots are scopes:
                no pin, no host edge, no pending activation, no publication; a scope's successors are
                its parent (I1, a scope; the root scope's parent is 0, gw), no running task (no run),
                no fork marker (gw)), nothing is admitted (every handle count is 0), there is no cleanup
                entry (gc) and no storage (no run): every computation, task, source, edge, activation
                and resource id would be kept (I3) only by live, a scope id, against unique ids. So the
                world holds no computation (tombstones included), task, run, source, edge, activation,
                resource, cleanup entry or publication.
    quiet-refused  every item is refused in a quiet world with qinv: host items by `host-shut` (no run
                holds a slice), creations and roots by raw0's released guards, token items for want of
                a run, the others for want of their row; so `world-step` leaves a quiet world as it
                is (`quiet-step`).

  The copy machinery is spindel.v2.lit's (`mk-bundle`, `prim!`, `lcopy!`)."
  (:require [ansatz.core :as a]
            [clojure.string :as str]
            [spindel.v2.state :refer :all]
            [spindel.v2.edits :refer :all]
            [spindel.v2.reach :refer :all]
            [spindel.v2.retain :refer :all]
            [spindel.v2.step :refer :all]
            [spindel.v2.rule :refer :all]
            [spindel.v2.engine :refer :all]
            [spindel.v2.casc :refer :all]
            [spindel.v2.acts :refer :all]
            [spindel.v2.inv :refer :all]
            [spindel.v2.lit :refer :all]
            [spindel.v2.p3 :refer :all]
            [spindel.v2.hmk2 :refer [p3l]]
            [spindel.v2.quiet :refer :all]
            [spindel.v2.i11] [spindel.v2.i1] [spindel.v2.i5] [spindel.v2.i1o] [spindel.v2.i1r :refer [gr0]] [spindel.v2.i8]
            [spindel.v2.hm] [spindel.v2.i14] [spindel.v2.i10]
            [spindel.v2.oscope :refer [gos-rest gos os-need hw]]
            [spindel.v2.ledger :refer [task-complete task-held task-srow scope-complete]]))

;; ===========================================================================
;; Part A. gc: every cleanup entry's run is a run row
;; ===========================================================================

(a/defn cl-run [rs :- (List RunRow), c :- CleanupRow] Bool (tbl-has run-id (:run c) rs))
(a/defn gc-rest [w :- World] Bool (tbl-all (cl-run (:runs w)) (:cleanup w)))
(a/defn gc [w :- World] Bool (Bool.and (inv-sample w) (gc-rest w)))

(a/theorem gc-sample [w :- World] (=> (= (gc w) true) (= (inv-sample w) true))
  (intro h) (simp only [gc Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem gc-rest-of [w :- World] (=> (= (gc w) true) (= (gc-rest w) true))
  (intro h) (simp only [gc Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem gc-intro [w :- World] (=> (= (inv-sample w) true) (= (gc-rest w) true) (= (gc w) true))
  (intros h1 h2) (simp only [gc h1 h2 Bool.and_self]))
(a/theorem gc-parts [w :- World]
  (=> (= (gc w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (gc-sample w h))))

;; the runs grow (as a set of ids), the cleanup table is the same
(a/theorem gc-rest-runs [w :- World, w2 :- World]
  (=> (= (:cleanup w2) (:cleanup w))
      (forall [y :- Nat] (=> (= (tbl-has run-id y (:runs w)) true) (= (tbl-has run-id y (:runs w2)) true)))
      (= (gc-rest w) true) (= (gc-rest w2) true))
  (intros e hy h)
  (simp only [gc-rest] at h) (simp only [gc-rest]) (rw [e])
  (exact (tbl-all-mono CleanupRow (cl-run (:runs w)) (cl-run (:runs w2))
           (fn [c :- CleanupRow, q :- (= (cl-run (:runs w) c) true)] (hy (:run c) q)) (:cleanup w) h)))

(a/theorem gc-rest-run-upd [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                            hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r)))]
  (=> (= (gc-rest w) true) (= (gc-rest (run-upd w x f)) true))
  (intro h)
  (exact (gc-rest-runs w (run-upd w x f) (rfl)
           (fn [y :- Nat, q :- (= (tbl-has run-id y (:runs w)) true)]
             (Eq.trans (tbl-has-upd RunRow run-id x y f hf (:runs w)) q)) h)))
(a/theorem gc-rest-run-ins [w :- World, r :- RunRow] (=> (= (gc-rest w) true) (= (gc-rest (bump (run-ins w r))) true))
  (intro h)
  (exact (gc-rest-runs w (bump (run-ins w r)) (rfl)
           (fn [y :- Nat, q :- (= (tbl-has run-id y (:runs w)) true)]
             (Eq.trans (tbl-has-ins RunRow run-id y r (:runs w)) (Eq.trans (congrArg (Bool.or (Nat.beq (run-id r) y)) q) (Bool.or_true _)))) h)))
(a/theorem gc-rest-cleanup-del [w :- World, x :- Nat] (=> (= (gc-rest w) true) (= (gc-rest (cleanup-del w x)) true))
  (intro h) (simp only [gc-rest] at h) (simp only [gc-rest cleanup-del set-cleanup])
  (exact (all-del-keep CleanupRow cleanup-id x (cl-run (:runs w)) (:cleanup w) h)))
(a/theorem gc-rest-cleanup-upd [w :- World, x :- Nat, f :- (=> CleanupRow CleanupRow),
                                hr :- (forall [c :- CleanupRow] (= (:run (f c)) (:run c)))]
  (=> (= (gc-rest w) true) (= (gc-rest (cleanup-upd w x f)) true))
  (intro h) (simp only [gc-rest] at h) (simp only [gc-rest cleanup-upd set-cleanup])
  (exact (all-upd-keep CleanupRow cleanup-id x f (cl-run (:runs w))
           (fn [c :- CleanupRow, q :- (= (cl-run (:runs w) c) true)] (Eq.trans (congrArg (fn [n :- Nat] (tbl-has run-id n (:runs w))) (hr c)) q))
           (:cleanup w) h)))
;; cleanup[rid] for a run row rid
(a/theorem gc-rest-set [w :- World, rid :- Nat, rows :- (List Nat)]
  (=> (= (tbl-has run-id rid (:runs w)) true) (= (gc-rest w) true) (= (gc-rest (cleanup-set w rid rows)) true))
  (intros hr h) (simp only [gc-rest] at h)
  (have t := (all-del-keep CleanupRow cleanup-id rid (cl-run (:runs w)) (:cleanup w) h))
  (simp only [gc-rest cleanup-set cleanup-ins cleanup-del set-cleanup tbl-ins tbl-all cl-run hr t Bool.and_self]))
;; T13: the run row and its cleanup entry go together
(a/theorem gc-rest-del-both [w :- World, x :- Nat] (=> (= (gc-rest w) true) (= (gc-rest (cleanup-del (run-del w x) x)) true))
  (intro h) (simp only [gc-rest] at h) (simp only [gc-rest cleanup-del run-del set-cleanup set-runs])
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
(a/theorem gc-rest-filter-keep [v :- World] (=> (= (gc-rest v) true) (= (gc-rest (filter-world (keep-fn v) v)) true))
  (intro h) (simp only [gc-rest] at h)
  (simp only [gc-rest filter-world])
  (apply all-of-mem) (intros c m)
  (have q := (tbl-all-mem CleanupRow _ c _ h m))
  (have k (= (keep-fn v (:run c)) true))
  (simp only [keep-fn keep-with cleanup-rows (cl-in-rows v c (:cleanup v) m) Bool.or_true Bool.true_or])
  (simp only [cl-run] at q)
  (simp only [cl-run (tbl-has-keep RunRow (keep-fn v) run-id (:run c) (:runs v)) k q Bool.and_self]))
(a/theorem gc-filter-keep [v :- World]
  (=> (= (gc v) true) (= (filter-safe v) true) (= (gc (filter-world (keep-fn v) v)) true))
  (intros h hs)
  (exact (gc-intro _ (inv-filter-world v (keep-fn v) (gc-sample v h) hs) (gc-rest-filter-keep v (gc-rest-of v h)))))

(a/theorem gc-rest-mark-edge [w :- World, x :- Nat] (= (gc-rest (mark-edge w x)) (gc-rest w))
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [mark-edge hf hm]))))
(a/theorem gc-rest-unmark-edge [w :- World, x :- Nat] (= (gc-rest (unmark-edge w x)) (gc-rest w))
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [unmark-edge hf hm]))))
(a/theorem gc-rest-remove-edge [w :- World, x :- Nat] (= (gc-rest (remove-edge w x)) (gc-rest w))
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [remove-edge hf hm]))))

;; ---- the GC copy
(def GC (mk-bundle 'gc [] "gc-" {'inv-cleanup-upd ['(fn [c :- CleanupRow] (Eq.refl (:run c))) 3]}))
(swap! (:renames GC) assoc 'inv-parts 'gc-parts)

(doseq [o '[inv-scope-upd inv-pub-upd inv-source-upd inv-resource-upd inv-set-pins inv-resource-del inv-scope-del
            inv-act-upd inv-edge-upd inv-drop-cred inv-drop-edges inv-comp-del-unref inv-comp-upd inv-drop-act inv-task-upd
            inv-source-ins-fresh inv-resource-ins-fresh inv-scope-ins-fresh inv-comp-ins-fresh inv-act-ins-fresh
            inv-task-ins-fresh inv-bump insert-edge-fresh-inv-sample inv-set-pending-act inv-set-released]]
  (prim! GC o nil))
(prim! GC 'mark-edge-inv-sample '(Eq.trans (gc-rest-mark-edge w x) R))
(prim! GC 'unmark-edge-inv-sample '(Eq.trans (gc-rest-unmark-edge w x) R))
(prim! GC 'inv-remove-edge '(Eq.trans (gc-rest-remove-edge w x) R))
(prim! GC 'inv-run-upd '(gc-rest-run-upd w x f hf R))
(prim! GC 'inv-run-ins-fresh '(gc-rest-run-ins w r R))
(prim! GC 'inv-cleanup-del '(gc-rest-cleanup-del w x R))
(a/theorem gc-cleanup-upd [w :- World, x :- Nat, f :- (=> CleanupRow CleanupRow),
                           hr :- (forall [c :- CleanupRow] (= (:run (f c)) (:run c)))]
  (=> (= (gc w) true) (= (gc (cleanup-upd w x f)) true))
  (intro h) (exact (gc-intro _ (inv-cleanup-upd w x f (gc-sample w h)) (gc-rest-cleanup-upd w x f hr (gc-rest-of w h)))))
(swap! (:renames GC) assoc 'inv-cleanup-upd 'gc-cleanup-upd)

(a/theorem gc-cleanup-set [w :- World, rid :- Nat, rows :- (List Nat)]
  (=> (= (tbl-has run-id rid (:runs w)) true) (= (gc w) true) (= (gc (cleanup-set w rid rows)) true))
  (intros hr h) (exact (gc-intro _ (inv-cleanup-set w rid rows (gc-sample w h)) (gc-rest-set w rid rows hr (gc-rest-of w h)))))
(a/theorem gc-del-both [w :- World, x :- Nat] (=> (= (gc w) true) (= (gc (cleanup-del (run-del w x) x)) true))
  (intro h) (exact (gc-intro _ (inv-cleanup-del _ x (inv-run-del w x (gc-sample w h))) (gc-rest-del-both w x (gc-rest-of w h)))))
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

(override! GC 'inv-cleanup-set '[]
  '(a/theorem gc-cleanup-set-x [w :- World, rid :- Nat, rows :- (List Nat)]
     (=> (= (tbl-has run-id rid (:runs w)) true) (= (gc w) true) (= (gc (cleanup-set w rid rows)) true))
     (intros hr h) (exact (gc-cleanup-set w rid rows hr h))))
(override! GC 'inv-retire-after '[]
  '(a/theorem gc-retire-after [w :- World, rid :- Nat]
     (=> (= (gc w) true) (= (gc (retire-after w rid)) true))
     (intro h)
     (cases hr (run-find w rid)) (case' [some r]) (case' [none])
     (simp only [retire-after hr]) (exact h)
     (cases ht (retirable r))
     (simp only [retire-after hr ht]) (exact (gc-cleanup-set w rid _ (tbl-find-has RunRow run-id rid r (:runs w) hr) h))
     (simp only [retire-after hr ht]) (exact h)))
(override! GC 'inv-cancel-run-local '[inv-cancel-debtor inv-cancel-res inv-cancel-acts]
  '(a/theorem gc-cancel-run-local [w :- World, r :- RunRow, rep :- Bool]
     (=> (= (tbl-has run-id (:id r) (:runs w)) true) (= (gc w) true) (= (gc (cancel-run-local w r rep)) true))
     (intros hr h)
     (have hr2 (= (tbl-has run-id (:id r) (:runs (cancel-res (cancel-acts (run-upd w (:id r) run-cancel-row) (:id r)) r))) true))
     (rw [runs-cancel-res runs-cancel-acts])
     (simp only [run-upd set-runs (tbl-has-upd RunRow run-id (:id r) (:id r) run-cancel-row run-cancel-row-id (:runs w)) hr])
     (simp only [cancel-run-local])
     (exact (gc-cancel-debtor rep _ r (gc-cleanup-set _ (:id r) (cleanup-rows-of w r) hr2
              (gc-cancel-res _ r (gc-cancel-acts _ (:id r) (gc-run-upd w (:id r) run-cancel-row run-cancel-row-id h))))))))
(override! GC 'inv-retire-with '[inv-remove-if-empty inv-close-local inv-clear-comp-run]
  '(a/theorem gc-retire-with [w :- World, r :- RunRow, sub :- (List Nat)]
     (=> (= (gc w) true) (= (gc (retire-with w r sub)) true))
     (intro h) (simp only [retire-with])
     (exact (gc-remove-if-empty _ sub (gc-del-both _ (:id r) (gc-close-local _ sub (gc-clear-comp-run w r h)))))))
(override! GC 'inv-job-apply '[inv-cancel-run-local inv-retire-local inv-close-scope-local]
  '(a/theorem gc-job-apply [w :- World, j :- Job]
     (=> (= (gc w) true) (= (gc (job-apply w j)) true))
     (intro h)
     (cases j)
     (rename_i rid rep) (cases hf (run-find w rid)) (case' [some r]) (case' [none])
     (simp only [job-apply hf]) (exact h)
     (cases ha (run-alive r)) (simp only [job-apply hf ha]) (exact h)
     (simp only [job-apply hf ha]) (exact (gc-cancel-run-local w r rep (run-has-of-find w rid r hf) h))
     (rename_i rid) (cases hf (run-find w rid)) (case' [some r]) (case' [none])
     (simp only [job-apply hf]) (exact h)
     (cases ha (retirable r)) (simp only [job-apply hf ha]) (exact h)
     (simp only [job-apply hf ha]) (exact (gc-retire-local w r h))
     (rename_i s) (cases hs (scope-has w s)) (simp only [job-apply hs]) (exact h)
     (simp only [job-apply hs]) (exact (gc-close-scope-local w s h))))

(lcopy! GC 'raw-inv)
(lcopy! GC 'inv-normalize)

(a/theorem gc-rule-r-round [w :- World]
  (=> (= (gc w) true) (= (filter-safe (normalize w)) true) (= (gc (rule-r-round w)) true))
  (intros h hf)
  (simp only [rule-r-round])
  (rw [rule-r-filter-eq])
  (exact (gc-filter-keep (normalize w) (gc-normalize w h) hf)))

(a/theorem gc-rr-loop [fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (gc w0) true) (= (rr-safe fuel w0) true) (= (gc (rr-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 h hs) (simp only [rr-safe] at hs) (simp only [rr-loop]) (exact (gc-rule-r-round w0 h hs)))
  (case [cons x f ih]
    (intros w0 h hs)
    (simp only [rr-safe Bool.and_eq_true] at hs)
    (have h1 := (gc-rule-r-round w0 h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false] (simp only [ho] at hs) (simp only [rr-loop ho]) (exact (ih (rule-r-round w0) h1 (And.right hs))))
    (case [true] (simp only [rr-loop ho]) (exact h1))))

(a/theorem gc-rule-r [w :- World]
  (=> (= (gc w) true) (= (rule-r-safe w) true) (= (gc (rule-r w)) true))
  (intros h hs) (simp only [rule-r-safe] at hs) (simp only [rule-r]) (exact (gc-rr-loop (rr-fuel w) w h hs)))

(a/theorem step-gc [w :- World, it :- Item]
  (=> (= (gc w) true) (= (rule-r-safe (:world (raw w it))) true) (= (gc (:world (world-step w it))) true))
  (intros h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true] (have e2 := (step-accepted w it ha)) (rw [e2]) (exact (gc-rule-r (:world (raw w it)) (raw-gc w it h) hs))))

;; Theorem: every cleanup entry's run is a run row, through every step from a p3b world
(a/theorem step-gc-rest [w :- World, it :- Item]
  (=> (= (p3b w) true) (= (gc-rest w) true) (= (gc-rest (:world (world-step w it))) true))
  (intros h hk)
  (exact (gc-rest-of _ (step-gc w it (gc-intro w (ga-sample w (And.left (p3b-parts w h))) hk) (step-rule-r-safe w it h)))))
(a/theorem gc-empty [] (= (gc-rest empty-world) true) (rfl))

;; ===========================================================================
;; Part B. The closure lemma: a quiet world holds only scopes
;; ===========================================================================

;; I3 as a state fact: the filter keeps every id (after every accepted step, `step-i3-total`)
(a/defn i3 [w :- World] Bool (tbl-all (keep-fn w) (all-ids w)))
;; C1c (question 10): and every open non-root scope lies in a run's run-scope subtree (spindel.v2.oscope `gos-rest`)
(a/defn qinv [w :- World] Bool (Bool.and (p3l w) (Bool.and (gk-rest w) (Bool.and (gc-rest w) (Bool.and (i3 w) (gos-rest w))))))

;; p3l's parts the closure reads
(a/theorem p3l-p3e [w :- World] (=> (= (p3l w) true) (= (p3e w) true))
  (intro h)
  (exact (And.left (p3f-parts _ (And.left (p3g-parts _ (And.left (p3h-parts _ (And.left (p3i-parts _
           (And.left (p3j-parts _ (And.left (p3k-parts _ (And.left (p3l-parts w h))))))))))))))))
(a/theorem p3l-p3d [w :- World] (=> (= (p3l w) true) (= (p3d w) true))
  (intro h) (exact (And.left (p3e-parts _ (p3l-p3e w h)))))
(a/theorem p3l-p3b [w :- World] (=> (= (p3l w) true) (= (p3b w) true))
  (intro h) (exact (And.left (p3c-parts _ (And.left (p3d-parts _ (p3l-p3d w h)))))))
(a/theorem p3l-sample [w :- World] (=> (= (p3l w) true) (= (inv-sample w) true))
  (intro h) (exact (ga-sample w (And.left (p3b-parts w (p3l-p3b w h))))))
(a/theorem p3l-gw [w :- World] (=> (= (p3l w) true) (= (gw-rest w) true))
  (intro h) (exact (gw-rest-of w (And.left (And.right (p3d-parts _ (p3l-p3d w h)))))))
(a/theorem p3l-i1 [w :- World] (=> (= (p3l w) true) (= (lit-i1-scope w) true))
  (intro h) (exact (g1-rest-of w (And.right (p3e-parts _ (p3l-p3e w h))))))

(a/theorem qinv-parts [w :- World]
  (=> (= (qinv w) true) (And (= (p3l w) true) (And (= (gk-rest w) true) (And (= (gc-rest w) true) (= (i3 w) true)))))
  (intro h) (simp only [qinv Bool.and_eq_true] at h)
  (exact (And.intro (And.left h) (And.intro (And.left (And.right h)) (And.intro (And.left (And.right (And.right h)))
           (And.left (And.right (And.right (And.right h)))))))))
(a/theorem qinv-gos [w :- World] (=> (= (qinv w) true) (= (gos-rest w) true))
  (intro h) (simp only [qinv Bool.and_eq_true] at h) (exact (And.right (And.right (And.right (And.right h))))))
(a/theorem qinv-intro [w :- World]
  (=> (= (p3l w) true) (= (gk-rest w) true) (= (gc-rest w) true) (= (i3 w) true) (= (gos-rest w) true) (= (qinv w) true))
  (intros h1 h2 h3 h4 h5) (simp only [qinv h1 h2 h3 h4 h5 Bool.and_self]))
(a/theorem p3l-gr0 [w :- World] (=> (= (p3l w) true) (= (gr0 w) true))
  (intro h)
  (exact (And.right (p3h-parts _ (And.left (p3i-parts _ (And.left (p3j-parts _ (And.left (p3k-parts _ (And.left (p3l-parts w h))))))))))))

(a/theorem step-i3-inv [w :- World, it :- Item] (=> (= (i3 w) true) (= (i3 (:world (world-step w it))) true))
  (intro h)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true] (simp only [i3]) (exact (step-i3-total w it ha))))

;; Theorem: qinv holds of the empty world and through every step
(a/theorem step-qinv [w :- World, it :- Item] (=> (= (qinv w) true) (= (qinv (:world (world-step w it))) true))
  (intro h)
  (have q := (qinv-parts w h))
  (have b := (p3l-p3b w (And.left q)))
  (have g := (step-gos w it (And.left (p3b-parts w b)) (p3l-gr0 w (And.left q))
                (gos-intro w (p3l-sample w (And.left q)) (qinv-gos w h)) (step-rule-r-safe w it b)))
  (exact (qinv-intro _ (step-p3l w it (And.left q)) (step-k w it b (And.left (And.right q)))
           (step-gc-rest w it b (And.left (And.right (And.right q)))) (step-i3-inv w it (And.right (And.right (And.right q))))
           (gos-rest-of _ g))))
(a/theorem qinv-empty [] (= (qinv empty-world) true) (rfl))

;; ---- uniqueness: a scope id is no other row's id
(a/defn other-has [w :- World, x :- Nat] Bool
  (Bool.or (tbl-has comp-id x (:comps w)) (Bool.or (tbl-has task-id x (:tasks w)) (Bool.or (tbl-has run-id x (:runs w))
  (Bool.or (tbl-has source-id x (:sources w)) (Bool.or (tbl-has edge-id x (:edges w)) (Bool.or (tbl-has act-id x (:acts w))
  (Bool.or (tbl-has resource-id x (:res w)) (tbl-has pub-id x (:pubs w))))))))))
(a/theorem scope-only [w :- World, x :- Nat]
  (=> (= (inv-sample w) true) (= (scope-has w x) true) (= (other-has w x) false))
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

;; ---- the quiet hypotheses: released, no run, no fork marker (C1c stage B), qinv
(a/defn qh [w :- World] Bool
  (Bool.and (qinv w) (Bool.and (:released w) (Bool.and (nats-empty (tbl-ids run-id (:runs w))) (forks-nil (:forks w))))))
(a/theorem qh-parts [w :- World]
  (=> (= (qh w) true) (And (= (qinv w) true) (And (= (:released w) true) (= (:runs w) (List.nil RunRow)))))
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
(a/theorem qh-of [w :- World] (=> (= (qinv w) true) (= (world-quiet w) true) (= (qh w) true))
  (intros h hq)
  (simp only [world-quiet world-runs Bool.and_eq_true] at hq)
  (have e (= (nats-empty (tbl-ids run-id (:runs w))) true))
  (have z := (Nat.eq_of_beq_eq_true (And.left (And.right hq))))
  (cases hr (:runs w)) (case [nil] (simp only [tbl-ids nats-empty])) (case [cons a t] (rw [hr] at z) (simp at z))
  (simp only [qh h (And.left hq) e (And.right (And.right hq)) Bool.and_self]))

(a/theorem k-parts [w :- World]
  (=> (= (gk-rest w) true) (= (:released w) true)
      (And (= (:pending-act w) 0) (And (= (:pubs w) (List.nil PubRow))
       (And (= (:pins w) (List.nil Nat)) (And (= (tbl-all not-host (:edges w)) true) (= (hz-all w) true))))))
  (intros h hr)
  (have k0 := (gk-rest-k0 w h)) (have g := (gk-rest-gh w h))
  (simp only [gk0-rest hr Bool.not_true Bool.false_or Bool.and_eq_true] at k0)
  (simp only [gh-rest hr Bool.not_true Bool.false_or] at g)
  (have ep (= (:pins w) (List.nil Nat)))
  (have pe := (And.left (And.right (And.right k0))))
  (cases hp (:pins w)) (case [nil] (rfl)) (case [cons a t] (rw [hp] at pe) (simp [nats-empty] at pe))
  (exact (And.intro (Nat.eq_of_beq_eq_true (And.left k0)) (And.intro (pa-all _ (And.left (And.right k0)))
           (And.intro ep (And.intro (And.right (And.right (And.right k0))) g))))))

(a/theorem cleanup-nil [w :- World] (=> (= (gc-rest w) true) (= (:runs w) (List.nil RunRow)) (= (:cleanup w) (List.nil CleanupRow)))
  (intros h hn)
  (simp only [gc-rest hn] at h)
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
  (have qi := (qinv-parts w (And.left q)))
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
  (have qi := (qinv-parts w (And.left (qh-parts w h))))
  (have i1 := (tbl-all-mem ScopeRow _ s _ (p3l-i1 w (And.left qi)) m))
  (simp only [lit-scope-parent hp Bool.false_or] at i1)
  (cases hk (Nat.beq (:kind s) scope-root))
  (case [false] (simp only [hk Bool.false_or] at i1) (exact i1))
  (case [true]
    (have g := (p3l-gw w (And.left qi)))
    (simp only [gw-rest gwk Bool.and_eq_true] at g)
    (have ro := (And.left g)) (rw [all-skws] at ro)
    (have r := (tbl-all-mem ScopeRow _ s _ ro m))
    (have hk2 (= (Nat.beq (:kind (skw s)) scope-root) true)) (exact hk)
    (simp only [root-ok hk2 Bool.true_or Bool.or_true Bool.not_true Bool.false_or Bool.and_eq_true] at r)
    (have e (= (Nat.beq (:parent (skw s)) 0) true)) (exact (And.right (And.right r)))
    (have e2 (= (Nat.beq (:parent s) 0) true)) (exact e)
    (rw [e2] at hp) (cases hp)))
(a/theorem scope-succ-scope [w :- World, s :- ScopeRow, z :- Nat]
  (=> (= (qh w) true) (List.Mem s (:scopes w)) (= (reach-mem z (scope-contrib w s)) true) (= (scope-has w z) true))
  (intros h m hz)
  (have q := (qh-parts w h))
  (have qi := (qinv-parts w (And.left q)))
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
  (have qi := (qinv-parts w (And.left (qh-parts w h))))
  (have o := (scope-only w x (p3l-sample w (And.left qi)) hx))
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
  (have qi := (qinv-parts w (And.left q)))
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
    (simp [cleanup-rows cn cleanup-rows-in admitted a1 a2 a3 pn tbl-any storage storage-with storage-gather storage-gather0
           ef fork-keep rn tbl-gather anc-close anc-all reach-mem] at b)))

;; Theorem (closure): a quiet world with qinv holds only scopes: no computation (tombstones
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
  (have qi := (qinv-parts w (And.left (qh-parts w h))))
  (exact (keep-scope w y h (all-nat-mem (keep-fn w) y (all-ids w) (And.right (And.right (And.right qi))) m))))

(a/theorem quiet-rows [w :- World] (=> (= (qh w) true) (only-scopes w))
  (intro h)
  (have q := (qh-parts w h))
  (have qi := (qinv-parts w (And.left q)))
  (have k := (k-parts w (And.left (And.right qi)) (And.left (And.right q))))
  (have hs := (p3l-sample w (And.left qi)))
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
(a/theorem root-id-2 [s :- ScopeRow] (=> (= (root-ok (skw s)) true) (= (is-root-scope s) true) (= (:id s) root-scope-id))
  (intros r k)
  (have hk2 (= (Nat.beq (:kind (skw s)) scope-root) true)) (exact k)
  (simp only [root-ok hk2 Bool.true_or Bool.not_true Bool.false_or Bool.and_eq_true] at r)
  (exact (Nat.eq_of_beq_eq_true (And.left r))))
(a/theorem oe-need-false [s :- ScopeRow] (=> (= (is-open-explicit s) true) (= (os-need s) false) False)
  (intros p n)
  (simp only [is-open-explicit Bool.and_eq_true] at p)
  (have e (= (:kind s) scope-explicit)) (exact (Nat.eq_of_beq_eq_true (And.left p)))
  (simp only [os-need e (And.right p)] at n) (cases n))
(a/theorem root-parent-0 [w :- World, s :- ScopeRow, y :- Nat]
  (=> (= (qh w) true) (List.Mem s (:scopes w)) (= (root-ok (skw s)) true) (= (id-is scope-id root-scope-id s) true)
      (= (reach-mem y (scope-contrib w s)) true) False)
  (intros h m r p hy)
  (have q := (qh-parts w h))
  (have qi := (qinv-parts w (And.left q)))
  (have i2 (= (Nat.beq (:id (skw s)) 2) true)) (simp only [id-is scope-id] at p) (exact p)
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
;; no open non-root scope: its witness would be a run (spindel.v2.oscope)
(a/theorem quiet-no-open [w :- World, c :- ScopeRow]
  (=> (= (qh w) true) (List.Mem c (:scopes w)) (= (os-need c) false))
  (intros h m)
  (have q := (qh-parts w h))
  (cases hn (os-need c))
  (case [false] (rfl))
  (case [true]
    (have x := (gos-rest-mem w c (qinv-gos w (And.left q)) m hn))
    (simp [hw (And.right (And.right q)) tbl-any] at x)))
;; the roots of a quiet world: the root scope (no open explicit scope)
(a/theorem roots-root [w :- World, y :- Nat]
  (=> (= (qh w) true) (= (reach-mem y (roots w)) true) (= y root-scope-id))
  (intros h hm)
  (have q := (qh-parts w h))
  (have qi := (qinv-parts w (And.left q)))
  (have k := (k-parts w (And.left (And.right qi)) (And.left (And.right q))))
  (have ne (= (reach-mem y (tbl-scan edge-id is-observe (:edges w))) false))
  (cases hb (reach-mem y (tbl-scan edge-id is-observe (:edges w)))) (rfl)
  (apply (False.elim (scan-prop EdgeRow edge-id is-observe (fn [z :- Nat] False) (:edges w) _ y hb)))
  (intros e me pe)
  (have t := (tbl-all-mem EdgeRow not-host e (:edges w) (And.left (And.right (And.right (And.right k)))) me))
  (simp only [is-observe] at pe) (simp [not-host pe] at t)
  (simp only [roots reach-mem-append (And.left (And.right (And.right k))) (And.left k) (And.left (And.right k)) ne
              nz Nat.beq_refl tbl-scan reach-mem Bool.or_false Bool.false_or] at hm)
  (have g := (p3l-gw w (And.left qi)))
  (simp only [gw-rest gwk Bool.and_eq_true] at g)
  (have ro := (And.left g)) (rw [all-skws] at ro)
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
  (have qi := (qinv-parts w (And.left (qh-parts w h))))
  (have o := (scope-only w root-scope-id (p3l-sample w (And.left qi)) hx))
  (simp only [other-has Bool.or_eq_false_iff] at o)
  (simp only [retain-succ reach-mem-append
              (gather-off CompRow comp-id root-scope-id (comp-contrib w) (:comps w) z (And.left o))
              (gather-off TaskRow task-id root-scope-id task-contrib (:tasks w) z (And.left (And.right o)))
              (gather-off RunRow run-id root-scope-id (run-contrib w) (:runs w) z (And.left (And.right (And.right o))))
              (gather-off EdgeRow edge-id root-scope-id edge-contrib (:edges w) z (And.left (And.right (And.right (And.right (And.right o))))))
              (gather-off ActRow act-id root-scope-id act-contrib (:acts w) z (And.left (And.right (And.right (And.right (And.right (And.right o)))))))
              (gather-off PubRow pub-id root-scope-id pub-contrib (:pubs w) z (And.right (And.right (And.right (And.right (And.right (And.right (And.right o))))))))
              Bool.or_false] at hm)
  (have g := (p3l-gw w (And.left qi)))
  (simp only [gw-rest gwk Bool.and_eq_true] at g)
  (have ro := (And.left g)) (rw [all-skws] at ro)
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
  (have qi := (qinv-parts w (And.left q)))
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
    (simp [cleanup-rows cn cleanup-rows-in admitted a1 a2 a3 pn tbl-any storage storage-with storage-gather storage-gather0
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
;; Theorem (questions 10, 14): a quiet world with qinv holds the root scope only
(a/theorem quiet-root-only [w :- World, y :- Nat]
  (=> (= (qh w) true) (= (scope-has w y) true) (= y root-scope-id))
  (intros h hy)
  (have qi := (qinv-parts w (And.left (qh-parts w h))))
  (have hm (= (nat-mem y (tbl-ids scope-id (:scopes w))) true)) (rw [nat-mem-ids]) (exact hy)
  (have m2 (= (nat-mem y (all-ids w)) true)) (simp only [all-ids nat-mem-app hm Bool.true_or])
  (have kk := (all-nat-mem (keep-fn w) y (all-ids w) (And.right (And.right (And.right qi))) m2))
  (exact (live-root w y h (keep-live w y h kk))))

;; Theorem (question 10): in a quiet world with qinv every task (id /= 0) and every non-root scope is complete
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

;; a non-host item: raw0's released guards (creations, roots, link items), a token for want of a
;; run, the rest for want of their row
(a/theorem raw0-quiet [w :- World, it :- Item]
  (=> (= (host-item it) false) (= (:runs w) (List.nil RunRow)) (= (:comps w) (List.nil CompRow))
      (= (:edges w) (List.nil EdgeRow)) (= (:res w) (List.nil ResRow)) (= (:sources w) (List.nil SourceRow))
      (= (:released w) true)
      (= (:accepted (raw0 w it)) false))
  (intros hh rn cn en zn sn hr)
  (cases it)
  (all_goals (simp only [host-item] at hh))
  (all_goals (simp only [raw0 body-shut cc-shut root-shut hr Bool.or_true Bool.true_or refuse]))
  (all_goals (simp [t7-track t9-fire fire-tok-ok t15-full ack-tok-ok t17-arm t18-resource-fire t5-start t6-await t11-dispatch
                    t12-complete t-schedule t-take t-finalize t-open-scope t-finally-enter t-finally-exit t-finally-leave t-slice-exit
                    t-release-world tok-run run-find comp-find edge-find resource-find resource-has source-find rn cn en zn sn hr
                    tbl-find tbl-has refuse in-cleanup fin-shut in-fin await-bad take-bad complete-refused fins-open opt-test]))
  (all_goals (cases hh)))

;; Theorem (refusal): in a quiet world with qinv every item is refused (host items by host-shut: no
;; run holds a slice)
(a/theorem quiet-refused [w :- World, it :- Item] (=> (= (qh w) true) (= (:accepted (raw w it)) false))
  (intro h)
  (have q := (qh-parts w h))
  (have o := (quiet-rows w h))
  (have hr := (And.left (And.right q)))
  (have rn := (And.right (And.right q)))
  (have sh (= (slice-held w) false)) (simp only [slice-held rn tbl-any])
  (have e0 (= (:accepted (raw0g w it)) false))
  (cases hh (host-item it))
  (simp only [raw0g host-shut hr sh hh Bool.and_false])
  (exact (raw0-quiet w it hh rn (And.left o) (And.left (And.right (And.right (And.right (And.right o)))))
           (And.left (And.right (And.right (And.right (And.right (And.right (And.right o)))))))
           (And.left (And.right (And.right (And.right o)))) hr))
  (simp only [raw0g host-shut hr sh hh Bool.not_false Bool.and_self refuse])
  (simp only [raw post e0]))

;; Theorem: a quiet world with qinv is left as it is by every step (so it stays quiet)
(a/theorem quiet-step [w :- World, it :- Item] (=> (= (qh w) true) (= (:world (world-step w it)) w))
  (intro h) (simp only [(step-refuse w it (quiet-refused w it h)) refuse]))
(a/theorem quiet-stays [w :- World, it :- Item]
  (=> (= (qinv w) true) (= (world-quiet w) true) (= (world-quiet (:world (world-step w it))) true))
  (intros h hq) (rw [(quiet-step w it (qh-of w h hq))]) (exact hq))
