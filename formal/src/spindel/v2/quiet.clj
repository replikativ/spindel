(ns spindel.v2.quiet
  "C1 completion stability, layer 1 (notes/PLAN.md C1, `hq`): a step keeps a released world released
  (`step-released`) and a quiet world (released, no run) quiet.

    grel rb w   inv-sample w and (b -> released w): the bundle copy of every inv-sample lemma of the step
               (`step-grel`), so released stays released (`step-released`).

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
            [spindel.v2.hmk2 :refer [p3l]]))

;; ===========================================================================
;; Part A. Released stays released
;; ===========================================================================

(a/defn grel-rest [rb :- Bool, w :- World] Bool (Bool.or (Bool.not rb) (:released w)))
(a/defn grel [rb :- Bool, w :- World] Bool (Bool.and (inv-sample w) (grel-rest rb w)))

(a/theorem grel-sample [rb :- Bool, w :- World] (=> (= (grel rb w) true) (= (inv-sample w) true))
  (intro h) (simp only [grel Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem grel-rest-of [rb :- Bool, w :- World] (=> (= (grel rb w) true) (= (grel-rest rb w) true))
  (intro h) (simp only [grel Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem grel-intro [rb :- Bool, w :- World] (=> (= (inv-sample w) true) (= (grel-rest rb w) true) (= (grel rb w) true))
  (intros h1 h2) (simp only [grel h1 h2 Bool.and_self]))
(a/theorem grel-parts [rb :- Bool, w :- World]
  (=> (= (grel rb w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (grel-sample rb w h))))

(a/theorem grel-rest-mark-edge [rb :- Bool, w :- World, x :- Nat] (= (grel-rest rb (mark-edge w x)) (grel-rest rb w))
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [mark-edge hf hm]))))
(a/theorem grel-rest-unmark-edge [rb :- Bool, w :- World, x :- Nat] (= (grel-rest rb (unmark-edge w x)) (grel-rest rb w))
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [unmark-edge hf hm]))))
(a/theorem grel-rest-remove-edge [rb :- Bool, w :- World, x :- Nat] (= (grel-rest rb (remove-edge w x)) (grel-rest rb w))
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]))
  (case [some e] (cases hm (:marked e)) (all_goals (simp only [remove-edge hf hm]))))
(a/theorem grel-rest-set-released [rb :- Bool, w :- World]
  (= (grel-rest rb (set-released w true)) true)
  (simp only [grel-rest set-released Bool.or_true]))

(def GR (mk-bundle 'grel '[rb :- Bool] "grel-" {}))
(swap! (:renames GR) assoc 'inv-parts 'grel-parts)

(doseq [o '[inv-scope-upd inv-pub-upd inv-source-upd inv-resource-upd inv-cleanup-upd inv-cleanup-del inv-set-pins
            inv-resource-del inv-scope-del inv-cleanup-ins inv-act-upd inv-edge-upd inv-drop-cred inv-drop-edges
            inv-comp-del-unref inv-comp-upd inv-drop-act inv-task-upd inv-run-upd inv-run-ins-fresh inv-run-del
            inv-source-ins-fresh inv-resource-ins-fresh inv-scope-ins-fresh inv-comp-ins-fresh inv-act-ins-fresh
            inv-task-ins-fresh inv-bump insert-edge-fresh-inv-sample inv-filter-world inv-set-pending-act]]
  (prim! GR o nil))
(prim! GR 'mark-edge-inv-sample '(Eq.trans (grel-rest-mark-edge rb w x) R))
(prim! GR 'unmark-edge-inv-sample '(Eq.trans (grel-rest-unmark-edge rb w x) R))
(prim! GR 'inv-remove-edge '(Eq.trans (grel-rest-remove-edge rb w x) R))
(override! GR 'inv-revoke-roots '[]
  '(a/theorem grel-revoke-roots [rb :- Bool, w :- World]
     (=> (= (grel rb w) true) (= (grel rb (revoke-roots w)) true))
     (intro h)
     (have r (= (grel-rest rb (revoke-roots w)) true))
     (simp only [grel-rest revoke-roots set-pending-act set-pins drop-edges set-released Bool.or_true])
     (exact (grel-intro rb _ (inv-revoke-roots w (grel-sample rb w h)) r))))

(lcopy! GR 'raw-inv)
(lcopy! GR 'inv-normalize)

(a/theorem grel-rule-r-round [rb :- Bool, w :- World]
  (=> (= (grel rb w) true) (= (filter-safe (normalize w)) true) (= (grel rb (rule-r-round w)) true))
  (intros h hf)
  (simp only [rule-r-round])
  (rw [rule-r-filter-eq])
  (exact (grel-filter-world rb _ (keep-fn (normalize w)) (grel-normalize rb w h) hf)))

(a/theorem grel-rr-loop [rb :- Bool, fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (grel rb w0) true) (= (rr-safe fuel w0) true) (= (grel rb (rr-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 h hs) (simp only [rr-safe] at hs) (simp only [rr-loop]) (exact (grel-rule-r-round rb w0 h hs)))
  (case [cons x f ih]
    (intros w0 h hs)
    (simp only [rr-safe Bool.and_eq_true] at hs)
    (have h1 := (grel-rule-r-round rb w0 h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false] (simp only [ho] at hs) (simp only [rr-loop ho]) (exact (ih (rule-r-round w0) h1 (And.right hs))))
    (case [true] (simp only [rr-loop ho]) (exact h1))))

(a/theorem grel-rule-r [rb :- Bool, w :- World]
  (=> (= (grel rb w) true) (= (rule-r-safe w) true) (= (grel rb (rule-r w)) true))
  (intros h hs) (simp only [rule-r-safe] at hs) (simp only [rule-r]) (exact (grel-rr-loop rb (rr-fuel w) w h hs)))

(a/theorem step-grel [rb :- Bool, w :- World, it :- Item]
  (=> (= (grel rb w) true) (= (rule-r-safe (:world (raw w it))) true) (= (grel rb (:world (world-step w it))) true))
  (intros h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true] (have e2 := (step-accepted w it ha)) (rw [e2]) (exact (grel-rule-r rb (:world (raw w it)) (raw-grel rb w it h) hs))))

;; Theorem (hq, released half): a step from a p3b world keeps a released world released
(a/theorem step-released [w :- World, it :- Item]
  (=> (= (p3b w) true) (= (:released w) true) (= (:released (:world (world-step w it))) true))
  (intros h hr)
  (have g (= (grel true w) true))
  (exact (grel-intro true w (ga-sample w (And.left (p3b-parts w h))) (Eq.trans (congrArg (fn [x :- Bool] (Bool.or false x)) hr) (rfl))))
  (have g2 := (grel-rest-of true _ (step-grel true w it g (step-rule-r-safe w it h))))
  (simp only [grel-rest Bool.not_true Bool.false_or] at g2)
  (exact g2))
