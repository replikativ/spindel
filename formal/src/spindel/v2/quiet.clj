(ns spindel.v2.quiet
  "C1 completion stability, layer 1 (notes/PLAN.md C1, `hq`): a step keeps a released world released
  (`step-released`) and a quiet world (released, no run) quiet.

    grel rb w   inv-sample w and (b -> released w): the bundle copy of every inv-sample lemma of the step
               (`step-grel`), so released stays released (`step-released`).
    gk w       inv-sample w and K: pending-act = 0, no publication row, and once released no pin and no
               host-creditor edge (`gk-rest`); `step-k`, `k-empty`. The copy is generic except where an
               edge is inserted (track, reactivation, await, take: no host root, `host-free`; T8, T22: only
               while not released, raw0's `root-shut`/`host-await-bad`), at pin/unpin and at T21's
               `revoke-roots`.

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

;; ===========================================================================
;; Part B. K: no pending activation, no publication, and once released no pin and no host-creditor
;; edge (the roots T21 revokes stay revoked: T8, T22 and pin are refused by raw0 once released)
;; ===========================================================================

(a/defn pub-absent [p :- PubRow] Bool false)
(a/defn host-free [w :- World, e :- EdgeRow] Bool (Bool.or (Bool.not (:released w)) (not-host e)))
(a/defn gk-rest [w :- World] Bool
  (Bool.and (Nat.beq (:pending-act w) 0)
   (Bool.and (tbl-all pub-absent (:pubs w))
    (Bool.or (Bool.not (:released w)) (Bool.and (nats-empty (:pins w)) (tbl-all not-host (:edges w)))))))
(a/defn gk [w :- World] Bool (Bool.and (inv-sample w) (gk-rest w)))

(a/theorem gk-sample [w :- World] (=> (= (gk w) true) (= (inv-sample w) true))
  (intro h) (simp only [gk Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem gk-rest-of [w :- World] (=> (= (gk w) true) (= (gk-rest w) true))
  (intro h) (simp only [gk Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem gk-intro [w :- World] (=> (= (inv-sample w) true) (= (gk-rest w) true) (= (gk w) true))
  (intros h1 h2) (simp only [gk h1 h2 Bool.and_self]))
(a/theorem gk-parts [w :- World]
  (=> (= (gk w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (gk-sample w h))))

;; the rest part from the fields it reads
(a/theorem gk-rest-mono [w :- World, w2 :- World]
  (=> (= (:pending-act w2) (:pending-act w)) (= (:released w2) (:released w)) (= (:pins w2) (:pins w))
      (=> (= (tbl-all pub-absent (:pubs w)) true) (= (tbl-all pub-absent (:pubs w2)) true))
      (=> (= (tbl-all not-host (:edges w)) true) (= (tbl-all not-host (:edges w2)) true))
      (= (gk-rest w) true) (= (gk-rest w2) true))
  (intros e1 e2 e3 hp he h)
  (simp only [gk-rest Bool.and_eq_true] at h)
  (have p2 := (hp (And.left (And.right h))))
  (have r := (And.right (And.right h)))
  (simp only [gk-rest e1 e2 e3 p2 (And.left h) Bool.true_and])
  (cases hr (:released w))
  (case [false] (simp only [Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [hr Bool.not_true Bool.false_or Bool.and_eq_true] at r)
    (simp only [Bool.not_true Bool.false_or (And.left r) (he (And.right r)) Bool.and_self])))

(a/theorem nh-upd [x :- Nat, f :- (=> EdgeRow EdgeRow),
                   hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                   hc :- (forall [e :- EdgeRow] (= (:creditor (f e)) (:creditor e))), es :- (List EdgeRow)]
  (= (tbl-all not-host (tbl-upd edge-id x f es)) (tbl-all not-host es))
  (have hf (forall [e :- EdgeRow] (= (not-host (f e)) (not-host e))))
  (intro e) (simp only [not-host host-cred (hk e) (hc e)])
  (exact (tbl-all-upd-same EdgeRow edge-id x f not-host hf es)))
(a/theorem pa-all [ps :- (List PubRow)] (=> (= (tbl-all pub-absent ps) true) (= ps (List.nil PubRow)))
  (intro h) (cases ps) (case [nil] (rfl)) (case [cons p t] (simp [tbl-all pub-absent] at h)))

(a/theorem gk-rest-edge-upd [w :- World, x :- Nat, f :- (=> EdgeRow EdgeRow),
                             hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                             hc :- (forall [e :- EdgeRow] (= (:creditor (f e)) (:creditor e)))]
  (=> (= (gk-rest w) true) (= (gk-rest (edge-upd w x f)) true))
  (intro h)
  (have e (= (:edges (edge-upd w x f)) (tbl-upd edge-id x f (:edges w)))) (rfl)
  (exact (gk-rest-mono w (edge-upd w x f) (rfl) (rfl) (rfl) (fn [q :- (= (tbl-all pub-absent (:pubs w)) true)] q)
           (fn [q :- (= (tbl-all not-host (:edges w)) true)] (Eq.trans (congrArg (tbl-all not-host) e) (Eq.trans (nh-upd x f hk hc (:edges w)) q))) h)))
(a/theorem gk-rest-mark-edge [w :- World, x :- Nat] (=> (= (gk-rest w) true) (= (gk-rest (mark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]) (exact h))
  (case [some e] (cases hm (:marked e))
    (case [true] (simp only [mark-edge hf hm]) (exact h))
    (case [false] (simp only [mark-edge hf hm])
      (exact (gk-rest-edge-upd w x (edge-set-marked true) (fn [q :- EdgeRow] (Eq.refl (:kind q))) (fn [q :- EdgeRow] (Eq.refl (:creditor q))) h)))))
(a/theorem gk-rest-unmark-edge [w :- World, x :- Nat] (=> (= (gk-rest w) true) (= (gk-rest (unmark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]) (exact h))
  (case [some e] (cases hm (:marked e))
    (case [false] (simp only [unmark-edge hf hm]) (exact h))
    (case [true] (simp only [unmark-edge hf hm])
      (exact (gk-rest-edge-upd w x (edge-set-marked false) (fn [q :- EdgeRow] (Eq.refl (:kind q))) (fn [q :- EdgeRow] (Eq.refl (:creditor q))) h)))))
(a/theorem gk-rest-edge-del [w :- World, x :- Nat] (=> (= (gk-rest w) true) (= (gk-rest (edge-del w x)) true))
  (intro h)
  (have e (= (:edges (edge-del w x)) (tbl-del edge-id x (:edges w)))) (rfl)
  (exact (gk-rest-mono w (edge-del w x) (rfl) (rfl) (rfl) (fn [q :- (= (tbl-all pub-absent (:pubs w)) true)] q)
           (fn [q :- (= (tbl-all not-host (:edges w)) true)]
             (Eq.trans (congrArg (tbl-all not-host) e)
               (tbl-all-del EdgeRow edge-id x not-host not-host (fn [r :- EdgeRow, a1 :- (= (not-host r) true), a2 :- (= (Nat.beq (edge-id r) x) false)] a1) (:edges w) q))) h)))
(a/theorem gk-rest-remove-edge [w :- World, x :- Nat] (=> (= (gk-rest w) true) (= (gk-rest (remove-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]) (exact h))
  (case [some e] (cases hm (:marked e))
    (all_goals (simp only [remove-edge hf hm]))
    (all_goals (exact (gk-rest-edge-del w x h)))))
(a/theorem gk-rest-filter-edges [w :- World, w2 :- World, p :- (=> EdgeRow Bool)]
  (=> (= (:pending-act w2) (:pending-act w)) (= (:released w2) (:released w)) (= (:pins w2) (:pins w)) (= (:pubs w2) (:pubs w))
      (= (:edges w2) (tbl-filter p (:edges w))) (= (gk-rest w) true) (= (gk-rest w2) true))
  (intros e1 e2 e3 e4 e5 h)
  (exact (gk-rest-mono w w2 e1 e2 e3 (fn [q :- (= (tbl-all pub-absent (:pubs w)) true)] (Eq.trans (congrArg (tbl-all pub-absent) e4) q))
           (fn [q :- (= (tbl-all not-host (:edges w)) true)] (Eq.trans (congrArg (tbl-all not-host) e5) (tbl-all-filter EdgeRow not-host p (:edges w) q))) h)))
(a/theorem gk-rest-drop-cred [w :- World, a :- Nat] (=> (= (gk-rest w) true) (= (gk-rest (drop-cred-edges w a)) true))
  (intro h) (exact (gk-rest-filter-edges w (drop-cred-edges w a) (cred-ne a) (rfl) (rfl) (rfl) (rfl) (rfl) h)))
(a/theorem gk-rest-drop-edges [w :- World, p :- (=> EdgeRow Bool)] (=> (= (gk-rest w) true) (= (gk-rest (drop-edges w p)) true))
  (intro h) (exact (gk-rest-filter-edges w (drop-edges w p) p (rfl) (rfl) (rfl) (rfl) (rfl) h)))
(a/theorem gk-rest-filter [w :- World, K :- (=> Nat Bool)] (=> (= (gk-rest w) true) (= (gk-rest (filter-world K w)) true))
  (intro h)
  (exact (gk-rest-mono w (filter-world K w) (rfl) (rfl) (rfl)
           (fn [q :- (= (tbl-all pub-absent (:pubs w)) true)] (tbl-all-keep-same PubRow K pub-id pub-absent (:pubs w) q))
           (fn [q :- (= (tbl-all not-host (:edges w)) true)] (tbl-all-keep-same EdgeRow K edge-id not-host (:edges w) q)) h)))
(a/theorem gk-rest-pub-upd [w :- World, x :- Nat, f :- (=> PubRow PubRow)] (=> (= (gk-rest w) true) (= (gk-rest (pub-upd w x f)) true))
  (intro h)
  (have e (= (:pubs (pub-upd w x f)) (tbl-upd pub-id x f (:pubs w)))) (rfl)
  (exact (gk-rest-mono w (pub-upd w x f) (rfl) (rfl) (rfl)
           (fn [q :- (= (tbl-all pub-absent (:pubs w)) true)]
             (Eq.trans (congrArg (tbl-all pub-absent) e) (Eq.trans (tbl-all-upd-same PubRow pub-id x f pub-absent (fn [p :- PubRow] (rfl)) (:pubs w)) q)))
           (fn [q :- (= (tbl-all not-host (:edges w)) true)] q) h)))
;; a new edge that is not a host root, or the world is not released
(a/theorem host-free-rel [w :- World, e :- EdgeRow] (=> (= (host-free w e) true) (= (:released w) true) (= (not-host e) true))
  (intros hf hr) (simp only [host-free hr Bool.not_true Bool.false_or] at hf) (exact hf))
(a/theorem nh-cons [x :- EdgeRow, xs :- (List EdgeRow)]
  (=> (= (not-host x) true) (= (tbl-all not-host xs) true) (= (tbl-all not-host (List.cons EdgeRow x xs)) true))
  (intros h1 h2) (simp only [tbl-all h1 h2 Bool.and_self]))
(a/theorem gk-rest-mono-rel [w :- World, w2 :- World]
  (=> (= (:pending-act w2) (:pending-act w)) (= (:released w2) (:released w)) (= (:pins w2) (:pins w))
      (=> (= (tbl-all pub-absent (:pubs w)) true) (= (tbl-all pub-absent (:pubs w2)) true))
      (=> (= (:released w) true) (= (tbl-all not-host (:edges w)) true) (= (tbl-all not-host (:edges w2)) true))
      (= (gk-rest w) true) (= (gk-rest w2) true))
  (intros e1 e2 e3 hp he h)
  (simp only [gk-rest Bool.and_eq_true] at h)
  (have p2 := (hp (And.left (And.right h))))
  (have r := (And.right (And.right h)))
  (simp only [gk-rest e1 e2 e3 p2 (And.left h) Bool.true_and])
  (cases hr (:released w))
  (case [false] (simp only [Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [hr Bool.not_true Bool.false_or Bool.and_eq_true] at r)
    (simp only [Bool.not_true Bool.false_or (And.left r) (he hr (And.right r)) Bool.and_self])))
;; a new edge that is not a host root, or the world is not released
(a/theorem gk-rest-insert [w :- World, e :- EdgeRow] (=> (= (host-free w e) true) (= (gk-rest w) true) (= (gk-rest (insert-edge-fresh w e)) true))
  (intros hf h)
  (have e1 (= (:edges (insert-edge-fresh w e)) (List.cons EdgeRow (edge-set-marked false (edge-set-id (:next-id w) e)) (:edges w)))) (rfl)
  (have nh (= (not-host (edge-set-marked false (edge-set-id (:next-id w) e))) (not-host e))) (rfl)
  (exact (gk-rest-mono-rel w (insert-edge-fresh w e) (rfl) (rfl) (rfl) (fn [q :- (= (tbl-all pub-absent (:pubs w)) true)] q)
           (fn [hr :- (= (:released w) true), q :- (= (tbl-all not-host (:edges w)) true)]
             (Eq.trans (congrArg (tbl-all not-host) e1) (nh-cons _ _ (Eq.trans nh (host-free-rel w e hf hr)) q)))
           h)))

(a/theorem gk-insert-edge-fresh [w :- World, e :- EdgeRow]
  (=> (= (edge-ok-in w e) true) (= (host-free w e) true) (= (gk w) true) (= (gk (insert-edge-fresh w e)) true))
  (intros he hf h)
  (exact (gk-intro _ (insert-edge-fresh-inv-sample w e he (gk-sample w h)) (gk-rest-insert w e hf (gk-rest-of w h)))))
(a/theorem gk-insert-edge-checked [w :- World, e :- EdgeRow]
  (=> (= (host-free w e) true) (= (gk w) true) (= (gk (insert-edge-checked w e)) true))
  (intros hf h)
  (cases hk (edge-ok-in w e))
  (case [false] (simp only [insert-edge-checked hk]) (exact h))
  (case [true] (simp only [insert-edge-checked hk]) (exact (gk-insert-edge-fresh w e hk hf h))))
(a/theorem host-free-nh [w :- World, e :- EdgeRow] (=> (= (not-host e) true) (= (host-free w e) true))
  (intro h) (simp only [host-free h Bool.or_true]))
(a/theorem host-free-open [w :- World, e :- EdgeRow] (=> (= (root-shut w) false) (= (host-free w e) true))
  (intro h) (simp only [root-shut] at h) (simp only [host-free h Bool.not_false Bool.true_or]))
(a/theorem host-await-root [w :- World, d :- Nat] (=> (= (host-await-bad w d) false) (= (root-shut w) false))
  (intro h) (cases hr (root-shut w)) (case [false] (rfl)) (case [true] (simp [host-await-bad hr] at h)))
(a/theorem next-pos [w :- World] (=> (= (inv-sample w) true) (= (Nat.beq (:next-id w) 0) false))
  (intro h)
  (have p := (And.right (And.right (inv-parts w h))))
  (simp only [ids-ok ids-below Bool.and_eq_true Nat.blt_eq] at p)
  (have q := (And.left (And.right p)))
  (cases hb (Nat.beq (:next-id w) 0)) (case [false] (rfl))
  (case [true] (have z := (Nat.eq_of_beq_eq_true hb)) (omega)))
(a/theorem take-edge-nh [r :- RunRow, w :- World, x :- Nat] (=> (= (inv-sample w) true) (= (not-host (take-edge r (:next-id w) x)) true))
  (intro h) (simp only [not-host host-cred take-edge ek-wait ek-observe (next-pos w h)]))

;; ---- the GK copy
(def GK (mk-bundle 'gk [] "gk-" {}))
(swap! (:renames GK) assoc 'inv-parts 'gk-parts
       'insert-edge-fresh-inv-sample 'gk-insert-edge-fresh 'inv-insert-edge-checked 'gk-insert-edge-checked)

(doseq [o '[inv-scope-upd inv-source-upd inv-resource-upd inv-cleanup-upd inv-cleanup-del inv-resource-del inv-scope-del
            inv-cleanup-ins inv-act-upd inv-comp-del-unref inv-comp-upd inv-task-upd inv-run-upd
            inv-run-ins-fresh inv-run-del inv-source-ins-fresh inv-resource-ins-fresh inv-scope-ins-fresh inv-comp-ins-fresh
            inv-act-ins-fresh inv-task-ins-fresh inv-bump]]
  (prim! GK o nil))
(prim! GK 'inv-edge-upd '(gk-rest-edge-upd w x f hk hc R))
(prim! GK 'mark-edge-inv-sample '(gk-rest-mark-edge w x R))
(prim! GK 'unmark-edge-inv-sample '(gk-rest-unmark-edge w x R))
(prim! GK 'inv-remove-edge '(gk-rest-remove-edge w x R))
(prim! GK 'inv-drop-cred '(gk-rest-drop-cred w a R))
(prim! GK 'inv-drop-act '(gk-rest-drop-cred w a R))
(prim! GK 'inv-drop-edges '(gk-rest-drop-edges w p R))
(prim! GK 'inv-filter-world '(gk-rest-filter w K R))
(prim! GK 'inv-pub-upd '(gk-rest-pub-upd w x f R))

;; a source theorem with one more premise (named hn) in front
(defn- add-premise [prem hn form]
  (let [[hd nm binders stmt & proof] form
        stmt2 (if (and (seq? stmt) (= '=> (first stmt))) (apply list '=> prem (rest stmt)) (list '=> prem stmt))
        [t1 & more] proof
        t1b (cond (and (seq? t1) (= 'intro (first t1))) [(list 'intros hn (second t1))]
                  (and (seq? t1) (= 'intros (first t1))) [(apply list 'intros hn (rest t1))]
                  :else [(list 'intro hn) t1])]
    (apply list hd nm binders stmt2 (concat t1b more))))
(defn- repl-form [old new] (fn [form] (subst-forms #(= % old) (fn [_] new) form)))

;; edges that are no host root: track, reactivation (dep edges), await (a dep edge, or a wait edge
;; whose creditor is the fresh activation), take (a wait edge, creditor the fresh activation)
(patch! GK 'inv-track-raw
  (repl-form '(insert-edge-fresh-inv-sample w (track-edge r x s k) (track-edge-ok w r x s k hc hs) h)
             '(insert-edge-fresh-inv-sample w (track-edge r x s k) (track-edge-ok w r x s k hc hs) (host-free-nh w (track-edge r x s k) (Eq.refl true)) h)))
(patch! GK 'inv-react-add
  (repl-form '(inv-insert-edge-checked w _ h) '(inv-insert-edge-checked w (valid-edge w c v) (host-free-nh w (valid-edge w c v) (Eq.refl true)) h)))
(a/theorem await-edge-nh [w :- World, r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, d :- Nat]
  (=> (= (Nat.beq a 0) false) (= (not-host (await-edge w r a mode k d)) true))
  (intro ha)
  (cases hd (as-dep w r d))
  (all_goals (simp only [not-host host-cred await-edge hd ek-wait ek-dep ek-observe ha])))
(patch! GK 'inv-await-step
  (fn [form] (->> form
                  (add-premise '(= (Nat.beq a 0) false) 'ha0)
                  (subst-forms #(= % '(inv-insert-edge-checked _ _ h))
                               (fn [_] '(inv-insert-edge-checked _ _ (host-free-nh _ _ (await-edge-nh _ r a mode k d ha0)) h))))))
(patch! GK 'inv-await-wire
  (fn [form] (->> form
                  (add-premise '(= (Nat.beq a 0) false) 'ha0)
                  (subst-forms #(= % '(inv-await-step r a mode k acc d h)) (fn [_] '(inv-await-step r a mode k acc d ha0 h))))))
(patch! GK 'inv-await-raw
  (fn [form] (subst-forms #(and (seq? %) (= 'inv-await-wire (first %)))
                          (fn [[hd r n m k ds & more]] (apply list hd r n m k ds '(next-pos w (gk-sample w h)) more)) form)))
(patch! GK 'inv-take-park
  (repl-form '(inv-insert-edge-checked _ _ (inv-act-ins-fresh w (take-act w r k) (rfl) h))
             '(inv-insert-edge-checked _ (take-edge r (:next-id w) x) (host-free-nh _ _ (take-edge-nh r w x (gk-sample w h)))
                (inv-act-ins-fresh w (take-act w r k) (rfl) h))))

;; host roots: T8 and T22 add one, refused by raw0 once released (root-shut, host-await-bad); pin
(patch! GK 't8-full-inv
  (fn [form] (->> form
                  (add-premise '(= (root-shut w) false) 'hr0)
                  (subst-forms #(= % '(insert-edge-fresh-inv-sample w (observe-edge w d cb) he h))
                               (fn [_] '(insert-edge-fresh-inv-sample w (observe-edge w d cb) he (host-free-open w _ hr0) h))))))
(patch! GK 't8-obs-inv
  (fn [form] (->> form
                  (add-premise '(= (root-shut w) false) 'hr0)
                  (subst-forms #(= % '(t8-full-inv w d cb fresh h)) (fn [_] '(t8-full-inv w d cb fresh hr0 h))))))
(patch! GK 'inv-host-await-raw
  (fn [form] (->> form
                  (add-premise '(= (root-shut w) false) 'hr0)
                  (subst-forms #(= % '(inv-insert-edge-checked w (host-wait-edge d) h))
                               (fn [_] '(inv-insert-edge-checked w (host-wait-edge d) (host-free-open w _ hr0) h))))))
(patch! GK 't22-inv
  (fn [form] (->> form
                  (add-premise '(= (root-shut w) false) 'hr0)
                  (subst-forms #(= % '(inv-host-await-raw w d h)) (fn [_] '(inv-host-await-raw w d hr0 h))))))
(a/theorem gk-set-pins-cons [w :- World, x :- Nat] (=> (= (root-shut w) false) (= (gk-rest w) true) (= (gk-rest (set-pins w (List.cons Nat x (:pins w)))) true))
  (intros hr h) (simp only [root-shut] at hr)
  (simp only [gk-rest Bool.and_eq_true] at h)
  (have hr2 (= (:released (set-pins w (List.cons Nat x (:pins w)))) false)) (exact hr)
  (simp only [gk-rest hr2 Bool.not_false Bool.or_true Bool.and_true])
  (simp only [Bool.and_eq_true]) (exact (And.intro (And.left h) (And.intro (And.left (And.right h)) True.intro))))
(a/theorem nat-del1-empty [x :- Nat, xs :- (List Nat)] (=> (= (nats-empty xs) true) (= (nats-empty (nat-del1 x xs)) true))
  (intro h) (cases xs) (case [nil] (simp only [nat-del1 nats-empty])) (case [cons y t] (simp [nats-empty] at h)))
(a/theorem gk-set-pins-del [w :- World, x :- Nat] (=> (= (gk-rest w) true) (= (gk-rest (set-pins w (nat-del1 x (:pins w)))) true))
  (intro h)
  (simp only [gk-rest Bool.and_eq_true] at h)
  (have r := (And.right (And.right h)))
  (cases hr (:released w))
  (case [false]
    (have hr2 (= (:released (set-pins w (nat-del1 x (:pins w)))) false)) (exact hr)
    (simp only [gk-rest hr2 Bool.not_false Bool.or_true Bool.and_true])
    (simp only [Bool.and_eq_true]) (exact (And.intro (And.left h) (And.intro (And.left (And.right h)) True.intro))))
  (case [true]
    (simp only [hr Bool.not_true Bool.false_or Bool.and_eq_true] at r)
    (have hr2 (= (:released (set-pins w (nat-del1 x (:pins w)))) true)) (exact hr)
    (have p := (nat-del1-empty x (:pins w) (And.left r)))
    (have e1 (= (:pins (set-pins w (nat-del1 x (:pins w)))) (nat-del1 x (:pins w)))) (rfl)
    (simp only [gk-rest hr2 e1 p (And.left h) (And.left (And.right h)) (And.right r) Bool.not_true Bool.false_or Bool.and_self])))
(override! GK 't20-pin-inv '[]
  '(a/theorem t20-pin-gk [w :- World, x :- Nat]
     (=> (= (root-shut w) false) (= (gk w) true) (= (gk (:world (t20-pin w x))) true))
     (intros hr0 h)
     (cases hg (Bool.or (comp-has w x) (source-has w x)))
     (simp only [t20-pin hg refuse]) (exact h)
     (simp only [t20-pin hg accept])
     (exact (gk-intro _ (inv-set-pins w (List.cons Nat x (:pins w)) (gk-sample w h)) (gk-set-pins-cons w x hr0 (gk-rest-of w h))))))
(override! GK 't20-unpin-inv '[]
  '(a/theorem t20-unpin-gk [w :- World, x :- Nat]
     (=> (= (gk w) true) (= (gk (:world (t20-unpin w x))) true))
     (intro h)
     (cases hm (nat-mem x (:pins w)))
     (simp only [t20-unpin hm refuse]) (exact h)
     (simp only [t20-unpin hm accept])
     (exact (gk-intro _ (inv-set-pins w (nat-del1 x (:pins w)) (gk-sample w h)) (gk-set-pins-del w x (gk-rest-of w h))))))
;; T21 revokes the roots: no pin, no host-creditor edge, no pending activation
(a/theorem gk-rest-revoke [w :- World] (=> (= (gk-rest w) true) (= (gk-rest (revoke-roots w)) true))
  (intro h)
  (simp only [gk-rest Bool.and_eq_true] at h)
  (have e1 (= (:edges (revoke-roots w)) (tbl-filter not-host (:edges w)))) (rfl)
  (have e2 (= (:pubs (revoke-roots w)) (:pubs w))) (rfl)
  (have e3 (= (:released (revoke-roots w)) true)) (rfl)
  (have e4 (= (:pins (revoke-roots w)) (List.nil Nat))) (rfl)
  (have e5 (= (:pending-act (revoke-roots w)) 0)) (rfl)
  (simp only [gk-rest e1 e2 e3 e4 e5 (And.left (And.right h)) (tbl-all-filter-self EdgeRow not-host (:edges w))
              nats-empty Nat.beq_refl Bool.not_true Bool.false_or Bool.and_self]))
(override! GK 'inv-revoke-roots '[]
  '(a/theorem gk-revoke-roots [w :- World]
     (=> (= (gk w) true) (= (gk (revoke-roots w)) true))
     (intro h)
     (exact (gk-intro _ (inv-revoke-roots w (gk-sample w h)) (gk-rest-revoke w (gk-rest-of w h))))))

;; raw0: the guards give the hypotheses
(patch! GK 'raw0-inv
  (fn [form] (->> form
                  (subst-forms #(= % '(t8-obs-inv w _ _ _ h)) (fn [_] '(t8-obs-inv w _ _ _ hc h)))
                  (subst-forms #(= % '(t20-pin-inv w _ h)) (fn [_] '(t20-pin-inv w _ hc h)))
                  (subst-forms #(= % '(t22-inv w _ _ h)) (fn [_] '(t22-inv w _ _ (host-await-root w _ hc) h))))))

(lcopy! GK 'raw-inv)
(lcopy! GK 'inv-normalize)

(a/theorem gk-rule-r-round [w :- World]
  (=> (= (gk w) true) (= (filter-safe (normalize w)) true) (= (gk (rule-r-round w)) true))
  (intros h hf)
  (simp only [rule-r-round])
  (rw [rule-r-filter-eq])
  (exact (gk-filter-world _ (keep-fn (normalize w)) (gk-normalize w h) hf)))

(a/theorem gk-rr-loop [fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (gk w0) true) (= (rr-safe fuel w0) true) (= (gk (rr-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 h hs) (simp only [rr-safe] at hs) (simp only [rr-loop]) (exact (gk-rule-r-round w0 h hs)))
  (case [cons x f ih]
    (intros w0 h hs)
    (simp only [rr-safe Bool.and_eq_true] at hs)
    (have h1 := (gk-rule-r-round w0 h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false] (simp only [ho] at hs) (simp only [rr-loop ho]) (exact (ih (rule-r-round w0) h1 (And.right hs))))
    (case [true] (simp only [rr-loop ho]) (exact h1))))

(a/theorem gk-rule-r [w :- World]
  (=> (= (gk w) true) (= (rule-r-safe w) true) (= (gk (rule-r w)) true))
  (intros h hs) (simp only [rule-r-safe] at hs) (simp only [rule-r]) (exact (gk-rr-loop (rr-fuel w) w h hs)))

(a/theorem step-gk [w :- World, it :- Item]
  (=> (= (gk w) true) (= (rule-r-safe (:world (raw w it))) true) (= (gk (:world (world-step w it))) true))
  (intros h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true] (have e2 := (step-accepted w it ha)) (rw [e2]) (exact (gk-rule-r (:world (raw w it)) (raw-gk w it h) hs))))

;; Theorem (K): no pending activation, no publication, and once released no pin and no host-creditor
;; edge, through every step from a p3b world; the empty world has it
(a/theorem step-k [w :- World, it :- Item]
  (=> (= (p3b w) true) (= (gk-rest w) true) (= (gk-rest (:world (world-step w it))) true))
  (intros h hk)
  (exact (gk-rest-of _ (step-gk w it (gk-intro w (ga-sample w (And.left (p3b-parts w h))) hk) (step-rule-r-safe w it h)))))
(a/theorem k-empty [] (= (gk-rest empty-world) true) (rfl))
