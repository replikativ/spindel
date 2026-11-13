(ns spindel.v2.i1r
  "Literal I1, the remaining clauses (resource owners; run entities and scopes) through `world-step`,
  kernel-checked (Init only), and with spindel.v2.i1 / spindel.v2.i1o all of literal I1 (`inv-i1`).

  Bundle grx xr w = inv-sample w && R1 (every resource's owner run exists and holds it, every run row
  with the owner's id lists it) && R2 (every run's entity and scope exist) && R3 (every run is alive,
  has a cleanup entry, or is exempt: in xr). gr0 = grx [] (no exemption).
    - A run made done joins the exemptions until its cleanup entry is set (`grx-run-upd-x`,
      `grx-cleanup-set`): T14's local part (`grx-cancel-run-local`).
    - T12 (`gr0-complete-raw`, with ga): a run that completes retirable has no cleanup entry; its
      retire job is the cascade's last, the cascade's worklist empties (P4, `casc-done-ga`), and the
      job retires it (`track-cascade` over the bundles krb: the rows of the run stay retirable, neb:
      no row of the run is made again).
    - T13 (`grx-retire-with`): a retirable run lists no resource, so no resource is owned by it.
    - Demotion deletes a computation only when no run of it is left (`gr0-demote-aa`: the demote's
      cascade kills its alive runs, P4 with acts-alive; a dead run has a cleanup entry that stores its
      entity, so demote-keep holds) — normalization is threaded with acts-alive (P2's bundle bn).
    - Rule R's filter keeps every run (`run-kept`: an alive run is live, normalized; a dead run's
      cleanup entry stores it) and with it the run's entity and scope (live closure / cleanup rows)
      and every resource's owner (`gr0-filter`).
  GRX is copied over T12's cascade, GR0 reuses every GRX lemma at [] and threads ga into T12
  (patched t12-inv/raw0-inv/raw0g-inv/raw-inv).

  Theorems:
    step-gr0             ga w, gr0 w, rule-r-safe raw -> gr0 (world-step w it)
    p3h = p3g && gr0     step-p3h, p3h-empty
    step-lit-i1-total    p3h w -> inv-i1 (world-step w it)     (literal I1, every clause)"
  (:require [ansatz.core :as a]
            [clojure.walk]
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
            [spindel.v2.i1o :refer :all]))

;; ---- R1: a resource's owner run exists and lists it (every run row with its id lists it)
(a/defn res-held [z :- ResRow, r :- RunRow] Bool (Bool.and (Nat.beq (:id r) (:owner z)) (nat-mem (:id z) (:resources r))))
(a/defn r1-ok [rs :- (List RunRow), z :- ResRow] Bool (Bool.and (tbl-any (res-held z) rs) (tbl-all (listed-in z) rs)))
;; ---- R2: a run's entity and scope exist
(a/defn r2-ok [w :- World, r :- RunRow] Bool
  (Bool.and (Bool.or (comp-has w (:of r)) (task-has w (:of r))) (scope-has w (:scope r))))
;; ---- R3: a run is not done, or it has a cleanup entry, or it is exempt
(a/defn r3-ok [cl :- (List CleanupRow), xr :- (List Nat), r :- RunRow] Bool
  (Bool.or (run-alive r) (Bool.or (tbl-has cleanup-id (:id r) cl) (reach-mem (:id r) xr))))
(a/defn grk-rest [xr :- (List Nat), w :- World] Bool
  (Bool.and (tbl-all (r1-ok (:runs w)) (:res w))
   (Bool.and (tbl-all (r2-ok w) (:runs w)) (tbl-all (r3-ok (:cleanup w) xr) (:runs w)))))
(a/defn grx [xr :- (List Nat), w :- World] Bool (Bool.and (inv-sample w) (grk-rest xr w)))
(a/defn gr0 [w :- World] Bool (grx (List.nil Nat) w))
(a/defn gr0-rest [w :- World] Bool (grk-rest (List.nil Nat) w))

(a/theorem grx-sample [xr :- (List Nat), w :- World] (=> (= (grx xr w) true) (= (inv-sample w) true))
  (intro h) (simp only [grx Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem grx-rest-of [xr :- (List Nat), w :- World] (=> (= (grx xr w) true) (= (grk-rest xr w) true))
  (intro h) (simp only [grx Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem grx-intro [xr :- (List Nat), w :- World] (=> (= (inv-sample w) true) (= (grk-rest xr w) true) (= (grx xr w) true))
  (intros h1 h2) (simp only [grx h1 h2 Bool.and_self]))
(a/theorem grx-parts [xr :- (List Nat), w :- World]
  (=> (= (grx xr w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (grx-sample xr w h))))
(a/theorem gr0-sample [w :- World] (=> (= (gr0 w) true) (= (inv-sample w) true)) (intro h) (exact (grx-sample (List.nil Nat) w h)))
(a/theorem gr0-rest-of [w :- World] (=> (= (gr0 w) true) (= (gr0-rest w) true)) (intro h) (exact (grx-rest-of (List.nil Nat) w h)))
(a/theorem gr0-intro [w :- World] (=> (= (inv-sample w) true) (= (gr0-rest w) true) (= (gr0 w) true))
  (intros h1 h2) (exact (grx-intro (List.nil Nat) w h1 h2)))
(a/theorem gr0-parts [w :- World]
  (=> (= (gr0 w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (gr0-sample w h))))

(a/theorem grk-mk [xr :- (List Nat), w :- World]
  (=> (= (tbl-all (r1-ok (:runs w)) (:res w)) true) (= (tbl-all (r2-ok w) (:runs w)) true) (= (tbl-all (r3-ok (:cleanup w) xr) (:runs w)) true)
      (= (grk-rest xr w) true))
  (intros h1 h2 h3) (simp only [grk-rest h1 h2 h3 Bool.and_self]))
(a/theorem grk-1 [xr :- (List Nat), w :- World] (=> (= (grk-rest xr w) true) (= (tbl-all (r1-ok (:runs w)) (:res w)) true))
  (intro h) (simp only [grk-rest Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem grk-2 [xr :- (List Nat), w :- World] (=> (= (grk-rest xr w) true) (= (tbl-all (r2-ok w) (:runs w)) true))
  (intro h) (simp only [grk-rest Bool.and_eq_true] at h) (exact (And.left (And.right h))))
(a/theorem grk-3 [xr :- (List Nat), w :- World] (=> (= (grk-rest xr w) true) (= (tbl-all (r3-ok (:cleanup w) xr) (:runs w)) true))
  (intro h) (simp only [grk-rest Bool.and_eq_true] at h) (exact (And.right (And.right h))))

;; ---- frames: the run, resource and cleanup tables fixed, existence of computations, tasks, scopes only grows
(a/theorem grk-frame [xr :- (List Nat), w :- World, w2 :- World]
  (=> (= (:runs w2) (:runs w)) (= (:res w2) (:res w)) (= (:cleanup w2) (:cleanup w))
      (forall [x :- Nat] (=> (= (comp-has w x) true) (= (comp-has w2 x) true)))
      (forall [x :- Nat] (=> (= (task-has w x) true) (= (task-has w2 x) true)))
      (forall [x :- Nat] (=> (= (scope-has w x) true) (= (scope-has w2 x) true)))
      (= (grk-rest xr w) true) (= (grk-rest xr w2) true))
  (intros e1 e2 e3 hc ht hs h)
  (have a1 := (grk-1 xr w h)) (have a2 := (grk-2 xr w h)) (have a3 := (grk-3 xr w h))
  (apply (grk-mk xr w2))
  (rw [e1 e2]) (exact a1)
  (rw [e1])
  (apply (tbl-all-mono RunRow (r2-ok w) (r2-ok w2) _ (:runs w) a2))
  (intros r hr)
  (simp only [r2-ok Bool.and_eq_true Bool.or_eq_true] at hr)
  (simp only [r2-ok Bool.and_eq_true Bool.or_eq_true])
  (have q := (And.left hr))
  (apply And.intro)
  (cases q) (case [inl a] (exact (Or.inl (hc _ a)))) (case [inr b] (exact (Or.inr (ht _ b))))
  (exact (hs _ (And.right hr)))
  (rw [e1 e3]) (exact a3))

(a/theorem grx-frame [xr :- (List Nat), w :- World, w2 :- World]
  (=> (= (inv-sample w2) true) (= (:runs w2) (:runs w)) (= (:res w2) (:res w)) (= (:cleanup w2) (:cleanup w))
      (forall [x :- Nat] (=> (= (comp-has w x) true) (= (comp-has w2 x) true)))
      (forall [x :- Nat] (=> (= (task-has w x) true) (= (task-has w2 x) true)))
      (forall [x :- Nat] (=> (= (scope-has w x) true) (= (scope-has w2 x) true)))
      (= (grx xr w) true) (= (grx xr w2) true))
  (intros hs e1 e2 e3 hc ht hsc h)
  (exact (grx-intro xr w2 hs (grk-frame xr w w2 e1 e2 e3 hc ht hsc (grx-rest-of xr w h)))))

(a/theorem grx-comp-upd [xr :- (List Nat), w :- World, x :- Nat, f :- (=> CompRow CompRow),
                         hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                         hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c)))]
  (=> (= (grx xr w) true) (= (grx xr (comp-upd w x f)) true))
  (intro h)
  (exact (grx-frame xr w _ (inv-comp-upd w x f hid hp (grx-sample xr w h)) (rfl) (rfl) (rfl)
           (fn [y :- Nat, q :- (= (comp-has w y) true)] (Eq.trans (tbl-has-upd CompRow comp-id x y f hid (:comps w)) q))
           (fn [y :- Nat, q :- (= (task-has w y) true)] q) (fn [y :- Nat, q :- (= (scope-has w y) true)] q) h)))
(a/theorem grx-task-upd [xr :- (List Nat), w :- World, x :- Nat, f :- (=> TaskRow TaskRow),
                         hid :- (forall [c :- TaskRow] (= (task-id (f c)) (task-id c)))]
  (=> (= (grx xr w) true) (= (grx xr (task-upd w x f)) true))
  (intro h)
  (exact (grx-frame xr w _ (inv-task-upd w x f hid (grx-sample xr w h)) (rfl) (rfl) (rfl)
           (fn [y :- Nat, q :- (= (comp-has w y) true)] q)
           (fn [y :- Nat, q :- (= (task-has w y) true)] (Eq.trans (tbl-has-upd TaskRow task-id x y f hid (:tasks w)) q))
           (fn [y :- Nat, q :- (= (scope-has w y) true)] q) h)))
(a/theorem grx-scope-upd [xr :- (List Nat), w :- World, x :- Nat, f :- (=> ScopeRow ScopeRow),
                          hid :- (forall [c :- ScopeRow] (= (scope-id (f c)) (scope-id c)))]
  (=> (= (grx xr w) true) (= (grx xr (scope-upd w x f)) true))
  (intro h)
  (exact (grx-frame xr w _ (inv-scope-upd w x f hid (grx-sample xr w h)) (rfl) (rfl) (rfl)
           (fn [y :- Nat, q :- (= (comp-has w y) true)] q) (fn [y :- Nat, q :- (= (task-has w y) true)] q)
           (fn [y :- Nat, q :- (= (scope-has w y) true)] (Eq.trans (tbl-has-upd ScopeRow scope-id x y f hid (:scopes w)) q)) h)))
(a/theorem has-ins-of [A :- Type, idf :- (=> A Nat), r :- A, xs :- (List A), y :- Nat]
  (=> (= (tbl-has idf y xs) true) (= (tbl-has idf y (tbl-ins r xs)) true))
  (intro h) (simp only [tbl-has-ins h Bool.or_true]))
(a/theorem grx-comp-ins [xr :- (List Nat), w :- World, r :- CompRow]
  (=> (= (comp-id r) (:next-id w)) (= (:pending r) (marked-in (:id r) (:edges w))) (= (grx xr w) true) (= (grx xr (bump (comp-ins w r))) true))
  (intros hi hp h)
  (exact (grx-frame xr w _ (inv-comp-ins-fresh w r hi hp (grx-sample xr w h)) (rfl) (rfl) (rfl)
           (fn [y :- Nat, q :- (= (comp-has w y) true)] (has-ins-of CompRow comp-id r (:comps w) y q))
           (fn [y :- Nat, q :- (= (task-has w y) true)] q) (fn [y :- Nat, q :- (= (scope-has w y) true)] q) h)))
(a/theorem grx-task-ins [xr :- (List Nat), w :- World, r :- TaskRow]
  (=> (= (task-id r) (:next-id w)) (= (grx xr w) true) (= (grx xr (bump (task-ins w r))) true))
  (intros hi h)
  (exact (grx-frame xr w _ (inv-task-ins-fresh w r hi (grx-sample xr w h)) (rfl) (rfl) (rfl)
           (fn [y :- Nat, q :- (= (comp-has w y) true)] q)
           (fn [y :- Nat, q :- (= (task-has w y) true)] (has-ins-of TaskRow task-id r (:tasks w) y q))
           (fn [y :- Nat, q :- (= (scope-has w y) true)] q) h)))
(a/theorem grx-scope-ins [xr :- (List Nat), w :- World, r :- ScopeRow]
  (=> (= (scope-id r) (:next-id w)) (= (grx xr w) true) (= (grx xr (bump (scope-ins w r))) true))
  (intros hi h)
  (exact (grx-frame xr w _ (inv-scope-ins-fresh w r hi (grx-sample xr w h)) (rfl) (rfl) (rfl)
           (fn [y :- Nat, q :- (= (comp-has w y) true)] q) (fn [y :- Nat, q :- (= (task-has w y) true)] q)
           (fn [y :- Nat, q :- (= (scope-has w y) true)] (has-ins-of ScopeRow scope-id r (:scopes w) y q)) h)))

;; ---- edge edits (pending of creditors only)
(a/theorem has-resync [es :- (List EdgeRow), cs :- (List CompRow), y :- Nat] (= (tbl-has comp-id y (comps-resync es cs)) (tbl-has comp-id y cs))
  (induction cs) (case [nil] (simp only [comps-resync tbl-has])) (case [cons h t ih] (simp only [comps-resync tbl-has ih comp-resync comp-set-pending comp-id])))
(a/theorem cpend-has [w :- World, x :- Nat, f :- (=> CompRow CompRow), hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))), y :- Nat]
  (=> (= (comp-has w y) true) (= (comp-has (comp-upd w x f) y) true))
  (intro q) (exact (Eq.trans (tbl-has-upd CompRow comp-id x y f hid (:comps w)) q)))
(a/theorem grk-remove-edge [xr :- (List Nat), w :- World, x :- Nat] (=> (= (grk-rest xr w) true) (= (grk-rest xr (remove-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [remove-edge hf hm])
      (exact (grk-frame xr w (edge-del w x) (rfl) (rfl) (rfl) (fn [y :- Nat, q :- (= (comp-has w y) true)] q)
               (fn [y :- Nat, q :- (= (task-has w y) true)] q) (fn [y :- Nat, q :- (= (scope-has w y) true)] q) h)))
    (case [true] (simp only [remove-edge hf hm])
      (exact (grk-frame xr w (comp-upd (edge-del w x) (:creditor e) comp-dec-pending) (rfl) (rfl) (rfl)
               (fn [y :- Nat, q :- (= (comp-has w y) true)] (cpend-has (edge-del w x) (:creditor e) comp-dec-pending (fn [c :- CompRow] (Eq.refl (comp-id c))) y q))
               (fn [y :- Nat, q :- (= (task-has w y) true)] q) (fn [y :- Nat, q :- (= (scope-has w y) true)] q) h)))))
(a/theorem grk-mark-edge [xr :- (List Nat), w :- World, x :- Nat] (=> (= (grk-rest xr w) true) (= (grk-rest xr (mark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [true] (simp only [mark-edge hf hm]) (exact h))
    (case [false] (simp only [mark-edge hf hm])
      (exact (grk-frame xr w (comp-upd (edge-upd w x (edge-set-marked true)) (:creditor e) comp-inc-pending) (rfl) (rfl) (rfl)
               (fn [y :- Nat, q :- (= (comp-has w y) true)] (cpend-has (edge-upd w x (edge-set-marked true)) (:creditor e) comp-inc-pending (fn [c :- CompRow] (Eq.refl (comp-id c))) y q))
               (fn [y :- Nat, q :- (= (task-has w y) true)] q) (fn [y :- Nat, q :- (= (scope-has w y) true)] q) h)))))
(a/theorem grk-unmark-edge [xr :- (List Nat), w :- World, x :- Nat] (=> (= (grk-rest xr w) true) (= (grk-rest xr (unmark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [unmark-edge hf hm]) (exact h))
    (case [true] (simp only [unmark-edge hf hm])
      (exact (grk-frame xr w (comp-upd (edge-upd w x (edge-set-marked false)) (:creditor e) comp-dec-pending) (rfl) (rfl) (rfl)
               (fn [y :- Nat, q :- (= (comp-has w y) true)] (cpend-has (edge-upd w x (edge-set-marked false)) (:creditor e) comp-dec-pending (fn [c :- CompRow] (Eq.refl (comp-id c))) y q))
               (fn [y :- Nat, q :- (= (task-has w y) true)] q) (fn [y :- Nat, q :- (= (scope-has w y) true)] q) h)))))
(a/theorem grk-drop-cred [xr :- (List Nat), w :- World, a :- Nat] (=> (= (grk-rest xr w) true) (= (grk-rest xr (drop-cred-edges w a)) true))
  (intro h)
  (exact (grk-frame xr w (drop-cred-edges w a) (rfl) (rfl) (rfl)
           (fn [y :- Nat, q :- (= (comp-has w y) true)] (cpend-has (set-edges w (tbl-filter (cred-ne a) (:edges w))) a (comp-set-pending 0) (fn [c :- CompRow] (Eq.refl (comp-id c))) y q))
           (fn [y :- Nat, q :- (= (task-has w y) true)] q) (fn [y :- Nat, q :- (= (scope-has w y) true)] q) h)))
(a/theorem grk-drop-act [xr :- (List Nat), w :- World, a :- Nat] (=> (= (grk-rest xr w) true) (= (grk-rest xr (drop-act w a)) true))
  (intro h) (exact (grk-drop-cred xr w a h)))
(a/theorem grk-drop-edges [xr :- (List Nat), w :- World, p :- (=> EdgeRow Bool)] (=> (= (grk-rest xr w) true) (= (grk-rest xr (drop-edges w p)) true))
  (intro h)
  (exact (grk-frame xr w (drop-edges w p) (rfl) (rfl) (rfl)
           (fn [y :- Nat, q :- (= (comp-has w y) true)] (Eq.trans (has-resync (tbl-filter p (:edges w)) (:comps w) y) q))
           (fn [y :- Nat, q :- (= (task-has w y) true)] q) (fn [y :- Nat, q :- (= (scope-has w y) true)] q) h)))

;; ---- run rows: an edit that keeps (id, entity, scope, alive, resources)
(a/structure RKR [] (id Nat) (of Nat) (scope Nat) (alive Bool) (res (List Nat)))
(a/defn rkr [r :- RunRow] RKR (RKR.mk (:id r) (:of r) (:scope r) (run-alive r) (:resources r)))
(a/theorem rkr-held [z :- ResRow, q :- RunRow, q2 :- RunRow] (=> (= (rkr q2) (rkr q)) (= (res-held z q2) (res-held z q)))
  (intro e)
  (have e1 (= (:id q2) (:id q))) (exact (congrArg (fn [k :- RKR] (:id k)) e))
  (have e2 (= (:resources q2) (:resources q))) (exact (congrArg (fn [k :- RKR] (:res k)) e))
  (simp only [res-held e1 e2]))
(a/theorem rkr-listed [z :- ResRow, q :- RunRow, q2 :- RunRow] (=> (= (rkr q2) (rkr q)) (= (listed-in z q2) (listed-in z q)))
  (intro e)
  (have e1 (= (:id q2) (:id q))) (exact (congrArg (fn [k :- RKR] (:id k)) e))
  (have e2 (= (:resources q2) (:resources q))) (exact (congrArg (fn [k :- RKR] (:res k)) e))
  (simp only [listed-in e1 e2]))
(a/theorem rkr-r2 [w :- World, q :- RunRow, q2 :- RunRow] (=> (= (rkr q2) (rkr q)) (= (r2-ok w q2) (r2-ok w q)))
  (intro e)
  (have e1 (= (:of q2) (:of q))) (exact (congrArg (fn [k :- RKR] (:of k)) e))
  (have e2 (= (:scope q2) (:scope q))) (exact (congrArg (fn [k :- RKR] (:scope k)) e))
  (simp only [r2-ok e1 e2]))
(a/theorem rkr-r3 [cl :- (List CleanupRow), xr :- (List Nat), q :- RunRow, q2 :- RunRow] (=> (= (rkr q2) (rkr q)) (= (r3-ok cl xr q2) (r3-ok cl xr q)))
  (intro e)
  (have e1 (= (:id q2) (:id q))) (exact (congrArg (fn [k :- RKR] (:id k)) e))
  (have e2 (= (run-alive q2) (run-alive q))) (exact (congrArg (fn [k :- RKR] (:alive k)) e))
  (simp only [r3-ok e1 e2]))

(a/theorem grx-run-upd [xr :- (List Nat), w :- World, x :- Nat, f :- (=> RunRow RunRow),
                        hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                        hk :- (forall [r :- RunRow] (= (rkr (f r)) (rkr r)))]
  (=> (= (grx xr w) true) (= (grx xr (run-upd w x f)) true))
  (intro h)
  (have r := (grx-rest-of xr w h))
  (have a1 := (grk-1 xr w r)) (have a2 := (grk-2 xr w r)) (have a3 := (grk-3 xr w r))
  (apply (grx-intro xr _ (inv-run-upd w x f hid (grx-sample xr w h))))
  (apply (grk-mk xr _))
  (simp only [run-upd set-runs])
  (apply (tbl-all-mono ResRow _ _ _ (:res w) a1))
  (intros z hz)
  (simp only [r1-ok Bool.and_eq_true] at hz)
  (simp only [r1-ok (tbl-any-upd-same RunRow (res-held z) run-id x f (fn [q :- RunRow] (rkr-held z q (f q) (hk q))) (:runs w))
              (tbl-all-upd-same RunRow run-id x f (listed-in z) (fn [q :- RunRow] (rkr-listed z q (f q) (hk q))) (:runs w))
              (And.left hz) (And.right hz) Bool.and_self])
  (simp only [run-upd set-runs])
  (rw [(tbl-all-upd-same RunRow run-id x f (r2-ok (run-upd w x f)) (fn [q :- RunRow] (rkr-r2 (run-upd w x f) q (f q) (hk q))) (:runs w))])
  (exact a2)
  (simp only [run-upd set-runs])
  (rw [(tbl-all-upd-same RunRow run-id x f (r3-ok (:cleanup w) xr) (fn [q :- RunRow] (rkr-r3 (:cleanup w) xr q (f q) (hk q))) (:runs w))])
  (exact a3))

;; ---- resource rows: an edit that keeps (id, owner)
(a/structure RZK [] (id Nat) (owner Nat))
(a/defn rzk [z :- ResRow] RZK (RZK.mk (:id z) (:owner z)))
(a/theorem tbl-any-congr [A :- Type, P :- (=> A Bool), Q :- (=> A Bool), h :- (forall [r :- A] (= (P r) (Q r))), xs :- (List A)]
  (= (tbl-any P xs) (tbl-any Q xs))
  (induction xs) (case [nil] (simp only [tbl-any])) (case [cons hd t ih] (simp only [tbl-any (h hd) ih])))
(a/theorem rzk-r1 [rs :- (List RunRow), z :- ResRow, z2 :- ResRow] (=> (= (rzk z2) (rzk z)) (= (r1-ok rs z2) (r1-ok rs z)))
  (intro e)
  (have e1 (= (:id z2) (:id z))) (exact (congrArg (fn [k :- RZK] (:id k)) e))
  (have e2 (= (:owner z2) (:owner z))) (exact (congrArg (fn [k :- RZK] (:owner k)) e))
  (have h1 (forall [q :- RunRow] (= (res-held z2 q) (res-held z q)))) (intro q) (simp only [res-held e1 e2])
  (have h2 (forall [q :- RunRow] (= (listed-in z2 q) (listed-in z q)))) (intro q) (simp only [listed-in e1 e2])
  (simp only [r1-ok (tbl-any-congr RunRow (res-held z2) (res-held z) h1 rs) (tbl-all-congr RunRow (listed-in z2) (listed-in z) h2 rs)]))
(a/theorem grx-resource-upd [xr :- (List Nat), w :- World, x :- Nat, f :- (=> ResRow ResRow),
                             hid :- (forall [z :- ResRow] (= (resource-id (f z)) (resource-id z))),
                             hk :- (forall [z :- ResRow] (= (rzk (f z)) (rzk z)))]
  (=> (= (grx xr w) true) (= (grx xr (resource-upd w x f)) true))
  (intro h)
  (have r := (grx-rest-of xr w h))
  (have b1 (= (tbl-all (r1-ok (:runs (resource-upd w x f))) (:res (resource-upd w x f))) true))
  (simp only [resource-upd set-res])
  (rw [(tbl-all-upd-same ResRow resource-id x f (r1-ok (:runs w)) (fn [z :- ResRow] (rzk-r1 (:runs w) z (f z) (hk z))) (:res w))])
  (exact (grk-1 xr w r))
  (have b2 (= (tbl-all (r2-ok (resource-upd w x f)) (:runs (resource-upd w x f))) true)) (exact (grk-2 xr w r))
  (have b3 (= (tbl-all (r3-ok (:cleanup (resource-upd w x f)) xr) (:runs (resource-upd w x f))) true)) (exact (grk-3 xr w r))
  (exact (grx-intro xr _ (inv-resource-upd w x f hid (grx-sample xr w h)) (grk-mk xr _ b1 b2 b3))))
(a/theorem rzk-cancel [z :- ResRow] (= (rzk (res-cancel-row z)) (rzk z))
  (cases h (Nat.beq (:phase z) rp-armed)) (all_goals (simp only [rzk res-cancel-row h])))
(a/theorem grx-res-cancel-row [xr :- (List Nat), w :- World, x :- Nat]
  (=> (= (grx xr w) true) (= (grx xr (resource-upd w x res-cancel-row)) true))
  (intro h) (exact (grx-resource-upd xr w x res-cancel-row res-cancel-row-id rzk-cancel h)))

;; ---- cleanup rows: an edit that keeps the run; an insertion only adds
(a/theorem grx-cleanup-upd [xr :- (List Nat), w :- World, x :- Nat, f :- (=> CleanupRow CleanupRow),
                            hk :- (forall [c :- CleanupRow] (= (cleanup-id (f c)) (cleanup-id c)))]
  (=> (= (grx xr w) true) (= (grx xr (cleanup-upd w x f)) true))
  (intro h)
  (have r := (grx-rest-of xr w h))
  (have b1 (= (tbl-all (r1-ok (:runs (cleanup-upd w x f))) (:res (cleanup-upd w x f))) true)) (exact (grk-1 xr w r))
  (have b2 (= (tbl-all (r2-ok (cleanup-upd w x f)) (:runs (cleanup-upd w x f))) true)) (exact (grk-2 xr w r))
  (have b3 (= (tbl-all (r3-ok (:cleanup (cleanup-upd w x f)) xr) (:runs (cleanup-upd w x f))) true))
  (apply (tbl-all-mono RunRow (r3-ok (:cleanup w) xr) _ _ (:runs w) (grk-3 xr w r)))
  (intros q hq)
  (simp only [r3-ok cleanup-upd set-cleanup (tbl-has-upd CleanupRow cleanup-id x (:id q) f hk (:cleanup w))])
  (exact hq)
  (exact (grx-intro xr _ (inv-cleanup-upd w x f (grx-sample xr w h)) (grk-mk xr _ b1 b2 b3))))
(a/theorem grx-cleanup-ins [xr :- (List Nat), w :- World, c :- CleanupRow]
  (=> (= (grx xr w) true) (= (grx xr (cleanup-ins w c)) true))
  (intro h)
  (have r := (grx-rest-of xr w h))
  (have b1 (= (tbl-all (r1-ok (:runs (cleanup-ins w c))) (:res (cleanup-ins w c))) true)) (exact (grk-1 xr w r))
  (have b2 (= (tbl-all (r2-ok (cleanup-ins w c)) (:runs (cleanup-ins w c))) true)) (exact (grk-2 xr w r))
  (apply (grx-intro xr _ (inv-cleanup-ins w c (grx-sample xr w h))))
  (apply (grk-mk xr _ b1 b2))
  (apply (tbl-all-mono RunRow (r3-ok (:cleanup w) xr) _ _ (:runs w) (grk-3 xr w r)))
  (intros q hq)
  (simp only [r3-ok Bool.or_eq_true] at hq)
  (simp only [r3-ok cleanup-ins set-cleanup tbl-has-ins Bool.or_eq_true])
  (cases hq) (case [inl a] (exact (Or.inl a)))
  (case [inr b] (cases b) (case [inl b1] (exact (Or.inr (Or.inl (Or.inr b1))))) (case [inr b2] (exact (Or.inr (Or.inr b2))))))

;; cleanup[R] set: R now has an entry; an exempt R is discharged
(a/theorem r3-cset [cl :- (List CleanupRow), xr :- (List Nat), rid :- Nat, rows :- (List Nat), q :- RunRow]
  (=> (= (r3-ok cl (List.cons Nat rid xr) q) true)
      (= (r3-ok (tbl-ins (CleanupRow.mk rid rows) (tbl-del cleanup-id rid cl)) xr q) true))
  (intro hq)
  (cases hb (Nat.beq rid (:id q)))
  (case [true] (simp only [r3-ok tbl-has-ins cleanup-id hb Bool.true_or Bool.or_true]))
  (case [false]
    (have ne2 (= (Nat.beq (:id q) rid) false)) (rw [beq-comm]) (exact hb)
    (simp only [r3-ok reach-mem ne2] at hq)
    (simp only [r3-ok tbl-has-ins cleanup-id hb Bool.false_or (tbl-has-del-ne CleanupRow cleanup-id rid (:id q) cl hb)])
    (exact hq)))
(a/theorem grx-cleanup-set [xr :- (List Nat), w :- World, rid :- Nat, rows :- (List Nat)]
  (=> (= (grx (List.cons Nat rid xr) w) true) (= (grx xr (cleanup-set w rid rows)) true))
  (intro h)
  (have r := (grx-rest-of _ w h))
  (have b1 (= (tbl-all (r1-ok (:runs (cleanup-set w rid rows))) (:res (cleanup-set w rid rows))) true)) (exact (grk-1 _ w r))
  (have b2 (= (tbl-all (r2-ok (cleanup-set w rid rows)) (:runs (cleanup-set w rid rows))) true)) (exact (grk-2 _ w r))
  (have b3 (= (tbl-all (r3-ok (:cleanup (cleanup-set w rid rows)) xr) (:runs (cleanup-set w rid rows))) true))
  (exact (tbl-all-mono RunRow _ _ (r3-cset (:cleanup w) xr rid rows) (:runs w) (grk-3 _ w r)))
  (exact (grx-intro xr _ (inv-cleanup-set w rid rows (grx-sample _ w h)) (grk-mk xr _ b1 b2 b3))))
(a/theorem grx-cleanup-set0 [xr :- (List Nat), w :- World, rid :- Nat, rows :- (List Nat)]
  (=> (= (grx xr w) true) (= (grx xr (cleanup-set w rid rows)) true))
  (intro h)
  (have r := (grx-rest-of _ w h))
  (have h2 (= (grx (List.cons Nat rid xr) w) true))
  (apply (grx-intro (List.cons Nat rid xr) w (grx-sample _ w h)))
  (apply (grk-mk (List.cons Nat rid xr) w (grk-1 _ w r) (grk-2 _ w r)))
  (apply (tbl-all-mono RunRow (r3-ok (:cleanup w) xr) _ _ (:runs w) (grk-3 _ w r)))
  (intros q hq)
  (simp only [r3-ok reach-mem Bool.or_eq_true] at hq)
  (simp only [r3-ok reach-mem Bool.or_eq_true])
  (cases hq) (case [inl a] (exact (Or.inl a)))
  (case [inr b] (cases b) (case [inl b1] (exact (Or.inr (Or.inl b1))))
    (case [inr b2] (apply Or.inr) (apply Or.inr) (cases hb (Nat.beq (:id q) rid)) (case [true] (simp only [hb])) (case [false] (simp only [hb]) (exact b2))))
  (exact (grx-cleanup-set xr w rid rows h2)))

;; ---- run rows made (or kept) alive: parking (id, entity, scope, resources kept)
(a/structure RKR0 [] (id Nat) (of Nat) (scope Nat) (res (List Nat)))
(a/defn rkr0 [r :- RunRow] RKR0 (RKR0.mk (:id r) (:of r) (:scope r) (:resources r)))
(a/theorem grx-run-upd-up [xr :- (List Nat), w :- World, x :- Nat, f :- (=> RunRow RunRow),
                           hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                           hk :- (forall [r :- RunRow] (= (rkr0 (f r)) (rkr0 r))),
                           ha :- (forall [r :- RunRow] (= (run-alive (f r)) true))]
  (=> (= (grx xr w) true) (= (grx xr (run-upd w x f)) true))
  (intro h)
  (have r := (grx-rest-of xr w h))
  (have a1 := (grk-1 xr w r)) (have a2 := (grk-2 xr w r)) (have a3 := (grk-3 xr w r))
  (have k1 (forall [q :- RunRow] (= (:id (f q)) (:id q)))) (intro q) (exact (congrArg (fn [k :- RKR0] (:id k)) (hk q)))
  (have k2 (forall [q :- RunRow] (= (:of (f q)) (:of q)))) (intro q) (exact (congrArg (fn [k :- RKR0] (:of k)) (hk q)))
  (have k3 (forall [q :- RunRow] (= (:scope (f q)) (:scope q)))) (intro q) (exact (congrArg (fn [k :- RKR0] (:scope k)) (hk q)))
  (have k4 (forall [q :- RunRow] (= (:resources (f q)) (:resources q)))) (intro q) (exact (congrArg (fn [k :- RKR0] (:res k)) (hk q)))
  (have b1 (= (tbl-all (r1-ok (:runs (run-upd w x f))) (:res (run-upd w x f))) true))
  (simp only [run-upd set-runs])
  (apply (tbl-all-mono ResRow _ _ _ (:res w) a1))
  (intros z hz)
  (simp only [r1-ok Bool.and_eq_true] at hz)
  (have e1 (forall [q :- RunRow] (= (res-held z (f q)) (res-held z q)))) (intro q) (simp only [res-held (k1 q) (k4 q)])
  (have e2 (forall [q :- RunRow] (= (listed-in z (f q)) (listed-in z q)))) (intro q) (simp only [listed-in (k1 q) (k4 q)])
  (simp only [r1-ok (tbl-any-upd-same RunRow (res-held z) run-id x f e1 (:runs w)) (tbl-all-upd-same RunRow run-id x f (listed-in z) e2 (:runs w))
              (And.left hz) (And.right hz) Bool.and_self])
  (have b2 (= (tbl-all (r2-ok (run-upd w x f)) (:runs (run-upd w x f))) true))
  (have e3 (forall [q :- RunRow] (= (r2-ok (run-upd w x f) (f q)) (r2-ok (run-upd w x f) q)))) (intro q) (simp only [r2-ok (k2 q) (k3 q)])
  (simp only [run-upd set-runs]) (rw [(tbl-all-upd-same RunRow run-id x f (r2-ok (run-upd w x f)) e3 (:runs w))]) (exact a2)
  (have b3 (= (tbl-all (r3-ok (:cleanup (run-upd w x f)) xr) (:runs (run-upd w x f))) true))
  (simp only [run-upd set-runs])
  (apply (tbl-all-upd RunRow run-id x f (r3-ok (:cleanup w) xr) (r3-ok (:cleanup w) xr) _ _ (:runs w) a3))
  (intros q h1 h2) (simp only [r3-ok (ha q) Bool.true_or])
  (intros q h1 h2) (exact h1)
  (exact (grx-intro xr _ (inv-run-upd w x f hid (grx-sample xr w h)) (grk-mk xr _ b1 b2 b3))))
(a/theorem rkr0-park [r :- RunRow] (= (rkr0 (run-park-row r)) (rkr0 r)) (rfl))
(a/theorem alive-park [r :- RunRow] (= (run-alive (run-park-row r)) true) (rfl))
(a/theorem rkr0-tick-park [r :- RunRow] (= (rkr0 (run-tick-park r)) (rkr0 r)) (rfl))
(a/theorem alive-tick-park [r :- RunRow] (= (run-alive (run-tick-park r)) true) (rfl))
(a/theorem rkr-wake [r :- RunRow] (= (rkr (run-wake r)) (rkr r)) (simp only [rkr run-wake-alive]))

(a/defn grx-rest [xr :- (List Nat), w :- World] Bool (grk-rest xr w))
(a/theorem grx-run-park [xr :- (List Nat), w :- World, x :- Nat]
  (=> (= (grx xr w) true) (= (grx xr (run-upd w x run-park-row)) true))
  (intro h) (exact (grx-run-upd-up xr w x run-park-row run-park-row-id rkr0-park alive-park h)))
(a/theorem grx-run-tick-park [xr :- (List Nat), w :- World, x :- Nat]
  (=> (= (grx xr w) true) (= (grx xr (run-upd w x run-tick-park)) true))
  (intro h) (exact (grx-run-upd-up xr w x run-tick-park run-tick-park-id rkr0-tick-park alive-tick-park h)))
(a/theorem grx-run-wake [xr :- (List Nat), w :- World, x :- Nat]
  (=> (= (grx xr w) true) (= (grx xr (run-upd w x run-wake)) true))
  (intro h) (exact (grx-run-upd xr w x run-wake run-wake-run-id rkr-wake h)))

(defn gr-patch [form]
  (->> form
       (subst-forms (fn [y] (and (seq? y) (= 'inv-run-upd (first y)) (#{'run-park-row 'run-tick-park 'run-wake} (nth y 3 nil))))
                    (fn [[_ w x f _ h]] (list ({'run-park-row 'rpark* 'run-tick-park 'rtpark* 'run-wake 'rwake*} f) w x h)))
       (subst-forms (fn [y] (and (seq? y) (= 'inv-resource-upd (first y)) (= 'res-cancel-row (nth y 3 nil))))
                    (fn [[_ w x _ _ h]] (list 'rcancel* w x h)))))

(def GRX (mk-bundle 'grx '[x1r :- (List Nat)] "grx-"
           {'inv-run-upd ['(fn [r :- RunRow] (Eq.refl (rkr r))) 4]
            'inv-resource-upd ['(fn [z :- ResRow] (Eq.refl (rzk z))) 4]
            'inv-cleanup-upd ['(fn [c :- CleanupRow] (Eq.refl (cleanup-id c))) 3]}))
(swap! (:renames GRX) assoc 'inv-parts 'grx-parts 'inv-run-upd 'grx-run-upd 'inv-resource-upd 'grx-resource-upd
       'inv-cleanup-upd 'grx-cleanup-upd 'inv-cleanup-ins 'grx-cleanup-ins 'inv-cleanup-set 'grx-cleanup-set0
       'inv-comp-upd 'grx-comp-upd 'inv-task-upd 'grx-task-upd 'inv-scope-upd 'grx-scope-upd
       'inv-comp-ins-fresh 'grx-comp-ins 'inv-task-ins-fresh 'grx-task-ins 'inv-scope-ins-fresh 'grx-scope-ins
       'rpark* 'grx-run-park 'rtpark* 'grx-run-tick-park 'rwake* 'grx-run-wake 'rcancel* 'grx-res-cancel-row)
(doseq [[n _] @@#'spindel.v2.lit/source-theorems] (patch! GRX n gr-patch))
(doseq [o '[inv-pub-upd inv-source-upd inv-set-pins inv-act-upd inv-edge-upd inv-bump inv-source-ins-fresh inv-act-ins-fresh insert-edge-fresh-inv-sample]]
  (prim! GRX o nil))
(prim! GRX 'inv-remove-edge '(grk-remove-edge x1r w x R))
(prim! GRX 'mark-edge-inv-sample '(grk-mark-edge x1r w x R))
(prim! GRX 'unmark-edge-inv-sample '(grk-unmark-edge x1r w x R))
(prim! GRX 'inv-drop-cred '(grk-drop-cred x1r w a R))
(prim! GRX 'inv-drop-act '(grk-drop-act x1r w a R))
(prim! GRX 'inv-drop-edges '(grk-drop-edges x1r w p R))

;; ---- remove-if-empty: an empty subtree holds no run scope
(a/structure SDK [] (runs (List RunRow)) (res (List ResRow)) (cl (List CleanupRow)) (comps (List CompRow)) (tasks (List TaskRow)))
(a/defn sdk [w :- World] SDK (SDK.mk (:runs w) (:res w) (:cleanup w) (:comps w) (:tasks w)))
(a/theorem sdk-scope-fold [sub :- (List Nat)] (forall [W :- World] (= (sdk (nat-fold scope-del W sub)) (sdk W)))
  (induction sub)
  (case [nil] (intro W) (rfl))
  (case [cons h t ih] (intro W) (simp only [nat-fold]) (exact (Eq.trans (ih (scope-del W h)) (rfl)))))
(a/theorem scope-fold-has [sub :- (List Nat)]
  (forall [W :- World, y :- Nat] (=> (= (scope-has W y) true) (= (reach-mem y sub) false) (= (scope-has (nat-fold scope-del W sub) y) true)))
  (induction sub)
  (case [nil] (intros W y h1 h2) (exact h1))
  (case [cons h t ih]
    (intros W y h1 h2)
    (simp only [reach-mem] at h2)
    (cases hb (Nat.beq y h))
    (case [true] (simp only [hb] at h2) (cases h2))
    (case [false]
      (simp only [hb] at h2)
      (simp only [nat-fold])
      (have ne (= (Nat.beq h y) false)) (rw [beq-comm]) (exact hb)
      (have h3 (= (scope-has (scope-del W h) y) true))
      (simp only [scope-has scope-del set-scopes (tbl-has-del-ne ScopeRow scope-id h y (:scopes W) ne)]) (exact h1)
      (exact (ih (scope-del W h) y h3 h2)))))
(a/theorem not-any-mem [A :- Type, p :- (=> A Bool), q :- A, xs :- (List A)]
  (=> (= (tbl-any p xs) false) (List.Mem q xs) (= (p q) false))
  (intros h m)
  (have a := (tbl-all-mem A (bnot-of p) q xs (any-false-all A p xs h) m))
  (simp only [bnot-of] at a) (exact (bnot-true _ a)))
(a/theorem grx-remove-if-empty [xr :- (List Nat), w :- World, sub :- (List Nat)]
  (=> (= (grx xr w) true) (= (grx xr (remove-if-empty w sub)) true))
  (intro h)
  (cases he (subtree-empty w sub))
  (case [false] (simp only [remove-if-empty he]) (exact h))
  (case [true]
    (simp only [remove-if-empty he])
    (have r := (grx-rest-of xr w h))
    (have e := (sdk-scope-fold sub w))
    (have e1 (= (:runs (nat-fold scope-del w sub)) (:runs w))) (exact (congrArg (fn [k :- SDK] (:runs k)) e))
    (have e2 (= (:res (nat-fold scope-del w sub)) (:res w))) (exact (congrArg (fn [k :- SDK] (:res k)) e))
    (have e3 (= (:cleanup (nat-fold scope-del w sub)) (:cleanup w))) (exact (congrArg (fn [k :- SDK] (:cl k)) e))
    (have e4 (= (:comps (nat-fold scope-del w sub)) (:comps w))) (exact (congrArg (fn [k :- SDK] (:comps k)) e))
    (have e5 (= (:tasks (nat-fold scope-del w sub)) (:tasks w))) (exact (congrArg (fn [k :- SDK] (:tasks k)) e))
    (simp only [subtree-empty Bool.and_eq_true] at he)
    (have nr := (bnot-true _ (And.left (And.right (And.right (And.right (And.right he)))))))
    (have b1 (= (tbl-all (r1-ok (:runs (nat-fold scope-del w sub))) (:res (nat-fold scope-del w sub))) true)) (rw [e1 e2]) (exact (grk-1 xr w r))
    (have b3 (= (tbl-all (r3-ok (:cleanup (nat-fold scope-del w sub)) xr) (:runs (nat-fold scope-del w sub))) true)) (rw [e1 e3]) (exact (grk-3 xr w r))
    (have b2 (= (tbl-all (r2-ok (nat-fold scope-del w sub)) (:runs (nat-fold scope-del w sub))) true))
    (rw [e1])
    (apply (tbl-all-mem-mono RunRow (r2-ok w) _ (:runs w) _ (grk-2 xr w r)))
    (intros q mq hq)
    (simp only [r2-ok Bool.and_eq_true] at hq)
    (have ns := (not-any-mem RunRow (run-scoped-in sub) q (:runs w) nr mq))
    (simp only [run-scoped-in] at ns)
    (have s2 := (scope-fold-has sub w (:scope q) (And.right hq) ns))
    (have c2 (= (Bool.or (comp-has (nat-fold scope-del w sub) (:of q)) (task-has (nat-fold scope-del w sub) (:of q))) true))
    (simp only [comp-has task-has e4 e5]) (exact (And.left hq))
    (simp only [r2-ok c2 s2 Bool.and_self])
    (exact (grx-intro xr _ (nat-fold-inv scope-del inv-scope-del sub w (grx-sample xr w h)) (grk-mk xr _ b1 b2 b3)))))

;; ---- the resource table through T13's local part (no resource is made or dropped there)
(a/theorem res-remove-edge [w :- World, y :- Nat] (= (:res (remove-edge w y)) (:res w))
  (cases hf (edge-find w y)) (case' [some e]) (case' [none])
  (simp only [remove-edge hf])
  (cases hm (:marked e)) (all_goals (simp only [remove-edge hf hm comp-upd edge-del set-comps set-edges])))
(a/theorem res-fill-slot [w :- World, a :- ActRow, y :- Nat, v :- RunResult] (= (:res (fill-slot w a y v)) (:res w))
  (cases hm (act-ready (act-fill y v a))) (all_goals (simp only [fill-slot hm resume])))
(a/theorem res-fire-dep [w :- World, e :- EdgeRow] (= (:res (fire-dep w e)) (:res w))
  (cases ha (act-with-member (:id e) (:acts w))) (case' [some a]) (case' [none])
  (simp only [fire-dep ha invalidate])
  (cases hc (Bool.and (run-current-of w (:run a) (:creditor e)) (deb-avail w (:debtor e))))
  (simp only [fire-dep ha hc invalidate])
  (simp only [fire-dep ha hc deliver-dep])
  (have e1 (= (:res (dep-consumed w e)) (:res w)))
  (cases hf (deb-final w (:debtor e)))
  (simp only [dep-consumed hf])
  (simp only [dep-consumed hf]) (exact (res-remove-edge w (:id e)))
  (exact (Eq.trans (res-fill-slot _ a _ _) e1)))
(a/theorem res-fire-wait [res :- RunResult, w :- World, e :- EdgeRow] (= (:res (fire-wait res w e)) (:res w))
  (cases hc (Nat.beq (:creditor e) 0))
  (case [true] (simp only [fire-wait hc]) (exact (res-remove-edge w (:id e))))
  (case [false]
    (simp only [fire-wait hc])
    (cases ha (act-find w (:creditor e))) (case' [some a]) (case' [none])
    (simp only [fire-wait-act ha])
    (cases hr (run-current w (:run a)))
    (simp only [fire-wait-act ha hr])
    (simp only [fire-wait-act ha hr]) (exact (res-fill-slot _ a _ _))))
(a/theorem res-fire-edge [res :- RunResult, w :- World, y :- Nat] (= (:res (fire-edge res w y)) (:res w))
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
  (simp only [fire-edge hf hp hk1 hk2]) (exact (res-fire-wait res w e))
  (simp only [fire-edge hf hp hk1]) (exact (res-fire-dep w e)))
(a/theorem res-fold [f :- (=> World Nat World), hf :- (forall [w :- World, x :- Nat] (= (:res (f w x)) (:res w))), xs :- (List Nat)]
  (forall [w :- World] (= (:res (nat-fold f w xs)) (:res w)))
  (induction xs)
  (case [nil] (intro w) (simp only [nat-fold]))
  (case [cons h t ih] (intro w) (simp only [nat-fold]) (exact (Eq.trans (ih (f w h)) (hf w h)))))
(a/theorem res-fin-loop [fuel :- (List Nat)]
  (forall [w :- World, ds :- (List Nat)] (= (:res (:world (fin-loop fuel w ds))) (:res w)))
  (induction fuel)
  (case [nil] (intros w ds) (simp only [fin-loop]))
  (case [cons h f ih]
    (intros w ds)
    (cases ds)
    (simp only [fin-loop])
    (rename_i d t)
    (simp only [fin-loop])
    (exact (Eq.trans (ih (finalize-one w d) _) (rfl)))))
(a/theorem res-close-source [w :- World, x :- Nat] (= (:res (close-source w x)) (:res w))
  (simp only [close-source finalize-debtor wake-closed])
  (exact (Eq.trans (res-fin-loop _ _ _) (res-fold (fire-edge _) (res-fire-edge _) _ (source-upd w x source-close-row)))))
(a/theorem res-close-local [w :- World, sub :- (List Nat)] (= (:res (close-local w sub)) (:res w))
  (simp only [close-local])
  (exact (Eq.trans (res-fold close-source res-close-source _ _) (res-fold close-scope-id (fn [W :- World, x :- Nat] (Eq.refl (:res W))) sub w))))
(a/theorem res-clear-comp-run [w :- World, r :- RunRow] (= (:res (clear-comp-run w r)) (:res w))
  (cases hc (comp-find w (:of r)))
  (case [none]
    (simp only [clear-comp-run hc clear-task-run])
    (cases ht (task-find w (:of r))) (case' [some t]) (case' [none])
    (simp only [ht])
    (cases hr (Nat.beq (:run t) (:id r))) (all_goals (simp only [ht hr])))
  (case [some c] (cases hr (Nat.beq (:run c) (:id r))) (all_goals (simp only [clear-comp-run hc hr]))))

(a/theorem any-del-keep [A :- Type, idf :- (=> A Nat), x :- Nat, p :- (=> A Bool),
                         hp :- (forall [q :- A] (=> (= (p q) true) (= (Nat.beq (idf q) x) false))), xs :- (List A)]
  (=> (= (tbl-any p xs) true) (= (tbl-any p (tbl-del idf x xs)) true))
  (induction xs)
  (case [nil] (intro h) (simp [tbl-any] at h))
  (case [cons hd t ih]
    (intro h)
    (simp only [tbl-any Bool.or_eq_true] at h)
    (cases hb (Nat.beq (idf hd) x))
    (case [true]
      (simp only [tbl-del hb])
      (cases h)
      (case [inl a] (have z := (hp hd a)) (rw [hb] at z) (cases z))
      (case [inr b] (exact (ih b))))
    (case [false]
      (simp only [tbl-del hb tbl-any Bool.or_eq_true])
      (cases h) (case [inl a] (exact (Or.inl a))) (case [inr b] (exact (Or.inr (ih b)))))))
(a/theorem del-ne-all [A :- Type, idf :- (=> A Nat), x :- Nat, xs :- (List A)]
  (= (tbl-all (fn [q :- A] (Bool.not (Nat.beq (idf q) x))) (tbl-del idf x xs)) true)
  (induction xs)
  (case [nil] (simp only [tbl-del tbl-all]))
  (case [cons hd t ih]
    (cases hb (Nat.beq (idf hd) x))
    (case [true] (simp only [tbl-del hb]) (exact ih))
    (case [false] (simp only [tbl-del hb tbl-all hb Bool.not_false ih Bool.true_and]))))

(a/theorem grk-run-del-cl [xr :- (List Nat), w :- World, rid :- Nat]
  (=> (forall [z :- ResRow] (=> (List.Mem z (:res w)) (= (Nat.beq (:owner z) rid) false)))
      (= (grk-rest xr w) true) (= (grk-rest xr (cleanup-del (run-del w rid) rid)) true))
  (intros hz h)
  (have b1 (= (tbl-all (r1-ok (:runs (cleanup-del (run-del w rid) rid))) (:res (cleanup-del (run-del w rid) rid))) true))
  (simp only [cleanup-del run-del set-cleanup set-runs])
  (apply (tbl-all-mem-mono ResRow (r1-ok (:runs w)) _ (:res w) _ (grk-1 xr w h)))
  (intros z mz hz2)
  (simp only [r1-ok Bool.and_eq_true] at hz2)
  (have a1 (= (tbl-any (res-held z) (tbl-del run-id rid (:runs w))) true))
  (apply (any-del-keep RunRow run-id rid (res-held z) _ (:runs w) (And.left hz2)))
  (intros q hq)
  (simp only [res-held Bool.and_eq_true] at hq)
  (have e (= (:id q) (:owner z))) (exact (Nat.eq_of_beq_eq_true (And.left hq)))
  (have hq2 (= (Nat.beq (run-id q) rid) false)) (simp only [run-id e]) (exact (hz z mz))
  (exact hq2)
  (simp only [r1-ok a1 (all-sub-del RunRow (listed-in z) run-id rid (:runs w) (And.right hz2)) Bool.and_self])
  (have b2 (= (tbl-all (r2-ok (cleanup-del (run-del w rid) rid)) (:runs (cleanup-del (run-del w rid) rid))) true))
  (exact (all-sub-del RunRow (r2-ok w) run-id rid (:runs w) (grk-2 xr w h)))
  (have b3 (= (tbl-all (r3-ok (:cleanup (cleanup-del (run-del w rid) rid)) xr) (:runs (cleanup-del (run-del w rid) rid))) true))
  (simp only [cleanup-del run-del set-cleanup set-runs])
  (have s := (all-sub-del RunRow (r3-ok (:cleanup w) xr) run-id rid (:runs w) (grk-3 xr w h)))
  (apply (tbl-all-mono2 RunRow _ _ _ _ (tbl-del run-id rid (:runs w)) s (del-ne-all RunRow run-id rid (:runs w))))
  (intros q h1 h2)
  (simp only [r3-ok Bool.or_eq_true] at h1)
  (simp only [r3-ok Bool.or_eq_true])
  (have ne (= (Nat.beq rid (:id q)) false)) (rw [beq-comm]) (exact (bnot-true _ h2))
  (cases h1) (case [inl a] (exact (Or.inl a)))
  (case [inr b] (cases b) (case [inl b1] (exact (Or.inr (Or.inl (Eq.trans (tbl-has-del-ne CleanupRow cleanup-id rid (:id q) (:cleanup w) ne) b1)))))
    (case [inr b2] (exact (Or.inr (Or.inr b2)))))
  (exact (grk-mk xr _ b1 b2 b3)))

(a/theorem retire-owner-ne [xr :- (List Nat), w :- World, r :- RunRow]
  (=> (List.Mem r (:runs w)) (= (retirable r) true) (= (grk-rest xr w) true)
      (forall [z :- ResRow] (=> (List.Mem z (:res w)) (= (Nat.beq (:owner z) (:id r)) false))))
  (intros hm hr h z mz)
  (have a := (tbl-all-mem ResRow (r1-ok (:runs w)) z (:res w) (grk-1 xr w h) mz))
  (simp only [r1-ok Bool.and_eq_true] at a)
  (have l := (tbl-all-mem RunRow (listed-in z) r (:runs w) (And.right a) hm))
  (simp only [retirable Bool.and_eq_true] at hr)
  (have re := (And.right (And.right (And.right hr))))
  (cases hres (:resources r))
  (case [cons x t] (rw [hres] at re) (simp [nats-empty] at re))
  (case [nil]
    (simp only [listed-in hres nat-mem Bool.or_false] at l)
    (have q := (bnot-true _ l))
    (rw [beq-comm]) (exact q)))

;; ---- a run made done joins the exemptions (until its cleanup entry is set)
(a/theorem grx-run-upd-x [xr :- (List Nat), w :- World, x :- Nat, f :- (=> RunRow RunRow),
                          hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                          hk :- (forall [r :- RunRow] (= (rkr0 (f r)) (rkr0 r)))]
  (=> (= (grx xr w) true) (= (grx (List.cons Nat x xr) (run-upd w x f)) true))
  (intro h)
  (have r := (grx-rest-of xr w h))
  (have a1 := (grk-1 xr w r)) (have a2 := (grk-2 xr w r)) (have a3 := (grk-3 xr w r))
  (have k1 (forall [q :- RunRow] (= (:id (f q)) (:id q)))) (intro q) (exact (congrArg (fn [k :- RKR0] (:id k)) (hk q)))
  (have k2 (forall [q :- RunRow] (= (:of (f q)) (:of q)))) (intro q) (exact (congrArg (fn [k :- RKR0] (:of k)) (hk q)))
  (have k3 (forall [q :- RunRow] (= (:scope (f q)) (:scope q)))) (intro q) (exact (congrArg (fn [k :- RKR0] (:scope k)) (hk q)))
  (have k4 (forall [q :- RunRow] (= (:resources (f q)) (:resources q)))) (intro q) (exact (congrArg (fn [k :- RKR0] (:res k)) (hk q)))
  (have b1 (= (tbl-all (r1-ok (:runs (run-upd w x f))) (:res (run-upd w x f))) true))
  (simp only [run-upd set-runs])
  (apply (tbl-all-mono ResRow _ _ _ (:res w) a1))
  (intros z hz)
  (simp only [r1-ok Bool.and_eq_true] at hz)
  (have e1 (forall [q :- RunRow] (= (res-held z (f q)) (res-held z q)))) (intro q) (simp only [res-held (k1 q) (k4 q)])
  (have e2 (forall [q :- RunRow] (= (listed-in z (f q)) (listed-in z q)))) (intro q) (simp only [listed-in (k1 q) (k4 q)])
  (simp only [r1-ok (tbl-any-upd-same RunRow (res-held z) run-id x f e1 (:runs w)) (tbl-all-upd-same RunRow run-id x f (listed-in z) e2 (:runs w))
              (And.left hz) (And.right hz) Bool.and_self])
  (have b2 (= (tbl-all (r2-ok (run-upd w x f)) (:runs (run-upd w x f))) true))
  (have e3 (forall [q :- RunRow] (= (r2-ok (run-upd w x f) (f q)) (r2-ok (run-upd w x f) q)))) (intro q) (simp only [r2-ok (k2 q) (k3 q)])
  (simp only [run-upd set-runs]) (rw [(tbl-all-upd-same RunRow run-id x f (r2-ok (run-upd w x f)) e3 (:runs w))]) (exact a2)
  (have b3 (= (tbl-all (r3-ok (:cleanup (run-upd w x f)) (List.cons Nat x xr)) (:runs (run-upd w x f))) true))
  (simp only [run-upd set-runs])
  (apply (tbl-all-upd RunRow run-id x f (r3-ok (:cleanup w) xr) (r3-ok (:cleanup w) (List.cons Nat x xr)) _ _ (:runs w) a3))
  (intros q h1 h2)
  (have h3 (= (Nat.beq (:id (f q)) x) true)) (rw [(k1 q)]) (exact h2)
  (simp only [r3-ok reach-mem h3 Bool.or_true])
  (intros q h1 h2)
  (simp only [r3-ok Bool.or_eq_true] at h1)
  (have h3 (= (Nat.beq (:id q) x) false)) (exact h2)
  (simp only [r3-ok reach-mem h3 Bool.or_eq_true])
  (exact h1)
  (exact (grx-intro _ _ (inv-run-upd w x f hid (grx-sample xr w h)) (grk-mk _ _ b1 b2 b3))))
(a/theorem rkr0-cancel [r :- RunRow] (= (rkr0 (run-cancel-row r)) (rkr0 r)) (rfl))
(a/theorem rkr0-complete [r :- RunRow] (= (rkr0 (run-complete-row r)) (rkr0 r)) (rfl))

(override! GRX 'inv-cancel-run-local '[inv-cancel-debtor inv-cancel-res inv-cancel-acts]
  '(a/theorem grx-cancel-run-local [x1r :- (List Nat), w :- World, r :- RunRow, rep :- Bool]
     (=> (= (grx x1r w) true) (= (grx x1r (cancel-run-local w r rep)) true))
     (intro h)
     (have h1 := (grx-run-upd-x x1r w (:id r) run-cancel-row run-cancel-row-id rkr0-cancel h))
     (simp only [cancel-run-local])
     (exact (grx-cancel-debtor x1r rep _ r
              (grx-cleanup-set x1r _ (:id r) (cleanup-rows-of w r)
                (grx-cancel-res (List.cons Nat (:id r) x1r) _ r (grx-cancel-acts (List.cons Nat (:id r) x1r) _ (:id r) h1)))))))
(override! GRX 'inv-retire-with '[inv-close-local inv-clear-comp-run inv-remove-if-empty]
  '(a/theorem grx-retire-with [x1r :- (List Nat), w :- World, r :- RunRow, sub :- (List Nat)]
     (=> (List.Mem r (:runs w)) (= (retirable r) true) (= (grx x1r w) true) (= (grx x1r (retire-with w r sub)) true))
     (intros hm hr h)
     (have h1 := (grx-close-local x1r _ sub (grx-clear-comp-run x1r w r h)))
     (have ne := (retire-owner-ne x1r w r hm hr (grx-rest-of x1r w h)))
     (have er (= (:res (close-local (clear-comp-run w r) sub)) (:res w))) (exact (Eq.trans (res-close-local _ sub) (res-clear-comp-run w r)))
     (have ne2 (forall [z :- ResRow] (=> (List.Mem z (:res (close-local (clear-comp-run w r) sub))) (= (Nat.beq (:owner z) (:id r)) false))))
     (intros z mz) (rw [er] at mz) (exact (ne z mz))
     (have h2 := (grx-intro x1r _ (inv-cleanup-del _ (:id r) (inv-run-del _ (:id r) (grx-sample x1r _ h1)))
                   (grk-run-del-cl x1r _ (:id r) ne2 (grx-rest-of x1r _ h1))))
     (simp only [retire-with])
     (exact (grx-remove-if-empty x1r _ sub h2))))
(override! GRX 'inv-retire-local '[inv-retire-with]
  '(a/theorem grx-retire-local [x1r :- (List Nat), w :- World, r :- RunRow]
     (=> (List.Mem r (:runs w)) (= (retirable r) true) (= (grx x1r w) true) (= (grx x1r (retire-local w r)) true))
     (intros hm hr h) (exact (grx-retire-with x1r w r (scope-subtree w (:scope r)) hm hr h))))
(swap! (:renames GRX) assoc 'inv-remove-if-empty 'grx-remove-if-empty)
(defn gr-patch2 [form]
  (->> (gr-patch form)
       (subst-forms #(= % '(inv-retire-local w r h)) (fn [_] '(inv-retire-local w r (tbl-find-mem RunRow run-id rid r (:runs w) hf) ha h)))))
(doseq [[n _] @@#'spindel.v2.lit/source-theorems] (patch! GRX n gr-patch2))

(lcopy! GRX 'inv-complete-body)
(lcopy! GRX 'inv-retire-after)
(lcopy! GRX 'inv-fin-if-final)
(lcopy! GRX 'inv-run-cascade)

;; ===========================================================================
;; GR0 = grx [] (no exemption): the step and normalization; every GRX lemma is reused at []
;; ===========================================================================
(a/theorem gr0-run-upd [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                        hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                        hk :- (forall [r :- RunRow] (= (rkr (f r)) (rkr r)))]
  (=> (= (gr0 w) true) (= (gr0 (run-upd w x f)) true))
  (intro h) (exact (grx-run-upd (List.nil Nat) w x f hid hk h)))
(a/theorem gr0-resource-upd [w :- World, x :- Nat, f :- (=> ResRow ResRow),
                             hid :- (forall [z :- ResRow] (= (resource-id (f z)) (resource-id z))),
                             hk :- (forall [z :- ResRow] (= (rzk (f z)) (rzk z)))]
  (=> (= (gr0 w) true) (= (gr0 (resource-upd w x f)) true))
  (intro h) (exact (grx-resource-upd (List.nil Nat) w x f hid hk h)))
(a/theorem gr0-cleanup-upd [w :- World, x :- Nat, f :- (=> CleanupRow CleanupRow),
                            hk :- (forall [c :- CleanupRow] (= (cleanup-id (f c)) (cleanup-id c)))]
  (=> (= (gr0 w) true) (= (gr0 (cleanup-upd w x f)) true))
  (intro h) (exact (grx-cleanup-upd (List.nil Nat) w x f hk h)))

(def GR0
  (let [special '#{inv-run-upd inv-resource-upd inv-cleanup-upd inv-parts}
        reuse (remove special (keys @(:renames GRX)))]
    (mk-bundle 'gr0 [] "gr0-"
      (merge (zipmap reuse (repeat ['(List.nil Nat) 0]))
             {'inv-run-upd ['(fn [r :- RunRow] (Eq.refl (rkr r))) 4]
              'inv-resource-upd ['(fn [z :- ResRow] (Eq.refl (rzk z))) 4]
              'inv-cleanup-upd ['(fn [c :- CleanupRow] (Eq.refl (cleanup-id c))) 3]}))))
(swap! (:renames GR0) merge (dissoc @(:renames GRX) 'inv-run-upd 'inv-resource-upd 'inv-cleanup-upd 'inv-parts))
(swap! (:renames GR0) assoc 'inv-parts 'gr0-parts 'inv-run-upd 'gr0-run-upd 'inv-resource-upd 'gr0-resource-upd 'inv-cleanup-upd 'gr0-cleanup-upd)
(doseq [[n _] @@#'spindel.v2.lit/source-theorems] (patch! GR0 n gr-patch2))

;; GR0 wrappers for GRX lemmas used as values (a bare function argument cannot take the [] parameter)
(defn- gr0-wrap-form [n]
  (let [f (@#'spindel.v2.lit/copy-form GRX (@#'spindel.v2.lit/source-of GRX n) 'x @(:renames GRX))
        [_ _ binders stmt] f
        bs (vec (drop 3 binders))
        stmt2 (clojure.walk/postwalk (fn [y] (if (and (seq? y) (= 'grx (first y)) (= 'x1r (second y))) (list 'gr0 (nth y 2)) y)) stmt)
        nm (@#'spindel.v2.lit/copy-name GR0 n)
        gx (get @(:renames GRX) n)]
    (list 'a/theorem nm bs stmt2 (list 'exact (apply list gx '(List.nil Nat) (take-nth 3 bs))))))
(def gr0-wrapped '[mark-edge-inv-sample inv-drop-act inv-fin-if-final inv-invalidate-id inv-res-cancel inv-close-source])
(doseq [n gr0-wrapped :when (contains? @(:renames GRX) n)]
  (let [form (gr0-wrap-form n)]
    (binding [*ns* (the-ns 'spindel.v2.lit)] (eval form))
    (swap! (:renames GR0) assoc n (second form))))
(def GR0 (assoc GR0 :extra-args (apply dissoc (:extra-args GR0) gr0-wrapped)))

;; ---- a new run (with its run scope): its entity exists (the caller's fact), its scope is new
(a/theorem any-elim [A :- Type, p :- (=> A Bool), P :- Prop, xs :- (List A)]
  (=> (= (tbl-any p xs) true) (forall [q :- A] (=> (List.Mem q xs) (= (p q) true) P)) P)
  (induction xs)
  (case [nil] (intros h k) (simp [tbl-any] at h))
  (case [cons hd t ih]
    (intros h k)
    (simp only [tbl-any Bool.or_eq_true] at h)
    (cases h)
    (case [inl a] (exact (k hd (List.Mem.head t) a)))
    (case [inr b] (exact (ih b (fn [q :- A, m :- (List.Mem q t), pq :- (= (p q) true)] (k q (List.Mem.tail hd m) pq)))))))
(a/theorem any-cons-of [A :- Type, p :- (=> A Bool), h :- A, t :- (List A)] (=> (= (tbl-any p t) true) (= (tbl-any p (List.cons A h t)) true))
  (intro q) (simp only [tbl-any q Bool.or_true]))
(a/theorem owner-below [xr :- (List Nat), w :- World, z :- ResRow]
  (=> (= (inv-sample w) true) (= (grk-rest xr w) true) (List.Mem z (:res w)) (< (:owner z) (:next-id w)))
  (intros hs h mz)
  (have a := (tbl-all-mem ResRow (r1-ok (:runs w)) z (:res w) (grk-1 xr w h) mz))
  (simp only [r1-ok Bool.and_eq_true] at a)
  (apply (any-elim RunRow (res-held z) (< (:owner z) (:next-id w)) (:runs w) (And.left a)))
  (intros q mq hq)
  (simp only [res-held Bool.and_eq_true] at hq)
  (have e (= (:id q) (:owner z))) (exact (Nat.eq_of_beq_eq_true (And.left hq)))
  (rw [← e]) (exact (run-below w q hs mq)))
(a/theorem cons-mem-or [A :- Type, q :- A, h :- A, t :- (List A)] (=> (List.Mem q (List.cons A h t)) (Or (= q h) (List.Mem q t)))
  (intro m) (cases m) (case [head] (exact (Or.inl (rfl)))) (case [tail m2] (exact (Or.inr m2))))

(a/theorem ars-r2 [w :- World, of :- Nat, epoch :- Nat, parent :- Nat, ei :- Nat]
  (=> (= (Bool.or (comp-has w of) (task-has w of)) true) (= (tbl-all (r2-ok w) (:runs w)) true)
      (= (tbl-all (r2-ok (add-run-scope w of epoch parent ei)) (:runs (add-run-scope w of epoch parent ei))) true))
  (intros he h2)
  (have sc (= (scope-has (add-run-scope w of epoch parent ei) (+ (:next-id w) 1)) true))
  (simp only [add-run-scope bump set-next-id scope-ins set-scopes run-ins set-runs scope-has tbl-ins tbl-has-ins new-scope-row scope-id Nat.beq_refl Bool.true_or])
  (have mono (forall [q :- RunRow] (=> (= (r2-ok w q) true) (= (r2-ok (add-run-scope w of epoch parent ei) q) true))))
  (intros q hq)
  (simp only [r2-ok Bool.and_eq_true] at hq)
  (have p1 (= (Bool.or (comp-has (add-run-scope w of epoch parent ei) (:of q)) (task-has (add-run-scope w of epoch parent ei) (:of q))) true)) (exact (And.left hq))
  (have p2 (= (scope-has (add-run-scope w of epoch parent ei) (:scope q)) true))
  (exact (has-ins-of ScopeRow scope-id (new-scope-row (+ (:next-id w) 1) parent) (:scopes w) (:scope q) (And.right hq)))
  (simp only [r2-ok p1 p2 Bool.and_self])
  (have rest := (tbl-all-mono RunRow (r2-ok w) _ mono (:runs w) h2))
  (have he2 (= (Bool.or (comp-has (add-run-scope w of epoch parent ei) of) (task-has (add-run-scope w of epoch parent ei) of)) true)) (exact he)
  (have hr0 (= (r2-ok (add-run-scope w of epoch parent ei) (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei)) true))
  (simp only [r2-ok new-run-row he2 sc Bool.and_self])
  (have e (= (:runs (add-run-scope w of epoch parent ei)) (List.cons RunRow (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei) (:runs w)))) (rfl)
  (rw [e])
  (simp only [tbl-all hr0 Bool.true_and])
  (exact rest))

(a/theorem gr0-add-run-scope [w :- World, of :- Nat, epoch :- Nat, parent :- Nat, ei :- Nat]
  (=> (= (Bool.or (comp-has w of) (task-has w of)) true) (= (gr0 w) true) (= (gr0 (add-run-scope w of epoch parent ei)) true))
  (intros he h)
  (have hs := (gr0-sample w h))
  (have r := (gr0-rest-of w h))
  (have b1 (= (tbl-all (r1-ok (:runs (add-run-scope w of epoch parent ei))) (:res (add-run-scope w of epoch parent ei))) true))
  (simp only [add-run-scope bump set-next-id scope-ins set-scopes run-ins set-runs tbl-ins])
  (apply (tbl-all-mem-mono ResRow (r1-ok (:runs w)) _ (:res w) _ (grk-1 _ w r)))
  (intros z mz hz)
  (simp only [r1-ok Bool.and_eq_true] at hz)
  (have lb := (owner-below _ w z hs r mz))
  (have ne (= (Nat.beq (:next-id w) (:owner z)) false)) (cases q (Nat.beq (:next-id w) (:owner z))) (case [false] (rfl)) (case [true] (have e := (Nat.eq_of_beq_eq_true q)) (omega))
  (have l0 (= (listed-in z (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei)) true)) (simp only [listed-in new-run-row ne Bool.not_false Bool.true_or])
  (simp only [r1-ok tbl-all l0 (And.right hz) (any-cons-of RunRow (res-held z) (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei) (:runs w) (And.left hz)) Bool.and_self])
  (have b2 := (ars-r2 w of epoch parent ei he (grk-2 _ w r)))
  (have b3 (= (tbl-all (r3-ok (:cleanup (add-run-scope w of epoch parent ei)) (List.nil Nat)) (:runs (add-run-scope w of epoch parent ei))) true))
  (simp only [add-run-scope bump set-next-id scope-ins set-scopes run-ins set-runs tbl-ins tbl-all])
  (have h0 (= (r3-ok (:cleanup w) (List.nil Nat) (new-run-row (:next-id w) of epoch (+ (:next-id w) 1) ei)) true)) (rfl)
  (simp only [h0 (grk-3 _ w r) Bool.and_self])
  (exact (gr0-intro _ (inv-add-run-scope w of epoch parent ei hs) (grk-mk _ _ b1 b2 b3))))

;; ---- T4/T5/T11 run creation: the entity exists
(a/theorem comp-find-has2 [w :- World, x :- Nat, c :- CompRow]
  (=> (= (comp-find w x) (Option.some CompRow c)) (= (comp-has w (:id c)) true))
  (intro hc)
  (have i := (tbl-find-id CompRow comp-id x c (:comps w) hc))
  (have hh := (tbl-find-has CompRow comp-id x c (:comps w) hc))
  (have i2 (= (:id c) x)) (exact i)
  (simp only [comp-has i2]) (exact hh))
(a/theorem or-comp [w :- World, x :- Nat] (=> (= (comp-has w x) true) (= (Bool.or (comp-has w x) (task-has w x)) true))
  (intro h) (simp only [h Bool.true_or]))
(override! GR0 'inv-spawn-rows '[]
  '(a/theorem gr0-spawn-rows [w :- World, owner :- Nat, inputs :- (List Nat)]
     (=> (= (gr0 w) true) (= (gr0 (spawn-rows w owner inputs)) true))
     (intro h)
     (simp only [spawn-rows])
     (have h1 := (grx-task-ins (List.nil Nat) w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs) (rfl) h))
     (have th (= (Bool.or (comp-has (bump (task-ins w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs))) (:next-id w))
                          (task-has (bump (task-ins w (new-task-row (:next-id w) owner (+ (:next-id w) 1) inputs))) (:next-id w))) true))
     (simp only [task-has bump task-ins set-next-id set-tasks tbl-ins tbl-has-ins new-task-row task-id Nat.beq_refl Bool.true_or Bool.or_true])
     (exact (gr0-add-run-scope _ (:next-id w) 0 (task-scope-parent w owner) 0 th h1))))
(override! GR0 'inv-start-raw '[]
  '(a/theorem gr0-start-raw [w :- World, c :- CompRow]
     (=> (= (comp-has w (:id c)) true) (= (gr0 w) true) (= (gr0 (start-raw w c)) true))
     (intros hc h)
     (simp only [start-raw])
     (exact (grx-comp-upd (List.nil Nat) _ (:id c) (comp-start-row (:next-id w)) (comp-start-row-id (:next-id w)) (comp-start-row-pending (:next-id w))
              (gr0-add-run-scope w (:id c) (start-epoch c) 0 0 (or-comp w (:id c) hc) h)))))
(override! GR0 'inv-new-run-of '[]
  '(a/theorem gr0-new-run-of [w :- World, c :- CompRow, ei :- Nat]
     (=> (= (comp-has w (:id c)) true) (= (gr0 w) true) (= (gr0 (new-run-of w c ei)) true))
     (intros hc h)
     (simp only [new-run-of])
     (exact (grx-comp-upd (List.nil Nat) _ (:id c) (comp-set-run (:next-id w)) (comp-set-run-id (:next-id w)) (comp-set-run-pending (:next-id w))
              (gr0-add-run-scope w (:id c) (:epoch c) 0 ei (or-comp w (:id c) hc) h)))))
(override! GR0 'inv-dispatch-raw '[inv-cancel-pred inv-cut-suffix inv-consume-entry inv-new-run-of]
  '(a/theorem gr0-dispatch-raw [w :- World, c :- CompRow]
     (=> (= (comp-has w (:id c)) true) (= (gr0 w) true) (= (gr0 (dispatch-raw w c)) true))
     (intros hc h)
     (have h1 := (gr0-cancel-pred w c h))
     (have c1 := (ch-cancel-pred (:id c) w c (ch-intro (:id c) w (gr0-sample w h) hc)))
     (cases he (entry-edge w (:id c))) (case' [some e]) (case' [none])
     (simp only [dispatch-raw he])
     (exact (gr0-new-run-of _ c 0 (ch-rest-of _ _ (ch-cut-suffix (:id c) _ (:id c) false 0 0 c1)) (gr0-cut-suffix _ (:id c) false 0 0 h1)))
     (simp only [dispatch-raw he])
     (have c2 := (ch-consume-entry (:id c) _ e (ch-cut-suffix (:id c) _ (:id c) true (:at e) (:id e) c1)))
     (have h2 := (gr0-consume-entry _ e (gr0-cut-suffix _ (:id c) true (:at e) (:id e) h1)))
     (exact (gr0-new-run-of _ c _ (ch-rest-of _ _ c2) h2))))
(defn gr-patch3 [form]
  (->> (gr-patch2 form)
       (subst-forms #(= % '(inv-start-raw w c h)) (fn [_] '(inv-start-raw w c (comp-find-has2 w cid c hc) h)))
       (subst-forms #(= % '(inv-dispatch-raw w c h)) (fn [_] '(inv-dispatch-raw w c (comp-find-has2 w cid c hc) h)))))
(doseq [[n _] @@#'spindel.v2.lit/source-theorems] (patch! GR0 n gr-patch3))

;; ---- T17 arm: the new resource is held by its run; T15 ack: the resource and its listing go
(a/theorem any-elim-of [A :- Type, p :- (=> A Bool), q :- A, xs :- (List A)] (=> (List.Mem q xs) (= (p q) true) (= (tbl-any p xs) true))
  (induction xs)
  (case [nil] (intros m h) (cases m))
  (case [cons hd t ih] (intros m h) (cases m) (case [head] (simp only [tbl-any h Bool.true_or])) (case [tail m2] (simp only [tbl-any (ih m2 h) Bool.or_true]))))
(a/theorem nat-mem-cons-of [y :- Nat, x :- Nat, xs :- (List Nat)] (=> (= (nat-mem y xs) true) (= (nat-mem y (List.cons Nat x xs)) true))
  (intro h) (cases hb (Nat.beq x y)) (case [true] (simp only [nat-mem hb])) (case [false] (simp only [nat-mem hb]) (exact h)))
(a/theorem held-arm5 [z :- ResRow, n :- Nat, q :- RunRow] (=> (= (res-held z q) true) (= (res-held z (run-arm n q)) true))
  (intro hq) (simp only [res-held Bool.and_eq_true] at hq)
  (simp only [res-held run-arm (And.left hq) (nat-mem-cons-of (:id z) n (:resources q) (And.right hq)) Bool.and_self]))
(a/theorem listed-arm5 [z :- ResRow, n :- Nat, q :- RunRow] (=> (= (listed-in z q) true) (= (listed-in z (run-arm n q)) true))
  (intro hq) (simp only [listed-in Bool.or_eq_true] at hq)
  (cases hq)
  (case [inl a] (simp only [listed-in run-arm a Bool.true_or]))
  (case [inr b] (simp only [listed-in run-arm (nat-mem-cons-of (:id z) n (:resources q) b) Bool.or_true])))
(a/theorem gr0-arm-raw [w :- World, r :- RunRow, kind :- Nat]
  (=> (List.Mem r (:runs w)) (= (gr0 w) true) (= (gr0 (arm-raw w r kind)) true))
  (intros hm h)
  (have hs := (gr0-sample w h))
  (have rr := (gr0-rest-of w h))
  (have b1 (= (tbl-all (r1-ok (:runs (arm-raw w r kind))) (:res (arm-raw w r kind))) true))
  (simp only [arm-raw run-upd set-runs bump set-next-id resource-ins set-res tbl-ins tbl-all])
  (have hz0 (= (r1-ok (tbl-upd run-id (:id r) (run-arm (:next-id w)) (:runs w)) (ResRow.mk (:next-id w) (:id r) kind (:effect-index r) rp-armed)) true))
  (have m1 := (tbl-upd-mem-self RunRow run-id (run-arm (:next-id w)) r (:runs w) hm))
  (have a1 (= (tbl-any (res-held (ResRow.mk (:next-id w) (:id r) kind (:effect-index r) rp-armed)) (tbl-upd run-id (:id r) (run-arm (:next-id w)) (:runs w))) true))
  (have q (= (res-held (ResRow.mk (:next-id w) (:id r) kind (:effect-index r) rp-armed) (run-arm (:next-id w) r)) true))
  (simp only [res-held run-arm nat-mem Nat.beq_refl Bool.true_and])
  (exact (any-elim-of RunRow _ (run-arm (:next-id w) r) _ m1 q))
  (have a2 (= (tbl-all (listed-in (ResRow.mk (:next-id w) (:id r) kind (:effect-index r) rp-armed)) (tbl-upd run-id (:id r) (run-arm (:next-id w)) (:runs w))) true))
  (apply (tbl-all-upd RunRow run-id (:id r) (run-arm (:next-id w)) (fn [q :- RunRow] true) _ _ _ (:runs w) (all-true-of RunRow (fn [q :- RunRow] true) (fn [q :- RunRow] (Eq.refl true)) (:runs w))))
  (intros q h1 h2) (simp only [listed-in run-arm nat-mem Nat.beq_refl Bool.or_true])
  (intros q h1 h2) (simp only [listed-in run-id] at h2) (simp only [listed-in h2 Bool.not_false Bool.true_or])
  (simp only [r1-ok a1 a2 Bool.and_self])
  (have rest (= (tbl-all (r1-ok (tbl-upd run-id (:id r) (run-arm (:next-id w)) (:runs w))) (:res w)) true))
  (apply (tbl-all-mono ResRow (r1-ok (:runs w)) _ _ (:res w) (grk-1 _ w rr)))
  (intros z hz)
  (simp only [r1-ok Bool.and_eq_true] at hz)
  (have m2 (forall [q :- RunRow] (=> (= (res-held z q) true) (= (res-held z (run-arm (:next-id w) q)) true)))) (exact (held-arm5 z (:next-id w)))
  (have m3 (forall [q :- RunRow] (=> (= (listed-in z q) true) (= (listed-in z (run-arm (:next-id w) q)) true)))) (exact (listed-arm5 z (:next-id w)))
  (simp only [r1-ok (any-upd-mono RunRow run-id (:id r) (run-arm (:next-id w)) (res-held z) m2 (:runs w) (And.left hz))
              (tbl-all-upd RunRow run-id (:id r) (run-arm (:next-id w)) (listed-in z) (listed-in z)
                 (fn [q :- RunRow, h1 :- (= (listed-in z q) true), h2 :- (= (Nat.beq (run-id q) (:id r)) true)] (m3 q h1))
                 (fn [q :- RunRow, h1 :- (= (listed-in z q) true), h2 :- (= (Nat.beq (run-id q) (:id r)) false)] h1) (:runs w) (And.right hz)) Bool.and_self])
  (simp only [hz0 rest Bool.and_self])
  (have b2 (= (tbl-all (r2-ok (arm-raw w r kind)) (:runs (arm-raw w r kind))) true))
  (simp only [arm-raw run-upd set-runs])
  (rw [(tbl-all-upd-same RunRow run-id (:id r) (run-arm (:next-id w)) (r2-ok (arm-raw w r kind)) (fn [q :- RunRow] (Eq.refl (r2-ok (arm-raw w r kind) q))) (:runs w))])
  (exact (grk-2 _ w rr))
  (have b3 (= (tbl-all (r3-ok (:cleanup (arm-raw w r kind)) (List.nil Nat)) (:runs (arm-raw w r kind))) true))
  (simp only [arm-raw run-upd set-runs])
  (rw [(tbl-all-upd-same RunRow run-id (:id r) (run-arm (:next-id w)) (r3-ok (:cleanup w) (List.nil Nat)) (fn [q :- RunRow] (Eq.refl (r3-ok (:cleanup w) (List.nil Nat) q))) (:runs w))])
  (exact (grk-3 _ w rr))
  (exact (gr0-intro _ (inv-arm-raw w r kind hs) (grk-mk _ _ b1 b2 b3))))

(override! GR0 'inv-arm-park '[inv-take-park]
  '(a/theorem gr0-arm-park [w :- World, r :- RunRow, kind :- Nat, k :- Nat]
     (=> (List.Mem r (:runs w)) (= (gr0 w) true) (= (gr0 (arm-park w r kind k)) true))
     (intros hm h) (simp only [arm-park])
     (exact (gr0-take-park _ (run-arm (:next-id w) r) (:next-id w) k (gr0-arm-raw w r kind hm h)))))

(a/theorem held-unres5 [z :- ResRow, x :- Nat, q :- RunRow] (=> (= (Nat.beq (:id z) x) false) (= (res-held z (run-unres x q)) (res-held z q)))
  (intro h) (simp only [res-held run-unres (nat-mem-del (:id z) x (:resources q) h)]))
(a/theorem listed-unres5 [z :- ResRow, x :- Nat, q :- RunRow] (=> (= (Nat.beq (:id z) x) false) (= (listed-in z (run-unres x q)) (listed-in z q)))
  (intro h) (simp only [listed-in run-unres (nat-mem-del (:id z) x (:resources q) h)]))
(a/theorem ack-b1 [w :- World, z :- Nat, owner :- Nat]
  (=> (= (tbl-all (r1-ok (:runs w)) (:res w)) true)
      (= (tbl-all (r1-ok (:runs (ack-raw w z owner))) (:res (ack-raw w z owner))) true))
  (intro h0)
  (have s := (all-sub-del ResRow (r1-ok (:runs w)) resource-id z (:res w) h0))
  (have e1 (= (:res (ack-raw w z owner)) (tbl-del resource-id z (:res w)))) (rfl)
  (have e2 (= (:runs (ack-raw w z owner)) (tbl-upd run-id owner (run-unres z) (:runs w)))) (rfl)
  (rw [e1 e2])
  (apply (tbl-all-mono2 ResRow (r1-ok (:runs w)) (fn [q :- ResRow] (Bool.not (Nat.beq (resource-id q) z))) _ _ (tbl-del resource-id z (:res w)) s (del-ne-all ResRow resource-id z (:res w))))
  (intros zz h1 h2)
  (have ne (= (Nat.beq (:id zz) z) false)) (exact (bnot-true _ h2))
  (simp only [r1-ok Bool.and_eq_true] at h1)
  (simp only [r1-ok (tbl-any-upd-same RunRow (res-held zz) run-id owner (run-unres z) (fn [q :- RunRow] (held-unres5 zz z q ne)) (:runs w))
              (tbl-all-upd-same RunRow run-id owner (run-unres z) (listed-in zz) (fn [q :- RunRow] (listed-unres5 zz z q ne)) (:runs w))
              (And.left h1) (And.right h1) Bool.and_self]))
(a/theorem gr0-ack-raw [w :- World, z :- Nat, owner :- Nat]
  (=> (= (tbl-all (no-debtor z) (:edges w)) true) (= (gr0 w) true) (= (gr0 (ack-raw w z owner)) true))
  (intros hu h)
  (have hs := (gr0-sample w h))
  (have rr := (gr0-rest-of w h))
  (have b1 := (ack-b1 w z owner (grk-1 _ w rr)))
  (have e2 (= (:runs (ack-raw w z owner)) (tbl-upd run-id owner (run-unres z) (:runs w)))) (rfl)
  (have b2 (= (tbl-all (r2-ok (ack-raw w z owner)) (:runs (ack-raw w z owner))) true))
  (rw [e2])
  (rw [(tbl-all-upd-same RunRow run-id owner (run-unres z) (r2-ok (ack-raw w z owner)) (fn [q :- RunRow] (Eq.refl (r2-ok (ack-raw w z owner) q))) (:runs w))])
  (exact (grk-2 _ w rr))
  (have e3 (= (:cleanup (ack-raw w z owner)) (tbl-upd cleanup-id owner (cleanup-drop z) (:cleanup w)))) (rfl)
  (have b3 (= (tbl-all (r3-ok (:cleanup (ack-raw w z owner)) (List.nil Nat)) (:runs (ack-raw w z owner))) true))
  (rw [e2 e3])
  (rw [(tbl-all-upd-same RunRow run-id owner (run-unres z) (r3-ok (tbl-upd cleanup-id owner (cleanup-drop z) (:cleanup w)) (List.nil Nat))
         (fn [q :- RunRow] (Eq.refl (r3-ok (tbl-upd cleanup-id owner (cleanup-drop z) (:cleanup w)) (List.nil Nat) q))) (:runs w))])
  (apply (tbl-all-mono RunRow (r3-ok (:cleanup w) (List.nil Nat)) _ _ (:runs w) (grk-3 _ w rr)))
  (intros q hq)
  (simp only [r3-ok (tbl-has-upd CleanupRow cleanup-id owner (:id q) (cleanup-drop z) (fn [c :- CleanupRow] (Eq.refl (cleanup-id c))) (:cleanup w))])
  (exact hq)
  (exact (gr0-intro _ (inv-ack-raw w z owner hu hs) (grk-mk _ _ b1 b2 b3))))
(swap! (:renames GR0) assoc 'inv-ack-raw 'gr0-ack-raw 'inv-arm-raw 'gr0-arm-raw)
(defn gr-patch4 [form]
  (->> (gr-patch3 form)
       (subst-forms #(= % '(inv-arm-park w r kind k h)) (fn [_] '(inv-arm-park w r kind k (tok-run-mem w st r ht) h)))))
(doseq [[n _] @@#'spindel.v2.lit/source-theorems] (patch! GR0 n gr-patch4))

;; ===========================================================================
;; T12's retirable run: the cascade's last job retires it (bundles krb, neb over the cascade's jobs)
;; ===========================================================================
(a/defn kr-ok [k :- Nat, r :- RunRow] Bool (Bool.or (Bool.not (Nat.beq (:id r) k)) (retirable r)))
(a/defn krb-rest [k2r :- Nat, w :- World] Bool (tbl-all (kr-ok k2r) (:runs w)))
(a/defn krb [k2r :- Nat, w :- World] Bool (Bool.and (inv-sample w) (krb-rest k2r w)))
(a/defn ne-ok [k :- Nat, r :- RunRow] Bool (Bool.not (Nat.beq (:id r) k)))
(a/defn neb-rest [k3r :- Nat, w :- World] Bool (tbl-all (ne-ok k3r) (:runs w)))
(a/defn neb [k3r :- Nat, w :- World] Bool (Bool.and (inv-sample w) (neb-rest k3r w)))
(a/theorem krb-sample [k :- Nat, w :- World] (=> (= (krb k w) true) (= (inv-sample w) true)) (intro h) (simp only [krb Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem krb-rest-of [k :- Nat, w :- World] (=> (= (krb k w) true) (= (krb-rest k w) true)) (intro h) (simp only [krb Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem krb-intro [k :- Nat, w :- World] (=> (= (inv-sample w) true) (= (krb-rest k w) true) (= (krb k w) true)) (intros h1 h2) (simp only [krb h1 h2 Bool.and_self]))
(a/theorem krb-parts [k :- Nat, w :- World] (=> (= (krb k w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (krb-sample k w h))))
(a/theorem neb-sample [k :- Nat, w :- World] (=> (= (neb k w) true) (= (inv-sample w) true)) (intro h) (simp only [neb Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem neb-rest-of [k :- Nat, w :- World] (=> (= (neb k w) true) (= (neb-rest k w) true)) (intro h) (simp only [neb Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem neb-intro [k :- Nat, w :- World] (=> (= (inv-sample w) true) (= (neb-rest k w) true) (= (neb k w) true)) (intros h1 h2) (simp only [neb h1 h2 Bool.and_self]))
(a/theorem neb-parts [k :- Nat, w :- World] (=> (= (neb k w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (neb-sample k w h))))

;; run rows: krb under an edit that keeps the id and does not undo retirability; neb under any
(a/theorem krb-run-upd [k :- Nat, w :- World, x :- Nat, f :- (=> RunRow RunRow),
                        hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                        hk :- (forall [r :- RunRow] (=> (= (retirable r) true) (= (retirable (f r)) true)))]
  (=> (= (krb k w) true) (= (krb k (run-upd w x f)) true))
  (intro h)
  (have r := (krb-rest-of k w h)) (simp only [krb-rest] at r)
  (have r2 (= (krb-rest k (run-upd w x f)) true))
  (simp only [krb-rest run-upd set-runs])
  (apply (tbl-all-upd RunRow run-id x f (kr-ok k) (kr-ok k) _ _ (:runs w) r))
  (intros q h1 h2)
  (simp only [kr-ok Bool.or_eq_true] at h1)
  (simp only [kr-ok Bool.or_eq_true])
  (have e (= (:id (f q)) (:id q))) (exact (hid q))
  (rw [e])
  (cases h1) (case [inl a] (exact (Or.inl a))) (case [inr b] (exact (Or.inr (hk q b))))
  (intros q h1 h2) (exact h1)
  (exact (krb-intro k _ (inv-run-upd w x f hid (krb-sample k w h)) r2)))
(a/theorem neb-run-upd [k :- Nat, w :- World, x :- Nat, f :- (=> RunRow RunRow),
                        hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r)))]
  (=> (= (neb k w) true) (= (neb k (run-upd w x f)) true))
  (intro h)
  (have r := (neb-rest-of k w h)) (simp only [neb-rest] at r)
  (have r2 (= (neb-rest k (run-upd w x f)) true))
  (simp only [neb-rest run-upd set-runs])
  (apply (tbl-all-upd RunRow run-id x f (ne-ok k) (ne-ok k) _ _ (:runs w) r))
  (intros q h1 h2) (simp only [ne-ok] at h1) (simp only [ne-ok]) (have e (= (:id (f q)) (:id q))) (exact (hid q)) (rw [e]) (exact h1)
  (intros q h1 h2) (exact h1)
  (exact (neb-intro k _ (inv-run-upd w x f hid (neb-sample k w h)) r2)))
(a/theorem ret-cancel [r :- RunRow] (=> (= (retirable r) true) (= (retirable (run-cancel-row r)) true))
  (intro h) (simp only [retirable Bool.and_eq_true] at h)
  (have h2 := (And.right h))
  (simp only [retirable run-cancel-row Nat.beq_refl Bool.true_and Bool.and_eq_true]) (exact h2))
(a/theorem ret-wake [r :- RunRow] (=> (= (retirable r) true) (= (retirable (run-wake r)) true))
  (intro h)
  (have h0 := h)
  (simp only [retirable Bool.and_eq_true] at h0)
  (have e (= (:act r) act-done)) (exact (Nat.eq_of_beq_eq_true (And.left h0)))
  (have e2 (= (wake-act (:act r)) (:act r))) (simp only [wake-act e]) 
  (have e3 (= (retirable (run-wake r)) (retirable r))) (simp only [retirable run-wake e2])
  (rw [e3]) (exact h))

(a/theorem krb-runs-eq [k :- Nat, w :- World, w2 :- World] (=> (= (:runs w2) (:runs w)) (= (krb-rest k w) true) (= (krb-rest k w2) true))
  (intros e h) (simp only [krb-rest e]) (exact h))
(a/theorem neb-runs-eq [k :- Nat, w :- World, w2 :- World] (=> (= (:runs w2) (:runs w)) (= (neb-rest k w) true) (= (neb-rest k w2) true))
  (intros e h) (simp only [neb-rest e]) (exact h))
(a/theorem krb-cancel-row [k :- Nat, w :- World, x :- Nat] (=> (= (krb k w) true) (= (krb k (run-upd w x run-cancel-row)) true))
  (intro h) (exact (krb-run-upd k w x run-cancel-row run-cancel-row-id ret-cancel h)))
(a/theorem krb-wake [k :- Nat, w :- World, x :- Nat] (=> (= (krb k w) true) (= (krb k (run-upd w x run-wake)) true))
  (intro h) (exact (krb-run-upd k w x run-wake run-wake-run-id ret-wake h)))

(defn kr-patch [form]
  (subst-forms (fn [y] (and (seq? y) (= 'inv-run-upd (first y)) (#{'run-cancel-row 'run-wake} (nth y 3 nil))))
               (fn [[_ w x f _ h]] (list ({'run-cancel-row 'krcancel* 'run-wake 'krwake*} f) w x h)) form))
(def KRB (mk-bundle 'krb '[k2r :- Nat] "krb-" {'inv-run-upd ['(fn [q :- RunRow, h :- (= (retirable q) true)] h) 4]}))
(swap! (:renames KRB) assoc 'inv-parts 'krb-parts 'inv-run-upd 'krb-run-upd 'krcancel* 'krb-cancel-row 'krwake* 'krb-wake)
(doseq [[n _] @@#'spindel.v2.lit/source-theorems] (patch! KRB n kr-patch))
(def NEB (mk-bundle 'neb '[k3r :- Nat] "neb-" {}))
(swap! (:renames NEB) assoc 'inv-parts 'neb-parts 'inv-run-upd 'neb-run-upd)
(doseq [B [KRB NEB]]
  (doseq [o '[inv-scope-upd inv-pub-upd inv-source-upd inv-resource-upd inv-cleanup-upd inv-cleanup-del inv-cleanup-ins inv-set-pins
              inv-resource-del inv-scope-del inv-act-upd inv-task-upd inv-comp-upd inv-bump inv-edge-upd inv-drop-cred inv-drop-act inv-drop-edges
              inv-comp-del-unref inv-act-ins-fresh inv-task-ins-fresh inv-comp-ins-fresh inv-scope-ins-fresh inv-resource-ins-fresh inv-source-ins-fresh
              insert-edge-fresh-inv-sample]]
    (prim! B o nil)))
(prim! KRB 'inv-remove-edge '(krb-runs-eq k2r w (remove-edge w x) (runs-remove-edge w x) R))
(prim! KRB 'mark-edge-inv-sample '(krb-runs-eq k2r w (mark-edge w x) (runs-mark-edge w x) R))
(prim! KRB 'unmark-edge-inv-sample '(krb-runs-eq k2r w (unmark-edge w x) (runs-unmark-edge w x) R))
(prim! KRB 'inv-run-del '(all-sub-del RunRow (kr-ok k2r) run-id x (:runs w) R))
(prim! NEB 'inv-remove-edge '(neb-runs-eq k3r w (remove-edge w x) (runs-remove-edge w x) R))
(prim! NEB 'mark-edge-inv-sample '(neb-runs-eq k3r w (mark-edge w x) (runs-mark-edge w x) R))
(prim! NEB 'unmark-edge-inv-sample '(neb-runs-eq k3r w (unmark-edge w x) (runs-unmark-edge w x) R))
(prim! NEB 'inv-run-del '(all-sub-del RunRow (ne-ok k3r) run-id x (:runs w) R))

(lcopy! KRB 'inv-job-apply)
(lcopy! NEB 'inv-job-apply)

(a/defn is-jr [k :- Nat, j :- Job] Bool (match j [(jcancel a b) false] [(jretire x) (Nat.beq x k)] [(jclose s) false]))
(a/defn jr-in [k :- Nat, ks :- (List Job)] Bool (tbl-any (is-jr k) ks))

(a/theorem runs-rie [w :- World, sub :- (List Nat)] (= (:runs (remove-if-empty w sub)) (:runs w))
  (cases he (subtree-empty w sub))
  (case [false] (simp only [remove-if-empty he]))
  (case [true] (simp only [remove-if-empty he]) (exact (congrArg (fn [k :- SDK] (:runs k)) (sdk-scope-fold sub w)))))
(a/theorem ne-retire [V :- World, r :- RunRow] (= (neb-rest (:id r) (retire-local V r)) true)
  (simp only [neb-rest retire-local retire-with runs-rie cleanup-del set-cleanup run-del set-runs])
  (exact (del-ne-all RunRow run-id (:id r) _)))
(a/theorem has-false-ne5 [k :- Nat, xs :- (List RunRow)] (=> (= (tbl-has run-id k xs) false) (= (tbl-all (ne-ok k) xs) true))
  (induction xs)
  (case [nil] (intro h) (simp only [tbl-all]))
  (case [cons hd t ih]
    (intro h)
    (cases hb (Nat.beq (run-id hd) k))
    (case [true] (simp only [tbl-has hb] at h) (cases h))
    (case [false] (simp only [tbl-has hb] at h) (have hb2 (= (Nat.beq (:id hd) k) false)) (exact hb) (simp only [tbl-all ne-ok hb2 Bool.not_false (ih h) Bool.and_self]))))
(a/theorem ne-of-none [V :- World, k :- Nat] (=> (= (run-find V k) (Option.none RunRow)) (= (neb-rest k V) true))
  (intro h) (simp only [neb-rest]) (exact (has-false-ne5 k (:runs V) (tbl-find-none-has RunRow run-id k (:runs V) h))))

;; the cascade retires a retirable run whose retire job is queued (the worklist empties: P4)
(a/theorem track-cascade [k :- Nat, fuel :- (List Nat)]
  (forall [V :- World, ks :- (List Job)]
    (=> (= (krb k V) true) (Or (= (neb-rest k V) true) (= (jr-in k ks) true)) (= (:rest (cascade fuel V ks)) (List.nil Job))
        (= (neb-rest k (:world (cascade fuel V ks))) true)))
  (induction fuel)
  (case [nil]
    (intros V ks hk ho hr)
    (simp only [cascade] at hr) (simp only [cascade])
    (cases ho) (case [inl a] (exact a)) (case [inr b] (rw [hr] at b) (simp [jr-in tbl-any] at b)))
  (case [cons u f ih]
    (intros V ks hk ho hr)
    (cases ks)
    (case [nil] (simp only [cascade]) (cases ho) (case [inl a] (exact a)) (case [inr b] (simp [jr-in tbl-any] at b)))
    (case [cons j t]
      (simp only [cascade] at hr) (simp only [cascade])
      (apply (ih (job-apply V j) (List.append Job t (job-next V j)) (krb-job-apply k V j hk) _ hr))
      (cases ho)
      (case [inl a] (exact (Or.inl (neb-rest-of k _ (neb-job-apply k V j (neb-intro k V (krb-sample k V hk) a))))))
      (case [inr b]
        (simp only [jr-in tbl-any Bool.or_eq_true] at b)
        (cases b)
        (case [inr b2]
          (apply Or.inr)
          (simp only [jr-in tbl-any-app b2 Bool.true_or]))
        (case [inl b1]
          (apply Or.inl)
          (cases j)
          (case [jcancel a c] (simp [is-jr] at b1))
          (case [jclose s] (simp [is-jr] at b1))
          (case [jretire x]
            (simp only [is-jr] at b1)
            (have ex (= x k)) (exact (Nat.eq_of_beq_eq_true b1))
            (rw [ex])
            (cases hf (run-find V k))
            (case [none] (simp only [job-apply hf]) (exact (ne-of-none V k hf)))
            (case [some r1]
              (have m := (tbl-find-mem RunRow run-id k r1 (:runs V) hf))
              (have i (= (:id r1) k)) (exact (tbl-find-id RunRow run-id k r1 (:runs V) hf))
              (have kr := (tbl-all-mem RunRow (kr-ok k) r1 (:runs V) (krb-rest-of k V hk) m))
              (have i2 (= (Nat.beq (:id r1) k) true)) (rw [i]) (exact (Nat.beq_refl k))
              (simp only [kr-ok i2 Bool.not_true Bool.false_or] at kr)
              (simp only [job-apply hf kr])
              (rw [← i]) (exact (ne-retire V r1)))))))))

(a/theorem grx-disch [x :- Nat, xr :- (List Nat), V :- World]
  (=> (= (grx (List.cons Nat x xr) V) true) (= (neb-rest x V) true) (= (grx xr V) true))
  (intros h hn)
  (have r := (grx-rest-of _ V h))
  (simp only [neb-rest] at hn)
  (have b3 (= (tbl-all (r3-ok (:cleanup V) xr) (:runs V)) true))
  (apply (tbl-all-mono2 RunRow (r3-ok (:cleanup V) (List.cons Nat x xr)) (ne-ok x) _ _ (:runs V) (grk-3 _ V r) hn))
  (intros q h1 h2)
  (simp only [ne-ok] at h2)
  (have ne := (bnot-true _ h2))
  (simp only [r3-ok reach-mem ne] at h1)
  (exact h1)
  (exact (grx-intro xr V (grx-sample _ V h) (grk-mk xr V (grk-1 _ V r) (grk-2 _ V r) b3))))
(a/theorem jobs-nil [js :- (List Job)] (=> (= (jobs-empty js) true) (= js (List.nil Job)))
  (intro h) (cases js) (case [nil] (rfl)) (case [cons a b] (simp [jobs-empty] at h)))
(a/theorem jr-last [k :- Nat, js :- (List Job)] (= (jr-in k (List.append Job js (List.cons Job (Job.jretire k) (List.nil Job)))) true)
  (simp only [jr-in tbl-any-app tbl-any is-jr Nat.beq_refl Bool.true_or Bool.or_true]))
(a/theorem krb-of-find [w :- World, k :- Nat, r1 :- RunRow]
  (=> (= (inv-sample w) true) (= (run-find w k) (Option.some RunRow r1)) (= (retirable r1) true) (= (krb k w) true))
  (intros hs hf hr)
  (have m := (tbl-find-mem RunRow run-id k r1 (:runs w) hf))
  (have i (= (run-id r1) k)) (exact (tbl-find-id RunRow run-id k r1 (:runs w) hf))
  (have u := (uniq-all RunRow run-id retirable r1 (:runs w) (runs-nodup w hs) m hr))
  (rw [i] at u)
  (have rest (= (krb-rest k w) true))
  (simp only [krb-rest])
  (apply (tbl-all-mono RunRow _ _ _ (:runs w) u))
  (intros q hq)
  (simp only [same-id-then] at hq) (simp only [kr-ok]) (exact hq)
  (exact (krb-intro k w hs rest)))

;; T12 (complete-raw) with ga: the run becomes done; cleanup or a retire job at the end of the cascade
(a/theorem gr0-complete-raw [w :- World, r :- RunRow, res :- RunResult]
  (=> (= (tbl-any (act-of-run (:id r)) (:acts w)) false) (= (ga w) true) (= (gr0 w) true) (= (gr0 (complete-raw w r res)) true))
  (intros hn hga h)
  (have h0 := (grx-run-upd-x (List.nil Nat) w (:id r) run-complete-row run-complete-row-id rkr0-complete h))
  (have h1 := (grx-complete-body (List.cons Nat (:id r) (List.nil Nat)) _ r res h0))
  (have g0 := (ga-run-upd-free w (:id r) run-complete-row run-complete-row-id hn hga))
  (have g1 := (ga-complete-body _ r res g0))
  (have g2 := (ga-retire-after _ (:id r) g1))
  (have hs1 := (grx-sample _ _ h1))
  (simp only [complete-raw])
  (apply (grx-fin-if-final (List.nil Nat) _ (:of r)))
  (cases hf (run-find (:world (complete-body (run-upd w (:id r) run-complete-row) r res)) (:id r)))
  (case [none]
    (simp only [retire-after hf])
    (exact (grx-run-cascade (List.nil Nat) _ _ (grx-disch (:id r) (List.nil Nat) _ h1 (ne-of-none _ (:id r) hf)))))
  (case [some r1]
    (cases hr (retirable r1))
    (case [false]
      (simp only [retire-after hf hr])
      (exact (grx-run-cascade (List.nil Nat) _ _ (grx-cleanup-set (List.nil Nat) _ (:id r) _ h1))))
    (case [true]
      (have g3 (= (ga (retire-after (:world (complete-body (run-upd w (:id r) run-complete-row) r res)) (:id r))) true)) (exact g2)
      (simp only [retire-after hf hr] at g3)
      (simp only [retire-after hf hr])
      (have hd := (jobs-nil _ (casc-done-ga _ (List.append Job (:rest (complete-body (run-upd w (:id r) run-complete-row) r res))
                                                           (List.cons Job (Job.jretire (:id r)) (List.nil Job))) g3)))
      (have ne := (track-cascade (:id r) _ _ _ (krb-of-find _ (:id r) r1 hs1 hf hr) (Or.inr (jr-last (:id r) _)) hd))
      (exact (grx-disch (:id r) (List.nil Nat) _ (grx-run-cascade (List.cons Nat (:id r) (List.nil Nat)) _ _ h1) ne)))))

(swap! (:renames GR0) assoc 'inv-complete-raw 'gr0-complete-raw)
(defn- add-ga-premise [form call-from call-to]
  (let [[hd nm binders stmt & proof] form
        stmt2 (apply list '=> '(= (ga w) true) (rest stmt))
        proof2 (map (fn [t] (if (= t '(intro h)) '(intros hga h) t)) proof)]
    (subst-forms #(= % call-from) (fn [_] call-to) (apply list hd nm binders stmt2 proof2))))
(patch! GR0 't12-inv (fn [form] (gr-patch4 (add-ga-premise form '(inv-complete-raw w r _ h) '(inv-complete-raw w r _ (ga-free-of-tok w st r hga ht) hga h)))))
(patch! GR0 'raw0-inv (fn [form] (gr-patch4 (add-ga-premise form '(t12-inv w _ _ _ h) '(t12-inv w _ _ _ hga h)))))
(patch! GR0 'raw0g-inv (fn [form] (gr-patch4 (add-ga-premise form '(raw0-inv w it h) '(raw0-inv w it hga h)))))
(patch! GR0 'raw-inv (fn [form] (gr-patch4 (add-ga-premise form '(raw0g-inv w it h) '(raw0g-inv w it hga h)))))

(lcopy! GR0 'raw-inv)
(lcopy! GR0 'inv-detach)
(lcopy! GR0 'inv-demote-epoch)

;; ---- a run with a cleanup entry: its stored rows (scope, entity, ...) are cleanup rows
(a/theorem find-self [A :- Type, idf :- (=> A Nat), q :- A, xs :- (List A)]
  (=> (= (nat-nodup (tbl-ids idf xs)) true) (List.Mem q xs) (= (tbl-find idf (idf q) xs) (Option.some A q)))
  (induction xs)
  (case [nil] (intros hn m) (cases m))
  (case [cons hd t ih]
    (intros hn m)
    (simp only [tbl-ids nat-nodup Bool.and_eq_true] at hn)
    (cases m)
    (case [head] (simp only [tbl-find Nat.beq_refl]))
    (case [tail m2]
      (have mi := (mem-ids-has A idf q t m2))
      (have ne (= (Nat.beq (idf hd) (idf q)) false))
      (cases b (Nat.beq (idf hd) (idf q)))
      (case [false] (rfl))
      (case [true] (have e := (Nat.eq_of_beq_eq_true b)) (rw [← e] at mi) (have z := (bnot-true _ (And.left hn))) (rw [mi] at z) (cases z))
      (simp only [tbl-find ne (ih (And.right hn) m2)]))))
(a/theorem cl-rows-of [V :- World, c0 :- CleanupRow, y :- Nat]
  (=> (List.Mem c0 (:cleanup V)) (= (reach-mem y (cleanup-base V c0)) true) (= (reach-mem y (cleanup-rows V)) true))
  (intros m h)
  (simp only [cleanup-rows])
  (have g (forall [cs :- (List CleanupRow)] (=> (List.Mem c0 cs) (= (reach-mem y (cleanup-rows-in V cs)) true))))
  (intro cs) (induction cs)
  (case [nil] (intro m0) (cases m0))
  (case [cons hd t ih]
    (intro m0)
    (simp only [cleanup-rows-in reach-mem-append Bool.or_eq_true])
    (cases m0)
    (case [head] (apply Or.inl) (simp only [cleanup-contrib anc-close reach-mem-append h Bool.true_or]))
    (case [tail m2] (exact (Or.inr (ih m2)))))
  (exact (g (:cleanup V) m)))
(a/theorem cl-stored [V :- World, q :- RunRow, y :- Nat]
  (=> (= (inv-sample V) true) (List.Mem q (:runs V)) (= (tbl-has cleanup-id (:id q) (:cleanup V)) true)
      (= (reach-mem y (run-stored q)) true) (= (reach-mem y (cleanup-rows V)) true))
  (intros hs mq hc hy)
  (cases hf (tbl-find cleanup-id (:id q) (:cleanup V)))
  (case [none] (have z := (tbl-find-none-has CleanupRow cleanup-id (:id q) (:cleanup V) hf)) (rw [hc] at z) (cases z))
  (case [some c0]
    (have m := (tbl-find-mem CleanupRow cleanup-id (:id q) c0 (:cleanup V) hf))
    (have i (= (:run c0) (:id q))) (exact (tbl-find-id CleanupRow cleanup-id (:id q) c0 (:cleanup V) hf))
    (have rf (= (run-find V (:run c0)) (Option.some RunRow q))) (rw [i]) (exact (find-self RunRow run-id q (:runs V) (runs-nodup V hs) mq))
    (have hb (= (reach-mem y (cleanup-base V c0)) true))
    (cases b (Nat.beq y (:run c0)))
    (case [true] (simp only [cleanup-base reach-mem b]))
    (case [false] (simp only [cleanup-base reach-mem b reach-mem-append rf opt-rows hy Bool.or_true]))
    (exact (cl-rows-of V c0 y m hb))))

;; ---- demotion: a computation is deleted only with no run of it left (its runs are dead after the
;; demote's cascade, P4 with acts-alive; a dead run has a cleanup entry storing its entity)
(a/theorem stored-of [q :- RunRow] (= (reach-mem (:of q) (run-stored q)) true)
  (cases b (Nat.beq (:of q) (:scope q)))
  (case [true] (simp only [run-stored reach-mem b]))
  (case [false] (simp only [run-stored reach-mem b Nat.beq_refl])))
(a/theorem stored-scope [q :- RunRow] (= (reach-mem (:scope q) (run-stored q)) true)
  (simp only [run-stored reach-mem Nat.beq_refl]))
(a/theorem no-run-of [w :- World, c :- CompRow]
  (=> (= (gr0 w) true) (= (tbl-all (not-alive-of (:id c)) (:runs w)) true) (= (demote-keep w c) false)
      (= (tbl-all (fn [q :- RunRow] (Bool.not (Nat.beq (:of q) (:id c)))) (:runs w)) true))
  (intros h hd hk)
  (have hs := (gr0-sample w h))
  (have r3 := (grk-3 _ w (gr0-rest-of w h)))
  (apply (tbl-all-mem-mono RunRow _ _ (:runs w) _ (tbl-all-mono2 RunRow _ _ (both (not-alive-of (:id c)) (r3-ok (:cleanup w) (List.nil Nat)))
                                                    (fn [q :- RunRow, h1 :- (= (not-alive-of (:id c) q) true), h2 :- (= (r3-ok (:cleanup w) (List.nil Nat) q) true)] (both-of RunRow _ _ q h1 h2))
                                                    (:runs w) hd r3)))
  (intros q mq hq)
  (have h1 := (both-left RunRow _ _ q hq)) (have h2 := (both-right RunRow _ _ q hq))
  (cases ho (Nat.beq (:of q) (:id c)))
  (case [false] (simp only [ho Bool.not_false]))
  (case [true]
    (simp only [not-alive-of ho Bool.not_true Bool.or_false] at h1)
    (have na := (bnot-true _ h1))
    (simp only [r3-ok na reach-mem Bool.false_or Bool.or_false] at h2)
    (have eo (= (:of q) (:id c))) (exact (Nat.eq_of_beq_eq_true ho))
    (have st := (stored-of q))
    (rw [eo] at st)
    (have cr := (cl-stored w q (:id c) hs mq h2 st))
    (simp only [demote-keep cr Bool.or_true] at hk)
    (cases hk)))

(a/theorem gr0-comp-del-free [w :- World, cid :- Nat]
  (=> (= (tbl-all (fn [q :- RunRow] (Bool.not (Nat.beq (:of q) cid))) (:runs w)) true) (= (unreferenced w cid) true)
      (= (gr0 w) true) (= (gr0 (comp-del w cid)) true))
  (intros hn hu h)
  (have r := (gr0-rest-of w h))
  (have b1 (= (tbl-all (r1-ok (:runs (comp-del w cid))) (:res (comp-del w cid))) true)) (exact (grk-1 _ w r))
  (have b3 (= (tbl-all (r3-ok (:cleanup (comp-del w cid)) (List.nil Nat)) (:runs (comp-del w cid))) true)) (exact (grk-3 _ w r))
  (have b2 (= (tbl-all (r2-ok (comp-del w cid)) (:runs (comp-del w cid))) true))
  (apply (tbl-all-mono2 RunRow (r2-ok w) (fn [q :- RunRow] (Bool.not (Nat.beq (:of q) cid))) _ _ (:runs w) (grk-2 _ w r) hn))
  (intros q h1 h2)
  (have ne (= (Nat.beq cid (:of q)) false)) (rw [beq-comm]) (exact (bnot-true _ h2))
  (simp only [r2-ok comp-has comp-del set-comps (tbl-has-del-ne CompRow comp-id cid (:of q) (:comps w) ne)])
  (simp only [r2-ok comp-has] at h1) (exact h1)
  (exact (gr0-intro _ (inv-comp-del-unref w cid hu (gr0-sample w h)) (grk-mk _ _ b1 b2 b3))))

(a/theorem gr0-demote-finish-o [w :- World, cid :- Nat, vs :- (List Valid)]
  (=> (= (tbl-all (not-alive-of cid) (:runs w)) true) (= (gr0 w) true) (= (gr0 (demote-finish w cid vs)) true))
  (intros hd h)
  (cases hf (comp-find w cid))
  (case [none] (simp only [demote-finish hf]) (exact h))
  (case [some c]
    (have i (= (:id c) cid)) (exact (tbl-find-id CompRow comp-id cid c (:comps w) hf))
    (cases hk (demote-keep w c))
    (case [true] (simp only [demote-finish hf hk])
      (exact (grx-comp-upd (List.nil Nat) w cid (comp-make-idle vs) (comp-make-idle-id vs) (comp-make-idle-pending vs) h)))
    (case [false]
      (simp only [demote-finish hf hk])
      (have hd2 (= (tbl-all (not-alive-of (:id c)) (:runs w)) true)) (rw [i]) (exact hd)
      (have nr := (no-run-of w c h hd2 hk))
      (rw [i] at nr)
      (have h2 := (grx-drop-edges (List.nil Nat) w (edge-avoids cid) h))
      (exact (gr0-comp-del-free (drop-edges w (edge-avoids cid)) cid nr (drop-edges-avoids w cid) h2)))))

(a/theorem gr0-demote-aa [w :- World, cid :- Nat]
  (=> (= (acts-alive w) true) (= (gr0 w) true) (= (gr0 (demote w cid)) true))
  (intros ha h)
  (have hs := (gr0-sample w h))
  (cases hf (comp-find w cid))
  (case [none] (simp only [demote hf]) (exact h))
  (case [some c]
    (cases hi (:idle c))
    (case [true] (simp only [demote hf hi]) (exact h))
    (case [false]
      (have i (= (:id c) cid)) (exact (tbl-find-id CompRow comp-id cid c (:comps w) hf))
      (have dd := (demote-dead w c hs ha))
      (rw [i] at dd)
      (simp only [demote hf hi demote-edges])
      (have h1 := (gr0-demote-epoch _ cid (demote-cur w c) (grx-run-cascade (List.nil Nat) w (cancel-jobs (demote-cancels w c)) h)))
      (have h2 := (grx-drop-edges (List.nil Nat) _ (not-dep-of cid) h1))
      (have dd2 (= (tbl-all (not-alive-of cid) (:runs (drop-edges (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) cid (demote-cur w c)) (not-dep-of cid)))) true))
      (simp only [drop-edges set-comps set-edges runs-demote-epoch]) (exact dd)
      (exact (gr0-demote-finish-o _ cid _ dd2 h2)))))

;; ---- normalization with acts-alive (P2's round bundle bn carries it)
(a/theorem gr0-demote-fold [a :- Nat, k :- Nat, L :- (List Nat)]
  (forall [W :- World] (=> (= (bn a k W) true) (= (gr0 W) true) (= (gr0 (nat-fold demote W L)) true)))
  (induction L)
  (case [nil] (intros W hb h) (simp only [nat-fold]) (exact h))
  (case [cons x t ih]
    (intros W hb h)
    (simp only [nat-fold])
    (have p := (bn-parts a k W hb))
    (exact (ih (demote W x) (bn-demote a k W x hb) (gr0-demote-aa W x (And.left (And.right p)) h)))))
(a/theorem gr0-norm-round-aa [w :- World]
  (=> (= (acts-alive w) true) (= (gr0 w) true) (= (gr0 (norm-round w)) true))
  (intros ha h)
  (have hs := (gr0-sample w h))
  (have b0 := (bn-intro (alive-cnt w) (act-cnt w) w hs ha (Nat.le_refl _) (Nat.le_refl _)))
  (simp only [norm-round norm-round-lv])
  (exact (gr0-detach _ (gr0-demote-fold (alive-cnt w) (act-cnt w) _ _
           (bn-run-cascade (alive-cnt w) (act-cnt w) w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w))) b0)
           (grx-run-cascade (List.nil Nat) w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w))) h)))))
(a/theorem gr0-norm-loop-aa [fuel :- (List Nat)]
  (forall [w :- World] (=> (= (acts-alive w) true) (= (gr0 w) true) (= (gr0 (norm-loop fuel w)) true)))
  (induction fuel)
  (case [nil] (intros w ha h) (simp only [norm-loop]) (exact h))
  (case [cons x f ih]
    (intros w ha h)
    (cases hn (normalized w))
    (case [true] (simp only [norm-loop hn]) (exact h))
    (case [false]
      (have p := (bn-round w (gr0-sample w h) ha))
      (simp only [norm-loop hn])
      (exact (ih (norm-round w) (And.right p) (gr0-norm-round-aa w ha h))))))
(a/theorem gr0-normalize-aa [w :- World]
  (=> (= (acts-alive w) true) (= (gr0 w) true) (= (gr0 (normalize w)) true))
  (intros ha h)
  (have hs := (gr0-sample w h))
  (have p := (bn-parts _ _ _ (bn-detach (alive-cnt w) (act-cnt w) w (bn-intro _ _ w hs ha (Nat.le_refl _) (Nat.le_refl _)))))
  (simp only [normalize])
  (exact (gr0-norm-loop-aa _ (detach w) (And.left (And.right p)) (gr0-detach w h))))

;; ===========================================================================
;; Rule R's filter keeps every run, and with it its entity, its scope and its resources' owner
;; ===========================================================================
(a/theorem keep-of-cl [W :- World, y :- Nat] (=> (= (reach-mem y (cleanup-rows W)) true) (= (keep-fn W y) true))
  (intro h) (simp only [keep-fn keep-with h Bool.true_or Bool.or_true]))
(a/theorem cl-id [W :- World, x :- Nat] (=> (= (tbl-has cleanup-id x (:cleanup W)) true) (= (reach-mem x (cleanup-rows W)) true))
  (intro hc)
  (cases hf (tbl-find cleanup-id x (:cleanup W)))
  (case [none] (have z := (tbl-find-none-has CleanupRow cleanup-id x (:cleanup W) hf)) (rw [hc] at z) (cases z))
  (case [some c0]
    (have m := (tbl-find-mem CleanupRow cleanup-id x c0 (:cleanup W) hf))
    (have i (= (:run c0) x)) (exact (tbl-find-id CleanupRow cleanup-id x c0 (:cleanup W) hf))
    (have hb (= (reach-mem x (cleanup-base W c0)) true)) (simp only [cleanup-base reach-mem i Nat.beq_refl])
    (exact (cl-rows-of W c0 x m hb))))
(a/theorem retain-run [W :- World, q :- RunRow, y :- Nat]
  (=> (List.Mem q (:runs W)) (= (reach-mem y (run-contrib W q)) true) (= (reach-mem y (retain-succ W (:id q))) true))
  (intros m h)
  (have g := (gather-mem RunRow (id-is run-id (:id q)) (run-contrib W) q y (:runs W) m (Nat.beq_refl (:id q)) h))
  (simp only [retain-succ reach-mem-append g Bool.true_or Bool.or_true]))
(a/theorem nz-mem5 [x :- Nat] (=> (= (Nat.beq x 0) false) (= (reach-mem x (nz x)) true))
  (intro h) (simp only [nz h reach-mem Nat.beq_refl]))
(a/theorem task-pos5 [w :- World, y :- Nat] (=> (= (inv-sample w) true) (= (task-has w y) true) (= (Nat.beq y 0) false))
  (intros h hh)
  (have hm (= (nat-mem y (tbl-ids task-id (:tasks w))) true)) (rw [nat-mem-ids]) (exact hh)
  (exact (id-pos w y h (mem-app-r _ _ _ (mem-app-r _ _ _ (mem-app-l _ _ _ hm))))))
(a/theorem run-kept [W :- World, q :- RunRow]
  (=> (= (normalized W) true) (= (gr0 W) true) (List.Mem q (:runs W))
      (And (= (keep-fn W (:id q)) true) (And (= (keep-fn W (:of q)) true) (= (keep-fn W (:scope q)) true))))
  (intros hn h m)
  (have hs := (gr0-sample W h))
  (have r := (gr0-rest-of W h))
  (have r2 := (tbl-all-mem RunRow (r2-ok W) q (:runs W) (grk-2 _ W r) m))
  (have r3 := (tbl-all-mem RunRow (r3-ok (:cleanup W) (List.nil Nat)) q (:runs W) (grk-3 _ W r) m))
  (simp only [r2-ok Bool.and_eq_true] at r2)
  (have so := (scope-pos W (:scope q) hs (And.right r2)))
  (have oo (= (Nat.beq (:of q) 0) false))
  (have e1 := (And.left r2))
  (simp only [Bool.or_eq_true] at e1)
  (cases e1)
  (case [inl a] (exact (comp-pos W (:of q) hs a)))
  (case [inr b] (exact (task-pos5 W (:of q) hs b)))
  (cases ha (run-alive q))
  (case [true]
    (have l := (normalized-runs W q hn m ha))
    (have ls (= (reach-mem (:scope q) (run-contrib W q)) true)) (simp only [run-contrib ha reach-mem-append (nz-mem5 (:scope q) so) Bool.true_or])
    (have lo (= (reach-mem (:of q) (run-contrib W q)) true)) (simp only [run-contrib ha reach-mem-append (nz-mem5 (:of q) oo) Bool.true_or Bool.or_true])
    (exact (And.intro (keep-of-live W (:id q) l)
             (And.intro (keep-of-live W (:of q) (live-close W (:id q) (:of q) l (retain-run W q (:of q) m lo)))
                        (keep-of-live W (:scope q) (live-close W (:id q) (:scope q) l (retain-run W q (:scope q) m ls)))))))
  (case [false]
    (simp only [r3-ok ha reach-mem Bool.false_or Bool.or_false] at r3)
    (exact (And.intro (keep-of-cl W (:id q) (cl-id W (:id q) r3))
             (And.intro (keep-of-cl W (:of q) (cl-stored W q (:of q) hs m r3 (stored-of q)))
                        (keep-of-cl W (:scope q) (cl-stored W q (:scope q) hs m r3 (stored-scope q))))))))

(a/theorem keep-all-of [A :- Type, K :- (=> Nat Bool), idf :- (=> A Nat), xs :- (List A)]
  (=> (forall [q :- A] (=> (List.Mem q xs) (= (K (idf q)) true))) (= (tbl-keep K idf xs) xs))
  (induction xs)
  (case [nil] (intro h) (simp only [tbl-keep]))
  (case [cons hd t ih]
    (intro h)
    (have k := (h hd (List.Mem.head t)))
    (simp only [tbl-keep k (ih (fn [q :- A, m :- (List.Mem q t)] (h q (List.Mem.tail hd m))))])))
(a/theorem gr0-filter [W :- World]
  (=> (= (normalized W) true) (= (gr0 W) true) (= (filter-safe W) true) (= (gr0 (rule-r-filter W)) true))
  (intros hn h hf)
  (have r := (gr0-rest-of W h))
  (rw [rule-r-filter-eq])
  (have kr (= (tbl-keep (keep-fn W) run-id (:runs W)) (:runs W)))
  (exact (keep-all-of RunRow (keep-fn W) run-id (:runs W) (fn [q :- RunRow, m :- (List.Mem q (:runs W))] (And.left (run-kept W q hn h m)))))
  (have er (= (:runs (filter-world (keep-fn W) W)) (:runs W))) (simp only [filter-world kr])
  (have b1 (= (tbl-all (r1-ok (:runs (filter-world (keep-fn W) W))) (:res (filter-world (keep-fn W) W))) true))
  (rw [er]) (simp only [filter-world])
  (exact (tbl-all-keep ResRow (keep-fn W) resource-id (r1-ok (:runs W)) (r1-ok (:runs W))
           (fn [z :- ResRow, h1 :- (= (r1-ok (:runs W) z) true), h2 :- (= (keep-fn W (resource-id z)) true)] h1) (:res W) (grk-1 _ W r)))
  (have b2 (= (tbl-all (r2-ok (filter-world (keep-fn W) W)) (:runs (filter-world (keep-fn W) W))) true))
  (rw [er])
  (apply (tbl-all-mem-mono RunRow (r2-ok W) _ (:runs W) _ (grk-2 _ W r)))
  (intros q m hq)
  (have kk := (run-kept W q hn h m))
  (simp only [r2-ok Bool.and_eq_true Bool.or_eq_true] at hq)
  (simp only [r2-ok comp-has task-has scope-has filter-world tbl-has-keep (And.left (And.right kk)) (And.right (And.right kk)) Bool.true_and Bool.and_eq_true Bool.or_eq_true])
  (simp only [comp-has task-has scope-has] at hq)
  (exact hq)
  (have b3 (= (tbl-all (r3-ok (:cleanup (filter-world (keep-fn W) W)) (List.nil Nat)) (:runs (filter-world (keep-fn W) W))) true))
  (rw [er]) (exact (grk-3 _ W r))
  (exact (gr0-intro _ (inv-filter-world W (keep-fn W) (gr0-sample W h) hf) (grk-mk _ _ b1 b2 b3))))

(a/theorem gr0-rule-r-round [w :- World]
  (=> (= (acts-alive w) true) (= (gr0 w) true) (= (filter-safe (normalize w)) true) (= (gr0 (rule-r-round w)) true))
  (intros ha h hf)
  (simp only [rule-r-round])
  (exact (gr0-filter (normalize w) (normalized-ok w (gr0-sample w h) ha) (gr0-normalize-aa w ha h) hf)))
(a/theorem gr0-rr-loop [fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (acts-alive w0) true) (= (gr0 w0) true) (= (rr-safe fuel w0) true)
                            (= (gr0 (rr-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 ha h hs) (simp only [rr-safe] at hs) (simp only [rr-loop]) (exact (gr0-rule-r-round w0 ha h hs)))
  (case [cons x f ih]
    (intros w0 ha h hs)
    (have hs0 := (rr-safe-head x f w0 hs))
    (have h1 := (gr0-rule-r-round w0 ha h hs0))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false]
      (rw [(rr-loop-f x f (rule-r-round w0) ho)])
      (exact (ih (rule-r-round w0) (acts-alive-round w0 (gr0-sample w0 h) ha) h1 (And.right (rr-safe-f x f w0 hs ho)))))
    (case [true] (rw [(rr-loop-t x f (rule-r-round w0) ho)]) (exact h1))))
(a/theorem gr0-rule-r [w :- World] (=> (= (acts-alive w) true) (= (gr0 w) true) (= (rule-r-safe w) true) (= (gr0 (rule-r w)) true))
  (intros ha h hs)
  (have hs2 (= (rr-safe (List.cons Nat 0 (all-ids w)) w) true)) (exact hs)
  (rw [rule-r-eq5])
  (exact (gr0-rr-loop (List.cons Nat 0 (all-ids w)) w ha h hs2)))
(a/theorem step-gr0 [w :- World, it :- Item]
  (=> (= (ga w) true) (= (gr0 w) true) (= (rule-r-safe (:world (raw w it))) true) (= (gr0 (:world (world-step w it))) true))
  (intros hg h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true] (have e2 := (step-accepted w it ha)) (rw [e2])
    (exact (gr0-rule-r (:world (raw w it)) (raw-acts-alive w it hg) (raw-gr0 w it hg h) hs))))
(a/theorem gr0-empty [] (= (gr0 empty-world) true) (rfl))

;; ---- literal I1, all clauses
(a/defn i1-runs [w :- World] Bool (Bool.and (tbl-all (res-owner-ok w) (:res w)) (tbl-all (run-entity-ok w) (:runs w))))
(a/theorem i1-runs-of [w :- World] (=> (= (gr0 w) true) (= (i1-runs w) true))
  (intro h)
  (have r := (gr0-rest-of w h))
  (have a1 (= (tbl-all (res-owner-ok w) (:res w)) true))
  (apply (tbl-all-mono ResRow (r1-ok (:runs w)) _ _ (:res w) (grk-1 _ w r)))
  (intros z hz)
  (simp only [r1-ok Bool.and_eq_true] at hz)
  (apply (any-elim RunRow (res-held z) _ (:runs w) (And.left hz)))
  (intros q mq hq)
  (simp only [res-held Bool.and_eq_true] at hq)
  (have e (= (:id q) (:owner z))) (exact (Nat.eq_of_beq_eq_true (And.left hq)))
  (simp only [res-owner-ok run-has])
  (rw [← e]) (exact (tbl-find-has-mem w q mq))
  (have a2 (= (tbl-all (run-entity-ok w) (:runs w)) true))
  (apply (tbl-all-mono RunRow (r2-ok w) _ _ (:runs w) (grk-2 _ w r)))
  (intros q hq) (simp only [r2-ok] at hq) (simp only [run-entity-ok]) (exact hq)
  (simp only [i1-runs a1 a2 Bool.and_self]))

(a/defn p3h [w :- World] Bool (Bool.and (p3g w) (gr0 w)))
(a/theorem p3h-parts [w :- World] (=> (= (p3h w) true) (And (= (p3g w) true) (= (gr0 w) true)))
  (intro h) (simp only [p3h Bool.and_eq_true] at h) (exact h))
(a/theorem p3h-empty [] (= (p3h empty-world) true) (rfl))
(a/theorem step-p3h [w :- World, it :- Item] (=> (= (p3h w) true) (= (p3h (:world (world-step w it))) true))
  (intro h)
  (have p := (p3h-parts w h))
  (have pg := (p3g-parts w (And.left p)))
  (have pf := (p3f-parts w (And.left pg)))
  (have pe := (p3e-parts w (And.left pf)))
  (have pd := (p3d-parts w (And.left pe)))
  (have pc := (p3c-parts w (And.left pd)))
  (have pb := (p3b-parts w (And.left pc)))
  (have a1 := (step-p3g w it (And.left p)))
  (have a2 := (step-gr0 w it (And.left pb) (And.right p) (step-rule-r-safe w it (And.left pc))))
  (simp only [p3h a1 a2 Bool.and_self]))

(a/theorem i1-scope-of [w :- World] (=> (= (lit-i1-scope w) true) (= (tbl-all (scope-parent-ok w) (:scopes w)) true))
  (intro h) (simp only [lit-i1-scope] at h)
  (apply (tbl-all-mono ScopeRow (lit-scope-parent w) _ _ (:scopes w) h))
  (intros s hs)
  (simp only [lit-scope-parent Bool.or_eq_true] at hs)
  (simp only [scope-parent-ok Bool.or_eq_true])
  (cases hs) (case [inl a] (exact (Or.inl a)))
  (case [inr b] (cases b) (case [inl b1] (exact (Or.inr (Or.inl b1)))) (case [inr b2] (exact (Or.inr (Or.inr (Or.inl b2)))))))
;; Theorem: literal I1 (every clause: scope parents, owners of tasks/computations/sources, resource
;; owners, run entities and scopes) after every step from a p3h world
(a/theorem step-lit-i1-total [w :- World, it :- Item]
  (=> (= (p3h w) true) (= (inv-i1 (:world (world-step w it))) true))
  (intro h)
  (have q := (step-p3h w it h))
  (have p := (p3h-parts _ q))
  (have pg := (p3g-parts _ (And.left p)))
  (have pf := (p3f-parts _ (And.left pg)))
  (have pe := (p3e-parts _ (And.left pf)))
  (have sc := (i1-scope-of _ (g1-rest-of _ (And.right pe))))
  (have ow := (And.right (And.right pg)))
  (simp only [i1-own Bool.and_eq_true] at ow)
  (have rr := (i1-runs-of _ (And.right p)))
  (simp only [i1-runs Bool.and_eq_true] at rr)
  (simp only [inv-i1 sc (And.left ow) (And.left (And.right ow)) (And.right (And.right ow)) (And.left rr) (And.right rr) Bool.and_self]))

