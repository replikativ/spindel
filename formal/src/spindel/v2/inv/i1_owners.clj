(ns spindel.v2.inv.i1-owners
  "Literal I1, owner clauses for tasks, computations and sources, through `world-step`, kernel-checked
  (Init only). §6 I1: a task's or computation's owner is 0 (detached) or an existing scope or
  computation; a source's owner exists, or it is detached (owner 0) and closed.

  The existence half is Rule R's: its loop runs rounds until no row has a missing owner
  (`no-orphans`), so the step's world has none once the loop stops for that reason, not for its fuel.
  Termination (`rule-r-no-orphans`): the owner count (`own-count`, rows with a non-zero owner)
  never grows through normalization (bundle NZ, every well-formed lemma of `normalize` restated by
  the generic step tree) or the filter, and drops at each round whose input has an orphan (`detach-lt`:
  detach sets the first orphan's owner to 0; the owner view `ow` of sources, tasks and computation
  keys is kept by the fires inside detach-source); the fuel 1 + #ids exceeds the count.
  The closed half: bundle `i1-detached-closed` (a source with owner 0 is closed, and every run's scope is not 0, so
  a source created in a run gets a non-zero owner: its computation or its current scope).

  Theorems:
    rule-r-no-orphans          well-formed w, rule-r-safe w -> no-orphans (rule-r w)
    step-i1-detached-closed                   i1-detached-closed w, rule-r-safe raw -> i1-detached-closed (world-step w it)
    chain-to-i1-detached-closed = chain-to-i5-dep-final && i1-detached-closed && lit-i1-own  step-chain-to-i1-detached-closed, chain-to-i1-detached-closed-empty
    step-lit-i1-owners-total   chain-to-i1-detached-closed w -> lit-i1-own (world-step w it)
  I1's resource owners and run entities/scopes: spindel.v2.inv.i1-runs (chain-to-i1-runs)."
  (:require [ansatz.core :as a]
            [spindel.v2.pres.frames :as frames]
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
            [spindel.v2.pres.tree :as tree]
            [spindel.v2.pres.part :refer :all]
            [spindel.v2.inv.copier :refer :all]
            [spindel.v2.inv.idle :refer :all]
            [spindel.v2.inv.base :refer :all]
            [spindel.v2.inv.i10 :refer :all]
            [spindel.v2.inv.i11 :refer :all]
            [spindel.v2.inv.i1-scopes :refer :all]
            [spindel.v2.inv.i5 :refer :all]))

;; ===========================================================================
;; Part A. The owner count never grows through normalization (bundle NZ)
;; ===========================================================================

;; ---- the owner count: rows (sources, tasks, computations) with a non-zero owner
(a/defn nzs [s :- SourceRow] Bool (Bool.not (Nat.beq (:owner s) 0)))
(a/defn nzt [t :- TaskRow] Bool (Bool.not (Nat.beq (:owner t) 0)))
(a/defn nzc [c :- CompRow] Bool (Bool.not (Nat.beq (:owner c) 0)))
(a/defn own-count [w :- World] Nat
  (+ (tbl-count nzs (:sources w)) (+ (tbl-count nzt (:tasks w)) (tbl-count nzc (:comps w)))))
(a/defn owner-count-at-most [n :- Nat, w :- World] Bool (Bool.and (well-formed w) (Nat.ble (own-count w) n)))
(a/defn owner-count-at-most-rest [n :- Nat, w :- World] Bool (Nat.ble (own-count w) n))

(a/theorem owner-count-at-most-well-formed [n :- Nat, w :- World] (=> (= (owner-count-at-most n w) true) (= (well-formed w) true))
  (intro h) (simp only [owner-count-at-most Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem owner-count-at-most-rest-of [n :- Nat, w :- World] (=> (= (owner-count-at-most n w) true) (= (owner-count-at-most-rest n w) true))
  (intro h) (simp only [owner-count-at-most Bool.and_eq_true] at h) (simp only [owner-count-at-most-rest]) (exact (And.right h)))
(a/theorem owner-count-at-most-intro [n :- Nat, w :- World] (=> (= (well-formed w) true) (= (owner-count-at-most-rest n w) true) (= (owner-count-at-most n w) true))
  (intros h1 h2) (simp only [owner-count-at-most-rest] at h2) (simp only [owner-count-at-most h1 h2 Bool.and_self]))
(a/theorem owner-count-at-most-parts [n :- Nat, w :- World]
  (=> (= (owner-count-at-most n w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (owner-count-at-most-well-formed n w h))))

(a/theorem tbl-count-upd-le [A :- Type, idf :- (=> A Nat), x :- Nat, f :- (=> A A), p :- (=> A Bool),
                             hf :- (forall [r :- A] (=> (= (p (f r)) true) (= (p r) true))), xs :- (List A)]
  (<= (tbl-count p (tbl-upd idf x f xs)) (tbl-count p xs))
  (induction xs)
  (case [nil] (simp only [tbl-upd tbl-count]) (exact (Nat.le_refl 0)))
  (case [cons h t ih]
    (cases hx (Nat.beq (idf h) x))
    (case [false] (simp only [tbl-upd hx tbl-count-cons]) (omega))
    (case [true]
      (simp only [tbl-upd hx tbl-count-cons])
      (cases hp (p (f h)))
      (case [false] (have z (= (b2n false) 0)) (rfl) (simp only [hp z]) (omega))
      (case [true] (have q := (hf h hp)) (simp only [hp q]) (omega)))))
(a/theorem tbl-count-keep-le [A :- Type, K :- (=> Nat Bool), idf :- (=> A Nat), p :- (=> A Bool), xs :- (List A)]
  (<= (tbl-count p (tbl-keep K idf xs)) (tbl-count p xs))
  (induction xs)
  (case [nil] (simp only [tbl-keep tbl-count]) (exact (Nat.le_refl 0)))
  (case [cons h t ih]
    (cases hk (K (idf h)))
    (case [false] (simp only [tbl-keep hk tbl-count-cons]) (omega))
    (case [true] (simp only [tbl-keep hk tbl-count-cons]) (omega))))

;; the rest from a count bound: edits that do not raise the count
(a/theorem owner-count-at-most-rest-le [n :- Nat, w :- World, w2 :- World]
  (=> (<= (own-count w2) (own-count w)) (= (owner-count-at-most-rest n w) true) (= (owner-count-at-most-rest n w2) true))
  (intros hl h) (simp only [owner-count-at-most-rest Nat.ble_eq] at h) (simp only [owner-count-at-most-rest Nat.ble_eq]) (omega))

(a/theorem oc-source-upd [w :- World, x :- Nat, f :- (=> SourceRow SourceRow),
                          hk :- (forall [s :- SourceRow] (=> (= (nzs (f s)) true) (= (nzs s) true)))]
  (<= (own-count (source-upd w x f)) (own-count w))
  (simp only [own-count source-upd set-sources])
  (have l := (tbl-count-upd-le SourceRow source-id x f nzs hk (:sources w)))
  (omega))
(a/theorem oc-task-upd [w :- World, x :- Nat, f :- (=> TaskRow TaskRow),
                        hk :- (forall [s :- TaskRow] (=> (= (nzt (f s)) true) (= (nzt s) true)))]
  (<= (own-count (task-upd w x f)) (own-count w))
  (simp only [own-count task-upd set-tasks])
  (have l := (tbl-count-upd-le TaskRow task-id x f nzt hk (:tasks w)))
  (omega))
(a/theorem oc-comp-upd [w :- World, x :- Nat, f :- (=> CompRow CompRow),
                        hk :- (forall [s :- CompRow] (=> (= (nzc (f s)) true) (= (nzc s) true)))]
  (<= (own-count (comp-upd w x f)) (own-count w))
  (simp only [own-count comp-upd set-comps])
  (have l := (tbl-count-upd-le CompRow comp-id x f nzc hk (:comps w)))
  (omega))
(a/theorem oc-comp-del [w :- World, x :- Nat] (<= (own-count (comp-del w x)) (own-count w))
  (simp only [own-count comp-del set-comps])
  (have l := (tbl-count-del-le CompRow comp-id x nzc (:comps w)))
  (omega))
(a/theorem oc-filter [w :- World, K :- (=> Nat Bool)] (<= (own-count (filter-world K w)) (own-count w))
  (simp only [own-count filter-world])
  (have l1 := (tbl-count-keep-le SourceRow K source-id nzs (:sources w)))
  (have l2 := (tbl-count-keep-le TaskRow K task-id nzt (:tasks w)))
  (have l3 := (tbl-count-keep-le CompRow K comp-id nzc (:comps w)))
  (omega))

(a/theorem owner-count-at-most-source-upd [nzn :- Nat, w :- World, x :- Nat, f :- (=> SourceRow SourceRow),
                           hid :- (forall [s :- SourceRow] (= (source-id (f s)) (source-id s))),
                           hk :- (forall [s :- SourceRow] (= (nzs (f s)) (nzs s)))]
  (=> (= (owner-count-at-most nzn w) true) (= (owner-count-at-most nzn (source-upd w x f)) true))
  (intro h)
  (exact (owner-count-at-most-intro nzn _ (well-formed-source-upd w x f hid (owner-count-at-most-well-formed nzn w h))
           (owner-count-at-most-rest-le nzn w _ (oc-source-upd w x f (fn [s :- SourceRow, q :- (= (nzs (f s)) true)] (Eq.trans (Eq.symm (hk s)) q))) (owner-count-at-most-rest-of nzn w h)))))
(a/theorem owner-count-at-most-task-upd [nzn :- Nat, w :- World, x :- Nat, f :- (=> TaskRow TaskRow),
                         hid :- (forall [s :- TaskRow] (= (task-id (f s)) (task-id s))),
                         hk :- (forall [s :- TaskRow] (= (nzt (f s)) (nzt s)))]
  (=> (= (owner-count-at-most nzn w) true) (= (owner-count-at-most nzn (task-upd w x f)) true))
  (intro h)
  (exact (owner-count-at-most-intro nzn _ (well-formed-task-upd w x f hid (owner-count-at-most-well-formed nzn w h))
           (owner-count-at-most-rest-le nzn w _ (oc-task-upd w x f (fn [s :- TaskRow, q :- (= (nzt (f s)) true)] (Eq.trans (Eq.symm (hk s)) q))) (owner-count-at-most-rest-of nzn w h)))))
(a/theorem owner-count-at-most-comp-upd [nzn :- Nat, w :- World, x :- Nat, f :- (=> CompRow CompRow),
                         hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                         hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                         hk :- (forall [s :- CompRow] (= (nzc (f s)) (nzc s)))]
  (=> (= (owner-count-at-most nzn w) true) (= (owner-count-at-most nzn (comp-upd w x f)) true))
  (intro h)
  (exact (owner-count-at-most-intro nzn _ (well-formed-comp-upd w x f hid hp (owner-count-at-most-well-formed nzn w h))
           (owner-count-at-most-rest-le nzn w _ (oc-comp-upd w x f (fn [s :- CompRow, q :- (= (nzc (f s)) true)] (Eq.trans (Eq.symm (hk s)) q))) (owner-count-at-most-rest-of nzn w h)))))

(a/theorem nzs-detach [s :- SourceRow] (=> (= (nzs (source-detach-row s)) true) (= (nzs s) true))
  (intro h) (simp [nzs source-detach-row] at h))
(a/theorem nzt-detach [s :- TaskRow] (=> (= (nzt (task-detach-row s)) true) (= (nzt s) true))
  (intro h) (simp [nzt task-detach-row] at h))
(a/theorem nzc-detach [s :- CompRow] (=> (= (nzc (comp-detach-row s)) true) (= (nzc s) true))
  (intro h) (simp [nzc comp-detach-row] at h))
(a/theorem owner-count-at-most-source-detach [nzn :- Nat, w :- World, x :- Nat]
  (=> (= (owner-count-at-most nzn w) true) (= (owner-count-at-most nzn (source-upd w x source-detach-row)) true))
  (intro h)
  (exact (owner-count-at-most-intro nzn _ (well-formed-source-upd w x source-detach-row source-detach-row-id (owner-count-at-most-well-formed nzn w h))
           (owner-count-at-most-rest-le nzn w _ (oc-source-upd w x source-detach-row nzs-detach) (owner-count-at-most-rest-of nzn w h)))))
(a/theorem owner-count-at-most-task-detach [nzn :- Nat, w :- World, x :- Nat]
  (=> (= (owner-count-at-most nzn w) true) (= (owner-count-at-most nzn (task-upd w x task-detach-row)) true))
  (intro h)
  (exact (owner-count-at-most-intro nzn _ (well-formed-task-upd w x task-detach-row task-detach-row-id (owner-count-at-most-well-formed nzn w h))
           (owner-count-at-most-rest-le nzn w _ (oc-task-upd w x task-detach-row nzt-detach) (owner-count-at-most-rest-of nzn w h)))))
(a/theorem owner-count-at-most-comp-detach [nzn :- Nat, w :- World, x :- Nat]
  (=> (= (owner-count-at-most nzn w) true) (= (owner-count-at-most nzn (comp-upd w x comp-detach-row)) true))
  (intro h)
  (exact (owner-count-at-most-intro nzn _ (well-formed-comp-upd w x comp-detach-row comp-detach-row-id comp-detach-row-pending (owner-count-at-most-well-formed nzn w h))
           (owner-count-at-most-rest-le nzn w _ (oc-comp-upd w x comp-detach-row nzc-detach) (owner-count-at-most-rest-of nzn w h)))))

(def NZ (mk-bundle 'owner-count-at-most '[nzn :- Nat] "owner-count-at-most-"
          {'well-formed-source-upd ['(fn [s :- SourceRow] (Eq.refl (nzs s))) 4]
           'well-formed-task-upd ['(fn [t :- TaskRow] (Eq.refl (nzt t))) 4]
           'well-formed-comp-upd ['(fn [c :- CompRow] (Eq.refl (nzc c))) 5]}))
(swap! (:renames NZ) assoc 'well-formed-parts 'owner-count-at-most-parts 'well-formed-source-upd 'owner-count-at-most-source-upd 'well-formed-task-upd 'owner-count-at-most-task-upd
       'well-formed-comp-upd 'owner-count-at-most-comp-upd)
(doseq [o '[well-formed-scope-upd well-formed-pub-upd well-formed-resource-upd well-formed-cleanup-upd well-formed-cleanup-del well-formed-cleanup-ins well-formed-set-pins
            well-formed-resource-del well-formed-scope-del well-formed-act-upd well-formed-run-upd well-formed-run-del well-formed-bump well-formed-edge-upd well-formed-fork-del]]
  (prim! NZ o nil))
(prim! NZ 'well-formed-comp-del-unref '(owner-count-at-most-rest-le nzn w (comp-del w x) (oc-comp-del w x) R))

(a/theorem oc-comps-pend [w :- World, w2 :- World, x :- Nat, f :- (=> CompRow CompRow),
                           hk :- (forall [c :- CompRow] (= (nzc (f c)) (nzc c)))]
  (=> (= (:sources w2) (:sources w)) (= (:tasks w2) (:tasks w)) (= (:comps w2) (tbl-upd comp-id x f (:comps w)))
      (<= (own-count w2) (own-count w)))
  (intros h1 h2 h3)
  (simp only [own-count h1 h2 h3 (tbl-count-upd-same CompRow comp-id x f nzc hk (:comps w))])
  (exact (Nat.le_refl _)))
(a/theorem oc-remove-edge [w :- World, x :- Nat] (<= (own-count (remove-edge w x)) (own-count w))
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]) (exact (Nat.le_refl _)))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [remove-edge hf hm]) (exact (Nat.le_refl _)))
    (case [true] (simp only [remove-edge hf hm])
      (exact (oc-comps-pend w (comp-upd (edge-del w x) (:creditor e) comp-dec-pending) (:creditor e) comp-dec-pending (fn [c :- CompRow] (Eq.refl (nzc c))) (rfl) (rfl) (rfl))))))
(a/theorem oc-mark-edge [w :- World, x :- Nat] (<= (own-count (mark-edge w x)) (own-count w))
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]) (exact (Nat.le_refl _)))
  (case [some e]
    (cases hm (:marked e))
    (case [true] (simp only [mark-edge hf hm]) (exact (Nat.le_refl _)))
    (case [false] (simp only [mark-edge hf hm])
      (exact (oc-comps-pend w (comp-upd (edge-upd w x (edge-set-marked true)) (:creditor e) comp-inc-pending) (:creditor e) comp-inc-pending (fn [c :- CompRow] (Eq.refl (nzc c))) (rfl) (rfl) (rfl))))))
(a/theorem oc-unmark-edge [w :- World, x :- Nat] (<= (own-count (unmark-edge w x)) (own-count w))
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]) (exact (Nat.le_refl _)))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [unmark-edge hf hm]) (exact (Nat.le_refl _)))
    (case [true] (simp only [unmark-edge hf hm])
      (exact (oc-comps-pend w (comp-upd (edge-upd w x (edge-set-marked false)) (:creditor e) comp-dec-pending) (:creditor e) comp-dec-pending (fn [c :- CompRow] (Eq.refl (nzc c))) (rfl) (rfl) (rfl))))))
(a/theorem oc-drop-cred [w :- World, a :- Nat] (<= (own-count (drop-cred-edges w a)) (own-count w))
  (exact (oc-comps-pend w (drop-cred-edges w a) a (comp-set-pending 0) (fn [c :- CompRow] (Eq.refl (nzc c))) (rfl) (rfl) (rfl))))
(a/theorem count-resync [es :- (List EdgeRow), cs :- (List CompRow)] (= (tbl-count nzc (comps-resync es cs)) (tbl-count nzc cs))
  (induction cs)
  (case [nil] (simp only [comps-resync tbl-count]))
  (case [cons h t ih] (simp only [comps-resync tbl-count-cons ih comp-resync comp-set-pending nzc])))
(a/theorem oc-drop-edges [w :- World, p :- (=> EdgeRow Bool)] (<= (own-count (drop-edges w p)) (own-count w))
  (simp only [own-count drop-edges set-comps set-edges count-resync]) (exact (Nat.le_refl _)))
(prim! NZ 'well-formed-remove-edge '(owner-count-at-most-rest-le nzn w (remove-edge w x) (oc-remove-edge w x) R))
(prim! NZ 'well-formed-mark-edge '(owner-count-at-most-rest-le nzn w (mark-edge w x) (oc-mark-edge w x) R))
(prim! NZ 'well-formed-unmark-edge '(owner-count-at-most-rest-le nzn w (unmark-edge w x) (oc-unmark-edge w x) R))
(prim! NZ 'well-formed-drop-cred-edges '(owner-count-at-most-rest-le nzn w (drop-cred-edges w a) (oc-drop-cred w a) R))
(prim! NZ 'well-formed-drop-act '(owner-count-at-most-rest-le nzn w (drop-act w a) (oc-drop-cred w a) R))
(prim! NZ 'well-formed-drop-edges '(owner-count-at-most-rest-le nzn w (drop-edges w p) (oc-drop-edges w p) R))

(a/theorem nzt-cancel-result [t :- TaskRow] (= (nzt (task-cancel-result t)) (nzt t))
  (cases h (Nat.beq (:tag (:result t)) res-none)) (all_goals (simp only [task-cancel-result h nzt])))
(a/theorem owner-count-at-most-task-cancel [nzn :- Nat, w :- World, x :- Nat]
  (=> (= (owner-count-at-most nzn w) true) (= (owner-count-at-most nzn (task-upd w x task-cancel-result)) true))
  (intro h) (exact (owner-count-at-most-task-upd nzn w x task-cancel-result task-cancel-result-id nzt-cancel-result h)))
;; owner-count-at-most on the generic tree: a detached or cancelled row keeps its owner (the four row lemmas above)
(tree/part! NZ
  :sites '{[well-formed-source-upd source-detach-row] (owner-count-at-most-source-detach nzn w x h0)
           [well-formed-task-upd task-detach-row]     (owner-count-at-most-task-detach nzn w x h0)
           [well-formed-comp-upd comp-detach-row]     (owner-count-at-most-comp-detach nzn w x h0)
           [well-formed-task-upd task-cancel-result]  (owner-count-at-most-task-cancel nzn w x h0)})

(tree/restate! NZ '[well-formed-normalize])

;; ===========================================================================
;; Part B. Detach lowers it when there is an orphan; Rule R terminates with no orphan
;; ===========================================================================

;; ---- detach strictly lowers the owner count when there is an orphan

(a/defn id-nz [A :- Type :implicit, idf :- (=> A Nat), q :- (=> A Bool), L :- (List Nat), r :- A] Bool
  (Bool.and (reach-mem (idf r) L) (q r)))

(a/theorem bool-absurd [b :- Bool, c :- Bool] (=> (= b false) (= b true) (= c true))
  (intros h1 h2) (rw [h1] at h2) (cases h2))

(a/theorem tbl-count-upd-lt [A :- Type, idf :- (=> A Nat), x :- Nat, f :- (=> A A), p :- (=> A Bool),
                             hf :- (forall [r :- A] (= (p (f r)) false)), xs :- (List A)]
  (=> (= (tbl-any (id-nz idf p (List.cons Nat x (List.nil Nat))) xs) true) (< (tbl-count p (tbl-upd idf x f xs)) (tbl-count p xs)))
  (induction xs)
  (case [nil] (intro h) (simp [tbl-any] at h))
  (case [cons h t ih]
    (intro ha)
    (have le := (tbl-count-upd-le A idf x f p (fn [r :- A, q :- (= (p (f r)) true)] (bool-absurd (p (f r)) (p r) (hf r) q)) t))
    (cases hx (Nat.beq (idf h) x))
    (case [false]
      (simp only [tbl-any id-nz reach-mem hx Bool.false_and Bool.false_or] at ha)
      (have l2 := (ih ha))
      (simp only [tbl-upd hx tbl-count-cons]) (omega))
    (case [true]
      (simp only [tbl-upd hx tbl-count-cons (hf h)])
      (cases hp (p h))
      (case [true] (have z (= (b2n true) 1)) (rfl) (have z0 (= (b2n false) 0)) (rfl) (simp only [z z0]) (omega))
      (case [false]
        (simp only [tbl-any id-nz reach-mem hx hp Bool.and_false Bool.false_or] at ha)
        (have l2 := (ih ha))
        (have z0 (= (b2n false) 0)) (rfl) (simp only [z0]) (omega)))))

;; a witness in L's ids moves to the tail when the head x is not its id
(a/theorem any-cons-split [A :- Type, idf :- (=> A Nat), q :- (=> A Bool), x :- Nat, t :- (List Nat), xs :- (List A)]
  (=> (= (tbl-any (id-nz idf q (List.cons Nat x t)) xs) true)
      (Or (= (tbl-any (id-nz idf q (List.cons Nat x (List.nil Nat))) xs) true) (= (tbl-any (id-nz idf q t) xs) true)))
  (induction xs)
  (case [nil] (intro h) (simp [tbl-any] at h))
  (case [cons hd tl ih]
    (intro h)
    (simp only [tbl-any Bool.or_eq_true] at h)
    (cases h)
    (case [inr b]
      (have r := (ih b))
      (cases r)
      (case [inl r1] (exact (Or.inl (Eq.trans (congrArg (fn [z :- Bool] (Bool.or (id-nz idf q (List.cons Nat x (List.nil Nat)) hd) z)) r1) (Bool.or_true _)))))
      (case [inr r2] (exact (Or.inr (Eq.trans (congrArg (fn [z :- Bool] (Bool.or (id-nz idf q t hd) z)) r2) (Bool.or_true _))))))
    (case [inl a]
      (simp only [id-nz reach-mem Bool.and_eq_true] at a)
      (cases hb (Nat.beq (idf hd) x))
      (case [true] (apply Or.inl) (simp only [tbl-any id-nz reach-mem hb (And.right a) Bool.and_self Bool.true_or]))
      (case [false]
        (simp only [hb] at a)
        (apply Or.inr) (simp only [tbl-any id-nz (And.left a) (And.right a) Bool.and_self Bool.true_or])))))

;; rows with an id other than x are unchanged by an edit at x
(a/theorem any-upd-other [A :- Type, idf :- (=> A Nat), q :- (=> A Bool), x :- Nat, f :- (=> A A), t :- (List Nat), xs :- (List A)]
  (=> (= (tbl-any (id-nz idf q (List.cons Nat x (List.nil Nat))) xs) false) (= (tbl-any (id-nz idf q t) xs) true)
      (= (tbl-any (id-nz idf q t) (tbl-upd idf x f xs)) true))
  (induction xs)
  (case [nil] (intros h1 h2) (simp [tbl-any] at h2))
  (case [cons hd tl ih]
    (intros h1 h2)
    (simp only [tbl-any Bool.or_eq_false_iff] at h1)
    (cases hx (Nat.beq (idf hd) x))
    (case [false]
      (simp only [tbl-upd hx tbl-any])
      (simp only [tbl-any Bool.or_eq_true] at h2)
      (cases h2)
      (case [inl a] (simp only [a Bool.true_or]))
      (case [inr b] (simp only [(ih (And.right h1) b) Bool.or_true])))
    (case [true]
      (simp only [tbl-upd hx tbl-any])
      (have n1 (= (id-nz idf q t hd) false))
      (have a0 := (And.left h1))
      (simp only [id-nz reach-mem hx Bool.true_and] at a0)
      (simp only [id-nz a0 Bool.and_false])
      (simp only [tbl-any n1 Bool.false_or] at h2)
      (simp only [(ih (And.right h1) h2) Bool.or_true]))))

;; ---- the owner view of a world: sources, tasks, computation (id, has-owner) keys
(a/structure CK1 [] (id Nat) (nz Bool))
(a/defn ck1 [c :- CompRow] CK1 (CK1.mk (:id c) (nzc c)))
(a/defn ck1s [cs :- (List CompRow)] (List CK1) (match cs nil (List.nil CK1) (cons h t) (List.cons CK1 (ck1 h) (ck1s t))))
(a/structure OW [] (srcs (List SourceRow)) (tsks (List TaskRow)) (cks (List CK1)))
(a/defn ow [w :- World] OW (OW.mk (:sources w) (:tasks w) (ck1s (:comps w))))

(a/theorem ck1s-upd [x :- Nat, f :- (=> CompRow CompRow), hk :- (forall [c :- CompRow] (= (ck1 (f c)) (ck1 c))), cs :- (List CompRow)]
  (= (ck1s (tbl-upd comp-id x f cs)) (ck1s cs))
  (induction cs)
  (case [nil] (simp only [tbl-upd ck1s]))
  (case [cons h t ih]
    (cases hx (Nat.beq (comp-id h) x))
    (case [false] (simp only [tbl-upd hx ck1s ih]))
    (case [true] (simp only [tbl-upd hx ck1s ih (hk h)]))))
(a/theorem ck1s-resync [es :- (List EdgeRow), cs :- (List CompRow)] (= (ck1s (comps-resync es cs)) (ck1s cs))
  (induction cs)
  (case [nil] (simp only [comps-resync ck1s]))
  (case [cons h t ih] (simp only [comps-resync ck1s ih ck1 comp-resync comp-set-pending nzc])))

(a/theorem ow-comp-upd [w :- World, x :- Nat, f :- (=> CompRow CompRow), hk :- (forall [c :- CompRow] (= (ck1 (f c)) (ck1 c)))]
  (= (ow (comp-upd w x f)) (ow w))
  (simp only [ow comp-upd set-comps (ck1s-upd x f hk (:comps w))]))
(a/theorem ow-remove-edge [w :- World, y :- Nat] (= (ow (remove-edge w y)) (ow w))
  (cases hf (edge-find w y)) (case' [some e]) (case' [none])
  (simp only [remove-edge hf])
  (cases hm (:marked e))
  (simp only [remove-edge hf hm])
  (simp only [remove-edge hf hm]) (exact (ow-comp-upd (edge-del w y) (:creditor e) comp-dec-pending (fn [c :- CompRow] (Eq.refl (ck1 c))))))
(a/theorem ow-fill-slot [w :- World, a :- ActRow, y :- Nat, v :- RunResult] (= (ow (fill-slot w a y v)) (ow w))
  (cases hm (act-ready (act-fill y v a)))
  (all_goals (simp only [fill-slot hm resume]))
  (exact (ow-comp-upd (set-edges w (tbl-filter (cred-ne (:id a)) (:edges w))) (:id a) (comp-set-pending 0) (fn [c :- CompRow] (Eq.refl (ck1 c))))))
(a/theorem ow-fire-dep [w :- World, e :- EdgeRow] (= (ow (fire-dep w e)) (ow w))
  (have ei (= (ow (invalidate w e)) (ow w)))
  (simp only [invalidate]) (exact (ow-comp-upd (edge-upd w (:id e) (edge-set-phase ph-fired)) (:creditor e) comp-inc-epoch (fn [c :- CompRow] (Eq.refl (ck1 c)))))
  (cases ha (act-with-member (:id e) (:acts w))) (case' [some a]) (case' [none])
  (simp only [fire-dep ha]) (exact ei)
  (cases hc (Bool.and (run-current-of w (:run a) (:creditor e)) (deb-avail w (:debtor e))))
  (simp only [fire-dep ha hc]) (exact ei)
  (simp only [fire-dep ha hc deliver-dep])
  (have e1 (= (ow (dep-consumed w e)) (ow w)))
  (cases hf (deb-final w (:debtor e)))
  (simp only [dep-consumed hf])
  (simp only [dep-consumed hf]) (exact (ow-remove-edge w (:id e)))
  (exact (Eq.trans (ow-fill-slot _ a _ _) e1)))
(a/theorem ow-fire-wait [res :- RunResult, w :- World, e :- EdgeRow] (= (ow (fire-wait res w e)) (ow w))
  (cases hc (Nat.beq (:creditor e) 0))
  (case [true] (simp only [fire-wait hc]) (exact (ow-remove-edge w (:id e))))
  (case [false]
    (simp only [fire-wait hc])
    (cases ha (act-find w (:creditor e))) (case' [some a]) (case' [none])
    (simp only [fire-wait-act ha])
    (cases hr (run-current w (:run a)))
    (simp only [fire-wait-act ha hr])
    (simp only [fire-wait-act ha hr]) (exact (ow-fill-slot _ a _ _))))
(a/theorem ow-fire-edge [res :- RunResult, w :- World, y :- Nat] (= (ow (fire-edge res w y)) (ow w))
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
  (simp only [fire-edge hf hp hk1 hk2]) (exact (ow-fire-wait res w e))
  (simp only [fire-edge hf hp hk1]) (exact (ow-fire-dep w e)))
(a/theorem ow-fold [f :- (=> World Nat World), hf :- (forall [w :- World, x :- Nat] (= (ow (f w x)) (ow w))), xs :- (List Nat)]
  (forall [w :- World] (= (ow (nat-fold f w xs)) (ow w)))
  (induction xs)
  (case [nil] (intro w) (simp only [nat-fold]))
  (case [cons h t ih] (intro w) (simp only [nat-fold]) (exact (Eq.trans (ih (f w h)) (hf w h)))))
(a/theorem ow-finalize-loop [fuel :- (List Nat)]
  (forall [w :- World, ds :- (List Nat)] (= (ow (:world (finalize-loop fuel w ds))) (ow w)))
  (induction fuel)
  (case [nil] (intros w ds) (simp only [finalize-loop]))
  (case [cons h f ih]
    (intros w ds)
    (cases ds)
    (simp only [finalize-loop])
    (rename_i d t)
    (simp only [finalize-loop])
    (have e1 (= (ow (finalize-one w d)) (ow w)))
    (simp only [ow finalize-one drop-edges set-comps set-edges ck1s-resync])
    (exact (Eq.trans (ih (finalize-one w d) _) e1))))
(a/theorem ow-detach-source [w :- World, x :- Nat]
  (= (ow (detach-source w x)) (OW.mk (tbl-upd source-id x source-detach-row (:sources w)) (:tasks w) (ck1s (:comps w))))
  (simp only [detach-source t10-finalize-debtor wake-closed])
  (exact (Eq.trans (ow-finalize-loop _ _ _) (ow-fold (fire-edge _) (ow-fire-edge _) _ (source-upd w x source-detach-row)))))

;; ---- the count through a fold is bounded by the start (the NZ copies)
(a/theorem oc-le-of [f :- (=> World Nat World),
                     hf :- (forall [nzn :- Nat, w :- World, x :- Nat] (=> (= (owner-count-at-most nzn w) true) (= (owner-count-at-most nzn (f w x)) true))),
                     xs :- (List Nat), w :- World]
  (=> (= (well-formed w) true) (<= (own-count (nat-fold f w xs)) (own-count w)))
  (intro hs)
  (have b (= (owner-count-at-most (own-count w) w) true)) (simp only [owner-count-at-most hs Nat.ble_eq Nat.le_refl Bool.and_self]) (simp)
  (have b2 := (owner-count-at-most-nat-fold (own-count w) f (hf (own-count w)) xs w b))
  (simp only [owner-count-at-most Bool.and_eq_true Nat.ble_eq] at b2)
  (exact (And.right b2)))
(a/theorem oc-le-one [f :- (=> World Nat World),
                      hf :- (forall [nzn :- Nat, w :- World, x :- Nat] (=> (= (owner-count-at-most nzn w) true) (= (owner-count-at-most nzn (f w x)) true))),
                      x :- Nat, w :- World]
  (=> (= (well-formed w) true) (<= (own-count (f w x)) (own-count w)))
  (intro hs) (exact (oc-le-of f hf (List.cons Nat x (List.nil Nat)) w hs)))

(a/theorem any-nil-false [A :- Type, idf :- (=> A Nat), q :- (=> A Bool), xs :- (List A)]
  (= (tbl-any (id-nz idf q (List.nil Nat)) xs) false)
  (induction xs)
  (case [nil] (simp only [tbl-any]))
  (case [cons h t ih] (simp only [tbl-any id-nz reach-mem Bool.false_and Bool.false_or ih])))

(a/theorem count-ck1 [cs :- (List CompRow)] (= (tbl-count nzc cs) (tbl-count (fn [k :- CK1] (:nz k)) (ck1s cs)))
  (induction cs) (case [nil] (simp only [tbl-count ck1s])) (case [cons h t ih] (simp only [tbl-count ck1s ih ck1])))
(a/theorem oc-ow [w :- World, w2 :- World] (=> (= (ow w2) (ow w)) (= (own-count w2) (own-count w)))
  (intro e)
  (have e1 (= (:sources w2) (:sources w))) (exact (congrArg (fn [q :- OW] (:srcs q)) e))
  (have e2 (= (:tasks w2) (:tasks w))) (exact (congrArg (fn [q :- OW] (:tsks q)) e))
  (have e3 (= (ck1s (:comps w2)) (ck1s (:comps w)))) (exact (congrArg (fn [q :- OW] (:cks q)) e))
  (simp only [own-count e1 e2 (count-ck1 (:comps w2)) (count-ck1 (:comps w)) e3]))

(a/theorem oc-source-step [W :- World, x :- Nat]
  (=> (= (tbl-any (id-nz source-id nzs (List.cons Nat x (List.nil Nat))) (:sources W)) true)
      (< (own-count (detach-source W x)) (own-count W)))
  (intro h)
  (have e := (oc-ow (source-upd W x source-detach-row) (detach-source W x) (ow-detach-source W x)))
  (rw [e])
  (simp only [own-count source-upd set-sources])
  (have l := (tbl-count-upd-lt SourceRow source-id x source-detach-row nzs (fn [s :- SourceRow] (Eq.refl false)) (:sources W) h))
  (omega))
(a/theorem oc-task-step [W :- World, x :- Nat]
  (=> (= (tbl-any (id-nz task-id nzt (List.cons Nat x (List.nil Nat))) (:tasks W)) true)
      (< (own-count (detach-task W x)) (own-count W)))
  (intro h)
  (simp only [own-count detach-task task-upd set-tasks])
  (have l := (tbl-count-upd-lt TaskRow task-id x task-detach-row nzt (fn [s :- TaskRow] (Eq.refl false)) (:tasks W) h))
  (omega))
(a/theorem oc-comp-step [W :- World, x :- Nat]
  (=> (= (tbl-any (id-nz comp-id nzc (List.cons Nat x (List.nil Nat))) (:comps W)) true)
      (< (own-count (detach-comp W x)) (own-count W)))
  (intro h)
  (simp only [own-count detach-comp comp-upd set-comps])
  (have l := (tbl-count-upd-lt CompRow comp-id x comp-detach-row nzc (fn [s :- CompRow] (Eq.refl false)) (:comps W) h))
  (omega))

(a/theorem oc-fold-lt [A :- Type, f :- (=> World Nat World), tab :- (=> World (List A)), idf :- (=> A Nat), q :- (=> A Bool), g :- (=> A A),
                       hf :- (forall [nzn :- Nat, w :- World, x :- Nat] (=> (= (owner-count-at-most nzn w) true) (= (owner-count-at-most nzn (f w x)) true))),
                       hs :- (forall [w :- World, x :- Nat] (=> (= (well-formed w) true) (= (well-formed (f w x)) true))),
                       ht :- (forall [w :- World, x :- Nat] (= (tab (f w x)) (tbl-upd idf x g (tab w)))),
                       hstep :- (forall [w :- World, x :- Nat] (=> (= (tbl-any (id-nz idf q (List.cons Nat x (List.nil Nat))) (tab w)) true)
                                                                    (< (own-count (f w x)) (own-count w)))),
                       L :- (List Nat)]
  (forall [W :- World] (=> (= (well-formed W) true) (= (tbl-any (id-nz idf q L) (tab W)) true)
                           (< (own-count (nat-fold f W L)) (own-count W))))
  (induction L)
  (case [nil] (intros W h0 h) (rw [any-nil-false] at h) (cases h))
  (case [cons x t ih]
    (intros W h0 h)
    (simp only [nat-fold])
    (have mono := (oc-le-of f hf t (f W x) (hs W x h0)))
    (have one := (oc-le-one f hf x W h0))
    (cases hx (tbl-any (id-nz idf q (List.cons Nat x (List.nil Nat))) (tab W)))
    (case [true] (have l := (hstep W x hx)) (omega))
    (case [false]
      (have sp := (any-cons-split A idf q x t (tab W) h))
      (have ht2 (= (tbl-any (id-nz idf q t) (tab W)) true))
      (cases sp) (case [inl a] (rw [hx] at a) (cases a)) (case [inr b] (exact b))
      (have h2 (= (tbl-any (id-nz idf q t) (tab (f W x))) true))
      (rw [ht]) (exact (any-upd-other A idf q x g t (tab W) hx ht2))
      (have l := (ih (f W x) (hs W x h0) h2))
      (omega))))

(a/theorem tasks-source-fold [L :- (List Nat)]
  (forall [W :- World] (And (= (:tasks (nat-fold detach-source W L)) (:tasks W)) (= (ck1s (:comps (nat-fold detach-source W L))) (ck1s (:comps W)))))
  (induction L)
  (case [nil] (intro W) (exact (And.intro (rfl) (rfl))))
  (case [cons x t ih]
    (intro W) (simp only [nat-fold])
    (have od := (ow-detach-source W x))
    (have a1 (= (:tasks (detach-source W x)) (:tasks W))) (exact (congrArg (fn [q :- OW] (:tsks q)) od))
    (have a2 (= (ck1s (:comps (detach-source W x))) (ck1s (:comps W)))) (exact (congrArg (fn [q :- OW] (:cks q)) od))
    (have r := (ih (detach-source W x)))
    (exact (And.intro (Eq.trans (And.left r) a1) (Eq.trans (And.right r) a2)))))
(a/theorem comps-task-fold [L :- (List Nat)]
  (forall [W :- World] (= (:comps (nat-fold detach-task W L)) (:comps W)))
  (induction L)
  (case [nil] (intro W) (simp only [nat-fold]))
  (case [cons x t ih] (intro W) (simp only [nat-fold]) (exact (Eq.trans (ih (detach-task W x)) (rfl)))))
(a/theorem any-ck1 [L :- (List Nat), cs :- (List CompRow)]
  (= (tbl-any (id-nz comp-id nzc L) cs) (tbl-any (fn [k :- CK1] (Bool.and (reach-mem (:id k) L) (:nz k))) (ck1s cs)))
  (induction cs) (case [nil] (simp only [tbl-any ck1s])) (case [cons h t ih] (simp only [tbl-any ck1s ih id-nz ck1 comp-id])))

(a/theorem any-mono-mem [A :- Type, p :- (=> A Bool), q :- (=> A Bool), xs :- (List A)]
  (=> (forall [r :- A] (=> (List.Mem r xs) (= (p r) true) (= (q r) true))) (= (tbl-any p xs) true) (= (tbl-any q xs) true))
  (induction xs)
  (case [nil] (intros hm h) (simp [tbl-any] at h))
  (case [cons hd t ih]
    (intros hm h)
    (simp only [tbl-any Bool.or_eq_true] at h)
    (cases h)
    (case [inl a] (simp only [tbl-any (hm hd (List.Mem.head t) a) Bool.true_or]))
    (case [inr b]
      (have r := (ih (fn [r :- A, m :- (List.Mem r t), pr :- (= (p r) true)] (hm r (List.Mem.tail hd m) pr)) b))
      (simp only [tbl-any r Bool.or_true]))))

(a/theorem orphan-nz-s [w :- World, r :- SourceRow] (=> (= (source-orphan w r) true) (= (nzs r) true))
  (intro h) (simp only [source-orphan owner-gone Bool.and_eq_true] at h) (simp only [nzs]) (exact (And.left h)))
(a/theorem orphan-nz-t [w :- World, r :- TaskRow] (=> (= (task-orphan w r) true) (= (nzt r) true))
  (intro h) (simp only [task-orphan owner-gone Bool.and_eq_true] at h) (simp only [nzt]) (exact (And.left h)))
(a/theorem orphan-nz-c [w :- World, r :- CompRow] (=> (= (comp-orphan w r) true) (= (nzc r) true))
  (intro h) (simp only [comp-orphan owner-gone Bool.and_eq_true] at h) (simp only [nzc]) (exact (And.left h)))

(a/theorem idnz-of [A :- Type, idf :- (=> A Nat), p :- (=> A Bool), q :- (=> A Bool), hq :- (forall [r :- A] (=> (= (p r) true) (= (q r) true))),
                    xs :- (List A)]
  (=> (= (tbl-any p xs) true) (= (tbl-any (id-nz idf q (tbl-scan idf p xs)) xs) true))
  (intro h)
  (apply (any-mono-mem A p _ xs _ h))
  (intros r m pr)
  (simp only [id-nz (scan-mem A idf p r xs m pr) (hq r pr) Bool.and_self]))

(a/theorem detach-lt [w :- World]
  (=> (= (well-formed w) true) (= (no-orphans w) false) (< (own-count (detach w)) (own-count w)))
  (intros hs hn)
  (have hs1 := (well-formed-nat-fold detach-source well-formed-detach-source (tbl-scan source-id (source-orphan w) (:sources w)) w hs))
  (have hs2 := (well-formed-nat-fold detach-task well-formed-detach-task (tbl-scan task-id (task-orphan w) (:tasks w)) _ hs1))
  (have le1 := (oc-le-of detach-source owner-count-at-most-detach-source (tbl-scan source-id (source-orphan w) (:sources w)) w hs))
  (have le2 := (oc-le-of detach-task owner-count-at-most-detach-task (tbl-scan task-id (task-orphan w) (:tasks w)) _ hs1))
  (have le3 := (oc-le-of detach-comp owner-count-at-most-detach-comp (tbl-scan comp-id (comp-orphan w) (:comps w)) _ hs2))
  (have tf := (tasks-source-fold (tbl-scan source-id (source-orphan w) (:sources w)) w))
  (have cf := (comps-task-fold (tbl-scan task-id (task-orphan w) (:tasks w)) (nat-fold detach-source w (tbl-scan source-id (source-orphan w) (:sources w)))))
  (simp only [detach])
  (cases a1 (tbl-any (source-orphan w) (:sources w)))
  (case [true]
    (have l := (oc-fold-lt SourceRow detach-source (fn [q :- World] (:sources q)) source-id nzs source-detach-row owner-count-at-most-detach-source well-formed-detach-source
                 (fn [q :- World, x :- Nat] (congrArg (fn [o :- OW] (:srcs o)) (ow-detach-source q x)))
                 oc-source-step (tbl-scan source-id (source-orphan w) (:sources w)) w hs
                 (idnz-of SourceRow source-id (source-orphan w) nzs (orphan-nz-s w) (:sources w) a1)))
    (omega))
  (case [false]
    (cases a2 (tbl-any (task-orphan w) (:tasks w)))
    (case [true]
      (have wt (= (tbl-any (id-nz task-id nzt (tbl-scan task-id (task-orphan w) (:tasks w)))
                           (:tasks (nat-fold detach-source w (tbl-scan source-id (source-orphan w) (:sources w))))) true))
      (rw [(And.left tf)]) (exact (idnz-of TaskRow task-id (task-orphan w) nzt (orphan-nz-t w) (:tasks w) a2))
      (have l := (oc-fold-lt TaskRow detach-task (fn [q :- World] (:tasks q)) task-id nzt task-detach-row owner-count-at-most-detach-task well-formed-detach-task
                   (fn [q :- World, x :- Nat] (Eq.refl (tbl-upd task-id x task-detach-row (:tasks q))))
                   oc-task-step (tbl-scan task-id (task-orphan w) (:tasks w)) _ hs1 wt))
      (omega))
    (case [false]
      (have a3 (= (tbl-any (comp-orphan w) (:comps w)) true))
      (simp only [no-orphans a1 a2 Bool.not_false Bool.true_and] at hn) (exact (bnot-false _ hn))
      (have w0 := (idnz-of CompRow comp-id (comp-orphan w) nzc (orphan-nz-c w) (:comps w) a3))
      (have ck (= (ck1s (:comps (nat-fold detach-task (nat-fold detach-source w (tbl-scan source-id (source-orphan w) (:sources w))) (tbl-scan task-id (task-orphan w) (:tasks w)))))
                  (ck1s (:comps w))))
      (rw [cf]) (exact (And.right tf))
      (have wc (= (tbl-any (id-nz comp-id nzc (tbl-scan comp-id (comp-orphan w) (:comps w)))
                           (:comps (nat-fold detach-task (nat-fold detach-source w (tbl-scan source-id (source-orphan w) (:sources w))) (tbl-scan task-id (task-orphan w) (:tasks w))))) true))
      (rw [any-ck1 ck]) (rw [any-ck1] at w0) (exact w0)
      (have l := (oc-fold-lt CompRow detach-comp (fn [q :- World] (:comps q)) comp-id nzc comp-detach-row owner-count-at-most-detach-comp well-formed-detach-comp
                   (fn [q :- World, x :- Nat] (Eq.refl (tbl-upd comp-id x comp-detach-row (:comps q))))
                   oc-comp-step (tbl-scan comp-id (comp-orphan w) (:comps w)) _ hs2 wc))
      (omega))))

;; ---- Rule R ends with no orphan (the loop terminates within its fuel)
(a/theorem oc-normalize [w :- World] (=> (= (well-formed w) true) (<= (own-count (normalize w)) (own-count w)))
  (intro hs)
  (have b (= (owner-count-at-most (own-count w) w) true)) (simp only [owner-count-at-most hs Nat.ble_eq Nat.le_refl Bool.and_self]) (simp)
  (have b2 := (owner-count-at-most-normalize (own-count w) w b))
  (simp only [owner-count-at-most Bool.and_eq_true Nat.ble_eq] at b2) (exact (And.right b2)))
(a/theorem oc-normalize-lt [w :- World]
  (=> (= (well-formed w) true) (= (no-orphans w) false) (< (own-count (normalize w)) (own-count w)))
  (intros hs hn)
  (have l := (detach-lt w hs hn))
  (have hs1 := (well-formed-detach w hs))
  (have b (= (owner-count-at-most (own-count (detach w)) (detach w)) true)) (simp only [owner-count-at-most hs1 Nat.ble_eq Nat.le_refl Bool.and_self]) (simp)
  (have b2 := (owner-count-at-most-normalize-loop (own-count (detach w)) (normalize-fuel (detach w)) (detach w) b))
  (simp only [owner-count-at-most Bool.and_eq_true Nat.ble_eq] at b2)
  (simp only [normalize])
  (have l2 := (And.right b2))
  (omega))
(a/theorem oc-round-le [w :- World] (=> (= (well-formed w) true) (<= (own-count (rule-r-round w)) (own-count w)))
  (intro hs)
  (have l := (oc-normalize w hs))
  (simp only [rule-r-round rule-r-filter-eq])
  (have l2 := (oc-filter (normalize w) (keep-fn (normalize w))))
  (omega))
(a/theorem oc-round-lt [w :- World] (=> (= (well-formed w) true) (= (no-orphans w) false) (< (own-count (rule-r-round w)) (own-count w)))
  (intros hs hn)
  (have l := (oc-normalize-lt w hs hn))
  (simp only [rule-r-round rule-r-filter-eq])
  (have l2 := (oc-filter (normalize w) (keep-fn (normalize w))))
  (omega))

(a/theorem count-ids-le [A :- Type, idf :- (=> A Nat), p :- (=> A Bool), xs :- (List A)]
  (<= (tbl-count p xs) (nat-len (tbl-ids idf xs)))
  (induction xs)
  (case [nil] (simp only [tbl-count tbl-ids nat-len]) (exact (Nat.le_refl 0)))
  (case [cons h t ih] (simp only [tbl-count-cons tbl-ids nat-len]) (cases hp (p h)) (all_goals (simp only [hp b2n])) (all_goals (omega))))
(a/theorem nat-len-app [xs :- (List Nat), ys :- (List Nat)] (= (nat-len (nat-app xs ys)) (+ (nat-len xs) (nat-len ys)))
  (induction xs)
  (case [nil] (simp only [nat-app nat-len]) (omega))
  (case [cons h t ih] (simp only [nat-app nat-len ih]) (omega)))
(a/theorem oc-ids [w :- World] (<= (own-count w) (nat-len (all-ids w)))
  (simp only [own-count all-ids nat-len-app])
  (have l1 := (count-ids-le SourceRow source-id nzs (:sources w)))
  (have l2 := (count-ids-le TaskRow task-id nzt (:tasks w)))
  (have l3 := (count-ids-le CompRow comp-id nzc (:comps w)))
  (omega))


(a/theorem rule-r-loop-t [x :- Nat, f :- (List Nat), w1 :- World]
  (=> (= (no-orphans w1) true) (= (rule-r-loop (List.cons Nat x f) w1) w1))
  (intro h) (simp only [rule-r-loop h]))
(a/theorem rule-r-loop-f [x :- Nat, f :- (List Nat), w1 :- World]
  (=> (= (no-orphans w1) false) (= (rule-r-loop (List.cons Nat x f) w1) (rule-r-loop f (rule-r-round w1))))
  (intro h) (simp only [rule-r-loop h]))
(a/theorem rounds-safe-loop-f [x :- Nat, f :- (List Nat), w0 :- World]
  (=> (= (rounds-safe-loop (List.cons Nat x f) w0) true) (= (no-orphans (rule-r-round w0)) false)
      (And (= (filter-safe (normalize w0)) true) (= (rounds-safe-loop f (rule-r-round w0)) true)))
  (intros h hn) (simp only [rounds-safe-loop hn Bool.and_eq_true] at h) (exact h))
(a/theorem rounds-safe-loop-head [x :- Nat, f :- (List Nat), w0 :- World]
  (=> (= (rounds-safe-loop (List.cons Nat x f) w0) true) (= (filter-safe (normalize w0)) true))
  (intro h) (simp only [rounds-safe-loop Bool.and_eq_true] at h) (exact (And.left h)))


(a/theorem rule-r-loop-no-orphans [f :- (List Nat)]
  (forall [x :- Nat, w1 :- World]
    (=> (= (well-formed w1) true) (< (own-count w1) (+ (nat-len f) 1))
        (=> (= (no-orphans w1) false) (= (rounds-safe-loop f w1) true))
        (= (no-orphans (rule-r-loop (List.cons Nat x f) w1)) true)))
  (induction f)
  (case [nil]
    (intros x w1 hs hl hr)
    (cases ho (no-orphans w1))
    (case [true] (rw [(rule-r-loop-t x (List.nil Nat) w1 ho)]) (exact ho))
    (case [false]
      (have hr1 := (hr ho))
      (have hs2 := (well-formed-rule-r-round w1 hs hr1))
      (have l := (oc-round-lt w1 hs ho))
      (have l0 (< (own-count w1) 1)) (exact hl)
      (omega)))
  (case [cons y g ih]
    (intros x w1 hs hl hr)
    (cases ho (no-orphans w1))
    (case [true] (rw [(rule-r-loop-t x (List.cons Nat y g) w1 ho)]) (exact ho))
    (case [false]
      (rw [(rule-r-loop-f x (List.cons Nat y g) w1 ho)])
      (have hr1 := (hr ho))
      (have hs2 := (well-formed-rule-r-round w1 hs (rounds-safe-loop-head y g w1 hr1)))
      (have l := (oc-round-lt w1 hs ho))
      (have l0 (< (own-count w1) (+ (+ (nat-len g) 1) 1))) (exact hl)
      (have l2 (< (own-count (rule-r-round w1)) (+ (nat-len g) 1))) (omega)
      (exact (ih y (rule-r-round w1) hs2 l2
               (fn [h2 :- (= (no-orphans (rule-r-round w1)) false)] (And.right (rounds-safe-loop-f y g w1 hr1 h2))))))))

(a/theorem rule-r-eq5 [w :- World] (= (rule-r w) (rule-r-loop (List.cons Nat 0 (all-ids w)) (rule-r-round w))) (rfl))
(a/theorem rule-r-no-orphans [w :- World] (=> (= (well-formed w) true) (= (rule-r-safe w) true) (= (no-orphans (rule-r w)) true))
  (intros hs hr)
  (have hr2 (= (rounds-safe-loop (List.cons Nat 0 (all-ids w)) w) true)) (exact hr)
  (have hs1 := (well-formed-rule-r-round w hs (rounds-safe-loop-head 0 (all-ids w) w hr2)))
  (have l1 := (oc-round-le w hs))
  (have l2 := (oc-ids w))
  (have l3 (< (own-count (rule-r-round w)) (+ (nat-len (all-ids w)) 1))) (omega)
  (rw [rule-r-eq5])
  (exact (rule-r-loop-no-orphans (all-ids w) 0 (rule-r-round w) hs1 l3
           (fn [h2 :- (= (no-orphans (rule-r-round w)) false)] (And.right (rounds-safe-loop-f 0 (all-ids w) w hr2 h2))))))

;; ===========================================================================
;; Part C. Sources with owner 0 are closed (bundle i1-detached-closed) and the owner clauses
;; ===========================================================================

;; ===========================================================================
;; A source with owner 0 is closed (it was detached); run scopes are not 0
;; ===========================================================================

(a/theorem id-pos [w :- World, y :- Nat] (=> (= (well-formed w) true) (= (nat-mem y (all-ids w)) true) (= (Nat.beq y 0) false))
  (intros h m)
  (have r := (all-nat-mem (id-in-range (:next-id w)) y (all-ids w) (ids-below-of w h) m))
  (simp only [id-in-range Bool.and_eq_true Nat.blt_eq] at r)
  (cases hb (Nat.beq y 0)) (case [false] (rfl)) (case [true] (have e (= y 0)) (exact (Nat.eq_of_beq_eq_true hb)) (have l := (And.left r)) (omega)))
(a/theorem scope-pos [w :- World, y :- Nat] (=> (= (well-formed w) true) (= (scope-has w y) true) (= (Nat.beq y 0) false))
  (intros h hh)
  (have hm (= (nat-mem y (tbl-ids scope-id (:scopes w))) true)) (rw [nat-mem-ids]) (exact hh)
  (exact (id-pos w y h (mem-app-l _ _ _ hm))))
(a/theorem comp-pos [w :- World, y :- Nat] (=> (= (well-formed w) true) (= (comp-has w y) true) (= (Nat.beq y 0) false))
  (intros h hh)
  (have hm (= (nat-mem y (tbl-ids comp-id (:comps w))) true)) (rw [nat-mem-ids]) (exact hh)
  (exact (id-pos w y h (mem-app-r _ _ _ (mem-app-l _ _ _ hm)))))

(a/defn src0-ok [s :- SourceRow] Bool (Bool.or (nzs s) (Bool.not (:open s))))
(a/defn rscope-nz [r :- RunRow] Bool (Bool.not (Nat.beq (:scope r) 0)))
(a/defn i1-detached-closed-rest [w :- World] Bool (Bool.and (tbl-all src0-ok (:sources w)) (tbl-all rscope-nz (:runs w))))
(a/defn i1-detached-closed [w :- World] Bool (Bool.and (well-formed w) (i1-detached-closed-rest w)))
(a/theorem i1-detached-closed-well-formed [w :- World] (=> (= (i1-detached-closed w) true) (= (well-formed w) true))
  (intro h) (simp only [i1-detached-closed Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem i1-detached-closed-rest-of [w :- World] (=> (= (i1-detached-closed w) true) (= (i1-detached-closed-rest w) true))
  (intro h) (simp only [i1-detached-closed Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem i1-detached-closed-intro [w :- World] (=> (= (well-formed w) true) (= (i1-detached-closed-rest w) true) (= (i1-detached-closed w) true))
  (intros h1 h2) (simp only [i1-detached-closed h1 h2 Bool.and_self]))
(a/theorem i1-detached-closed-parts [w :- World]
  (=> (= (i1-detached-closed w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (i1-detached-closed-well-formed w h))))

(a/theorem i1-detached-closed-mk [w :- World, w2 :- World]
  (=> (= (well-formed w2) true) (= (tbl-all src0-ok (:sources w2)) true) (= (tbl-all rscope-nz (:runs w2)) true) (= (i1-detached-closed w2) true))
  (intros h1 h2 h3) (simp only [i1-detached-closed i1-detached-closed-rest h1 h2 h3 Bool.and_self]))
(a/theorem i1-detached-closed-source [w :- World] (=> (= (i1-detached-closed w) true) (= (tbl-all src0-ok (:sources w)) true))
  (intro h) (have r := (i1-detached-closed-rest-of w h)) (simp only [i1-detached-closed-rest Bool.and_eq_true] at r) (exact (And.left r)))
(a/theorem i1-detached-closed-runs [w :- World] (=> (= (i1-detached-closed w) true) (= (tbl-all rscope-nz (:runs w)) true))
  (intro h) (have r := (i1-detached-closed-rest-of w h)) (simp only [i1-detached-closed-rest Bool.and_eq_true] at r) (exact (And.right r)))

(a/theorem i1-detached-closed-source-upd [w :- World, x :- Nat, f :- (=> SourceRow SourceRow),
                           hid :- (forall [s :- SourceRow] (= (source-id (f s)) (source-id s))),
                           hk :- (forall [s :- SourceRow] (=> (= (src0-ok s) true) (= (src0-ok (f s)) true)))]
  (=> (= (i1-detached-closed w) true) (= (i1-detached-closed (source-upd w x f)) true))
  (intro h)
  (exact (i1-detached-closed-mk w _ (well-formed-source-upd w x f hid (i1-detached-closed-well-formed w h))
           (tbl-all-upd SourceRow source-id x f src0-ok src0-ok (fn [s :- SourceRow, h1 :- (= (src0-ok s) true), hx :- (= (Nat.beq (source-id s) x) true)] (hk s h1))
             (fn [s :- SourceRow, h1 :- (= (src0-ok s) true), hx :- (= (Nat.beq (source-id s) x) false)] h1) (:sources w) (i1-detached-closed-source w h))
           (i1-detached-closed-runs w h))))

(a/theorem i1-detached-closed-run-upd [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                        hid :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                        hk :- (forall [r :- RunRow] (= (:scope (f r)) (:scope r)))]
  (=> (= (i1-detached-closed w) true) (= (i1-detached-closed (run-upd w x f)) true))
  (intro h)
  (exact (i1-detached-closed-mk w _ (well-formed-run-upd w x f hid (i1-detached-closed-well-formed w h)) (i1-detached-closed-source w h)
           (tbl-all-upd RunRow run-id x f rscope-nz rscope-nz
             (fn [r :- RunRow, h1 :- (= (rscope-nz r) true), hx :- (= (Nat.beq (run-id r) x) true)]
               (Eq.trans (congrArg (fn [z :- Nat] (Bool.not (Nat.beq z 0))) (hk r)) h1))
             (fn [r :- RunRow, h1 :- (= (rscope-nz r) true), hx :- (= (Nat.beq (run-id r) x) false)] h1) (:runs w) (i1-detached-closed-runs w h)))))

(a/theorem src0-close [s :- SourceRow] (=> (= (src0-ok s) true) (= (src0-ok (source-close-row s)) true))
  (intro h) (simp only [src0-ok source-close-row Bool.not_false Bool.or_true]))
(a/theorem src0-detach [s :- SourceRow] (=> (= (src0-ok s) true) (= (src0-ok (source-detach-row s)) true))
  (intro h) (simp only [src0-ok source-detach-row Bool.not_false Bool.or_true]))
(a/theorem i1-detached-closed-source-close [w :- World, x :- Nat] (=> (= (i1-detached-closed w) true) (= (i1-detached-closed (source-upd w x source-close-row)) true))
  (intro h) (exact (i1-detached-closed-source-upd w x source-close-row source-close-row-id src0-close h)))
(a/theorem i1-detached-closed-source-detach [w :- World, x :- Nat] (=> (= (i1-detached-closed w) true) (= (i1-detached-closed (source-upd w x source-detach-row)) true))
  (intro h) (exact (i1-detached-closed-source-upd w x source-detach-row source-detach-row-id src0-detach h)))

(a/theorem i1-detached-closed-add-run-scope [w :- World, of :- Nat, epoch :- Nat, parent :- Nat, ei :- Nat]
  (=> (= (i1-detached-closed w) true) (= (i1-detached-closed (add-run-scope w of epoch parent ei)) true))
  (intro h)
  (have r1 (= (tbl-all rscope-nz (:runs (add-run-scope w of epoch parent ei))) true))
  (simp only [add-run-scope bump set-next-id scope-ins set-scopes run-ins set-runs tbl-ins tbl-all (i1-detached-closed-runs w h) Bool.and_true])
  (simp only [rscope-nz new-run-row])
  (have z (= (Nat.beq (+ (:next-id w) 1) 0) false)) (cases q (Nat.beq (+ (:next-id w) 1) 0)) (case [false] (rfl)) (case [true] (have e := (Nat.eq_of_beq_eq_true q)) (omega))
  (simp only [z Bool.not_false])
  (exact (i1-detached-closed-mk w _ (well-formed-add-run-scope w of epoch parent ei (i1-detached-closed-well-formed w h)) (i1-detached-closed-source w h) r1)))

(a/theorem i1-detached-closed-source-ins [w :- World, r :- SourceRow]
  (=> (= (source-id r) (:next-id w)) (= (src0-ok r) true) (= (i1-detached-closed w) true) (= (i1-detached-closed (bump (source-ins w r))) true))
  (intros hi hz h)
  (exact (i1-detached-closed-mk w _ (well-formed-source-ins-fresh w r hi (i1-detached-closed-well-formed w h))
           (Eq.trans (congrArg (fn [b :- Bool] (Bool.and b (tbl-all src0-ok (:sources w)))) hz) (Eq.trans (Bool.true_and _) (i1-detached-closed-source w h)))
           (i1-detached-closed-runs w h))))

;; a new source's owner is a computation or a run scope (both exist, hence not 0)
(a/theorem src0-new [id :- Nat, o :- Nat, k :- Nat, v :- Nat] (=> (= (Nat.beq o 0) false) (= (src0-ok (new-source id o k v)) true))
  (intro h) (simp only [src0-ok nzs new-source h Bool.not_false Bool.true_or]))
(a/theorem nat-max-ge [xs :- (List Nat)] (forall [m :- Nat, m0 :- Nat] (=> (<= m0 m) (<= m0 (nat-max m xs))))
  (induction xs)
  (case [nil] (intros m m0 h) (simp only [nat-max]) (exact h))
  (case [cons h t ih]
    (intros m m0 hm) (simp only [nat-max])
    (cases hb (Nat.blt m h))
    (case [false] (simp only [hb]) (exact (ih m m0 hm)))
    (case [true] (simp only [hb]) (simp only [Nat.blt_eq] at hb) (have l (<= m0 h)) (omega) (exact (ih h m0 l)))))
(a/theorem nat-max-nz [xs :- (List Nat), m :- Nat] (=> (= (Nat.beq m 0) false) (= (Nat.beq (nat-max m xs) 0) false))
  (intro h)
  (have p (<= 1 m)) (have z := (Nat.ne_of_beq_eq_false h)) (omega)
  (have l := (nat-max-ge xs m 1 p))
  (cases q (Nat.beq (nat-max m xs) 0)) (case [false] (rfl)) (case [true] (have e := (Nat.eq_of_beq_eq_true q)) (omega)))
(a/theorem cur-scope-nz [w :- World, r :- RunRow] (=> (= (rscope-nz r) true) (= (Nat.beq (cur-scope w r) 0) false))
  (intro h)
  (simp only [rscope-nz] at h)
  (simp only [cur-scope])
  (exact (nat-max-nz _ (:scope r) (bnot-true _ h))))

(def GSO (mk-bundle 'i1-detached-closed [] "i1-detached-closed-"
           {'well-formed-source-upd ['(fn [s :- SourceRow, q :- (= (src0-ok s) true)] q) 4]
            'well-formed-run-upd ['(fn [r :- RunRow] (Eq.refl (:scope r))) 4]
            'well-formed-serve-or ['(fn [s :- SourceRow, q :- (= (src0-ok s) true)] q) 5]
            ;; C0: the other fresh rows (links owned by the root scope) are owned
            'well-formed-source-ins-fresh ['(Eq.refl true) 3]}))
(swap! (:renames GSO) assoc 'well-formed-parts 'i1-detached-closed-parts 'well-formed-source-upd 'i1-detached-closed-source-upd 'well-formed-run-upd 'i1-detached-closed-run-upd
       'well-formed-source-ins-fresh 'i1-detached-closed-source-ins
       'well-formed-add-run-scope 'i1-detached-closed-add-run-scope)
(a/theorem i1-detached-closed-rest-run-del [w :- World, x :- Nat] (=> (= (i1-detached-closed-rest w) true) (= (i1-detached-closed-rest (run-del w x)) true))
  (intro h) (simp only [i1-detached-closed-rest Bool.and_eq_true] at h)
  (simp only [i1-detached-closed-rest run-del set-runs (And.left h) (all-sub-del RunRow rscope-nz run-id x (:runs w) (And.right h)) Bool.and_self]))
(prim! GSO 'well-formed-run-del '(i1-detached-closed-rest-run-del w x R))
(defpart GSO :reads '[runs sources])
(frames/frame-theorem! 'i1-detached-closed-rest-mark-edge 'i1-detached-closed-rest 'well-formed-mark-edge)
(frames/frame-theorem! 'i1-detached-closed-rest-unmark-edge 'i1-detached-closed-rest 'well-formed-unmark-edge)
(frames/frame-theorem! 'i1-detached-closed-rest-remove-edge 'i1-detached-closed-rest 'well-formed-remove-edge)

(a/theorem src0-consume [s :- SourceRow] (=> (= (src0-ok s) true) (= (src0-ok (source-consume s)) true))
  (intro h) (cases ha (source-available s)) (simp only [source-consume ha]) (exact h)
  (cases hm (Nat.beq (:kind s) sk-mailbox)) (all_goals (simp only [src0-ok nzs source-consume ha hm] at h)) (all_goals (simp only [src0-ok nzs source-consume ha hm])) (all_goals (exact h)))
(a/theorem i1-detached-closed-source-consume [w :- World, x :- Nat] (=> (= (i1-detached-closed w) true) (= (i1-detached-closed (source-upd w x source-consume)) true))
  (intro h) (exact (i1-detached-closed-source-upd w x source-consume source-consume-id src0-consume h)))
;; i1-detached-closed on the generic tree: its table. Its own proofs follow: a new source, stream or link is owned
;; (by a scope that exists, or by the run's computation or scope).
(tree/part! GSO
  :over '{well-formed-serve-or          i1-detached-closed-serve-or
          well-formed-t1-create-nonstream-top            i1-detached-closed-t1-create-nonstream-top
          well-formed-create-source-in-run i1-detached-closed-create-source-in-run
          well-formed-stream-rows       i1-detached-closed-stream-rows
          well-formed-create-stream-in-run i1-detached-closed-create-stream-in-run
          well-formed-t1-create-source-top       i1-detached-closed-t1-create-source-top
          well-formed-t-create-link-top i1-detached-closed-t-create-link-top}
  ;; ---- sites: a closed, detached or consumed source row keeps its owner
  :sites '{[well-formed-source-upd source-close-row]  (i1-detached-closed-source-close w x h0)
           [well-formed-source-upd source-detach-row] (i1-detached-closed-source-detach w x h0)
           [well-formed-source-upd source-consume]    (i1-detached-closed-source-consume w x h0)}
  ;; ---- facts from the path: the creating run is the world's (the token's run); a stream's owner exists
  :ctx '{well-formed-create-source-in-run [(List.Mem r (:runs w))]
         well-formed-create-stream-in-run [(List.Mem r (:runs w))]
         well-formed-stream-rows       [(= (Nat.beq owner 0) false)]}
  :pass '{well-formed-t1-create-nonstream   {well-formed-create-source-in-run [(tok-run-mem w st r ht)]}
          well-formed-t1-create-stream {well-formed-create-stream-in-run [(tok-run-mem w st r ht)]}})
(tree/restate! GSO '[well-formed-fire-edge])
(a/theorem i1-detached-closed-serve-or [w :- World, x :- Nat, res :- RunResult, keep :- (=> SourceRow SourceRow),
                         hk :- (forall [s :- SourceRow] (= (source-id (keep s)) (source-id s))),
                         hg :- (forall [s :- SourceRow] (=> (= (src0-ok s) true) (= (src0-ok (keep s)) true)))]
  (=> (= (i1-detached-closed w) true) (= (i1-detached-closed (serve-or w x res keep)) true))
  (intro h)
  (cases hz (Nat.beq (oldest-waiter w x) 0))
  (simp only [serve-or hz]) (exact (i1-detached-closed-fire-edge res w _ h))
  (simp only [serve-or hz]) (exact (i1-detached-closed-source-upd w x keep hk hg h)))
(a/theorem i1-detached-closed-t1-create-nonstream-top [w :- World, scope :- Nat, kind :- Nat, v :- Nat, fresh :- Nat]
  (=> (= (i1-detached-closed w) true) (= (i1-detached-closed (:world (t1-create-nonstream-top w scope kind v fresh))) true))
  (intro h)
  (cases hg (Bool.and (Bool.and (Nat.beq fresh (:next-id w)) (source-kind-ok kind)) (scope-open-at w scope)))
  (simp only [t1-create-nonstream-top hg refuse]) (exact h)
  (have hso (= (scope-open-at w scope) true)) (simp only [Bool.and_eq_true] at hg) (exact (And.right hg))
  (simp only [t1-create-nonstream-top hg accept])
  (exact (i1-detached-closed-source-ins w (new-source (:next-id w) scope kind v) (rfl)
           (src0-new (:next-id w) scope kind v (scope-pos w scope (i1-detached-closed-well-formed w h) (open-at-has w scope hso))) h)))
(tree/restate! GSO '[well-formed-record-basis well-formed-run-upd])
(a/theorem i1-detached-closed-create-source-in-run [w :- World, r :- RunRow, kind :- Nat, v :- Nat]
  (=> (List.Mem r (:runs w)) (= (i1-detached-closed w) true) (= (i1-detached-closed (create-source-in-run w r kind v)) true))
  (intros hm h)
  (have nz (= (Nat.beq (source-owner-in-run w r) 0) false))
  (cases hc (in-comp w r))
  (case [true] (simp only [source-owner-in-run hc]) (exact (comp-pos w (:of r) (i1-detached-closed-well-formed w h) hc)))
  (case [false] (simp only [source-owner-in-run hc]) (exact (cur-scope-nz w r (tbl-all-mem RunRow rscope-nz r (:runs w) (i1-detached-closed-runs w h) hm))))
  (simp only [create-source-in-run])
  (exact (i1-detached-closed-run-upd _ (:id r) run-tick run-tick-run-id (fn [q :- RunRow] (Eq.refl (:scope q)))
           (i1-detached-closed-record-basis _ r (:next-id w)
             (i1-detached-closed-source-ins w (new-source (:next-id w) (source-owner-in-run w r) kind v) (rfl) (src0-new (:next-id w) _ kind v nz) h)))))

;; C0: a stream (owned like a source) and its first tail link (the root scope's); a top-level link
(a/theorem src0-stream [id :- Nat, o :- Nat, v :- Nat] (=> (= (Nat.beq o 0) false) (= (src0-ok (new-stream id o v)) true))
  (intro h) (simp only [src0-ok nzs new-stream h Bool.not_false Bool.true_or]))
(a/theorem src0-link [id :- Nat, o :- Nat, t :- Nat] (=> (= (Nat.beq o 0) false) (= (src0-ok (new-link id o t)) true))
  (intro h) (simp only [src0-ok nzs new-link h Bool.not_false Bool.true_or]))
(a/theorem i1-detached-closed-stream-rows [w :- World, owner :- Nat, v :- Nat]
  (=> (= (Nat.beq owner 0) false) (= (i1-detached-closed w) true) (= (i1-detached-closed (stream-rows w owner v)) true))
  (intros nz h)
  (simp only [stream-rows])
  (exact (i1-detached-closed-source-ins (bump (source-ins w (new-stream (:next-id w) owner v))) (new-link (+ (:next-id w) 1) root-scope-id (:next-id w))
           (rfl) (Eq.refl true) (i1-detached-closed-source-ins w (new-stream (:next-id w) owner v) (rfl) (src0-stream (:next-id w) owner v nz) h))))
(tree/restate! GSO '[well-formed-record-basis well-formed-run-upd])
(a/theorem i1-detached-closed-create-stream-in-run [w :- World, r :- RunRow, v :- Nat]
  (=> (List.Mem r (:runs w)) (= (i1-detached-closed w) true) (= (i1-detached-closed (create-stream-in-run w r v)) true))
  (intros hm h)
  (have nz (= (Nat.beq (source-owner-in-run w r) 0) false))
  (cases hc (in-comp w r))
  (case [true] (simp only [source-owner-in-run hc]) (exact (comp-pos w (:of r) (i1-detached-closed-well-formed w h) hc)))
  (case [false] (simp only [source-owner-in-run hc]) (exact (cur-scope-nz w r (tbl-all-mem RunRow rscope-nz r (:runs w) (i1-detached-closed-runs w h) hm))))
  (simp only [create-stream-in-run])
  (exact (i1-detached-closed-run-upd _ (:id r) run-tick run-tick-run-id (fn [q :- RunRow] (Eq.refl (:scope q)))
           (i1-detached-closed-record-basis _ r (:next-id w) (i1-detached-closed-stream-rows w (source-owner-in-run w r) v nz h)))))
(a/theorem i1-detached-closed-t1-create-source-top [w :- World, scope :- Nat, kind :- Nat, v :- Nat, fresh :- Nat]
  (=> (= (i1-detached-closed w) true) (= (i1-detached-closed (:world (t1-create-source-top w scope kind v fresh))) true))
  (intro h)
  (cases hk (Nat.beq kind sk-stream))
  (simp only [t1-create-source-top hk]) (exact (i1-detached-closed-t1-create-nonstream-top w scope kind v fresh h))
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (scope-open-at w scope)))
  (simp only [t1-create-source-top hk hg refuse]) (exact h)
  (have hso (= (scope-open-at w scope) true)) (simp only [Bool.and_eq_true] at hg) (exact (And.right hg))
  (simp only [t1-create-source-top hk hg accept])
  (exact (i1-detached-closed-stream-rows w scope v (scope-pos w scope (i1-detached-closed-well-formed w h) (open-at-has w scope hso)) h)))
(a/theorem i1-detached-closed-t-create-link-top [w :- World, scope :- Nat, l :- Nat]
  (=> (= (i1-detached-closed w) true) (= (i1-detached-closed (:world (t-create-link-top w scope l))) true))
  (intro h)
  (cases hg (Bool.and (Nat.beq l (:next-id w)) (scope-open-at w scope)))
  (simp only [t-create-link-top hg refuse]) (exact h)
  (have hso (= (scope-open-at w scope) true)) (simp only [Bool.and_eq_true] at hg) (exact (And.right hg))
  (simp only [t-create-link-top hg accept])
  (exact (i1-detached-closed-source-ins w (new-link (:next-id w) scope 0) (rfl)
           (src0-link (:next-id w) scope 0 (scope-pos w scope (i1-detached-closed-well-formed w h) (open-at-has w scope hso))) h)))

(tree/restate! GSO '[well-formed-raw well-formed-normalize])

(a/theorem i1-detached-closed-filter-world [w :- World, K :- (=> Nat Bool)]
  (=> (= (i1-detached-closed w) true) (= (filter-safe-for K w) true) (= (i1-detached-closed (filter-world K w)) true))
  (intros h hf)
  (exact (i1-detached-closed-mk w _ (well-formed-filter-world w K (i1-detached-closed-well-formed w h) hf)
           (tbl-all-keep SourceRow K source-id src0-ok src0-ok (fn [s :- SourceRow, h1 :- (= (src0-ok s) true), h2 :- (= (K (source-id s)) true)] h1) (:sources w) (i1-detached-closed-source w h))
           (tbl-all-keep RunRow K run-id rscope-nz rscope-nz (fn [s :- RunRow, h1 :- (= (rscope-nz s) true), h2 :- (= (K (run-id s)) true)] h1) (:runs w) (i1-detached-closed-runs w h)))))
(a/theorem i1-detached-closed-rule-r-round [w :- World]
  (=> (= (i1-detached-closed w) true) (= (filter-safe (normalize w)) true) (= (i1-detached-closed (rule-r-round w)) true))
  (intros h hf) (simp only [rule-r-round]) (rw [rule-r-filter-eq])
  (exact (i1-detached-closed-filter-world _ (keep-fn (normalize w)) (i1-detached-closed-normalize w h) hf)))
(a/theorem i1-detached-closed-rule-r-loop [fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (i1-detached-closed w0) true) (= (rounds-safe-loop fuel w0) true) (= (i1-detached-closed (rule-r-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 h hs) (simp only [rounds-safe-loop] at hs) (simp only [rule-r-loop]) (exact (i1-detached-closed-rule-r-round w0 h hs)))
  (case [cons x f ih]
    (intros w0 h hs)
    (simp only [rounds-safe-loop Bool.and_eq_true] at hs)
    (have h1 := (i1-detached-closed-rule-r-round w0 h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false] (simp only [ho] at hs) (simp only [rule-r-loop ho]) (exact (ih (rule-r-round w0) h1 (And.right hs))))
    (case [true] (simp only [rule-r-loop ho]) (exact h1))))
(a/theorem i1-detached-closed-rule-r [w :- World] (=> (= (i1-detached-closed w) true) (= (rule-r-safe w) true) (= (i1-detached-closed (rule-r w)) true))
  (intros h hs) (simp only [rule-r-safe] at hs) (simp only [rule-r]) (exact (i1-detached-closed-rule-r-loop (rule-r-fuel w) w h hs)))
(a/theorem i1-detached-closed-empty [] (= (i1-detached-closed empty-world) true) (rfl))

;; ---- literal I1: the owners of tasks, computations and sources
(a/defn lit-i1-own [w :- World] Bool
  (Bool.and (tbl-all (task-owner-ok w) (:tasks w))
   (Bool.and (tbl-all (comp-owner-ok w) (:comps w)) (tbl-all (source-owner-ok w) (:sources w)))))

(a/theorem all-not-any [A :- Type, p :- (=> A Bool), q :- (=> A Bool), hq :- (forall [r :- A] (=> (= (p r) false) (= (q r) true))), xs :- (List A)]
  (=> (= (tbl-any p xs) false) (= (tbl-all q xs) true))
  (induction xs)
  (case [nil] (intro h) (simp only [tbl-all]))
  (case [cons hd t ih]
    (intro h) (simp only [tbl-any Bool.or_eq_false_iff] at h)
    (simp only [tbl-all (hq hd (And.left h)) (ih (And.right h)) Bool.and_self])))
(a/theorem gone-owner [w :- World, o :- Nat]
  (=> (= (owner-gone w o) false) (= (Bool.or (Nat.beq o 0) (owner-exists w o)) true))
  (intro h)
  (cases hz (Nat.beq o 0))
  (case [true] (simp only [hz Bool.true_or]))
  (case [false]
    (simp only [owner-gone hz Bool.not_false Bool.true_and] at h)
    (simp only [owner-exists Bool.false_or])
    (cases hs (scope-has w o))
    (case [true] (simp only [Bool.true_or]))
    (case [false] (simp only [hs Bool.not_false Bool.true_and] at h) (simp only [Bool.false_or]) (exact (bnot-false _ h)))))
(a/theorem lit-i1-own-of [w :- World] (=> (= (no-orphans w) true) (= (i1-detached-closed w) true) (= (lit-i1-own w) true))
  (intros hn hg)
  (simp only [no-orphans Bool.and_eq_true] at hn)
  (have n1 := (bnot-true _ (And.left hn)))
  (have n2 := (bnot-true _ (And.left (And.right hn))))
  (have n3 := (bnot-true _ (And.right (And.right hn))))
  (have a1 := (all-not-any TaskRow (task-orphan w) (task-owner-ok w)
                (fn [t :- TaskRow, q :- (= (task-orphan w t) false)] (gone-owner w (:owner t) q)) (:tasks w) n2))
  (have a2 := (all-not-any CompRow (comp-orphan w) (comp-owner-ok w)
                (fn [t :- CompRow, q :- (= (comp-orphan w t) false)] (gone-owner w (:owner t) q)) (:comps w) n3))
  (have a3 (= (tbl-all (source-owner-ok w) (:sources w)) true))
  (apply (tbl-all-mono2 SourceRow (bnot-of (source-orphan w)) src0-ok (source-owner-ok w) _ (:sources w) (any-false-all SourceRow (source-orphan w) (:sources w) n1) (i1-detached-closed-source w hg)))
  (intros s h1 h2)
  (simp only [bnot-of] at h1)
  (have g := (gone-owner w (:owner s) (bnot-true _ h1)))
  (cases hz (Nat.beq (:owner s) 0))
  (case [true] (simp only [src0-ok nzs hz Bool.not_true Bool.false_or] at h2) (simp only [source-owner-ok hz]) (exact h2))
  (case [false] (simp only [hz Bool.false_or] at g) (simp only [source-owner-ok hz]) (exact g))
  (simp only [lit-i1-own a1 a2 a3 Bool.and_self]))

(a/theorem step-i1-detached-closed [w :- World, it :- Item]
  (=> (= (i1-detached-closed w) true) (= (rule-r-safe (:world (raw w it))) true) (= (i1-detached-closed (:world (world-step w it))) true))
  (intros h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true] (have e2 := (step-accepted w it ha)) (rw [e2]) (exact (i1-detached-closed-rule-r (:world (raw w it)) (i1-detached-closed-raw w it h) hs))))

;; the combined bundle: chain-to-i1-detached-closed = chain-to-i5-dep-final && i1-detached-closed && the owner clauses
(a/defn chain-to-i1-detached-closed [w :- World] Bool (Bool.and (chain-to-i5-dep-final w) (Bool.and (i1-detached-closed w) (lit-i1-own w))))
(a/theorem chain-to-i1-detached-closed-parts [w :- World] (=> (= (chain-to-i1-detached-closed w) true) (And (= (chain-to-i5-dep-final w) true) (And (= (i1-detached-closed w) true) (= (lit-i1-own w) true))))
  (intro h) (simp only [chain-to-i1-detached-closed Bool.and_eq_true] at h) (exact h))
(a/theorem chain-to-i1-detached-closed-empty [] (= (chain-to-i1-detached-closed empty-world) true) (rfl))
(a/theorem step-chain-to-i1-detached-closed [w :- World, it :- Item] (=> (= (chain-to-i1-detached-closed w) true) (= (chain-to-i1-detached-closed (:world (world-step w it))) true))
  (intro h)
  (have p := (chain-to-i1-detached-closed-parts w h))
  (have pf := (chain-to-i5-dep-final-parts w (And.left p)))
  (have pe := (chain-to-i1-scopes-parts w (And.left pf)))
  (have pd := (chain-to-i11a-parts w (And.left pe)))
  (have pc := (chain-to-i10-current-parts w (And.left pd)))
  (have rs := (step-rule-r-safe w it (And.left pc)))
  (have a1 := (step-chain-to-i5-dep-final w it (And.left p)))
  (have a2 := (step-i1-detached-closed w it (And.left (And.right p)) rs))
  (have a3 (= (lit-i1-own (:world (world-step w it))) true))
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact (And.right (And.right p))))
  (case [true]
    (have e2 := (step-accepted w it ha))
    (have hs := (well-formed-raw w it (i1-detached-closed-well-formed w (And.left (And.right p)))))
    (have no := (rule-r-no-orphans (:world (raw w it)) hs rs))
    (rw [← e2] at no)
    (exact (lit-i1-own-of _ no a2)))
  (simp only [chain-to-i1-detached-closed a1 a2 a3 Bool.and_self]))
;; Theorem: literal I1 for the owners of tasks, computations and sources (0 or an existing scope or
;; computation; a source with owner 0 is closed), through every step
(a/theorem step-lit-i1-owners-total [w :- World, it :- Item]
  (=> (= (chain-to-i1-detached-closed w) true) (= (lit-i1-own (:world (world-step w it))) true))
  (intro h) (exact (And.right (And.right (chain-to-i1-detached-closed-parts _ (step-chain-to-i1-detached-closed w it h))))))

