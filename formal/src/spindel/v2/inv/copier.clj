(ns ^:ansatz/lean spindel.v2.inv.copier
  "The spec's literal layer-1 invariants (§6) as theorems through the model's step `world-step`,
  kernel-checked (Init only). Predicates: spindel.v2.inv's `lit-*` and `inv-i10-task`.

  Bundles (well-formed plus a rest part; the bundle record, the cells and the copier are
  spindel.v2.pres.part's: every composite well-formed lemma of `step-well-formed` is re-checked for the
  bundle by `lcopy!` from primitive lemmas and overrides, or restated from the generic tree):
    i10-task   I10, task part: every run's `of` is below the allocator, every run of a task K is K.run,
         a task without result has its run, not done. Stated over key projections of the run and
         task rows (`run-keys`, `task-keys`), so an edit that keeps the keys is a frame. Its lemmas here:
         a run made alive (resume, park: `i10-task-run-upd-up`), the exempt rest `i10-task-exempt` (T14's local part
         and T12: the run is done, its task gets its result), T13 (`retire-rest`), run creation
         (T4 `i10-task-spawn-rows-hand`, T5/T11 `i10-task-comp-run-hand`), the Rule R filter (alive runs are kept:
         `normalized` of every round, from P2 with acts-alive). Not copied: it goes through the
         generic tree (spindel.v2.pres.tree), with its table and step in spindel.v2.inv.i10-task.
    comp-exists   T11 keeps C: computation cx exists through the predecessor's cancel and the cut.
    i9-res   I9, resources: every resource's owner is below the allocator and listed in its run's
         `resources`, phases are valid, and `lit-i9-res`. Its lemmas here: a resource row change
         that keeps id and owner (`i9-res-res-upd-q`), T14's cancel-res (`i9-res-cancel-mid`), T17 arm
         (`i9-res-arm-hand`), T15 ack (`i9-res-ack-raw-hand`). Not copied: it goes through the generic tree, with
         its table and step in spindel.v2.inv.i9-res.

  Theorems (step-i10-task and step-lit-i10-task, I10's task part, are in spindel.v2.inv.i10-task;
  step-i9-res and step-lit-i9-res, I9's resource part, in spindel.v2.inv.i9-res):
    filter-safe-of-refs   P3 core: well-formed, acts-alive, normalized and `p3-refs` (dep edges have
                       non-idle creditors, activations' runs exist, marked edges are dep edges, no
                       edge id is a cleanup row or storage ref) and `refs-untomb` (C1 Q6: no dep
                       edge's creditor is a tombstone) -> filter-safe. Their preservation
                       through the step is proved in spindel.v2.inv.base (bundle `round-facts`, `step-chain-start`,
                       `step-rule-r-safe`); `p3-refs` also runs as a tripwire in lit-test.
  Model changes made for these proofs (spec-faithful, no reachable behaviour changes): `complete`
  with a result tag other than ok/err is refused (`complete-refused`; it let a task end with
  result none: inv_test complete-tag-none-refused), and cancel(R, replace) skips the debtor side
  only for a computation run (`cancel-debtor`)."
  (:require [ansatz.core :as a]
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
            [spindel.v2.pres.part :refer :all]
            [spindel.v2.pres.tree :as tree]
            [spindel.v2.pres.frames :as frames]
            [spindel.v2.pres.exempt :as exempt]))

;; ===========================================================================
;; Part A. Keys and the invariant
;; ===========================================================================

(a/structure RunKey [] (id Nat) (of Nat) (alive Bool))
(a/defn run-key [r :- RunRow] RunKey (RunKey.mk (:id r) (:of r) (run-alive r)))
(a/defn run-key-id [k :- RunKey] Nat (:id k))
(a/defn task-done [t :- TaskRow] Bool (Bool.not (Nat.beq (:tag (:result t)) res-none)))
(a/structure TaskKey [] (id Nat) (run Nat) (done Bool))
(a/defn task-key [t :- TaskRow] TaskKey (TaskKey.mk (:id t) (:run t) (task-done t)))
(a/defn task-key-id [k :- TaskKey] Nat (:id k))
(a/defn run-keys [rs :- (List RunRow)] (List RunKey)
  (match rs nil (List.nil RunKey) (cons h t) (List.cons RunKey (run-key h) (run-keys t))))
(a/defn task-keys [ts :- (List TaskRow)] (List TaskKey)
  (match ts nil (List.nil TaskKey) (cons h t) (List.cons TaskKey (task-key h) (task-keys t))))

(a/defn of-below-k [n :- Nat, r :- RunKey] Bool (Nat.blt (:of r) n))
;; every task with id r.of has run r.id
(a/defn trun-one [r :- RunKey, t :- TaskKey] Bool (Bool.or (Bool.not (Nat.beq (:id t) (:of r))) (Nat.beq (:run t) (:id r))))
(a/defn trun-ok [tks :- (List TaskKey), r :- RunKey] Bool (tbl-all (trun-one r) tks))
;; a run with id t.run, of t.id, not done
(a/defn run-for [t :- TaskKey, r :- RunKey] Bool
  (Bool.and (Nat.beq (:id r) (:run t)) (Bool.and (Nat.beq (:of r) (:id t)) (:alive r))))
(a/defn thas-ok [rks :- (List RunKey), t :- TaskKey] Bool (Bool.or (:done t) (tbl-any (run-for t) rks)))
(a/defn i10-task-keys-ok [rks :- (List RunKey), tks :- (List TaskKey), n :- Nat] Bool
  (Bool.and (tbl-all (of-below-k n) rks) (Bool.and (tbl-all (trun-ok tks) rks) (tbl-all (thas-ok rks) tks))))
(a/defn i10-task-rest [w :- World] Bool (i10-task-keys-ok (run-keys (:runs w)) (task-keys (:tasks w)) (:next-id w)))
(a/defn i10-task [w :- World] Bool (Bool.and (well-formed w) (i10-task-rest w)))

(a/theorem i10-task-well-formed [w :- World] (=> (= (i10-task w) true) (= (well-formed w) true))
  (intro h) (simp only [i10-task Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem i10-task-rest-of [w :- World] (=> (= (i10-task w) true) (= (i10-task-rest w) true))
  (intro h) (simp only [i10-task Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem i10-task-intro [w :- World] (=> (= (well-formed w) true) (= (i10-task-rest w) true) (= (i10-task w) true))
  (intros h1 h2) (simp only [i10-task h1 h2 Bool.and_self]))
(a/theorem i10-task-parts [w :- World]
  (=> (= (i10-task w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (i10-task-well-formed w h))))

;; ---- key lists under the table edits

(a/theorem run-keys-upd [x :- Nat, f :- (=> RunRow RunRow), hk :- (forall [r :- RunRow] (= (run-key (f r)) (run-key r))),
                      rs :- (List RunRow)]
  (= (run-keys (tbl-upd run-id x f rs)) (run-keys rs))
  (induction rs)
  (case [nil] (simp only [tbl-upd run-keys]))
  (case [cons h t ih]
    (cases hx (Nat.beq (run-id h) x))
    (case [false] (simp only [tbl-upd hx run-keys ih]))
    (case [true] (simp only [tbl-upd hx run-keys ih (hk h)]))))

(a/theorem task-keys-upd [x :- Nat, f :- (=> TaskRow TaskRow), hk :- (forall [t :- TaskRow] (= (task-key (f t)) (task-key t))),
                      ts :- (List TaskRow)]
  (= (task-keys (tbl-upd task-id x f ts)) (task-keys ts))
  (induction ts)
  (case [nil] (simp only [tbl-upd task-keys]))
  (case [cons h t ih]
    (cases hx (Nat.beq (task-id h) x))
    (case [false] (simp only [tbl-upd hx task-keys ih]))
    (case [true] (simp only [tbl-upd hx task-keys ih (hk h)]))))

(a/theorem of-below-one [n :- Nat, m :- Nat, r :- RunKey]
  (=> (<= n m) (= (of-below-k n r) true) (= (of-below-k m r) true))
  (intros hn hr)
  (simp only [of-below-k Nat.blt_eq] at hr) (simp only [of-below-k Nat.blt_eq])
  (exact (Nat.lt_of_lt_of_le hr hn)))

(a/theorem of-below-mono [n :- Nat, m :- Nat, rks :- (List RunKey)]
  (=> (<= n m) (= (tbl-all (of-below-k n) rks) true) (= (tbl-all (of-below-k m) rks) true))
  (intros hn h)
  (exact (tbl-all-mono RunKey (of-below-k n) (of-below-k m)
           (fn [r :- RunKey, hr :- (= (of-below-k n r) true)] (of-below-one n m r hn hr)) rks h)))

(a/theorem i10-task-rest-next [w :- World, v :- Nat]
  (=> (= (i10-task-rest w) true) (<= (:next-id w) v) (= (i10-task-rest (set-next-id w v)) true))
  (intros h hv)
  (simp only [i10-task-rest i10-task-keys-ok Bool.and_eq_true] at h)
  (have e1 (= (:runs (set-next-id w v)) (:runs w))) (rfl)
  (have e2 (= (:tasks (set-next-id w v)) (:tasks w))) (rfl)
  (have e3 (= (:next-id (set-next-id w v)) v)) (rfl)
  (simp only [i10-task-rest i10-task-keys-ok Bool.and_eq_true e1 e2 e3])
  (exact (And.intro (of-below-mono (:next-id w) v (run-keys (:runs w)) hv (And.left h)) (And.right h))))

(a/theorem i10-task-rest-bump [w :- World] (=> (= (i10-task-rest w) true) (= (i10-task-rest (bump w)) true))
  (intro h) (simp only [bump]) (exact (i10-task-rest-next w (+ (:next-id w) 1) h (Nat.le_succ (:next-id w)))))

;; Part B, the bundle copier and the declaration front end (`mk-bundle`, `prim!`, `defpart`, `lcopy!`),
;; is spindel.v2.pres.part.

;; ---------------------------------------------------------------------------
;; The part i10-task: I10, task part (spec §6 I10; formal/notes/proof-layout.md §4.5). Here: its predicate
;; (Part A), view and cells (below), keys and exempt form (Part C). Its table in the generic tree and
;; its step theorem, with the fixed comment block of proof-layout.md §4.4: spindel.v2.inv.i10-task.

(def GL (mk-bundle 'i10-task [] "i10-task-"
          {'well-formed-run-upd ['(fn [r :- RunRow] (Eq.refl (run-key r))) 4]
           'well-formed-task-upd ['(fn [t :- TaskRow] (Eq.refl (task-key t))) 4]}))
(swap! (:renames GL) assoc 'well-formed-parts 'i10-task-parts)

;; ---- the cells

(a/theorem i10-task-run-upd [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                       hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                       hk :- (forall [r :- RunRow] (= (run-key (f r)) (run-key r)))]
  (=> (= (i10-task w) true) (= (i10-task (run-upd w x f)) true))
  (intro h)
  (have e (= (i10-task-rest (run-upd w x f)) (i10-task-rest w)))
  (simp only [i10-task-rest run-upd set-runs (run-keys-upd x f hk (:runs w))])
  (exact (i10-task-intro _ (well-formed-run-upd w x f hf (i10-task-well-formed w h)) (Eq.trans e (i10-task-rest-of w h)))))

(a/theorem i10-task-task-upd [w :- World, x :- Nat, f :- (=> TaskRow TaskRow),
                        hf :- (forall [t :- TaskRow] (= (task-id (f t)) (task-id t))),
                        hk :- (forall [t :- TaskRow] (= (task-key (f t)) (task-key t)))]
  (=> (= (i10-task w) true) (= (i10-task (task-upd w x f)) true))
  (intro h)
  (have e (= (i10-task-rest (task-upd w x f)) (i10-task-rest w)))
  (simp only [i10-task-rest task-upd set-tasks (task-keys-upd x f hk (:tasks w))])
  (exact (i10-task-intro _ (well-formed-task-upd w x f hf (i10-task-well-formed w h)) (Eq.trans e (i10-task-rest-of w h)))))

(defpart GL
  :reads '[runs tasks next-id]
  :cells (into {'well-formed-run-upd 'i10-task-run-upd                ; keeps the run key
                'well-formed-task-upd 'i10-task-task-upd              ; keeps the task key
                'well-formed-bump '(i10-task-rest-bump w R)           ; (a) only gains room
                'well-formed-insert-edge-fresh '(i10-task-rest-bump (insert-edge w (edge-set-id (:next-id w) e)) (Eq.trans (rfl) R))}
               (for [o '[well-formed-source-ins-fresh well-formed-fork-ins-fresh well-formed-resource-ins-fresh well-formed-scope-ins-fresh
                         well-formed-comp-ins-fresh well-formed-act-ins-fresh]]      ; a row that i10-task does not read, and bump
                 [o (list 'i10-task-rest-bump (list (symbol (str/replace (subs (name o) 12) "-fresh" "")) 'w 'r)
                          (list 'Eq.trans '(rfl) 'R))])))

;; the per-edit frame lemmas of the edge edits, now from the view
(frames/frame-theorem! 'i10-task-rest-mark-edge 'i10-task-rest 'well-formed-mark-edge)
(frames/frame-theorem! 'i10-task-rest-unmark-edge 'i10-task-rest 'well-formed-unmark-edge)
(frames/frame-theorem! 'i10-task-rest-remove-edge 'i10-task-rest 'well-formed-remove-edge)

;; ===========================================================================
;; Part C. The invariant under key changes
;; ===========================================================================

;; ---- generic list lemmas

(a/theorem any-upd-mono [A :- Type, idf :- (=> A Nat), x :- Nat, g :- (=> A A), p :- (=> A Bool),
                         hg :- (forall [a :- A] (=> (= (p a) true) (= (p (g a)) true))), xs :- (List A)]
  (=> (= (tbl-any p xs) true) (= (tbl-any p (tbl-upd idf x g xs)) true))
  (induction xs)
  (case [nil] (intro h) (simp [tbl-any] at h))
  (case [cons h t ih]
    (intro ha)
    (cases hp (p h))
    (case [false]
      (simp only [tbl-any hp Bool.false_or] at ha)
      (cases hx (Nat.beq (idf h) x))
      (all_goals (simp only [tbl-upd hx tbl-any (ih ha) Bool.or_true])))
    (case [true]
      (cases hx (Nat.beq (idf h) x))
      (case [false] (simp only [tbl-upd hx tbl-any hp Bool.true_or]))
      (case [true] (simp only [tbl-upd hx tbl-any (hg h hp) Bool.true_or])))))

(a/theorem any-upd-off [A :- Type, idf :- (=> A Nat), x :- Nat, g :- (=> A A), p :- (=> A Bool),
                        hoff :- (forall [a :- A] (=> (= (p a) true) (= (Nat.beq (idf a) x) false))), xs :- (List A)]
  (=> (= (tbl-any p xs) true) (= (tbl-any p (tbl-upd idf x g xs)) true))
  (induction xs)
  (case [nil] (intro h) (simp [tbl-any] at h))
  (case [cons h t ih]
    (intro ha)
    (cases hp (p h))
    (case [false]
      (simp only [tbl-any hp Bool.false_or] at ha)
      (cases hx (Nat.beq (idf h) x))
      (all_goals (simp only [tbl-upd hx tbl-any (ih ha) Bool.or_true])))
    (case [true] (simp only [tbl-upd (hoff h hp) tbl-any hp Bool.true_or]))))

(a/theorem any-del-off [A :- Type, idf :- (=> A Nat), x :- Nat, p :- (=> A Bool),
                        hoff :- (forall [a :- A] (=> (= (p a) true) (= (Nat.beq (idf a) x) false))), xs :- (List A)]
  (=> (= (tbl-any p xs) true) (= (tbl-any p (tbl-del idf x xs)) true))
  (induction xs)
  (case [nil] (intro h) (simp [tbl-any] at h))
  (case [cons h t ih]
    (intro ha)
    (cases hp (p h))
    (case [false]
      (simp only [tbl-any hp Bool.false_or] at ha)
      (cases hx (Nat.beq (idf h) x))
      (all_goals (simp only [tbl-del hx tbl-any (ih ha) Bool.or_true])))
    (case [true] (simp only [tbl-del (hoff h hp) tbl-any hp Bool.true_or]))))

(a/theorem any-keep-on [A :- Type, K :- (=> Nat Bool), idf :- (=> A Nat), p :- (=> A Bool),
                        hon :- (forall [a :- A] (=> (= (p a) true) (= (K (idf a)) true))), xs :- (List A)]
  (=> (= (tbl-any p xs) true) (= (tbl-any p (tbl-keep K idf xs)) true))
  (induction xs)
  (case [nil] (intro h) (simp [tbl-any] at h))
  (case [cons h t ih]
    (intro ha)
    (cases hp (p h))
    (case [false]
      (simp only [tbl-any hp Bool.false_or] at ha)
      (cases hk (K (idf h)))
      (all_goals (simp only [tbl-keep hk tbl-any (ih ha) Bool.or_true])))
    (case [true] (simp only [tbl-keep (hon h hp) tbl-any hp Bool.true_or]))))

;; ---- the rest under key edits

;; a task without result does not have run x
(a/defn off-run [x :- Nat, t :- TaskKey] Bool (Bool.or (:done t) (Bool.not (Nat.beq (:run t) x))))

(a/theorem trun-one-eq [k2 :- RunKey, k :- RunKey, t :- TaskKey]
  (=> (= (:id k2) (:id k)) (= (:of k2) (:of k)) (= (trun-one k2 t) (trun-one k t)))
  (intros h1 h2) (simp only [trun-one h1 h2]))
(a/theorem trun-one-teq [k :- RunKey, t2 :- TaskKey, t :- TaskKey]
  (=> (= (:id t2) (:id t)) (= (:run t2) (:run t)) (= (trun-one k t2) (trun-one k t)))
  (intros h1 h2) (simp only [trun-one h1 h2]))

(a/theorem run-for-up [t :- TaskKey, k :- RunKey, k2 :- RunKey]
  (=> (= (:id k2) (:id k)) (= (:of k2) (:of k)) (= (:alive k2) true) (= (run-for t k) true) (= (run-for t k2) true))
  (intros h1 h2 h3 h)
  (simp only [run-for Bool.and_eq_true] at h)
  (simp only [run-for h1 h2 h3 Bool.and_eq_true])
  (exact (And.intro (And.left h) (And.intro (And.left (And.right h)) True.intro))))

(a/theorem run-for-off [x :- Nat, t :- TaskKey, k :- RunKey]
  (=> (= (off-run x t) true) (= (:done t) false) (= (run-for t k) true) (= (Nat.beq (run-key-id k) x) false))
  (intros ho hd h)
  (simp only [off-run hd Bool.false_or] at ho)
  (simp only [run-for Bool.and_eq_true] at h)
  (have e (= (:id k) (:run t))) (exact (Nat.eq_of_beq_eq_true (And.left h)))
  (simp only [run-key-id e]) (exact (bnot-true _ ho)))

(a/theorem i10-task-keys-ok-up [rks :- (List RunKey), tks :- (List TaskKey), n :- Nat, x :- Nat, g :- (=> RunKey RunKey),
                    hid :- (forall [k :- RunKey] (= (:id (g k)) (:id k))),
                    hof :- (forall [k :- RunKey] (= (:of (g k)) (:of k))),
                    hal :- (forall [k :- RunKey] (= (:alive (g k)) true))]
  (=> (= (i10-task-keys-ok rks tks n) true) (= (i10-task-keys-ok (tbl-upd run-key-id x g rks) tks n) true))
  (intro h)
  (simp only [i10-task-keys-ok Bool.and_eq_true] at h)
  (have e1 (forall [k :- RunKey] (= (of-below-k n (g k)) (of-below-k n k)))) (intro k) (simp only [of-below-k (hof k)])
  (have e2 (forall [k :- RunKey] (= (trun-ok tks (g k)) (trun-ok tks k))))
  (intro k) (simp only [trun-ok])
  (exact (tbl-all-congr TaskKey (trun-one (g k)) (trun-one k) (fn [t :- TaskKey] (trun-one-eq (g k) k t (hid k) (hof k))) tks))
  (have e3 (forall [t :- TaskKey] (=> (= (thas-ok rks t) true) (= (thas-ok (tbl-upd run-key-id x g rks) t) true))))
  (intros t ht)
  (cases hd (:done t))
  (case [true] (simp only [thas-ok hd Bool.true_or]))
  (case [false]
    (simp only [thas-ok hd Bool.false_or] at ht)
    (simp only [thas-ok hd Bool.false_or])
    (exact (any-upd-mono RunKey run-key-id x g (run-for t)
             (fn [k :- RunKey, hk :- (= (run-for t k) true)] (run-for-up t k (g k) (hid k) (hof k) (hal k) hk)) rks ht)))
  (simp only [i10-task-keys-ok Bool.and_eq_true (tbl-all-upd-same RunKey run-key-id x g (of-below-k n) e1 rks)
              (tbl-all-upd-same RunKey run-key-id x g (trun-ok tks) e2 rks)])
  (exact (And.intro (And.left h) (And.intro (And.left (And.right h))
           (tbl-all-mono TaskKey (thas-ok rks) (thas-ok (tbl-upd run-key-id x g rks)) e3 tks (And.right (And.right h)))))))

(a/theorem i10-task-keys-ok-down [rks :- (List RunKey), tks :- (List TaskKey), n :- Nat, x :- Nat, g :- (=> RunKey RunKey),
                      hid :- (forall [k :- RunKey] (= (:id (g k)) (:id k))),
                      hof :- (forall [k :- RunKey] (= (:of (g k)) (:of k)))]
  (=> (= (i10-task-keys-ok rks tks n) true) (= (tbl-all (off-run x) tks) true) (= (i10-task-keys-ok (tbl-upd run-key-id x g rks) tks n) true))
  (intros h hx)
  (simp only [i10-task-keys-ok Bool.and_eq_true] at h)
  (have e1 (forall [k :- RunKey] (= (of-below-k n (g k)) (of-below-k n k)))) (intro k) (simp only [of-below-k (hof k)])
  (have e2 (forall [k :- RunKey] (= (trun-ok tks (g k)) (trun-ok tks k))))
  (intro k) (simp only [trun-ok])
  (exact (tbl-all-congr TaskKey (trun-one (g k)) (trun-one k) (fn [t :- TaskKey] (trun-one-eq (g k) k t (hid k) (hof k))) tks))
  (have e3 (forall [t :- TaskKey] (=> (= (off-run x t) true) (= (thas-ok rks t) true) (= (thas-ok (tbl-upd run-key-id x g rks) t) true))))
  (intros t ho ht)
  (cases hd (:done t))
  (case [true] (simp only [thas-ok hd Bool.true_or]))
  (case [false]
    (simp only [thas-ok hd Bool.false_or] at ht)
    (simp only [thas-ok hd Bool.false_or])
    (exact (any-upd-off RunKey run-key-id x g (run-for t)
             (fn [k :- RunKey, hk :- (= (run-for t k) true)] (run-for-off x t k ho hd hk)) rks ht)))
  (simp only [i10-task-keys-ok Bool.and_eq_true (tbl-all-upd-same RunKey run-key-id x g (of-below-k n) e1 rks)
              (tbl-all-upd-same RunKey run-key-id x g (trun-ok tks) e2 rks)])
  (exact (And.intro (And.left h) (And.intro (And.left (And.right h))
           (tbl-all-mono2 TaskKey (off-run x) (thas-ok rks) (thas-ok (tbl-upd run-key-id x g rks)) e3 tks hx (And.right (And.right h)))))))

(a/theorem i10-task-keys-ok-del [rks :- (List RunKey), tks :- (List TaskKey), n :- Nat, x :- Nat]
  (=> (= (i10-task-keys-ok rks tks n) true) (= (tbl-all (off-run x) tks) true) (= (i10-task-keys-ok (tbl-del run-key-id x rks) tks n) true))
  (intros h hx)
  (simp only [i10-task-keys-ok Bool.and_eq_true] at h)
  (have e3 (forall [t :- TaskKey] (=> (= (off-run x t) true) (= (thas-ok rks t) true) (= (thas-ok (tbl-del run-key-id x rks) t) true))))
  (intros t ho ht)
  (cases hd (:done t))
  (case [true] (simp only [thas-ok hd Bool.true_or]))
  (case [false]
    (simp only [thas-ok hd Bool.false_or] at ht)
    (simp only [thas-ok hd Bool.false_or])
    (exact (any-del-off RunKey run-key-id x (run-for t)
             (fn [k :- RunKey, hk :- (= (run-for t k) true)] (run-for-off x t k ho hd hk)) rks ht)))
  (simp only [i10-task-keys-ok Bool.and_eq_true])
  (exact (And.intro
           (tbl-all-del RunKey run-key-id x (of-below-k n) (of-below-k n)
             (fn [k :- RunKey, h1 :- (= (of-below-k n k) true), h2 :- (= (Nat.beq (run-key-id k) x) false)] h1) rks (And.left h))
           (And.intro
             (tbl-all-del RunKey run-key-id x (trun-ok tks) (trun-ok tks)
               (fn [k :- RunKey, h1 :- (= (trun-ok tks k) true), h2 :- (= (Nat.beq (run-key-id k) x) false)] h1) rks (And.left (And.right h)))
             (tbl-all-mono2 TaskKey (off-run x) (thas-ok rks) (thas-ok (tbl-del run-key-id x rks)) e3 tks hx (And.right (And.right h)))))))

;; a task gets its result (its id and run are kept)
(a/theorem i10-task-keys-ok-done [rks :- (List RunKey), tks :- (List TaskKey), n :- Nat, x :- Nat, g :- (=> TaskKey TaskKey),
                      hid :- (forall [t :- TaskKey] (= (:id (g t)) (:id t))),
                      hrun :- (forall [t :- TaskKey] (= (:run (g t)) (:run t))),
                      hd :- (forall [t :- TaskKey] (= (:done (g t)) true))]
  (=> (= (i10-task-keys-ok rks tks n) true) (= (i10-task-keys-ok rks (tbl-upd task-key-id x g tks) n) true))
  (intro h)
  (simp only [i10-task-keys-ok Bool.and_eq_true] at h)
  (have e2 (forall [k :- RunKey] (= (trun-ok (tbl-upd task-key-id x g tks) k) (trun-ok tks k))))
  (intro k) (simp only [trun-ok])
  (exact (tbl-all-upd-same TaskKey task-key-id x g (trun-one k)
           (fn [t :- TaskKey] (trun-one-teq k (g t) t (hid t) (hrun t)))
           tks))
  (have hin (forall [t :- TaskKey] (=> (= (thas-ok rks t) true) (= (Nat.beq (task-key-id t) x) true) (= (thas-ok rks (g t)) true))))
  (intros t h1 h2) (simp only [thas-ok (hd t) Bool.true_or])
  (have hout (forall [t :- TaskKey] (=> (= (thas-ok rks t) true) (= (Nat.beq (task-key-id t) x) false) (= (thas-ok rks t) true))))
  (intros t h1 h2) (exact h1)
  (simp only [i10-task-keys-ok Bool.and_eq_true (tbl-all-congr RunKey (trun-ok (tbl-upd task-key-id x g tks)) (trun-ok tks) e2 rks)])
  (exact (And.intro (And.left h) (And.intro (And.left (And.right h))
           (tbl-all-upd TaskKey task-key-id x g (thas-ok rks) (thas-ok rks) hin hout tks (And.right (And.right h)))))))

;; ---- unique ids

(a/defn same-id-then [A :- Type :implicit, idf :- (=> A Nat), x :- Nat, Q :- (=> A Bool), b :- A] Bool
  (Bool.or (Bool.not (Nat.beq (idf b) x)) (Q b)))

(a/theorem mem-ids-has [A :- Type, idf :- (=> A Nat), a :- A, xs :- (List A)]
  (=> (List.Mem a xs) (= (nat-mem (idf a) (tbl-ids idf xs)) true))
  (induction xs)
  (case [nil] (intro hm) (cases hm))
  (case [cons h t ih]
    (intro hm)
    (cases hm)
    (simp [nat-mem tbl-ids])
    (rename_i hm2)
    (cases hx (Nat.beq (idf h) (idf a)))
    (all_goals (simp only [nat-mem tbl-ids hx]))
    (exact (ih hm2))))

(a/theorem absent-then [A :- Type, idf :- (=> A Nat), x :- Nat, Q :- (=> A Bool), xs :- (List A)]
  (=> (= (nat-mem x (tbl-ids idf xs)) false) (= (tbl-all (same-id-then idf x Q) xs) true))
  (induction xs)
  (case [nil] (intro h) (simp [tbl-all]))
  (case [cons h t ih]
    (intro hn)
    (cases hx (Nat.beq (idf h) x))
    (case [true] (simp [nat-mem tbl-ids hx] at hn))
    (case [false]
      (simp only [nat-mem tbl-ids hx] at hn)
      (simp only [tbl-all same-id-then hx Bool.not_false Bool.true_or Bool.true_and])
      (exact (ih hn)))))

;; with unique ids, every row with a's id satisfies Q when a does
(a/theorem uniq-all [A :- Type, idf :- (=> A Nat), Q :- (=> A Bool), a :- A, xs :- (List A)]
  (=> (= (nat-nodup (tbl-ids idf xs)) true) (List.Mem a xs) (= (Q a) true)
      (= (tbl-all (same-id-then idf (idf a) Q) xs) true))
  (induction xs)
  (case [nil] (intros hn hm hq) (cases hm))
  (case [cons h t ih]
    (intros hn hm hq)
    (simp only [tbl-ids nat-nodup Bool.and_eq_true] at hn)
    (have hn1 := (bnot-true _ (And.left hn)))
    (cases hm)
    (case [head]
      (simp only [tbl-all same-id-then hq Bool.or_true Bool.true_and])
      (exact (absent-then _ idf _ Q _ hn1)))
    (case [tail]
      (rename_i hm2)
      (have hne (= (Nat.beq (idf h) (idf a)) false))
      (cases he (Nat.beq (idf h) (idf a)))
      (rfl)
      (have e (= (idf h) (idf a))) (exact (Nat.eq_of_beq_eq_true he))
      (have hm3 := (mem-ids-has _ idf a _ hm2))
      (rw [← e] at hm3) (rw [hm3] at hn1) (cases hn1)
      (simp only [tbl-all same-id-then hne Bool.not_false Bool.true_or Bool.true_and])
      (exact (ih (And.right hn) hm2 hq)))))

(a/theorem nodup-app-disj [x :- Nat, xs :- (List Nat), ys :- (List Nat)]
  (=> (= (nat-nodup (nat-app xs ys)) true) (= (nat-mem x xs) true) (= (nat-mem x ys) false))
  (induction xs)
  (case [nil] (intros hn hm) (simp [nat-mem] at hm))
  (case [cons h t ih]
    (intros hn hm)
    (simp only [nat-app nat-nodup Bool.and_eq_true] at hn)
    (cases hx (Nat.beq h x))
    (case [false] (simp only [nat-mem hx] at hm) (exact (ih (And.right hn) hm)))
    (case [true]
      (have e (= h x)) (exact (Nat.eq_of_beq_eq_true hx))
      (have h1 := (bnot-true _ (And.left hn)))
      (simp only [nat-mem-app Bool.or_eq_false_iff] at h1)
      (rw [e] at h1) (exact (And.right h1)))))

(a/theorem ids-unique-of [w :- World]
  (=> (= (well-formed w) true) (= (nat-nodup (all-ids w)) true))
  (intro h)
  (have hi := (And.right (And.right (well-formed-parts w h))))
  (simp only [ids-ok ids-unique Bool.and_eq_true] at hi)
  (exact (And.left hi)))

(a/theorem tk-not-comp [w :- World, y :- Nat]
  (=> (= (well-formed w) true) (= (tbl-has task-id y (:tasks w)) true) (= (tbl-has comp-id y (:comps w)) false))
  (intros h ha)
  (cases hc (tbl-has comp-id y (:comps w)))
  (case [false] (rfl))
  (case [true]
    (have u := (ids-unique-of w h))
    (simp only [all-ids] at u)
    (have u2 := (nat-nodup-app-right _ _ u))
    (have hm (= (nat-mem y (tbl-ids comp-id (:comps w))) true)) (rw [nat-mem-ids]) (exact hc)
    (have hm2 (= (nat-mem y (tbl-ids task-id (:tasks w))) true)) (rw [nat-mem-ids]) (exact ha)
    (have d := (nodup-app-disj y _ _ u2 hm))
    (simp only [nat-mem-app Bool.or_eq_false_iff] at d)
    (have d2 := (And.left d))
    (rw [hm2] at d2) (cases d2)))
;; Z#77: a run of a fork-local task is no computation run
(a/theorem local-run-nocomp [w :- World, r :- RunRow]
  (=> (= (well-formed w) true) (= (run-of-local w r) true) (= (comp-find w (:of r)) (Option.none CompRow)))
  (intros h hl)
  (cases ht (task-find w (:of r))) (case' [some t]) (case' [none])
  (simp only [run-of-local task-local-id opt-test ht] at hl) (cases hl)
  (have hn := (tk-not-comp w (:of r) h (tbl-find-has TaskRow task-id (:of r) t (:tasks w) ht)))
  (cases hc (comp-find w (:of r))) (case' [some c]) (case' [none])
  (rfl)
  (have z := (tbl-find-has CompRow comp-id (:of r) c (:comps w) hc))
  (rw [hn] at z) (cases z))
(a/theorem bool-and-left [a :- Bool, b :- Bool] (=> (= (Bool.and a b) true) (= a true))
  (cases a) (all_goals (simp)))
(a/theorem bool-and-right [a :- Bool, b :- Bool] (=> (= (Bool.and a b) true) (= b true))
  (cases a) (all_goals (simp)))
(a/theorem lit-runs-nodup [w :- World]
  (=> (= (well-formed w) true) (= (nat-nodup (tbl-ids run-id (:runs w))) true))
  (intro h)
  (have u := (ids-unique-of w h))
  (simp only [all-ids] at u)
  (exact (nat-nodup-app-left _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ u))))))

(a/theorem tasks-nodup [w :- World]
  (=> (= (well-formed w) true) (= (nat-nodup (tbl-ids task-id (:tasks w))) true))
  (intro h)
  (have u := (ids-unique-of w h))
  (simp only [all-ids] at u)
  (exact (nat-nodup-app-left _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ u)))))

;; a computation id is no task id
(a/theorem comp-not-task [w :- World, x :- Nat]
  (=> (= (well-formed w) true) (= (comp-has w x) true) (= (nat-mem x (tbl-ids task-id (:tasks w))) false))
  (intros h hc)
  (have u := (ids-unique-of w h))
  (simp only [all-ids] at u)
  (have u2 := (nat-nodup-app-right _ _ u))
  (have hm (= (nat-mem x (tbl-ids comp-id (:comps w))) true)) (rw [nat-mem-ids]) (exact hc)
  (have d := (nodup-app-disj x _ _ u2 hm))
  (simp only [nat-mem-app Bool.or_eq_false_iff] at d)
  (exact (And.left d)))

;; ---- key lists of the rows

(a/defn on-rkey [P :- (=> RunKey Bool), r :- RunRow] Bool (P (run-key r)))
(a/defn on-tkey [P :- (=> TaskKey Bool), t :- TaskRow] Bool (P (task-key t)))
(a/theorem all-run-keys [P :- (=> RunKey Bool), rs :- (List RunRow)] (= (tbl-all P (run-keys rs)) (tbl-all (on-rkey P) rs))
  (induction rs) (case [nil] (simp only [run-keys tbl-all])) (case [cons h t ih] (simp only [run-keys tbl-all on-rkey ih])))
(a/theorem all-task-keys [P :- (=> TaskKey Bool), ts :- (List TaskRow)] (= (tbl-all P (task-keys ts)) (tbl-all (on-tkey P) ts))
  (induction ts) (case [nil] (simp only [task-keys tbl-all])) (case [cons h t ih] (simp only [task-keys tbl-all on-tkey ih])))

(a/defn not-id [x :- Nat, t :- TaskKey] Bool (Bool.not (Nat.beq (:id t) x)))
(a/theorem not-id-tasks [x :- Nat, ts :- (List TaskRow)]
  (=> (= (nat-mem x (tbl-ids task-id ts)) false) (= (tbl-all (not-id x) (task-keys ts)) true))
  (induction ts)
  (case [nil] (intro h) (simp [task-keys tbl-all]))
  (case [cons h t ih]
    (intro hn)
    (cases hx (Nat.beq (task-id h) x))
    (case [true] (simp [nat-mem tbl-ids hx] at hn))
    (case [false]
      (simp only [nat-mem tbl-ids hx] at hn)
      (have hx2 (= (Nat.beq (:id h) x) false)) (exact hx)
      (simp only [task-keys tbl-all not-id task-key hx2 Bool.not_false Bool.true_and])
      (exact (ih hn)))))

(a/theorem find-none-tasks [x :- Nat, ts :- (List TaskRow)]
  (=> (= (tbl-find task-id x ts) (Option.none TaskRow)) (= (tbl-all (not-id x) (task-keys ts)) true))
  (induction ts)
  (case [nil] (intro h) (simp [task-keys tbl-all]))
  (case [cons h t ih]
    (intro hn)
    (cases hx (Nat.beq (task-id h) x))
    (case [true] (simp [tbl-find hx] at hn))
    (case [false]
      (simp only [tbl-find hx] at hn)
      (have hx2 (= (Nat.beq (:id h) x) false)) (exact hx)
      (simp only [task-keys tbl-all not-id task-key hx2 Bool.not_false Bool.true_and])
      (exact (ih hn)))))

(a/defn of-is [k :- Nat, b :- RunRow] Bool (Nat.beq (:of b) k))
(a/defn of-at [x :- Nat, k :- Nat, r :- RunKey] Bool (Bool.or (Bool.not (Nat.beq (:id r) x)) (Nat.beq (:of r) k)))
(a/defn not-alive [b :- RunRow] Bool (Bool.not (run-alive b)))
(a/defn dead-at [x :- Nat, r :- RunKey] Bool (Bool.or (Bool.not (Nat.beq (:id r) x)) (Bool.not (:alive r))))

(a/theorem of-at-runs [w :- World, r :- RunRow]
  (=> (= (well-formed w) true) (List.Mem r (:runs w)) (= (tbl-all (of-at (:id r) (:of r)) (run-keys (:runs w))) true))
  (intros h hm)
  (have u := (uniq-all RunRow run-id (of-is (:of r)) r (:runs w) (lit-runs-nodup w h) hm (Nat.beq_refl (:of r))))
  (rw [all-run-keys])
  (exact (Eq.trans (tbl-all-congr RunRow (on-rkey (of-at (:id r) (:of r))) (same-id-then run-id (run-id r) (of-is (:of r)))
                     (fn [b :- RunRow] (Eq.refl (on-rkey (of-at (:id r) (:of r)) b))) (:runs w)) u)))

(a/theorem dead-at-runs [w :- World, r :- RunRow]
  (=> (= (well-formed w) true) (List.Mem r (:runs w)) (= (run-alive r) false)
      (= (tbl-all (dead-at (:id r)) (run-keys (:runs w))) true))
  (intros h hm ha)
  (have hq (= (not-alive r) true)) (simp only [not-alive ha Bool.not_false])
  (have u := (uniq-all RunRow run-id not-alive r (:runs w) (lit-runs-nodup w h) hm hq))
  (rw [all-run-keys])
  (exact (Eq.trans (tbl-all-congr RunRow (on-rkey (dead-at (:id r))) (same-id-then run-id (run-id r) not-alive)
                     (fn [b :- RunRow] (Eq.refl (on-rkey (dead-at (:id r)) b))) (:runs w)) u)))

(a/defn both [A :- Type :implicit, p :- (=> A Bool), q :- (=> A Bool), a :- A] Bool (Bool.and (p a) (q a)))
(a/theorem both-left [A :- Type, p :- (=> A Bool), q :- (=> A Bool), a :- A] (=> (= (both p q a) true) (= (p a) true))
  (intro h) (simp only [both Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem both-right [A :- Type, p :- (=> A Bool), q :- (=> A Bool), a :- A] (=> (= (both p q a) true) (= (q a) true))
  (intro h) (simp only [both Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem any-and-all [A :- Type, p :- (=> A Bool), q :- (=> A Bool), xs :- (List A)]
  (=> (= (tbl-any p xs) true) (= (tbl-all q xs) true) (= (tbl-any (both p q) xs) true))
  (induction xs)
  (case [nil] (intros h1 h2) (simp [tbl-any] at h1))
  (case [cons h t ih]
    (intros h1 h2)
    (simp only [tbl-all Bool.and_eq_true] at h2)
    (cases hp (p h))
    (case [true] (simp only [tbl-any both hp (And.left h2) Bool.and_self Bool.true_or]))
    (case [false]
      (simp only [tbl-any hp Bool.false_or] at h1)
      (simp only [tbl-any (ih h1 (And.right h2)) Bool.or_true]))))

;; ---- the exempt rest: task k may be without result and run

(a/defn thas-x [k :- Nat, rks :- (List RunKey), t :- TaskKey] Bool (Bool.or (Nat.beq (:id t) k) (thas-ok rks t)))
(a/defn i10-task-exempt-keys-ok [k :- Nat, rks :- (List RunKey), tks :- (List TaskKey), n :- Nat] Bool
  (Bool.and (tbl-all (of-below-k n) rks) (Bool.and (tbl-all (trun-ok tks) rks) (tbl-all (thas-x k rks) tks))))

(a/theorem run-for-at [x :- Nat, k :- Nat, t :- TaskKey, kk :- RunKey]
  (=> (= (of-at x k kk) true) (= (Nat.beq (:id t) k) false) (= (run-for t kk) true) (= (Nat.beq (run-key-id kk) x) false))
  (intros ho hk hr)
  (simp only [run-for Bool.and_eq_true] at hr)
  (have e (= (:of kk) (:id t))) (exact (Nat.eq_of_beq_eq_true (And.left (And.right hr))))
  (simp only [run-key-id])
  (cases hx (Nat.beq (:id kk) x))
  (case [false] (rfl))
  (case [true]
    (simp only [of-at hx Bool.not_true Bool.false_or] at ho)
    (have e2 (= (:of kk) k)) (exact (Nat.eq_of_beq_eq_true ho))
    (rw [e] at e2) (rw [e2] at hk) (simp at hk)))

(a/theorem i10-task-keys-ok-kill [rks :- (List RunKey), tks :- (List TaskKey), n :- Nat, x :- Nat, k :- Nat, g :- (=> RunKey RunKey),
                      hid :- (forall [kk :- RunKey] (= (:id (g kk)) (:id kk))),
                      hof :- (forall [kk :- RunKey] (= (:of (g kk)) (:of kk)))]
  (=> (= (i10-task-keys-ok rks tks n) true) (= (tbl-all (of-at x k) rks) true) (= (i10-task-exempt-keys-ok k (tbl-upd run-key-id x g rks) tks n) true))
  (intros h hx)
  (simp only [i10-task-keys-ok Bool.and_eq_true] at h)
  (have e1 (forall [kk :- RunKey] (= (of-below-k n (g kk)) (of-below-k n kk)))) (intro kk) (simp only [of-below-k (hof kk)])
  (have e2 (forall [kk :- RunKey] (= (trun-ok tks (g kk)) (trun-ok tks kk))))
  (intro kk) (simp only [trun-ok])
  (exact (tbl-all-congr TaskKey (trun-one (g kk)) (trun-one kk) (fn [t :- TaskKey] (trun-one-eq (g kk) kk t (hid kk) (hof kk))) tks))
  (have e3 (forall [t :- TaskKey] (=> (= (thas-ok rks t) true) (= (thas-x k (tbl-upd run-key-id x g rks) t) true))))
  (intros t ht)
  (cases hk (Nat.beq (:id t) k))
  (case [true] (simp only [thas-x hk Bool.true_or]))
  (case [false]
    (simp only [thas-x hk Bool.false_or])
    (cases hd (:done t))
    (case [true] (simp only [thas-ok hd Bool.true_or]))
    (case [false]
      (simp only [thas-ok hd Bool.false_or] at ht)
      (simp only [thas-ok hd Bool.false_or])
      (have hb := (any-and-all RunKey (run-for t) (of-at x k) rks ht hx))
      (have hoff (forall [kk :- RunKey] (=> (= (both (run-for t) (of-at x k) kk) true) (= (Nat.beq (run-key-id kk) x) false))))
      (intros kk hkk) (simp only [both Bool.and_eq_true] at hkk) (exact (run-for-at x k t kk (And.right hkk) hk (And.left hkk)))
      (exact (tbl-any-mono RunKey (both (run-for t) (of-at x k)) (run-for t) (both-left RunKey (run-for t) (of-at x k)) _
               (any-upd-off RunKey run-key-id x g (both (run-for t) (of-at x k)) hoff rks hb)))))
  (simp only [i10-task-exempt-keys-ok Bool.and_eq_true (tbl-all-upd-same RunKey run-key-id x g (of-below-k n) e1 rks)
              (tbl-all-upd-same RunKey run-key-id x g (trun-ok tks) e2 rks)])
  (exact (And.intro (And.left h) (And.intro (And.left (And.right h))
           (tbl-all-mono TaskKey (thas-ok rks) (thas-x k (tbl-upd run-key-id x g rks)) e3 tks (And.right (And.right h)))))))

(a/theorem i10-task-exempt-keys-ok-done [rks :- (List RunKey), tks :- (List TaskKey), n :- Nat, k :- Nat, g :- (=> TaskKey TaskKey),
                       hid :- (forall [t :- TaskKey] (= (:id (g t)) (:id t))),
                       hrun :- (forall [t :- TaskKey] (= (:run (g t)) (:run t))),
                       hd :- (forall [t :- TaskKey] (= (:done (g t)) true))]
  (=> (= (i10-task-exempt-keys-ok k rks tks n) true) (= (i10-task-keys-ok rks (tbl-upd task-key-id k g tks) n) true))
  (intro h)
  (simp only [i10-task-exempt-keys-ok Bool.and_eq_true] at h)
  (have e2 (forall [kk :- RunKey] (= (trun-ok (tbl-upd task-key-id k g tks) kk) (trun-ok tks kk))))
  (intro kk) (simp only [trun-ok])
  (exact (tbl-all-upd-same TaskKey task-key-id k g (trun-one kk) (fn [t :- TaskKey] (trun-one-teq kk (g t) t (hid t) (hrun t))) tks))
  (have hin (forall [t :- TaskKey] (=> (= (thas-x k rks t) true) (= (Nat.beq (task-key-id t) k) true) (= (thas-ok rks (g t)) true))))
  (intros t h1 h2) (simp only [thas-ok (hd t) Bool.true_or])
  (have hout (forall [t :- TaskKey] (=> (= (thas-x k rks t) true) (= (Nat.beq (task-key-id t) k) false) (= (thas-ok rks t) true))))
  (intros t h1 h2)
  (have h3 (= (Nat.beq (:id t) k) false)) (exact h2)
  (simp only [thas-x h3 Bool.false_or] at h1) (exact h1)
  (simp only [i10-task-keys-ok Bool.and_eq_true (tbl-all-congr RunKey (trun-ok (tbl-upd task-key-id k g tks)) (trun-ok tks) e2 rks)])
  (exact (And.intro (And.left h) (And.intro (And.left (And.right h))
           (tbl-all-upd TaskKey task-key-id k g (thas-x k rks) (thas-ok rks) hin hout tks (And.right (And.right h)))))))

(a/theorem i10-task-exempt-keys-ok-none [rks :- (List RunKey), tks :- (List TaskKey), n :- Nat, k :- Nat]
  (=> (= (i10-task-exempt-keys-ok k rks tks n) true) (= (tbl-all (not-id k) tks) true) (= (i10-task-keys-ok rks tks n) true))
  (intros h hn)
  (simp only [i10-task-exempt-keys-ok Bool.and_eq_true] at h)
  (have hpq (forall [t :- TaskKey] (=> (= (not-id k t) true) (= (thas-x k rks t) true) (= (thas-ok rks t) true))))
  (intros t h1 h2)
  (simp only [not-id] at h1)
  (simp only [thas-x (bnot-true _ h1) Bool.false_or] at h2) (exact h2)
  (simp only [i10-task-keys-ok Bool.and_eq_true])
  (exact (And.intro (And.left h) (And.intro (And.left (And.right h))
           (tbl-all-mono2 TaskKey (not-id k) (thas-x k rks) (thas-ok rks) hpq tks hn (And.right (And.right h)))))))

(a/defn const-b [b :- Bool, kk :- RunKey] Bool b)
(a/theorem any-const [b :- Bool, xs :- (List RunKey)] (=> (= (tbl-any (const-b b) xs) true) (= b true))
  (induction xs)
  (case [nil] (intro h) (simp [tbl-any] at h))
  (case [cons h t ih]
    (intro ha)
    (simp only [tbl-any const-b Bool.or_eq_true] at ha)
    (cases ha)
    (case [inl h1] (exact h1))
    (case [inr h2] (exact (ih h2)))))
(a/theorem any-all-imp [A :- Type, p :- (=> A Bool), q :- (=> A Bool), r :- (=> A Bool),
                        h :- (forall [a :- A] (=> (= (p a) true) (= (q a) true) (= (r a) true))), xs :- (List A)]
  (=> (= (tbl-any p xs) true) (= (tbl-all q xs) true) (= (tbl-any r xs) true))
  (intros h1 h2)
  (exact (tbl-any-mono A (both p q) r
           (fn [a :- A, ha :- (= (both p q a) true)]
             (h a (both-left A p q a ha) (both-right A p q a ha)))
           xs (any-and-all A p q xs h1 h2))))

(a/theorem dead-run [t :- TaskKey, x :- Nat, kk :- RunKey]
  (=> (= (run-for t kk) true) (= (dead-at x kk) true) (= (const-b (Bool.not (Nat.beq (:run t) x)) kk) true))
  (intros h1 h2)
  (simp only [run-for Bool.and_eq_true] at h1)
  (have e (= (:id kk) (:run t))) (exact (Nat.eq_of_beq_eq_true (And.left h1)))
  (simp only [dead-at (And.right (And.right h1)) Bool.not_true Bool.or_false] at h2)
  (rw [e] at h2) (simp only [const-b]) (exact h2))

;; all rows with id x are done: no task without result has run x
(a/theorem dead-off [rks :- (List RunKey), tks :- (List TaskKey), n :- Nat, x :- Nat]
  (=> (= (i10-task-keys-ok rks tks n) true) (= (tbl-all (dead-at x) rks) true) (= (tbl-all (off-run x) tks) true))
  (intros h hd)
  (simp only [i10-task-keys-ok Bool.and_eq_true] at h)
  (have hin (forall [t :- TaskKey] (=> (= (thas-ok rks t) true) (= (off-run x t) true))))
  (intros t ht)
  (cases hdn (:done t))
  (case [true] (simp only [off-run hdn Bool.true_or]))
  (case [false]
    (simp only [thas-ok hdn Bool.false_or] at ht)
    (have hc := (any-all-imp RunKey (run-for t) (dead-at x) (const-b (Bool.not (Nat.beq (:run t) x)))
                  (fn [kk :- RunKey, h1 :- (= (run-for t kk) true), h2 :- (= (dead-at x kk) true)] (dead-run t x kk h1 h2)) rks ht hd))
    (simp only [off-run hdn Bool.false_or])
    (exact (any-const _ rks hc)))
  (exact (tbl-all-mono TaskKey (thas-ok rks) (off-run x) hin tks (And.right (And.right h)))))

(a/defn clr [t :- TaskKey] TaskKey (TaskKey.mk (:id t) 0 (:done t)))
(a/defn run-is-if [k :- Nat, x :- Nat, t :- TaskKey] Bool (Bool.or (Bool.not (Nat.beq (:id t) k)) (Nat.beq (:run t) x)))
(a/defn done-if-id [k :- Nat, t :- TaskKey] Bool (Bool.or (Bool.not (Nat.beq (:id t) k)) (:done t)))

(a/theorem all-upd2 [A :- Type, idf :- (=> A Nat), x :- Nat, f :- (=> A A), P :- (=> A Bool), R :- (=> A Bool), Q :- (=> A Bool),
                     hin :- (forall [r :- A] (=> (= (P r) true) (= (R r) true) (= (Nat.beq (idf r) x) true) (= (Q (f r)) true))),
                     hout :- (forall [r :- A] (=> (= (P r) true) (= (R r) true) (= (Nat.beq (idf r) x) false) (= (Q r) true))),
                     xs :- (List A)]
  (=> (= (tbl-all P xs) true) (= (tbl-all R xs) true) (= (tbl-all Q (tbl-upd idf x f xs)) true))
  (induction xs)
  (case [nil] (intros h1 h2) (simp [tbl-all tbl-upd]))
  (case [cons h t ih]
    (intros h1 h2)
    (simp only [tbl-all Bool.and_eq_true] at h1)
    (simp only [tbl-all Bool.and_eq_true] at h2)
    (have r := (ih (And.right h1) (And.right h2)))
    (cases hx (Nat.beq (idf h) x))
    (case [false] (simp only [tbl-upd hx tbl-all (hout h (And.left h1) (And.left h2) hx) r Bool.and_self]))
    (case [true] (simp only [tbl-upd hx tbl-all (hin h (And.left h1) (And.left h2) hx) r Bool.and_self]))))

(a/theorem trun-clear [k :- Nat, x :- Nat, kk :- RunKey, t :- TaskKey]
  (=> (= (trun-one kk t) true) (= (run-is-if k x t) true) (= (Nat.beq (task-key-id t) k) true) (= (Nat.beq (run-key-id kk) x) false)
      (= (trun-one kk (clr t)) true))
  (intros h1 h2 h3 h4)
  (have e (= (:id t) k)) (exact (Nat.eq_of_beq_eq_true h3))
  (have h3b (= (Nat.beq (:id t) k) true)) (exact h3)
  (simp only [run-is-if h3b Bool.not_true Bool.false_or] at h2)
  (have ex (= (:run t) x)) (exact (Nat.eq_of_beq_eq_true h2))
  (cases ho (Nat.beq (:id t) (:of kk)))
  (case [false] (simp only [trun-one clr ho Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [trun-one ho Bool.not_true Bool.false_or] at h1)
    (have e2 (= (:run t) (:id kk))) (exact (Nat.eq_of_beq_eq_true h1))
    (rw [ex] at e2)
    (simp only [run-key-id] at h4) (rw [← e2] at h4) (simp at h4)))

(a/theorem thas-clr [k :- Nat, rks :- (List RunKey), t :- TaskKey]
  (=> (= (done-if-id k t) true) (= (Nat.beq (task-key-id t) k) true) (= (thas-ok rks (clr t)) true))
  (intros h1 h2)
  (have h3 (= (Nat.beq (:id t) k) true)) (exact h2)
  (simp only [done-if-id h3 Bool.not_true Bool.false_or] at h1)
  (simp only [thas-ok clr h1 Bool.true_or]))

(a/theorem i10-task-keys-ok-clear-del [rks :- (List RunKey), tks :- (List TaskKey), n :- Nat, x :- Nat, k :- Nat]
  (=> (= (i10-task-keys-ok rks tks n) true) (= (tbl-all (dead-at x) rks) true) (= (tbl-all (run-is-if k x) tks) true)
      (= (i10-task-keys-ok (tbl-del run-key-id x rks) (tbl-upd task-key-id k clr tks) n) true))
  (intros h hd hr)
  (have hoff := (dead-off rks tks n x h hd))
  (have h1 := (i10-task-keys-ok-del rks tks n x h hoff))
  (simp only [i10-task-keys-ok Bool.and_eq_true] at h1)
  (simp only [i10-task-keys-ok Bool.and_eq_true] at h)
  (have hkeep (forall [kk :- RunKey] (=> (= (trun-ok tks kk) true) (= (Nat.beq (run-key-id kk) x) false)
                                       (= (trun-ok (tbl-upd task-key-id k clr tks) kk) true))))
  (intros kk ht hx)
  (simp only [trun-ok] at ht) (simp only [trun-ok])
  (exact (all-upd2 TaskKey task-key-id k clr (trun-one kk) (run-is-if k x) (trun-one kk)
           (fn [t :- TaskKey, a1 :- (= (trun-one kk t) true), a2 :- (= (run-is-if k x t) true), a3 :- (= (Nat.beq (task-key-id t) k) true)]
             (trun-clear k x kk t a1 a2 a3 hx))
           (fn [t :- TaskKey, a1 :- (= (trun-one kk t) true), a2 :- (= (run-is-if k x t) true), a3 :- (= (Nat.beq (task-key-id t) k) false)] a1)
           tks ht hr))
  (have htr := (tbl-all-del RunKey run-key-id x (trun-ok tks) (trun-ok (tbl-upd task-key-id k clr tks)) hkeep rks (And.left (And.right h))))
  (have hdi (forall [t :- TaskKey] (=> (= (run-is-if k x t) true) (= (off-run x t) true) (= (done-if-id k t) true))))
  (intros t a1 a2)
  (cases hk (Nat.beq (:id t) k))
  (case [false] (simp only [done-if-id hk Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [run-is-if hk Bool.not_true Bool.false_or] at a1)
    (simp only [off-run a1 Bool.not_true Bool.or_false] at a2)
    (simp only [done-if-id hk a2 Bool.or_true]))
  (have hd2 := (tbl-all-mono2 TaskKey (run-is-if k x) (off-run x) (done-if-id k) hdi tks hr hoff))
  (have hth := (all-upd2 TaskKey task-key-id k clr (thas-ok (tbl-del run-key-id x rks)) (done-if-id k) (thas-ok (tbl-del run-key-id x rks))
                 (fn [t :- TaskKey, a1 :- (= (thas-ok (tbl-del run-key-id x rks) t) true), a2 :- (= (done-if-id k t) true),
                      a3 :- (= (Nat.beq (task-key-id t) k) true)]
                   (thas-clr k (tbl-del run-key-id x rks) t a2 a3))
                 (fn [t :- TaskKey, a1 :- (= (thas-ok (tbl-del run-key-id x rks) t) true), a2 :- (= (done-if-id k t) true),
                      a3 :- (= (Nat.beq (task-key-id t) k) false)] a1)
                 tks (And.right (And.right h1)) hd2))
  (simp only [i10-task-keys-ok Bool.and_eq_true])
  (exact (And.intro (And.left h1) (And.intro htr hth))))

;; ---- new rows

(a/theorem not-id-trun [o :- Nat, m :- Nat, t :- TaskKey]
  (=> (= (not-id o t) true) (= (trun-one (RunKey.mk m o true) t) true))
  (intro h) (simp only [not-id] at h) (simp only [trun-one h Bool.true_or]))

(a/theorem thas-cons [rks :- (List RunKey), kk :- RunKey, t :- TaskKey]
  (=> (= (thas-ok rks t) true) (= (thas-ok (List.cons RunKey kk rks) t) true))
  (intro h)
  (cases hd (:done t))
  (case [true] (simp only [thas-ok hd Bool.true_or]))
  (case [false]
    (simp only [thas-ok hd Bool.false_or] at h)
    (simp only [thas-ok hd Bool.false_or tbl-any h Bool.or_true])))

(a/theorem i10-task-keys-ok-ins-run [rks :- (List RunKey), tks :- (List TaskKey), n :- Nat, n2 :- Nat, m :- Nat, o :- Nat]
  (=> (= (i10-task-keys-ok rks tks n) true) (<= n n2) (< o n2) (= (tbl-all (not-id o) tks) true)
      (= (i10-task-keys-ok (List.cons RunKey (RunKey.mk m o true) rks) tks n2) true))
  (intros h hn ho hnt)
  (simp only [i10-task-keys-ok Bool.and_eq_true] at h)
  (have h1 (= (of-below-k n2 (RunKey.mk m o true)) true)) (simp only [of-below-k Nat.blt_eq]) (exact ho)
  (have h2 (= (trun-ok tks (RunKey.mk m o true)) true))
  (simp only [trun-ok])
  (exact (tbl-all-mono TaskKey (not-id o) (trun-one (RunKey.mk m o true)) (not-id-trun o m) tks hnt))
  (have h3 := (tbl-all-mono TaskKey (thas-ok rks) (thas-ok (List.cons RunKey (RunKey.mk m o true) rks))
                (thas-cons rks (RunKey.mk m o true)) tks (And.right (And.right h))))
  (simp only [i10-task-keys-ok tbl-all Bool.and_eq_true h1 h2 Bool.true_and])
  (exact (And.intro (of-below-mono n n2 rks hn (And.left h)) (And.intro (And.left (And.right h)) h3))))

(a/theorem trun-new-task [n :- Nat, m :- Nat, kk :- RunKey]
  (=> (= (of-below-k n kk) true) (= (trun-one kk (TaskKey.mk n m false)) true))
  (intro h)
  (simp only [of-below-k Nat.blt_eq] at h)
  (have hne (= (Nat.beq n (:of kk)) false))
  (cases hb (Nat.beq n (:of kk)))
  (rfl)
  (have e (= n (:of kk))) (exact (Nat.eq_of_beq_eq_true hb))
  (rw [e] at h) (omega)
  (simp only [trun-one hne Bool.not_false Bool.true_or]))

(a/theorem i10-task-keys-ok-ins-task [rks :- (List RunKey), tks :- (List TaskKey), n :- Nat, n2 :- Nat, m :- Nat]
  (=> (= (i10-task-keys-ok rks tks n) true) (< n n2) (= (tbl-all (not-id n) tks) true)
      (= (i10-task-keys-ok (List.cons RunKey (RunKey.mk m n true) rks) (List.cons TaskKey (TaskKey.mk n m false) tks) n2) true))
  (intros h hn hnt)
  (simp only [i10-task-keys-ok Bool.and_eq_true] at h)
  (have h1 (= (of-below-k n2 (RunKey.mk m n true)) true)) (simp only [of-below-k Nat.blt_eq]) (exact hn)
  (have h2 (= (trun-ok (List.cons TaskKey (TaskKey.mk n m false) tks) (RunKey.mk m n true)) true))
  (simp only [trun-ok tbl-all trun-one Nat.beq_refl Bool.not_true Bool.false_or Bool.true_and])
  (exact (tbl-all-mono TaskKey (not-id n) (trun-one (RunKey.mk m n true)) (not-id-trun n m) tks hnt))
  (have h2b (forall [kk :- RunKey] (=> (= (of-below-k n kk) true) (= (trun-ok tks kk) true)
                                     (= (trun-ok (List.cons TaskKey (TaskKey.mk n m false) tks) kk) true))))
  (intros kk a1 a2)
  (simp only [trun-ok] at a2)
  (simp only [trun-ok tbl-all (trun-new-task n m kk a1) a2 Bool.and_self])
  (have h3 (= (thas-ok (List.cons RunKey (RunKey.mk m n true) rks) (TaskKey.mk n m false)) true))
  (simp only [thas-ok tbl-any run-for Nat.beq_refl Bool.and_self Bool.true_or Bool.or_true])
  (have h4 := (tbl-all-mono TaskKey (thas-ok rks) (thas-ok (List.cons RunKey (RunKey.mk m n true) rks))
                (thas-cons rks (RunKey.mk m n true)) tks (And.right (And.right h))))
  (have nle (<= n n2)) (omega)
  (simp only [i10-task-keys-ok tbl-all Bool.and_eq_true h1 h2 h3 Bool.true_and])
  (exact (And.intro (of-below-mono n n2 rks nle (And.left h))
           (And.intro (tbl-all-mono2 RunKey (of-below-k n) (trun-ok tks) (trun-ok (List.cons TaskKey (TaskKey.mk n m false) tks)) h2b rks
                        (And.left h) (And.left (And.right h)))
                      h4))))

;; ---- facts from well-formed

(a/theorem ids-below-of [w :- World]
  (=> (= (well-formed w) true) (= (tbl-all (id-in-range (:next-id w)) (all-ids w)) true))
  (intro h)
  (have hi := (And.right (And.right (well-formed-parts w h))))
  (simp only [ids-ok ids-below Bool.and_eq_true] at hi)
  (exact (And.right (And.right hi))))

(a/theorem range-not-id [n :- Nat, ts :- (List TaskRow)]
  (=> (= (tbl-all (id-in-range n) (tbl-ids task-id ts)) true) (= (tbl-all (not-id n) (task-keys ts)) true))
  (induction ts)
  (case [nil] (intro h) (simp [task-keys tbl-all]))
  (case [cons h t ih]
    (intro ha)
    (simp only [tbl-ids tbl-all Bool.and_eq_true] at ha)
    (have h1 := (And.left ha))
    (simp only [id-in-range task-id Bool.and_eq_true Nat.blt_eq] at h1)
    (have hne (= (Nat.beq (:id h) n) false))
    (cases hb (Nat.beq (:id h) n))
    (rfl)
    (have e (= (:id h) n)) (exact (Nat.eq_of_beq_eq_true hb))
    (rw [e] at h1) (omega)
    (simp only [task-keys tbl-all not-id task-key hne Bool.not_false Bool.true_and])
    (exact (ih (And.right ha)))))

(a/theorem tasks-below [w :- World]
  (=> (= (well-formed w) true) (= (tbl-all (not-id (:next-id w)) (task-keys (:tasks w))) true))
  (intro h)
  (have hb := (ids-below-of w h))
  (simp only [all-ids tbl-all-nat-app Bool.and_eq_true] at hb)
  (exact (range-not-id (:next-id w) (:tasks w) (And.left (And.right (And.right hb))))))

(a/theorem all-nat-mem [p :- (=> Nat Bool), x :- Nat, xs :- (List Nat)]
  (=> (= (tbl-all p xs) true) (= (nat-mem x xs) true) (= (p x) true))
  (induction xs)
  (case [nil] (intros h1 h2) (simp [nat-mem] at h2))
  (case [cons h t ih]
    (intros h1 h2)
    (simp only [tbl-all Bool.and_eq_true] at h1)
    (cases hx (Nat.beq h x))
    (case [true] (have e (= h x)) (exact (Nat.eq_of_beq_eq_true hx)) (rw [← e]) (exact (And.left h1)))
    (case [false] (simp only [nat-mem hx] at h2) (exact (ih (And.right h1) h2)))))

(a/theorem comp-below [w :- World, x :- Nat]
  (=> (= (well-formed w) true) (= (comp-has w x) true) (< x (:next-id w)))
  (intros h hc)
  (have hb := (ids-below-of w h))
  (simp only [all-ids tbl-all-nat-app Bool.and_eq_true] at hb)
  (have hm (= (nat-mem x (tbl-ids comp-id (:comps w))) true)) (rw [nat-mem-ids]) (exact hc)
  (have r := (all-nat-mem (id-in-range (:next-id w)) x _ (And.left (And.right hb)) hm))
  (simp only [id-in-range Bool.and_eq_true Nat.blt_eq] at r)
  (exact (And.right r)))

;; ---- frames: edits that keep the run and task keys and the allocator

(a/structure I10TaskView [] (rks (List RunKey)) (tks (List TaskKey)) (n Nat))
(a/defn i10-task-view [w :- World] I10TaskView (I10TaskView.mk (run-keys (:runs w)) (task-keys (:tasks w)) (:next-id w)))

(a/theorem i10-task-rest-frame [w :- World, w2 :- World]
  (=> (= (i10-task-view w2) (i10-task-view w)) (= (i10-task-rest w2) (i10-task-rest w)))
  (intro e)
  (have e1 (= (run-keys (:runs w2)) (run-keys (:runs w)))) (exact (congrArg (fn [k :- I10TaskView] (:rks k)) e))
  (have e2 (= (task-keys (:tasks w2)) (task-keys (:tasks w)))) (exact (congrArg (fn [k :- I10TaskView] (:tks k)) e))
  (have e3 (= (:next-id w2) (:next-id w))) (exact (congrArg (fn [k :- I10TaskView] (:n k)) e))
  (simp only [i10-task-rest e1 e2 e3]))

(a/theorem i10-task-view-fold [f :- (=> World Nat World), hf :- (forall [w :- World, x :- Nat] (= (i10-task-view (f w x)) (i10-task-view w))), xs :- (List Nat)]
  (forall [w :- World] (= (i10-task-view (nat-fold f w xs)) (i10-task-view w)))
  (induction xs)
  (case [nil] (intro w) (simp only [nat-fold]))
  (case [cons h t ih] (intro w) (simp only [nat-fold]) (exact (Eq.trans (ih (f w h)) (hf w h)))))

(a/theorem i10-task-view-finalize-loop [fuel :- (List Nat)]
  (forall [w :- World, ds :- (List Nat)] (= (i10-task-view (:world (finalize-loop fuel w ds))) (i10-task-view w)))
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
(a/theorem run-key-run-wake [r :- RunRow] (= (run-key (run-wake r)) (run-key r)) (simp only [run-key run-wake-alive]))
(a/theorem i10-task-view-resume [w :- World, a :- ActRow] (= (i10-task-view (resume w a)) (i10-task-view w))
  (simp only [resume i10-task-view run-upd set-runs])
  (rw [(run-keys-upd (:run a) run-wake run-key-run-wake (:runs w))]))
(a/theorem i10-task-view-fill-slot [w :- World, a :- ActRow, y :- Nat, v :- RunResult] (= (i10-task-view (fill-slot w a y v)) (i10-task-view w))
  (cases hm (act-ready (act-fill y v a)))
  (simp only [fill-slot hm])
  (simp only [fill-slot hm]) (exact (i10-task-view-resume w a)))
(a/theorem i10-task-view-remove-edge [w :- World, y :- Nat] (= (i10-task-view (remove-edge w y)) (i10-task-view w))
  (cases hf (edge-find w y)) (case' [some e]) (case' [none])
  (simp only [remove-edge hf])
  (cases hm (:marked e))
  (all_goals (simp only [remove-edge hf hm])))
(a/theorem i10-task-view-fire-dep [w :- World, e :- EdgeRow] (= (i10-task-view (fire-dep w e)) (i10-task-view w))
  (cases ha (act-with-member (:id e) (:acts w))) (case' [some a]) (case' [none])
  (simp only [fire-dep ha invalidate])
  (cases hc (Bool.and (run-current-of w (:run a) (:creditor e)) (deb-avail w (:debtor e))))
  (simp only [fire-dep ha hc invalidate])
  (simp only [fire-dep ha hc deliver-dep])
  (have e1 (= (i10-task-view (dep-consumed w e)) (i10-task-view w)))
  (cases hf (deb-final w (:debtor e)))
  (simp only [dep-consumed hf])
  (simp only [dep-consumed hf]) (exact (i10-task-view-remove-edge w (:id e)))
  (exact (Eq.trans (i10-task-view-fill-slot _ a _ _) e1)))
(a/theorem i10-task-view-fire-wait [res :- RunResult, w :- World, e :- EdgeRow] (= (i10-task-view (fire-wait res w e)) (i10-task-view w))
  (cases hc (Nat.beq (:creditor e) 0))
  (case [true] (simp only [fire-wait hc]) (exact (i10-task-view-remove-edge w (:id e))))
  (case [false]
    (simp only [fire-wait hc])
    (cases ha (act-find w (:creditor e))) (case' [some a]) (case' [none])
    (simp only [fire-wait-act ha])
    (cases hr (run-current w (:run a)))
    (simp only [fire-wait-act ha hr])
    (simp only [fire-wait-act ha hr]) (exact (i10-task-view-fill-slot _ a _ _))))
(a/theorem i10-task-view-fire-edge [res :- RunResult, w :- World, y :- Nat] (= (i10-task-view (fire-edge res w y)) (i10-task-view w))
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
  (simp only [fire-edge hf hp hk1 hk2]) (exact (i10-task-view-fire-wait res w e))
  (simp only [fire-edge hf hp hk1]) (exact (i10-task-view-fire-dep w e)))
(a/theorem i10-task-view-wake-closed [w :- World, x :- Nat] (= (i10-task-view (wake-closed w x)) (i10-task-view w))
  (simp only [wake-closed])
  (exact (i10-task-view-fold (fire-edge (deb-result w x)) (i10-task-view-fire-edge (deb-result w x)) _ w)))

(a/theorem i10-task-view-t10-finalize-debtor [w :- World, d :- Nat] (= (i10-task-view (t10-finalize-debtor w d)) (i10-task-view w))
  (simp only [t10-finalize-debtor]) (exact (i10-task-view-finalize-loop _ w _)))
(a/theorem i10-task-view-deliver-res [w :- World, x :- Nat, v :- Nat, res :- RunResult] (= (i10-task-view (deliver-res w x v res)) (i10-task-view w))
  (simp only [deliver-res])
  (exact (Eq.trans (i10-task-view-t10-finalize-debtor _ x)
           (Eq.trans (i10-task-view-fold (fire-edge res) (i10-task-view-fire-edge res) _ _)
             (i10-task-view-fold (fire-edge res) (i10-task-view-fire-edge res) _ (source-upd w x (source-write v)))))))
(a/theorem i10-task-view-realize-link [w :- World, x :- Nat, v :- Nat, fl :- Bool, n :- Nat] (= (i10-task-view (realize-link w x v fl n)) (i10-task-view w))
  (simp only [realize-link]) (exact (i10-task-view-deliver-res _ x v _)))
(a/theorem i10-task-view-end-link [w :- World, x :- Nat, fl :- Bool, v :- Nat] (= (i10-task-view (end-link w x fl v)) (i10-task-view w))
  (cases hp (link-pending w x))
  (simp only [end-link hp])
  (simp only [end-link hp]) (exact (i10-task-view-realize-link w x _ fl 0)))
(a/theorem i10-task-view-end-stream [w :- World, x :- Nat] (= (i10-task-view (end-stream w x)) (i10-task-view w))
  (cases hf (source-find w x)) (case' [some s]) (case' [none])
  (simp only [end-stream hf])
  (cases hk (Nat.beq (:kind s) sk-stream))
  (simp only [end-stream hf hk])
  (simp only [end-stream hf hk]) (exact (i10-task-view-end-link w _ false 0)))
(a/theorem i10-task-view-close-source-ended [w :- World, x :- Nat] (= (i10-task-view (close-source-ended w x)) (i10-task-view w))
  (simp only [close-source-ended t10-finalize-debtor])
  (exact (Eq.trans (i10-task-view-finalize-loop _ (wake-closed (source-upd w x source-close-row) x) _)
                   (i10-task-view-wake-closed (source-upd w x source-close-row) x))))
(a/theorem i10-task-view-close-source [w :- World, x :- Nat] (= (i10-task-view (close-source w x)) (i10-task-view w))
  (simp only [close-source]) (exact (Eq.trans (i10-task-view-close-source-ended _ x) (i10-task-view-end-stream w x))))
(a/theorem i10-task-view-clear-rtasks [w :- World, k :- Nat] (= (i10-task-view (clear-rtasks w k)) (i10-task-view w))
  (simp only [clear-rtasks]) (exact (i10-task-view-fold clear-rtask (fn [w2 :- World, y :- Nat] (Eq.refl (i10-task-view w2))) _ w)))
(a/theorem i10-task-view-close-scope-id [w :- World, x :- Nat] (= (i10-task-view (close-scope-id w x)) (i10-task-view w)) (rfl))
(a/theorem i10-task-view-close-local [w :- World, sub :- (List Nat)] (= (i10-task-view (close-local w sub)) (i10-task-view w))
  (simp only [close-local])
  (exact (Eq.trans (i10-task-view-fold close-source i10-task-view-close-source _ _) (i10-task-view-fold close-scope-id i10-task-view-close-scope-id sub w))))
(a/theorem i10-task-view-scope-del [w :- World, x :- Nat] (= (i10-task-view (scope-del w x)) (i10-task-view w)) (rfl))
(a/theorem i10-task-view-remove-if-empty [w :- World, sub :- (List Nat)] (= (i10-task-view (remove-if-empty w sub)) (i10-task-view w))
  (cases he (subtree-empty w sub))
  (case [false] (simp only [remove-if-empty he]))
  (case [true] (simp only [remove-if-empty he]) (exact (i10-task-view-fold scope-del i10-task-view-scope-del sub w))))
(a/theorem i10-task-view-drop-act [w :- World, x :- Nat] (= (i10-task-view (drop-act w x)) (i10-task-view w)) (rfl))
(a/theorem i10-task-view-res-cancel [w :- World, x :- Nat] (= (i10-task-view (res-cancel w x)) (i10-task-view w)) (rfl))

;; ---- key lists under row functions

(a/defn run-key-up [k :- RunKey] RunKey (RunKey.mk (:id k) (:of k) true))
(a/defn run-key-down [k :- RunKey] RunKey (RunKey.mk (:id k) (:of k) false))
(a/defn task-key-done [t :- TaskKey] TaskKey (TaskKey.mk (:id t) (:run t) true))

(a/theorem run-keys-upd-g [x :- Nat, f :- (=> RunRow RunRow), g :- (=> RunKey RunKey),
                        hc :- (forall [r :- RunRow] (= (run-key (f r)) (g (run-key r)))), rs :- (List RunRow)]
  (= (run-keys (tbl-upd run-id x f rs)) (tbl-upd run-key-id x g (run-keys rs)))
  (induction rs)
  (case [nil] (simp only [tbl-upd run-keys]))
  (case [cons h t ih]
    (cases hx (Nat.beq (run-id h) x))
    (case [false]
      (have hx2 (= (Nat.beq (run-key-id (run-key h)) x) false)) (exact hx)
      (simp only [tbl-upd hx run-keys hx2 ih]))
    (case [true]
      (have hx2 (= (Nat.beq (run-key-id (run-key h)) x) true)) (exact hx)
      (simp only [tbl-upd hx run-keys hx2 ih (hc h)]))))

(a/theorem task-keys-upd-g [x :- Nat, f :- (=> TaskRow TaskRow), g :- (=> TaskKey TaskKey),
                        hc :- (forall [t :- TaskRow] (= (task-key (f t)) (g (task-key t)))), ts :- (List TaskRow)]
  (= (task-keys (tbl-upd task-id x f ts)) (tbl-upd task-key-id x g (task-keys ts)))
  (induction ts)
  (case [nil] (simp only [tbl-upd task-keys]))
  (case [cons h t ih]
    (cases hx (Nat.beq (task-id h) x))
    (case [false]
      (have hx2 (= (Nat.beq (task-key-id (task-key h)) x) false)) (exact hx)
      (simp only [tbl-upd hx task-keys hx2 ih]))
    (case [true]
      (have hx2 (= (Nat.beq (task-key-id (task-key h)) x) true)) (exact hx)
      (simp only [tbl-upd hx task-keys hx2 ih (hc h)]))))

(a/theorem run-keys-del [x :- Nat, rs :- (List RunRow)] (= (run-keys (tbl-del run-id x rs)) (tbl-del run-key-id x (run-keys rs)))
  (induction rs)
  (case [nil] (simp only [tbl-del run-keys]))
  (case [cons h t ih]
    (cases hx (Nat.beq (run-id h) x))
    (case [false]
      (have hx2 (= (Nat.beq (run-key-id (run-key h)) x) false)) (exact hx)
      (simp only [tbl-del hx run-keys hx2 ih]))
    (case [true]
      (have hx2 (= (Nat.beq (run-key-id (run-key h)) x) true)) (exact hx)
      (simp only [tbl-del hx run-keys hx2 ih]))))

(a/theorem task-key-cancel-result [t :- TaskRow] (= (task-key (task-cancel-result t)) (task-key-done (task-key t)))
  (cases hn (Nat.beq (:tag (:result t)) res-none))
  (case [true] (simp only [task-cancel-result hn]))
  (case [false] (simp only [task-cancel-result hn task-key task-key-done task-done Bool.not_false])))

(a/theorem task-key-result-row [res :- RunResult, t :- TaskRow]
  (=> (= (Nat.beq (:tag res) res-none) false) (= (task-key (task-result-row res t)) (task-key-done (task-key t))))
  (intro hn) (simp only [task-key task-result-row task-key-done task-done hn Bool.not_false]))

;; ---- run rows made alive (resume, park)

(a/theorem i10-task-run-upd-up [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                          hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                          hk :- (forall [r :- RunRow] (= (run-key (f r)) (RunKey.mk (:id r) (:of r) true)))]
  (=> (= (i10-task w) true) (= (i10-task (run-upd w x f)) true))
  (intro h)
  (have e := (run-keys-upd-g x f run-key-up hk (:runs w)))
  (have hr (= (i10-task-rest (run-upd w x f)) true))
  (simp only [i10-task-rest run-upd set-runs e])
  (exact (i10-task-keys-ok-up _ _ _ x run-key-up (fn [k :- RunKey] (Eq.refl (:id k))) (fn [k :- RunKey] (Eq.refl (:of k))) (fn [k :- RunKey] (Eq.refl true))
           (i10-task-rest-of w h)))
  (exact (i10-task-intro _ (well-formed-run-upd w x f hf (i10-task-well-formed w h)) hr)))

;; Z#50: resume wakes only a parked run (alive before and after), so it keeps the run keys
(a/theorem run-wake-run-key [r :- RunRow] (= (run-key (run-wake r)) (run-key r))
  (simp only [run-key run-wake-alive]))
;; ---- the exempt world predicate

(a/defn i10-task-exempt [k :- Nat, w :- World] Bool (i10-task-exempt-keys-ok k (run-keys (:runs w)) (task-keys (:tasks w)) (:next-id w)))

(a/theorem i10-task-exempt-frame [k :- Nat, w :- World, w2 :- World] (=> (= (i10-task-view w2) (i10-task-view w)) (= (i10-task-exempt k w2) (i10-task-exempt k w)))
  (intro e)
  (have e1 (= (run-keys (:runs w2)) (run-keys (:runs w)))) (exact (congrArg (fn [q :- I10TaskView] (:rks q)) e))
  (have e2 (= (task-keys (:tasks w2)) (task-keys (:tasks w)))) (exact (congrArg (fn [q :- I10TaskView] (:tks q)) e))
  (have e3 (= (:next-id w2) (:next-id w))) (exact (congrArg (fn [q :- I10TaskView] (:n q)) e))
  (simp only [i10-task-exempt e1 e2 e3]))

;; a run row made done: only its own task (r.of) may lack a run
(a/theorem i10-task-exempt-kill [w :- World, r :- RunRow, f :- (=> RunRow RunRow),
                     hk :- (forall [q :- RunRow] (= (run-key (f q)) (run-key-down (run-key q))))]
  (=> (= (well-formed w) true) (List.Mem r (:runs w)) (= (i10-task w) true) (= (i10-task-exempt (:of r) (run-upd w (:id r) f)) true))
  (intros hs hm h)
  (have e := (run-keys-upd-g (:id r) f run-key-down hk (:runs w)))
  (simp only [i10-task-exempt run-upd set-runs e])
  (exact (i10-task-keys-ok-kill _ _ _ (:id r) (:of r) run-key-down (fn [k :- RunKey] (Eq.refl (:id k))) (fn [k :- RunKey] (Eq.refl (:of k)))
           (i10-task-rest-of w h) (of-at-runs w r hs hm))))

(a/theorem i10-task-of-i10-task-exempt-comp [w :- World, k :- Nat]
  (=> (= (well-formed w) true) (= (i10-task-exempt k w) true) (= (comp-has w k) true) (= (i10-task w) true))
  (intros hs hx hc)
  (exact (i10-task-intro w hs (i10-task-exempt-keys-ok-none _ _ _ k hx (not-id-tasks k (:tasks w) (comp-not-task w k hs hc))))))

(a/theorem i10-task-of-i10-task-exempt-find [w :- World, k :- Nat]
  (=> (= (well-formed w) true) (= (i10-task-exempt k w) true) (= (task-find w k) (Option.none TaskRow)) (= (i10-task w) true))
  (intros hs hx hf)
  (exact (i10-task-intro w hs (i10-task-exempt-keys-ok-none _ _ _ k hx (find-none-tasks k (:tasks w) hf)))))

(a/theorem i10-task-task-done-x [w :- World, k :- Nat, f :- (=> TaskRow TaskRow),
                           hf :- (forall [t :- TaskRow] (= (task-id (f t)) (task-id t))),
                           hk :- (forall [t :- TaskRow] (= (task-key (f t)) (task-key-done (task-key t))))]
  (=> (= (well-formed w) true) (= (i10-task-exempt k w) true) (= (i10-task (task-upd w k f)) true))
  (intros hs hx)
  (have e := (task-keys-upd-g k f task-key-done hk (:tasks w)))
  (have hr (= (i10-task-rest (task-upd w k f)) true))
  (simp only [i10-task-rest task-upd set-tasks e])
  (exact (i10-task-exempt-keys-ok-done _ _ _ k task-key-done (fn [t :- TaskKey] (Eq.refl (:id t))) (fn [t :- TaskKey] (Eq.refl (:run t)))
           (fn [t :- TaskKey] (Eq.refl true)) hx))
  (exact (i10-task-intro _ (well-formed-task-upd w k f hf hs) hr)))

;; ---- i10-task's exempt form, uniform names (spindel.v2.pres.exempt): `i10-task-exempt k` waives clause (c) for task k
(exempt/defexempt 'i10-task
  :form "i10-task-exempt k w (i10-task-rest with (c) waived for task k)" :ids "one task id" :commit "i10-task (no task waived)"
  :break '{run-done i10-task-exempt-kill}                  ; a run of task k is made done: k may lack a run
  :repair '{task-done i10-task-task-done-x           ; task k gets its result
            comp i10-task-of-i10-task-exempt-comp                ; k is a computation, not a task
            no-task i10-task-of-i10-task-exempt-find}            ; there is no task k
  :transport '{view i10-task-exempt-frame})                     ; edits that keep the key lists keep i10-task-exempt

;; ---- T14's local part (cancel): the run is done, its task gets err ::cancelled

(a/defn cancel-mid [w :- World, r :- RunRow] World
  (cleanup-set (cancel-res (cancel-acts (run-upd w (:id r) run-cancel-row) (:id r)) r) (:id r) (cleanup-rows-of w r)))

(a/theorem cancel-mid-well-formed [w :- World, r :- RunRow]
  (=> (= (well-formed w) true) (= (well-formed (cancel-mid w r)) true))
  (intro h)
  (exact (well-formed-cleanup-set _ (:id r) (cleanup-rows-of w r)
           (well-formed-cancel-res _ r (well-formed-cancel-acts _ (:id r) (well-formed-run-upd w (:id r) run-cancel-row run-cancel-row-id h))))))

(a/theorem cancel-mid-frame [w :- World, r :- RunRow] (= (i10-task-view (cancel-mid w r)) (i10-task-view (run-upd w (:id r) run-cancel-row)))
  (simp only [cancel-mid cancel-res cancel-acts])
  (exact (Eq.trans (Eq.trans (Eq.refl _) (i10-task-view-fold res-cancel i10-task-view-res-cancel (:resources r) _))
                   (i10-task-view-fold drop-act i10-task-view-drop-act _ _))))

;; ---- T13 (retire): the run row goes, its task's run is cleared (the task has its result)

(a/theorem i10-task-view-run-del-congr [w :- World, w2 :- World, x :- Nat]
  (=> (= (i10-task-view w2) (i10-task-view w)) (= (i10-task-view (run-del w2 x)) (i10-task-view (run-del w x))))
  (intro e)
  (have e1 (= (run-keys (:runs w2)) (run-keys (:runs w)))) (exact (congrArg (fn [q :- I10TaskView] (:rks q)) e))
  (have e2 (= (task-keys (:tasks w2)) (task-keys (:tasks w)))) (exact (congrArg (fn [q :- I10TaskView] (:tks q)) e))
  (have e3 (= (:next-id w2) (:next-id w))) (exact (congrArg (fn [q :- I10TaskView] (:n q)) e))
  (simp only [i10-task-view run-del set-runs run-keys-del e1 e2 e3]))

(a/theorem i10-task-view-t13-retire-with-subtree [w :- World, r :- RunRow, sub :- (List Nat)]
  (= (i10-task-view (t13-retire-with-subtree w r sub)) (i10-task-view (run-del (clear-comp-run w r) (:id r))))
  (simp only [t13-retire-with-subtree])
  (have e1 := (i10-task-view-remove-if-empty (cleanup-del (run-del (close-local (clear-comp-run w r) sub) (:id r)) (:id r)) sub))
  (have e2 (= (i10-task-view (cleanup-del (run-del (close-local (clear-comp-run w r) sub) (:id r)) (:id r)))
              (i10-task-view (run-del (close-local (clear-comp-run w r) sub) (:id r)))))
  (rfl)
  (have e3 := (i10-task-view-run-del-congr (clear-comp-run w r) (close-local (clear-comp-run w r) sub) (:id r)
                (i10-task-view-close-local (clear-comp-run w r) sub)))
  (exact (Eq.trans e1 (Eq.trans e2 e3))))

(a/defn run-of-is [x :- Nat, t :- TaskRow] Bool (Nat.beq (:run t) x))

(a/theorem retire-rest [w :- World, r :- RunRow]
  (=> (= (well-formed w) true) (List.Mem r (:runs w)) (= (run-alive r) false) (= (i10-task-rest w) true)
      (= (i10-task-rest (run-del (clear-comp-run w r) (:id r))) true))
  (intros hs hm ha h)
  (have hd := (dead-at-runs w r hs hm ha))
  (have plain (= (i10-task-rest (run-del w (:id r))) true))
  (simp only [i10-task-rest run-del set-runs run-keys-del])
  (exact (i10-task-keys-ok-del _ _ _ (:id r) h (dead-off _ _ _ (:id r) h hd)))
  (cases hc (comp-find w (:of r)))
  (case [some c]
    (cases hr (Nat.beq (:run c) (:id r)))
    (case [false] (simp only [clear-comp-run hc hr]) (exact plain))
    (case [true] (simp only [clear-comp-run hc hr]) (exact plain)))
  (case [none]
    (simp only [clear-comp-run hc])
    (cases hk (task-find w (:of r)))
    (case [none] (simp only [clear-task-run hk]) (exact plain))
    (case [some t]
      (cases hr (Nat.beq (:run t) (:id r)))
      (case [false] (simp only [clear-task-run hk hr]) (exact plain))
      (case [true]
        (simp only [clear-task-run hk hr])
        (have ek (= (task-id t) (:of r))) (exact (tbl-find-id TaskRow task-id (:of r) t (:tasks w) hk))
        (have u := (uniq-all TaskRow task-id (run-of-is (:id r)) t (:tasks w) (tasks-nodup w hs)
                     (tbl-find-mem TaskRow task-id (:of r) t (:tasks w) hk) hr))
        (rw [ek] at u)
        (have hri (= (tbl-all (run-is-if (:of r) (:id r)) (task-keys (:tasks w))) true))
        (rw [all-task-keys])
        (exact (Eq.trans (tbl-all-congr TaskRow (on-tkey (run-is-if (:of r) (:id r))) (same-id-then task-id (:of r) (run-of-is (:id r)))
                           (fn [b :- TaskRow] (Eq.refl (on-tkey (run-is-if (:of r) (:id r)) b))) (:tasks w)) u))
        (have e := (task-keys-upd-g (:of r) task-clear-run clr (fn [q :- TaskRow] (Eq.refl (clr (task-key q)))) (:tasks w)))
        (simp only [i10-task-rest run-del set-runs task-upd set-tasks run-keys-del e])
        (exact (i10-task-keys-ok-clear-del _ _ _ (:id r) (:of r) h hd hri))))))

(a/theorem i10-task-retire-run-hand [w :- World, r :- RunRow]
  (=> (List.Mem r (:runs w)) (= (run-alive r) false) (= (i10-task w) true) (= (i10-task (retire-run w r)) true))
  (intros hm ha h)
  (have hs := (i10-task-well-formed w h))
  (have hr (= (i10-task-rest (retire-run w r)) true))
  (simp only [retire-run])
  (rw [(i10-task-rest-frame _ _ (i10-task-view-t13-retire-with-subtree w r (scope-subtree w (:scope r))))])
  (exact (retire-rest w r hs hm ha (i10-task-rest-of w h)))
  (exact (i10-task-intro _ (well-formed-retire-run w r hs) hr)))

(a/theorem retirable-dead [r :- RunRow] (=> (= (retirable r) true) (= (run-alive r) false))
  (intro h)
  (simp only [retirable Bool.and_eq_true] at h)
  (have e (= (:act r) act-done)) (exact (Nat.eq_of_beq_eq_true (And.left h)))
  (simp only [run-alive e Nat.beq_refl Bool.not_true]))

;; ---- T12 (complete): the run is done, its task gets the result (ok/err, never none)

(a/theorem tag-ok-none [tag :- Nat] (=> (= (res-tag-ok tag) true) (= (Nat.beq tag res-none) false))
  (intro h)
  (cases hb (Nat.beq tag res-none))
  (case [false] (rfl))
  (case [true]
    (have e (= tag res-none)) (exact (Nat.eq_of_beq_eq_true hb))
    (simp [res-tag-ok e res-none res-ok res-err] at h)))
;; the same, for the result T12 builds (the tree's pass at T12's call of complete-raw)
(a/theorem tag-ok-res [tag :- Nat, v :- Nat] (=> (= (res-tag-ok tag) true) (= (Nat.beq (:tag (RunResult.mk tag v)) res-none) false))
  (intro h) (exact (tag-ok-none tag h)))

(a/theorem refused-tag-ok [w :- World, st :- Nat, tag :- Nat]
  (=> (= (complete-refused w st tag) false) (= (res-tag-ok tag) true))
  (intro h)
  (simp only [complete-refused Bool.or_eq_false_iff] at h)
  (have h2 := (And.right h))
  (cases hb (res-tag-ok tag))
  (case [true] (rfl))
  (case [false] (simp [hb] at h2)))

;; ---- T4/T5/T11: the new run (and T4's task)

(a/theorem i10-task-spawn-rows-hand [w :- World, owner :- Nat, inputs :- (List Nat), loc :- Bool]
  (=> (= (i10-task w) true) (= (i10-task (spawn-rows w owner inputs loc)) true))
  (intro h)
  (have hs := (i10-task-well-formed w h))
  (have lt (< (:next-id w) (+ (:next-id w) 3))) (omega)
  (have hr (= (i10-task-rest (spawn-rows w owner inputs loc)) true))
  (exact (i10-task-keys-ok-ins-task (run-keys (:runs w)) (task-keys (:tasks w)) (:next-id w) (+ (:next-id w) 3) (+ (:next-id w) 1)
           (i10-task-rest-of w h) lt (tasks-below w hs)))
  (exact (i10-task-intro _ (well-formed-spawn-rows w owner inputs loc hs) hr)))

;; a computation's new run: of = an existing computation (no task id, below the allocator)
(a/theorem i10-task-comp-run-hand [w :- World, cid :- Nat, ep :- Nat, ei :- Nat, f :- (=> CompRow CompRow),
                          hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                          hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c)))]
  (=> (= (comp-has w cid) true) (= (i10-task w) true) (= (i10-task (comp-upd (add-run-scope w cid ep 0 ei) cid f)) true))
  (intros hc h)
  (have hs := (i10-task-well-formed w h))
  (have lt := (comp-below w cid hs hc))
  (have le (<= (:next-id w) (+ (:next-id w) 2))) (omega)
  (have lt2 (< cid (+ (:next-id w) 2))) (omega)
  (have hr (= (i10-task-rest (comp-upd (add-run-scope w cid ep 0 ei) cid f)) true))
  (exact (i10-task-keys-ok-ins-run (run-keys (:runs w)) (task-keys (:tasks w)) (:next-id w) (+ (:next-id w) 2) (:next-id w) cid
           (i10-task-rest-of w h) le lt2 (not-id-tasks cid (:tasks w) (comp-not-task w cid hs hc))))
  (exact (i10-task-intro _ (well-formed-comp-upd _ cid f hid hp (well-formed-add-run-scope w cid ep 0 ei hs)) hr)))

(a/theorem i10-task-start-raw [w :- World, c :- CompRow]
  (=> (= (comp-has w (:id c)) true) (= (i10-task w) true) (= (i10-task (start-raw w c)) true))
  (intros hc h)
  (simp only [start-raw])
  (exact (i10-task-comp-run-hand w (:id c) (start-epoch c) 0 (comp-start-row (:next-id w)) (comp-start-row-id (:next-id w))
           (comp-start-row-pending (:next-id w)) hc h)))

(a/theorem i10-task-new-run-of [w :- World, c :- CompRow, ei :- Nat]
  (=> (= (comp-has w (:id c)) true) (= (i10-task w) true) (= (i10-task (new-run-of w c ei)) true))
  (intros hc h)
  (simp only [new-run-of])
  (exact (i10-task-comp-run-hand w (:id c) (:epoch c) ei (comp-set-run (:next-id w)) (comp-set-run-id (:next-id w))
           (comp-set-run-pending (:next-id w)) hc h)))

(a/theorem find-comp-has [w :- World, cid :- Nat, c :- CompRow]
  (=> (= (comp-find w cid) (Option.some CompRow c)) (= (comp-has w (:id c)) true))
  (intro hf)
  (have e (= (comp-id c) cid)) (exact (tbl-find-id CompRow comp-id cid c (:comps w) hf))
  (have e2 (= (:id c) cid)) (exact e)
  (rw [e2]) (exact (tbl-find-has CompRow comp-id cid c (:comps w) hf)))

;; ---- T11 keeps C: bundle `comp-exists cx` = well-formed and computation cx exists, through the
;; predecessor's cancel and the cut (no computation is removed there)

(a/defn comp-exists-rest [cx :- Nat, w :- World] Bool (comp-has w cx))
(a/defn comp-exists [cx :- Nat, w :- World] Bool (Bool.and (well-formed w) (comp-exists-rest cx w)))
(a/theorem comp-exists-well-formed [cx :- Nat, w :- World] (=> (= (comp-exists cx w) true) (= (well-formed w) true))
  (intro h) (simp only [comp-exists Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem comp-exists-rest-of [cx :- Nat, w :- World] (=> (= (comp-exists cx w) true) (= (comp-exists-rest cx w) true))
  (intro h) (simp only [comp-exists Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem comp-exists-intro [cx :- Nat, w :- World] (=> (= (well-formed w) true) (= (comp-exists-rest cx w) true) (= (comp-exists cx w) true))
  (intros h1 h2) (simp only [comp-exists h1 h2 Bool.and_self]))
(a/theorem comp-exists-parts [cx :- Nat, w :- World]
  (=> (= (comp-exists cx w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (comp-exists-well-formed cx w h))))

(def CH (mk-bundle 'comp-exists '[cx :- Nat] "comp-exists-" {}))
(swap! (:renames CH) assoc 'well-formed-parts 'comp-exists-parts)

(a/theorem comp-exists-eq-comp-upd-eq [w :- World, y :- Nat, f :- (=> CompRow CompRow),
                           hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))), cx :- Nat]
  (= (comp-exists-rest cx (comp-upd w y f)) (comp-exists-rest cx w))
  (simp only [comp-exists-rest comp-has comp-upd set-comps])
  (exact (tbl-has-upd CompRow comp-id y cx f hid (:comps w))))
(a/theorem comp-exists-eq-drop-cred [w :- World, a :- Nat, cx :- Nat] (= (comp-exists-rest cx (drop-cred-edges w a)) (comp-exists-rest cx w))
  (simp only [drop-cred-edges])
  (exact (comp-exists-eq-comp-upd-eq _ a (comp-set-pending 0) (fn [c :- CompRow] (Eq.refl (comp-id c))) cx)))
(a/theorem lit-resync-has [es :- (List EdgeRow), cs :- (List CompRow), cx :- Nat]
  (= (tbl-has comp-id cx (comps-resync es cs)) (tbl-has comp-id cx cs))
  (induction cs)
  (case [nil] (simp only [comps-resync]))
  (case [cons h t ih]
    (have e (= (comp-id (comp-resync es h)) (comp-id h))) (rfl)
    (simp only [comps-resync tbl-has e ih])))
(a/theorem comp-exists-eq-drop-edges [w :- World, p :- (=> EdgeRow Bool), cx :- Nat] (= (comp-exists-rest cx (drop-edges w p)) (comp-exists-rest cx w))
  (simp only [comp-exists-rest comp-has drop-edges set-comps set-edges lit-resync-has]))
(a/theorem comp-exists-eq-mark-edge [w :- World, x :- Nat, cx :- Nat] (= (comp-exists-rest cx (mark-edge w x)) (comp-exists-rest cx w))
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]))
  (case [some e] (cases hm (:marked e))
    (case [true] (simp only [mark-edge hf hm]))
    (case [false] (simp only [mark-edge hf hm]) (exact (comp-exists-eq-comp-upd-eq _ (:creditor e) comp-inc-pending (fn [c :- CompRow] (Eq.refl (comp-id c))) cx)))))
(a/theorem comp-exists-eq-unmark-edge [w :- World, x :- Nat, cx :- Nat] (= (comp-exists-rest cx (unmark-edge w x)) (comp-exists-rest cx w))
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]))
  (case [some e] (cases hm (:marked e))
    (case [false] (simp only [unmark-edge hf hm]))
    (case [true] (simp only [unmark-edge hf hm]) (exact (comp-exists-eq-comp-upd-eq _ (:creditor e) comp-dec-pending (fn [c :- CompRow] (Eq.refl (comp-id c))) cx)))))
(a/theorem comp-exists-eq-remove-edge [w :- World, x :- Nat, cx :- Nat] (= (comp-exists-rest cx (remove-edge w x)) (comp-exists-rest cx w))
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]))
  (case [some e] (cases hm (:marked e))
    (case [false] (simp only [remove-edge hf hm]))
    (case [true] (simp only [remove-edge hf hm]) (exact (comp-exists-eq-comp-upd-eq _ (:creditor e) comp-dec-pending (fn [c :- CompRow] (Eq.refl (comp-id c))) cx)))))
(a/theorem comp-exists-comp-ins [w :- World, r :- CompRow, cx :- Nat]
  (=> (= (comp-exists-rest cx w) true) (= (comp-exists-rest cx (bump (comp-ins w r))) true))
  (intro h)
  (simp only [comp-exists-rest comp-has] at h)
  (cases hx (Nat.beq (comp-id r) cx))
  (all_goals (simp only [comp-exists-rest comp-has bump comp-ins set-next-id set-comps tbl-ins tbl-has hx h])))

(doseq [o '[well-formed-scope-upd well-formed-pub-upd well-formed-source-upd well-formed-resource-upd well-formed-cleanup-upd well-formed-cleanup-del
            well-formed-set-pins well-formed-resource-del well-formed-scope-del well-formed-cleanup-ins well-formed-act-upd well-formed-edge-upd well-formed-run-upd well-formed-task-upd
            well-formed-run-del well-formed-source-ins-fresh well-formed-fork-ins-fresh well-formed-resource-ins-fresh well-formed-scope-ins-fresh well-formed-act-ins-fresh
            well-formed-run-ins-fresh well-formed-task-ins-fresh well-formed-bump well-formed-insert-edge-fresh well-formed-fork-del]]
  (prim! CH o nil))
(prim! CH 'well-formed-comp-upd '(Eq.trans (comp-exists-eq-comp-upd-eq w x f hid cx) R))
(prim! CH 'well-formed-drop-cred-edges '(Eq.trans (comp-exists-eq-drop-cred w a cx) R))
(prim! CH 'well-formed-drop-act '(Eq.trans (comp-exists-eq-drop-cred w a cx) R))
(prim! CH 'well-formed-drop-edges '(Eq.trans (comp-exists-eq-drop-edges w p cx) R))
(prim! CH 'well-formed-mark-edge '(Eq.trans (comp-exists-eq-mark-edge w x cx) R))
(prim! CH 'well-formed-unmark-edge '(Eq.trans (comp-exists-eq-unmark-edge w x cx) R))
(prim! CH 'well-formed-remove-edge '(Eq.trans (comp-exists-eq-remove-edge w x cx) R))
(prim! CH 'well-formed-comp-ins-fresh '(comp-exists-comp-ins w r cx R))

(tree/restate! CH '[well-formed-cancel-pred well-formed-cut-suffix well-formed-consume-entry])   ; comp-exists on the generic tree: no own proof
;; ---- Rule R: the filter keeps every run that is not done (normalized: they are live)

(a/defn alive-kept [K :- (=> Nat Bool), k :- RunKey] Bool (Bool.or (Bool.not (:alive k)) (K (:id k))))

(a/theorem run-for-kept [K :- (=> Nat Bool), t :- TaskKey, k :- RunKey]
  (=> (= (both (run-for t) (alive-kept K) k) true) (= (K (run-key-id k)) true))
  (intro h)
  (simp only [both run-for Bool.and_eq_true] at h)
  (have h2 := (And.right h))
  (simp only [alive-kept (And.right (And.right (And.left h))) Bool.not_true Bool.false_or] at h2)
  (exact h2))

(a/theorem i10-task-keys-ok-keep [rks :- (List RunKey), tks :- (List TaskKey), n :- Nat, K :- (=> Nat Bool)]
  (=> (= (i10-task-keys-ok rks tks n) true) (= (tbl-all (alive-kept K) rks) true)
      (= (i10-task-keys-ok (tbl-keep K run-key-id rks) (tbl-keep K task-key-id tks) n) true))
  (intros h hk)
  (simp only [i10-task-keys-ok Bool.and_eq_true] at h)
  (have h2 (forall [kk :- RunKey] (=> (= (trun-ok tks kk) true) (= (trun-ok (tbl-keep K task-key-id tks) kk) true))))
  (intros kk a1) (simp only [trun-ok] at a1) (simp only [trun-ok])
  (exact (tbl-all-keep-same TaskKey K task-key-id (trun-one kk) tks a1))
  (have h3 (forall [t :- TaskKey] (=> (= (thas-ok rks t) true) (= (thas-ok (tbl-keep K run-key-id rks) t) true))))
  (intros t a1)
  (cases hd (:done t))
  (case [true] (simp only [thas-ok hd Bool.true_or]))
  (case [false]
    (simp only [thas-ok hd Bool.false_or] at a1)
    (simp only [thas-ok hd Bool.false_or])
    (exact (tbl-any-mono RunKey (both (run-for t) (alive-kept K)) (run-for t) (both-left RunKey (run-for t) (alive-kept K)) _
             (any-keep-on RunKey K run-key-id (both (run-for t) (alive-kept K)) (run-for-kept K t) rks
               (any-and-all RunKey (run-for t) (alive-kept K) rks a1 hk)))))
  (simp only [i10-task-keys-ok Bool.and_eq_true])
  (exact (And.intro (tbl-all-keep-same RunKey K run-key-id (of-below-k n) rks (And.left h))
           (And.intro (tbl-all-keep-same RunKey K run-key-id (trun-ok (tbl-keep K task-key-id tks))
                        rks (tbl-all-mono RunKey (trun-ok tks) (trun-ok (tbl-keep K task-key-id tks)) h2 rks (And.left (And.right h))))
                      (tbl-all-keep-same TaskKey K task-key-id (thas-ok (tbl-keep K run-key-id rks))
                        tks (tbl-all-mono TaskKey (thas-ok rks) (thas-ok (tbl-keep K run-key-id rks)) h3 tks (And.right (And.right h))))))))

(a/theorem run-keys-keep [K :- (=> Nat Bool), rs :- (List RunRow)] (= (run-keys (tbl-keep K run-id rs)) (tbl-keep K run-key-id (run-keys rs)))
  (induction rs)
  (case [nil] (simp only [tbl-keep run-keys]))
  (case [cons h t ih]
    (have e (= (K (run-key-id (run-key h))) (K (run-id h)))) (rfl)
    (cases hk (K (run-id h)))
    (all_goals (simp only [tbl-keep run-keys e hk ih]))))
(a/theorem task-keys-keep [K :- (=> Nat Bool), ts :- (List TaskRow)] (= (task-keys (tbl-keep K task-id ts)) (tbl-keep K task-key-id (task-keys ts)))
  (induction ts)
  (case [nil] (simp only [tbl-keep task-keys]))
  (case [cons h t ih]
    (have e (= (K (task-key-id (task-key h))) (K (task-id h)))) (rfl)
    (cases hk (K (task-id h)))
    (all_goals (simp only [tbl-keep task-keys e hk ih]))))

(a/theorem all-of-mem [A :- Type, P :- (=> A Bool), xs :- (List A),
                       h :- (forall [x :- A] (=> (List.Mem x xs) (= (P x) true)))]
  (= (tbl-all P xs) true)
  (induction xs)
  (case [nil] (simp [tbl-all]))
  (case [cons hd t ih]
    (have h1 (= (P hd) true)) (exact (h hd (List.Mem.head t)))
    (have h2 (= (tbl-all P t) true))
    (apply ih) (intros x hm) (exact (h x (List.Mem.tail hd hm)))
    (simp only [tbl-all h1 h2 Bool.and_self])))

(a/theorem alive-kept-of [w :- World, K :- (=> Nat Bool),
                          hK :- (forall [r :- RunRow] (=> (List.Mem r (:runs w)) (= (run-alive r) true) (= (K (:id r)) true)))]
  (= (tbl-all (alive-kept K) (run-keys (:runs w))) true)
  (rw [all-run-keys])
  (apply all-of-mem)
  (intros r hm)
  (cases ha (run-alive r))
  (case [false] (simp only [on-rkey alive-kept run-key ha Bool.not_false Bool.true_or]))
  (case [true] (simp only [on-rkey alive-kept run-key ha (hK r hm ha) Bool.or_true])))

(a/theorem i10-task-filter-world-hand [w :- World, K :- (=> Nat Bool),
                              hK :- (forall [r :- RunRow] (=> (List.Mem r (:runs w)) (= (run-alive r) true) (= (K (:id r)) true)))]
  (=> (= (i10-task w) true) (= (filter-safe-for K w) true) (= (i10-task (filter-world K w)) true))
  (intros h hf)
  (have hr (= (i10-task-rest (filter-world K w)) true))
  (simp only [i10-task-rest filter-world run-keys-keep task-keys-keep])
  (exact (i10-task-keys-ok-keep _ _ _ K (i10-task-rest-of w h) (alive-kept-of w K hK)))
  (exact (i10-task-intro _ (well-formed-filter-world w K (i10-task-well-formed w h) hf) hr)))

(a/theorem i10-task-rule-r-filter-hand [w :- World]
  (=> (= (normalized w) true) (= (i10-task w) true) (= (filter-safe w) true) (= (i10-task (rule-r-filter w)) true))
  (intros hn h hf)
  (rw [rule-r-filter-eq])
  (exact (i10-task-filter-world-hand w (keep-fn w)
           (fn [r :- RunRow, hm :- (List.Mem r (:runs w)), ha :- (= (run-alive r) true)]
             (keep-of-live w (:id r) (normalized-runs w r hn hm ha)))
           h hf)))

;; ---- the literal I10 (task part)

(a/theorem any-run-keys [P :- (=> RunKey Bool), rs :- (List RunRow)] (= (tbl-any P (run-keys rs)) (tbl-any (on-rkey P) rs))
  (induction rs) (case [nil] (simp only [run-keys tbl-any])) (case [cons h t ih] (simp only [run-keys tbl-any on-rkey ih])))

(a/theorem any-run-for-mem [tk :- TaskKey, rs :- (List RunRow)]
  (=> (= (tbl-any (on-rkey (run-for tk)) rs) true) (= (nat-mem (:run tk) (tbl-ids run-id rs)) true))
  (induction rs)
  (case [nil] (intro h) (simp [tbl-any] at h))
  (case [cons h t ih]
    (intro ha)
    (cases hx (Nat.beq (run-id h) (:run tk)))
    (case [true] (simp only [nat-mem tbl-ids hx]))
    (case [false]
      (have hp (= (on-rkey (run-for tk) h) false))
      (have hx2 (= (Nat.beq (:id h) (:run tk)) false)) (exact hx)
      (simp only [on-rkey run-for run-key hx2 Bool.false_and])
      (simp only [tbl-any hp Bool.false_or] at ha)
      (simp only [nat-mem tbl-ids hx])
      (exact (ih ha)))))

(a/theorem find-witness [tk :- TaskKey, r0 :- RunRow, rs :- (List RunRow)]
  (=> (= (nat-nodup (tbl-ids run-id rs)) true) (= (tbl-any (on-rkey (run-for tk)) rs) true)
      (= (tbl-find run-id (:run tk) rs) (Option.some RunRow r0))
      (= (Bool.and (Nat.beq (:of r0) (:id tk)) (run-alive r0)) true))
  (induction rs)
  (case [nil] (intros hn ha hf) (simp [tbl-find] at hf))
  (case [cons h t ih]
    (intros hn ha hf)
    (simp only [tbl-ids nat-nodup Bool.and_eq_true] at hn)
    (cases hx (Nat.beq (run-id h) (:run tk)))
    (case [true]
      (simp only [tbl-find hx Option.some.injEq] at hf)
      (cases hp (on-rkey (run-for tk) h))
      (case [true]
        (simp only [on-rkey run-for run-key Bool.and_eq_true] at hp)
        (simp only [hf] at hp)
        (simp only [(And.left (And.right hp)) (And.right (And.right hp)) Bool.and_self]))
      (case [false]
        (simp only [tbl-any hp Bool.false_or] at ha)
        (have hm := (any-run-for-mem tk t ha))
        (have e (= (run-id h) (:run tk))) (exact (Nat.eq_of_beq_eq_true hx))
        (have h1 := (bnot-true _ (And.left hn)))
        (rw [e] at h1) (rw [hm] at h1) (cases h1)))
    (case [false]
      (simp only [tbl-find hx] at hf)
      (have hp (= (on-rkey (run-for tk) h) false))
      (have hx2 (= (Nat.beq (:id h) (:run tk)) false)) (exact hx)
      (simp only [on-rkey run-for run-key hx2 Bool.false_and])
      (simp only [tbl-any hp Bool.false_or] at ha)
      (exact (ih (And.right hn) ha hf)))))

(a/theorem i10-task-task-run-is [w :- World, r :- RunRow]
  (=> (= (i10-task w) true) (List.Mem r (:runs w)) (= (task-run-is w r) true))
  (intros h hm)
  (have hr := (i10-task-rest-of w h))
  (simp only [i10-task-rest i10-task-keys-ok Bool.and_eq_true all-run-keys] at hr)
  (have h1 := (tbl-all-mem RunRow (on-rkey (trun-ok (task-keys (:tasks w)))) r (:runs w) (And.left (And.right hr)) hm))
  (simp only [on-rkey trun-ok all-task-keys] at h1)
  (cases hf (task-find w (:of r)))
  (case [none] (simp only [task-run-is hf]))
  (case [some t]
    (have h2 := (tbl-all-mem TaskRow (on-tkey (trun-one (run-key r))) t (:tasks w) h1 (tbl-find-mem TaskRow task-id (:of r) t (:tasks w) hf)))
    (have e (= (task-id t) (:of r))) (exact (tbl-find-id TaskRow task-id (:of r) t (:tasks w) hf))
    (have e2 (= (:id t) (:of r))) (exact e)
    (simp only [on-tkey trun-one task-key run-key e2 Nat.beq_refl Bool.not_true Bool.false_or] at h2)
    (simp only [task-run-is hf h2])))

(a/theorem tbl-find-none-has [A :- Type, idf :- (=> A Nat), x :- Nat, xs :- (List A)]
  (=> (= (tbl-find idf x xs) (Option.none A)) (= (tbl-has idf x xs) false))
  (induction xs)
  (case [nil] (intro h) (simp [tbl-has]))
  (case [cons h t ih]
    (intro hf)
    (cases hx (Nat.beq (idf h) x))
    (case [true] (simp [tbl-find hx] at hf))
    (case [false] (simp only [tbl-find hx] at hf) (simp only [tbl-has hx]) (exact (ih hf)))))

(a/theorem i10-task-task-has-run [w :- World, t :- TaskRow]
  (=> (= (i10-task w) true) (List.Mem t (:tasks w)) (= (task-has-run w t) true))
  (intros h hm)
  (have hr := (i10-task-rest-of w h))
  (simp only [i10-task-rest i10-task-keys-ok Bool.and_eq_true all-task-keys] at hr)
  (have h1 := (tbl-all-mem TaskRow (on-tkey (thas-ok (run-keys (:runs w)))) t (:tasks w) (And.right (And.right hr)) hm))
  (simp only [on-tkey thas-ok] at h1)
  (cases hd (task-done t))
  (case [true] (simp only [task-done] at hd) (simp only [task-has-run hd Bool.true_or]))
  (case [false]
    (have hd2 (= (:done (task-key t)) false)) (exact hd)
    (simp only [hd2 Bool.false_or any-run-keys] at h1)
    (have hd3 (= (Bool.not (Nat.beq (:tag (:result t)) res-none)) false)) (exact hd)
    (simp only [task-has-run hd3 Bool.false_or])
    (cases hf (run-find w (:run t)))
    (case [none]
      (have hm2 := (any-run-for-mem (task-key t) (:runs w) h1))
      (have hh (= (tbl-has run-id (:run t) (:runs w)) true)) (rw [← nat-mem-ids]) (exact hm2)
      (have hn := (tbl-find-none-has RunRow run-id (:run t) (:runs w) hf))
      (rw [hh] at hn) (cases hn))
    (case [some r0]
      (exact (find-witness (task-key t) r0 (:runs w) (lit-runs-nodup w (i10-task-well-formed w h)) h1 hf)))))

(a/theorem inv-i10-task-of [w :- World] (=> (= (i10-task w) true) (= (inv-i10-task w) true))
  (intro h)
  (simp only [inv-i10-task Bool.and_eq_true])
  (exact (And.intro (all-of-mem RunRow (task-run-is w) (:runs w) (fn [r :- RunRow, hm :- (List.Mem r (:runs w))] (i10-task-task-run-is w r h hm)))
                    (all-of-mem TaskRow (task-has-run w) (:tasks w) (fn [t :- TaskRow, hm :- (List.Mem t (:tasks w))] (i10-task-task-has-run w t h hm))))))

;; ===========================================================================
;; Part D. I9, resources: an unwinding run's resources are cancelling or fired
;;
;; Bundle `i9-res` = well-formed, every resource's owner is below the allocator, every run row with a
;; resource's owner id lists it in `resources` (so T14's cancel-res reaches every resource the
;; run owns), and `lit-i9-res`.
;; ===========================================================================

(a/defn res-below-z [n :- Nat, z :- ResRow] Bool (Nat.blt (:owner z) n))
(a/defn phase-ok [z :- ResRow] Bool
  (Bool.or (Nat.beq (:phase z) rp-armed) (Bool.or (Nat.beq (:phase z) rp-fired) (Nat.beq (:phase z) rp-cancelling))))
(a/defn res-good [n :- Nat, z :- ResRow] Bool (Bool.and (res-below-z n z) (phase-ok z)))
(a/defn listed-in [z :- ResRow, r :- RunRow] Bool
  (Bool.or (Bool.not (Nat.beq (:id r) (:owner z))) (nat-mem (:id z) (:resources r))))
(a/defn res-listed [rs :- (List RunRow), z :- ResRow] Bool (tbl-all (listed-in z) rs))
(a/defn i9-res-rest [w :- World] Bool
  (Bool.and (tbl-all (res-good (:next-id w)) (:res w))
            (Bool.and (tbl-all (res-listed (:runs w)) (:res w)) (lit-i9-res w))))
(a/defn i9-res [w :- World] Bool (Bool.and (well-formed w) (i9-res-rest w)))

(a/theorem i9-res-well-formed [w :- World] (=> (= (i9-res w) true) (= (well-formed w) true))
  (intro h) (simp only [i9-res Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem i9-res-rest-of [w :- World] (=> (= (i9-res w) true) (= (i9-res-rest w) true))
  (intro h) (simp only [i9-res Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem i9-res-intro [w :- World] (=> (= (well-formed w) true) (= (i9-res-rest w) true) (= (i9-res w) true))
  (intros h1 h2) (simp only [i9-res h1 h2 Bool.and_self]))
(a/theorem i9-res-parts [w :- World]
  (=> (= (i9-res w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (i9-res-well-formed w h))))

(a/structure I9ResRunKey [] (id Nat) (mode Nat) (resources (List Nat)))
(a/defn i9-res-run-key [r :- RunRow] I9ResRunKey (I9ResRunKey.mk (:id r) (:mode r) (:resources r)))
(def G9 (mk-bundle 'i9-res [] "i9-res-" {'well-formed-run-upd ['(fn [r :- RunRow] (Eq.refl (i9-res-run-key r))) 4]}))
(swap! (:renames G9) assoc 'well-formed-parts 'i9-res-parts)

;; the pieces of i9-res-rest under a run-table change that keeps id, mode and resources
(a/theorem listed-same [z :- ResRow, r2 :- RunRow, r :- RunRow]
  (=> (= (:id r2) (:id r)) (= (:resources r2) (:resources r)) (= (listed-in z r2) (listed-in z r)))
  (intros h1 h2) (simp only [listed-in h1 h2]))
(a/theorem unw-same [w :- World, r2 :- RunRow, r :- RunRow]
  (=> (= (:id r2) (:id r)) (= (:mode r2) (:mode r)) (= (unwinding-res-ok w r2) (unwinding-res-ok w r)))
  (intros h1 h2) (simp only [unwinding-res-ok h1 h2]))

(a/theorem i9-res-runs-same [w :- World, rs :- (List RunRow),
                         hl :- (forall [z :- ResRow] (= (res-listed rs z) (res-listed (:runs w) z))),
                         hu :- (= (tbl-all (unwinding-res-ok w) rs) (tbl-all (unwinding-res-ok w) (:runs w)))]
  (= (i9-res-rest (set-runs w rs)) (i9-res-rest w))
  (have e1 (= (tbl-all (res-listed rs) (:res w)) (tbl-all (res-listed (:runs w)) (:res w))))
  (exact (tbl-all-congr ResRow (res-listed rs) (res-listed (:runs w)) hl (:res w)))
  (have e2 (= (lit-i9-res (set-runs w rs)) (tbl-all (unwinding-res-ok w) rs))) (rfl)
  (simp only [i9-res-rest e1 e2 hu]))

(a/theorem i9-res-run-upd [w :- World, x :- Nat, f :- (=> RunRow RunRow),
                       hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                       hk :- (forall [r :- RunRow] (= (i9-res-run-key (f r)) (i9-res-run-key r)))]
  (=> (= (i9-res w) true) (= (i9-res (run-upd w x f)) true))
  (intro h)
  (have hid (forall [r :- RunRow] (= (:id (f r)) (:id r)))) (intro r) (exact (congrArg (fn [k :- I9ResRunKey] (:id k)) (hk r)))
  (have hm (forall [r :- RunRow] (= (:mode (f r)) (:mode r)))) (intro r) (exact (congrArg (fn [k :- I9ResRunKey] (:mode k)) (hk r)))
  (have hr (forall [r :- RunRow] (= (:resources (f r)) (:resources r)))) (intro r) (exact (congrArg (fn [k :- I9ResRunKey] (:resources k)) (hk r)))
  (have hl (forall [z :- ResRow] (= (res-listed (tbl-upd run-id x f (:runs w)) z) (res-listed (:runs w) z))))
  (intro z) (simp only [res-listed])
  (exact (tbl-all-upd-same RunRow run-id x f (listed-in z) (fn [r :- RunRow] (listed-same z (f r) r (hid r) (hr r))) (:runs w)))
  (have hu (= (tbl-all (unwinding-res-ok w) (tbl-upd run-id x f (:runs w))) (tbl-all (unwinding-res-ok w) (:runs w))))
  (exact (tbl-all-upd-same RunRow run-id x f (unwinding-res-ok w) (fn [r :- RunRow] (unw-same w (f r) r (hid r) (hm r))) (:runs w)))
  (have e := (i9-res-runs-same w (tbl-upd run-id x f (:runs w)) hl hu))
  (exact (i9-res-intro _ (well-formed-run-upd w x f hf (i9-res-well-formed w h)) (Eq.trans e (i9-res-rest-of w h)))))

(a/theorem res-below-one [n :- Nat, m :- Nat, z :- ResRow]
  (=> (<= n m) (= (res-below-z n z) true) (= (res-below-z m z) true))
  (intros hn hz)
  (simp only [res-below-z Nat.blt_eq] at hz) (simp only [res-below-z Nat.blt_eq])
  (exact (Nat.lt_of_lt_of_le hz hn)))

(a/theorem res-good-one [n :- Nat, m :- Nat, z :- ResRow]
  (=> (<= n m) (= (res-good n z) true) (= (res-good m z) true))
  (intros hn hz)
  (simp only [res-good Bool.and_eq_true] at hz) (simp only [res-good Bool.and_eq_true])
  (exact (And.intro (res-below-one n m z hn (And.left hz)) (And.right hz))))

(a/theorem i9-res-rest-next [w :- World, v :- Nat]
  (=> (= (i9-res-rest w) true) (<= (:next-id w) v) (= (i9-res-rest (set-next-id w v)) true))
  (intros h hv)
  (simp only [i9-res-rest Bool.and_eq_true] at h)
  (have e1 (= (lit-i9-res (set-next-id w v)) (lit-i9-res w))) (rfl)
  (have e2 (= (:res (set-next-id w v)) (:res w))) (rfl)
  (have e3 (= (:runs (set-next-id w v)) (:runs w))) (rfl)
  (have e4 (= (:next-id (set-next-id w v)) v)) (rfl)
  (simp only [i9-res-rest Bool.and_eq_true e1 e2 e3 e4])
  (exact (And.intro (tbl-all-mono ResRow (res-good (:next-id w)) (res-good v)
                      (fn [z :- ResRow, hz :- (= (res-good (:next-id w) z) true)] (res-good-one (:next-id w) v z hv hz))
                      (:res w) (And.left h))
                    (And.right h))))
(a/theorem i9-res-rest-bump [w :- World] (=> (= (i9-res-rest w) true) (= (i9-res-rest (bump w)) true))
  (intro h) (simp only [bump]) (exact (i9-res-rest-next w (+ (:next-id w) 1) h (Nat.le_succ (:next-id w)))))


(a/theorem i9-res-unw-res-del [x :- Nat, w :- World, r :- RunRow]
  (=> (= (unwinding-res-ok w r) true) (= (unwinding-res-ok (resource-del w x) r) true))
  (intro h)
  (cases hu (Nat.beq (:mode r) mode-unwinding))
  (case [false] (simp only [unwinding-res-ok hu Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [unwinding-res-ok hu Bool.not_true Bool.false_or] at h)
    (simp only [unwinding-res-ok hu Bool.not_true Bool.false_or resource-del set-res])
    (exact (tbl-all-del ResRow resource-id x (res-of-quiet (:id r)) (res-of-quiet (:id r))
             (fn [z :- ResRow, h1 :- (= (res-of-quiet (:id r) z) true), h2 :- (= (Nat.beq (resource-id z) x) false)] h1)
             (:res w) h))))

(a/theorem i9-res-rest-resource-del [w :- World, x :- Nat]
  (=> (= (i9-res-rest w) true) (= (i9-res-rest (resource-del w x)) true))
  (intro h)
  (simp only [i9-res-rest lit-i9-res Bool.and_eq_true] at h)
  (have e1 (= (:res (resource-del w x)) (tbl-del resource-id x (:res w)))) (rfl)
  (have e2 (= (:runs (resource-del w x)) (:runs w))) (rfl)
  (have e3 (= (:next-id (resource-del w x)) (:next-id w))) (rfl)
  (simp only [i9-res-rest lit-i9-res Bool.and_eq_true e1 e2 e3])
  (exact (And.intro
           (tbl-all-del ResRow resource-id x (res-good (:next-id w)) (res-good (:next-id w))
             (fn [z :- ResRow, h1 :- (= (res-good (:next-id w) z) true), h2 :- (= (Nat.beq (resource-id z) x) false)] h1) (:res w) (And.left h))
           (And.intro
             (tbl-all-del ResRow resource-id x (res-listed (:runs w)) (res-listed (:runs w))
               (fn [z :- ResRow, h1 :- (= (res-listed (:runs w) z) true), h2 :- (= (Nat.beq (resource-id z) x) false)] h1) (:res w) (And.left (And.right h)))
             (tbl-all-mono RunRow (unwinding-res-ok w) (unwinding-res-ok (resource-del w x)) (i9-res-unw-res-del x w) (:runs w)
               (And.right (And.right h)))))))

(a/theorem i9-res-rest-run-del [w :- World, x :- Nat]
  (=> (= (i9-res-rest w) true) (= (i9-res-rest (run-del w x)) true))
  (intro h)
  (simp only [i9-res-rest lit-i9-res Bool.and_eq_true] at h)
  (have hl (forall [z :- ResRow] (=> (= (res-listed (:runs w) z) true) (= (res-listed (tbl-del run-id x (:runs w)) z) true))))
  (intros z hz) (simp only [res-listed] at hz) (simp only [res-listed])
  (exact (tbl-all-del RunRow run-id x (listed-in z) (listed-in z)
           (fn [r :- RunRow, h1 :- (= (listed-in z r) true), h2 :- (= (Nat.beq (run-id r) x) false)] h1) (:runs w) hz))
  (have e1 (= (:runs (run-del w x)) (tbl-del run-id x (:runs w)))) (rfl)
  (have e2 (= (:res (run-del w x)) (:res w))) (rfl)
  (have e3 (= (:next-id (run-del w x)) (:next-id w))) (rfl)
  (have e4 (forall [r :- RunRow] (= (unwinding-res-ok (run-del w x) r) (unwinding-res-ok w r)))) (intro r) (rfl)
  (simp only [i9-res-rest lit-i9-res Bool.and_eq_true e1 e2 e3 (tbl-all-congr RunRow (unwinding-res-ok (run-del w x)) (unwinding-res-ok w) e4)])
  (exact (And.intro (And.left h)
           (And.intro (tbl-all-mono ResRow (res-listed (:runs w)) (res-listed (tbl-del run-id x (:runs w))) hl (:res w) (And.left (And.right h)))
             (tbl-all-del RunRow run-id x (unwinding-res-ok w) (unwinding-res-ok w)
               (fn [r :- RunRow, h1 :- (= (unwinding-res-ok w r) true), h2 :- (= (Nat.beq (run-id r) x) false)] h1) (:runs w)
               (And.right (And.right h)))))))

(a/theorem owner-ne-next [n :- Nat, z :- ResRow] (=> (= (res-good n z) true) (= (Nat.beq n (:owner z)) false))
  (intro h)
  (simp only [res-good res-below-z Bool.and_eq_true Nat.blt_eq] at h)
  (cases hb (Nat.beq n (:owner z)))
  (case [false] (rfl))
  (case [true] (have e (= n (:owner z))) (exact (Nat.eq_of_beq_eq_true hb)) (rw [e] at h) (omega)))

(a/theorem i9-res-run-ins [w :- World, r :- RunRow]
  (=> (= (run-id r) (:next-id w)) (= (i9-res-rest w) true) (= (i9-res-rest (bump (run-ins w r))) true))
  (intros hr h)
  (have h0 (= (i9-res-rest (run-ins w r)) true))
  (simp only [i9-res-rest lit-i9-res Bool.and_eq_true] at h)
  (have hid (= (:id r) (:next-id w))) (exact hr)
  (have hl (forall [z :- ResRow] (=> (= (res-good (:next-id w) z) true) (= (res-listed (:runs w) z) true)
                                     (= (res-listed (List.cons RunRow r (:runs w)) z) true))))
  (intros z a1 a2)
  (simp only [res-listed tbl-all listed-in hid (owner-ne-next (:next-id w) z a1) Bool.not_false Bool.true_or Bool.true_and])
  (exact a2)
  (have hq (= (tbl-all (res-of-quiet (:id r)) (:res w)) true))
  (exact (tbl-all-mono ResRow (res-good (:next-id w)) (res-of-quiet (:id r))
           (fn [z :- ResRow, a1 :- (= (res-good (:next-id w) z) true)]
             (Eq.trans (congrArg (fn [b :- Bool] (Bool.or (Bool.not b) (res-quiet z)))
                         (Eq.trans (beq-comm (:owner z) (:id r)) (Eq.trans (congrArg (fn [m :- Nat] (Nat.beq m (:owner z))) hid) (owner-ne-next (:next-id w) z a1))))
                       (Eq.refl true)))
           (:res w) (And.left h)))
  (have e1 (= (:runs (run-ins w r)) (List.cons RunRow r (:runs w)))) (rfl)
  (have e2 (= (:res (run-ins w r)) (:res w))) (rfl)
  (have e3 (= (:next-id (run-ins w r)) (:next-id w))) (rfl)
  (have e4 (forall [q :- RunRow] (= (unwinding-res-ok (run-ins w r) q) (unwinding-res-ok w q)))) (intro q) (rfl)
  (simp only [i9-res-rest lit-i9-res Bool.and_eq_true e1 e2 e3 tbl-all (tbl-all-congr RunRow (unwinding-res-ok (run-ins w r)) (unwinding-res-ok w) e4)])
  (have hu (= (unwinding-res-ok w r) true)) (simp only [unwinding-res-ok hq Bool.or_true])
  (exact (And.intro (And.left h)
           (And.intro (tbl-all-mono2 ResRow (res-good (:next-id w)) (res-listed (:runs w)) (res-listed (List.cons RunRow r (:runs w))) hl
                        (:res w) (And.left h) (And.left (And.right h)))
                      (And.intro hu (And.right (And.right h))))))
  (exact (i9-res-rest-bump _ h0)))

(a/theorem i9-res-filter [w :- World, K :- (=> Nat Bool)]
  (=> (= (i9-res-rest w) true) (= (i9-res-rest (filter-world K w)) true))
  (intro h)
  (simp only [i9-res-rest lit-i9-res Bool.and_eq_true] at h)
  (have hl (forall [z :- ResRow] (=> (= (res-listed (:runs w) z) true) (= (res-listed (tbl-keep K run-id (:runs w)) z) true))))
  (intros z a1) (simp only [res-listed] at a1) (simp only [res-listed])
  (exact (tbl-all-keep-same RunRow K run-id (listed-in z) (:runs w) a1))
  (have hu (forall [q :- RunRow] (=> (= (unwinding-res-ok w q) true) (= (unwinding-res-ok (filter-world K w) q) true))))
  (intros q a1)
  (cases hm (Nat.beq (:mode q) mode-unwinding))
  (case [false] (simp only [unwinding-res-ok hm Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [unwinding-res-ok hm Bool.not_true Bool.false_or] at a1)
    (simp only [unwinding-res-ok hm Bool.not_true Bool.false_or filter-world])
    (exact (tbl-all-keep-same ResRow K resource-id (res-of-quiet (:id q)) (:res w) a1)))
  (simp only [i9-res-rest lit-i9-res Bool.and_eq_true filter-world])
  (exact (And.intro (tbl-all-keep-same ResRow K resource-id (res-good (:next-id w)) (:res w) (And.left h))
           (And.intro (tbl-all-keep-same ResRow K resource-id (res-listed (tbl-keep K run-id (:runs w)))
                        (:res w) (tbl-all-mono ResRow (res-listed (:runs w)) (res-listed (tbl-keep K run-id (:runs w))) hl (:res w) (And.left (And.right h))))
                      (tbl-all-keep-same RunRow K run-id (unwinding-res-ok (filter-world K w))
                        (:runs w) (tbl-all-mono RunRow (unwinding-res-ok w) (unwinding-res-ok (filter-world K w)) hu (:runs w) (And.right (And.right h))))))))

(a/theorem res-good-f [n :- Nat, z :- ResRow, z2 :- ResRow]
  (=> (= (:owner z2) (:owner z)) (=> (= (phase-ok z) true) (= (phase-ok z2) true)) (= (res-good n z) true) (= (res-good n z2) true))
  (intros ho hp h)
  (simp only [res-good res-below-z Bool.and_eq_true] at h)
  (simp only [res-good res-below-z Bool.and_eq_true ho])
  (exact (And.intro (And.left h) (hp (And.right h)))))
(a/theorem listed-in-eq [z :- ResRow, z2 :- ResRow, r :- RunRow]
  (=> (= (:id z2) (:id z)) (= (:owner z2) (:owner z)) (= (listed-in z2 r) (listed-in z r)))
  (intros h1 h2) (simp only [listed-in h1 h2]))
(a/theorem listed-f [rs :- (List RunRow), z :- ResRow, z2 :- ResRow]
  (=> (= (:id z2) (:id z)) (= (:owner z2) (:owner z)) (= (res-listed rs z2) (res-listed rs z)))
  (intros h1 h2)
  (simp only [res-listed])
  (exact (tbl-all-congr RunRow (listed-in z2) (listed-in z) (fn [r :- RunRow] (listed-in-eq z z2 r h1 h2)) rs)))
(a/theorem quiet-f [x :- Nat, z :- ResRow, z2 :- ResRow]
  (=> (= (:owner z2) (:owner z)) (=> (= (res-quiet z) true) (= (res-quiet z2) true)) (= (res-of-quiet x z) true) (= (res-of-quiet x z2) true))
  (intros ho hq h)
  (cases hx (Nat.beq (:owner z) x))
  (case [false] (simp only [res-of-quiet ho hx Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [res-of-quiet hx Bool.not_true Bool.false_or] at h)
    (simp only [res-of-quiet ho hx Bool.not_true Bool.false_or (hq h)])))

;; a resource row change that keeps id and owner, keeps the phase valid and never un-quiets
(a/theorem i9-res-res-upd-q [w :- World, x :- Nat, f :- (=> ResRow ResRow),
                         hid :- (forall [z :- ResRow] (= (resource-id (f z)) (resource-id z))),
                         ho :- (forall [z :- ResRow] (= (:owner (f z)) (:owner z))),
                         hp :- (forall [z :- ResRow] (=> (= (phase-ok z) true) (= (phase-ok (f z)) true))),
                         hq :- (forall [z :- ResRow] (=> (= (res-quiet z) true) (= (res-quiet (f z)) true)))]
  (=> (= (i9-res w) true) (= (i9-res (resource-upd w x f)) true))
  (intro h)
  (have hr := (i9-res-rest-of w h))
  (simp only [i9-res-rest lit-i9-res Bool.and_eq_true] at hr)
  (have hid2 (forall [z :- ResRow] (= (:id (f z)) (:id z)))) (intro z) (exact (hid z))
  (have h1 (= (tbl-all (res-good (:next-id w)) (tbl-upd resource-id x f (:res w))) true))
  (exact (tbl-all-upd ResRow resource-id x f (res-good (:next-id w)) (res-good (:next-id w))
           (fn [z :- ResRow, a1 :- (= (res-good (:next-id w) z) true), a2 :- (= (Nat.beq (resource-id z) x) true)]
             (res-good-f (:next-id w) z (f z) (ho z) (hp z) a1))
           (fn [z :- ResRow, a1 :- (= (res-good (:next-id w) z) true), a2 :- (= (Nat.beq (resource-id z) x) false)] a1)
           (:res w) (And.left hr)))
  (have h2 (= (tbl-all (res-listed (:runs w)) (tbl-upd resource-id x f (:res w))) true))
  (rw [(tbl-all-upd-same ResRow resource-id x f (res-listed (:runs w))
         (fn [z :- ResRow] (listed-f (:runs w) z (f z) (hid2 z) (ho z))) (:res w))])
  (exact (And.left (And.right hr)))
  (have h3 (forall [q :- RunRow] (=> (= (unwinding-res-ok w q) true) (= (unwinding-res-ok (resource-upd w x f) q) true))))
  (intros q a1)
  (cases hm (Nat.beq (:mode q) mode-unwinding))
  (case [false] (simp only [unwinding-res-ok hm Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [unwinding-res-ok hm Bool.not_true Bool.false_or] at a1)
    (simp only [unwinding-res-ok hm Bool.not_true Bool.false_or resource-upd set-res])
    (exact (tbl-all-upd ResRow resource-id x f (res-of-quiet (:id q)) (res-of-quiet (:id q))
             (fn [z :- ResRow, b1 :- (= (res-of-quiet (:id q) z) true), b2 :- (= (Nat.beq (resource-id z) x) true)]
               (quiet-f (:id q) z (f z) (ho z) (hq z) b1))
             (fn [z :- ResRow, b1 :- (= (res-of-quiet (:id q) z) true), b2 :- (= (Nat.beq (resource-id z) x) false)] b1)
             (:res w) a1)))
  (have e1 (= (:res (resource-upd w x f)) (tbl-upd resource-id x f (:res w)))) (rfl)
  (have e2 (= (:runs (resource-upd w x f)) (:runs w))) (rfl)
  (have e3 (= (:next-id (resource-upd w x f)) (:next-id w))) (rfl)
  (have hr2 (= (i9-res-rest (resource-upd w x f)) true))
  (simp only [i9-res-rest lit-i9-res Bool.and_eq_true e1 e2 e3])
  (exact (And.intro h1 (And.intro h2 (tbl-all-mono RunRow (unwinding-res-ok w) (unwinding-res-ok (resource-upd w x f)) h3 (:runs w)
                                       (And.right (And.right hr))))))
  (exact (i9-res-intro _ (well-formed-resource-upd w x f hid (i9-res-well-formed w h)) hr2)))

;; ---- T14's cancel-res over the run's resource list

(a/theorem cancel-row-phase [z :- ResRow] (=> (= (phase-ok z) true) (= (phase-ok (res-cancel-row z)) true))
  (intro h)
  (cases hb (Nat.beq (:phase z) rp-armed))
  (case [false] (simp only [res-cancel-row hb]) (exact h))
  (case [true] (simp only [res-cancel-row hb])))
(a/theorem cancel-row-quiet [z :- ResRow] (=> (= (res-quiet z) true) (= (res-quiet (res-cancel-row z)) true))
  (intro h)
  (cases hb (Nat.beq (:phase z) rp-armed))
  (case [false] (simp only [res-cancel-row hb]) (exact h))
  (case [true] (simp only [res-cancel-row hb])))
(a/theorem cancel-row-quiets [z :- ResRow] (=> (= (phase-ok z) true) (= (res-quiet (res-cancel-row z)) true))
  (intro h)
  (cases hb (Nat.beq (:phase z) rp-armed))
  (case [true] (simp only [res-cancel-row hb]))
  (case [false]
    (simp only [res-cancel-row hb])
    (simp only [phase-ok hb Bool.false_or] at h)
    (simp only [res-quiet])
    (cases hf (Nat.beq (:phase z) rp-fired))
    (case [true] (simp only [hf Bool.or_true]))
    (case [false] (simp only [hf Bool.false_or] at h) (simp only [h Bool.true_or]))))

(a/defn rcl [L :- (List Nat), rs :- (List ResRow)] (List ResRow)
  (match L nil rs (cons x t) (rcl t (tbl-upd resource-id x res-cancel-row rs))))

(a/theorem res-cancel-fold [L :- (List Nat)]
  (forall [V :- World] (= (:res (nat-fold res-cancel V L)) (rcl L (:res V))))
  (induction L)
  (case [nil] (intro V) (simp only [nat-fold rcl]))
  (case [cons x t ih] (intro V) (simp only [nat-fold rcl]) (exact (ih (res-cancel V x)))))
(a/theorem runs-cancel-fold [L :- (List Nat)]
  (forall [V :- World] (= (:runs (nat-fold res-cancel V L)) (:runs V)))
  (induction L)
  (case [nil] (intro V) (simp only [nat-fold]))
  (case [cons x t ih] (intro V) (simp only [nat-fold]) (exact (ih (res-cancel V x)))))
(a/theorem next-cancel-fold [L :- (List Nat)]
  (forall [V :- World] (= (:next-id (nat-fold res-cancel V L)) (:next-id V)))
  (induction L)
  (case [nil] (intro V) (simp only [nat-fold]))
  (case [cons x t ih] (intro V) (simp only [nat-fold]) (exact (ih (res-cancel V x)))))
(a/theorem runs-acts-fold [L :- (List Nat)]
  (forall [V :- World] (And (= (:runs (nat-fold drop-act V L)) (:runs V))
                            (And (= (:res (nat-fold drop-act V L)) (:res V)) (= (:next-id (nat-fold drop-act V L)) (:next-id V)))))
  (induction L)
  (case [nil] (intro V) (exact (And.intro (Eq.refl (:runs V)) (And.intro (Eq.refl (:res V)) (Eq.refl (:next-id V))))))
  (case [cons x t ih] (intro V) (simp only [nat-fold]) (exact (ih (drop-act V x)))))

(a/theorem rcl-all [P :- (=> ResRow Bool), hp :- (forall [z :- ResRow] (=> (= (P z) true) (= (P (res-cancel-row z)) true))), L :- (List Nat)]
  (forall [rs :- (List ResRow)] (=> (= (tbl-all P rs) true) (= (tbl-all P (rcl L rs)) true)))
  (induction L)
  (case [nil] (intros rs h) (simp only [rcl]) (exact h))
  (case [cons x t ih]
    (intros rs h) (simp only [rcl])
    (exact (ih _ (tbl-all-upd ResRow resource-id x res-cancel-row P P
                   (fn [z :- ResRow, a1 :- (= (P z) true), a2 :- (= (Nat.beq (resource-id z) x) true)] (hp z a1))
                   (fn [z :- ResRow, a1 :- (= (P z) true), a2 :- (= (Nat.beq (resource-id z) x) false)] a1) rs h)))))

(a/defn quiet-in [L :- (List Nat), z :- ResRow] Bool (Bool.or (Bool.not (nat-mem (:id z) L)) (res-quiet z)))

(a/theorem quiet-in-step [x :- Nat, M :- (List Nat), L :- (List Nat), z :- ResRow]
  (= (quiet-in (nat-app (List.cons Nat x M) L) z) (quiet-in (nat-app M (List.cons Nat x L)) z))
  (simp only [quiet-in nat-app nat-mem-app nat-mem])
  (cases h1 (Nat.beq x (:id z))) (all_goals (cases h2 (nat-mem (:id z) M))) (all_goals (simp only [h1 h2 Bool.true_or Bool.or_true Bool.false_or Bool.or_false])))

(a/theorem cancel-row-owner [z :- ResRow] (= (:owner (res-cancel-row z)) (:owner z))
  (cases hb (Nat.beq (:phase z) rp-armed)) (all_goals (simp only [res-cancel-row hb])))
(a/theorem quiet-in-nil [M :- (List Nat), z :- ResRow] (= (quiet-in (nat-app M (List.nil Nat)) z) (quiet-in M z))
  (simp only [quiet-in nat-mem-app nat-mem Bool.or_false]))
(a/theorem quiet-in-hit [x :- Nat, M :- (List Nat), n :- Nat, z :- ResRow]
  (=> (= (res-good n z) true) (= (quiet-in (List.cons Nat x M) (res-cancel-row z)) true))
  (intro h)
  (simp only [res-good Bool.and_eq_true] at h)
  (simp only [quiet-in (cancel-row-quiets z (And.right h)) Bool.or_true]))
(a/theorem quiet-in-miss [x :- Nat, M :- (List Nat), z :- ResRow]
  (=> (= (Nat.beq (resource-id z) x) false) (= (quiet-in M z) true) (= (quiet-in (List.cons Nat x M) z) true))
  (intros h1 h2)
  (have h3 (= (Nat.beq x (:id z)) false)) (rw [beq-comm]) (exact h1)
  (simp only [quiet-in nat-mem h3] ) (exact h2))

(a/theorem rcl-quiet [n :- Nat, L :- (List Nat)]
  (forall [M :- (List Nat), rs :- (List ResRow)]
    (=> (= (tbl-all (res-good n) rs) true) (= (tbl-all (quiet-in M) rs) true)
        (= (tbl-all (quiet-in (nat-app M L)) (rcl L rs)) true)))
  (induction L)
  (case [nil]
    (intros M rs h1 h2) (simp only [rcl])
    (exact (Eq.trans (tbl-all-congr ResRow (quiet-in (nat-app M (List.nil Nat))) (quiet-in M)
                       (fn [z :- ResRow] (quiet-in-nil M z)) rs) h2)))
  (case [cons x t ih]
    (intros M rs h1 h2) (simp only [rcl])
    (have g1 := (tbl-all-upd ResRow resource-id x res-cancel-row (res-good n) (res-good n)
                  (fn [z :- ResRow, a1 :- (= (res-good n z) true), a2 :- (= (Nat.beq (resource-id z) x) true)]
                    (res-good-f n z (res-cancel-row z) (cancel-row-owner z) (cancel-row-phase z) a1))
                  (fn [z :- ResRow, a1 :- (= (res-good n z) true), a2 :- (= (Nat.beq (resource-id z) x) false)] a1) rs h1))
    (have g2 := (all-upd2 ResRow resource-id x res-cancel-row (res-good n) (quiet-in M) (quiet-in (List.cons Nat x M))
                  (fn [z :- ResRow, a1 :- (= (res-good n z) true), a2 :- (= (quiet-in M z) true), a3 :- (= (Nat.beq (resource-id z) x) true)]
                    (quiet-in-hit x M n z a1))
                  (fn [z :- ResRow, a1 :- (= (res-good n z) true), a2 :- (= (quiet-in M z) true), a3 :- (= (Nat.beq (resource-id z) x) false)]
                    (quiet-in-miss x M z a3 a2))
                  rs h1 h2))
    (have r := (ih (List.cons Nat x M) _ g1 g2))
    (exact (Eq.trans (tbl-all-congr ResRow (quiet-in (nat-app M (List.cons Nat x t))) (quiet-in (nat-app (List.cons Nat x M) t))
                       (fn [z :- ResRow] (Eq.symm (quiet-in-step x M t z))) _) r))))

(a/defn listed-by [r :- RunRow, z :- ResRow] Bool (listed-in z r))

(a/theorem quiet-own [r :- RunRow, x :- Nat, z :- ResRow]
  (=> (= x (:id r)) (= (quiet-in (:resources r) z) true) (= (listed-by r z) true) (= (res-of-quiet x z) true))
  (intros hx h1 h2)
  (cases ho (Nat.beq (:owner z) x))
  (case [false] (simp only [res-of-quiet ho Bool.not_false Bool.true_or]))
  (case [true]
    (have ho2 (= (Nat.beq (:id r) (:owner z)) true)) (rw [beq-comm]) (rw [← hx]) (exact ho)
    (simp only [listed-by listed-in ho2 Bool.not_true Bool.false_or] at h2)
    (simp only [quiet-in h2 Bool.not_true Bool.false_or] at h1)
    (simp only [res-of-quiet ho h1 Bool.or_true])))

(a/theorem cancel-row-id [z :- ResRow] (= (:id (res-cancel-row z)) (:id z))
  (cases hb (Nat.beq (:phase z) rp-armed)) (all_goals (simp only [res-cancel-row hb])))
(a/theorem all-quiet-nil [rs :- (List ResRow)] (= (tbl-all (quiet-in (List.nil Nat)) rs) true)
  (induction rs)
  (case [nil] (simp only [tbl-all]))
  (case [cons h t ih] (simp only [tbl-all quiet-in nat-mem Bool.not_false Bool.true_or ih Bool.and_self])))

(a/theorem i9-res-cancel-mid [w :- World, r :- RunRow]
  (=> (List.Mem r (:runs w)) (= (i9-res w) true) (= (i9-res (cancel-mid w r)) true))
  (intros hm h)
  (have hs := (i9-res-well-formed w h))
  (have hr := (i9-res-rest-of w h))
  (simp only [i9-res-rest lit-i9-res Bool.and_eq_true] at hr)
  (have fa := (runs-acts-fold (tbl-scan act-id (act-of-run (:id r)) (:acts w))
                (run-upd w (:id r) run-cancel-row)))
  (have e-runs (= (:runs (cancel-mid w r)) (tbl-upd run-id (:id r) run-cancel-row (:runs w))))
  (simp only [cancel-mid cleanup-set cleanup-ins cleanup-del set-cleanup cancel-res cancel-acts runs-cancel-fold])
  (exact (And.left fa))
  (have e-res (= (:res (cancel-mid w r)) (rcl (:resources r) (:res w))))
  (simp only [cancel-mid cleanup-set cleanup-ins cleanup-del set-cleanup cancel-res cancel-acts res-cancel-fold])
  (rw [(And.left (And.right fa))])
  (have e-next (= (:next-id (cancel-mid w r)) (:next-id w)))
  (simp only [cancel-mid cleanup-set cleanup-ins cleanup-del set-cleanup cancel-res cancel-acts next-cancel-fold])
  (exact (And.right (And.right fa)))
  (have p1 := (rcl-all (res-good (:next-id w))
                (fn [z :- ResRow, a1 :- (= (res-good (:next-id w) z) true)]
                  (res-good-f (:next-id w) z (res-cancel-row z) (cancel-row-owner z) (cancel-row-phase z) a1))
                (:resources r) (:res w) (And.left hr)))
  (have p2a := (rcl-all (res-listed (:runs w))
                 (fn [z :- ResRow, a1 :- (= (res-listed (:runs w) z) true)]
                   (Eq.trans (listed-f (:runs w) z (res-cancel-row z) (cancel-row-id z) (cancel-row-owner z)) a1))
                 (:resources r) (:res w) (And.left (And.right hr))))
  (have hl (forall [z :- ResRow] (= (res-listed (tbl-upd run-id (:id r) run-cancel-row (:runs w)) z) (res-listed (:runs w) z))))
  (intro z) (simp only [res-listed])
  (exact (tbl-all-upd-same RunRow run-id (:id r) run-cancel-row (listed-in z)
           (fn [q :- RunRow] (listed-same z (run-cancel-row q) q (Eq.refl (:id q)) (Eq.refl (:resources q)))) (:runs w)))
  (have p2 (= (tbl-all (res-listed (tbl-upd run-id (:id r) run-cancel-row (:runs w))) (rcl (:resources r) (:res w))) true))
  (rw [(tbl-all-congr ResRow (res-listed (tbl-upd run-id (:id r) run-cancel-row (:runs w))) (res-listed (:runs w)) hl _)])
  (exact p2a)
  (have q1 := (rcl-quiet (:next-id w) (:resources r) (List.nil Nat) (:res w) (And.left hr) (all-quiet-nil (:res w))))
  (have q2 (= (tbl-all (listed-by r) (rcl (:resources r) (:res w))) true))
  (exact (tbl-all-mono ResRow (res-listed (:runs w)) (listed-by r)
           (fn [z :- ResRow, a1 :- (= (res-listed (:runs w) z) true)] (tbl-all-mem RunRow (listed-in z) r (:runs w) a1 hm))
           _ p2a))
  (have hin (forall [q :- RunRow] (=> (= (unwinding-res-ok w q) true) (= (Nat.beq (run-id q) (:id r)) true)
                                      (= (unwinding-res-ok (cancel-mid w r) (run-cancel-row q)) true))))
  (intros q a1 a2)
  (have eq (= (:id q) (:id r))) (exact (Nat.eq_of_beq_eq_true a2))
  (have hq (= (tbl-all (res-of-quiet (:id q)) (rcl (:resources r) (:res w))) true))
  (exact (tbl-all-mono2 ResRow (quiet-in (:resources r)) (listed-by r) (res-of-quiet (:id q))
           (fn [z :- ResRow, b1 :- (= (quiet-in (:resources r) z) true), b2 :- (= (listed-by r z) true)] (quiet-own r (:id q) z eq b1 b2))
           _ q1 q2))
  (simp only [unwinding-res-ok e-res run-cancel-row hq Bool.or_true])
  (have hout (forall [q :- RunRow] (=> (= (unwinding-res-ok w q) true) (= (Nat.beq (run-id q) (:id r)) false)
                                       (= (unwinding-res-ok (cancel-mid w r) q) true))))
  (intros q a1 a2)
  (cases hu (Nat.beq (:mode q) mode-unwinding))
  (case [false] (simp only [unwinding-res-ok hu Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [unwinding-res-ok hu Bool.not_true Bool.false_or] at a1)
    (simp only [unwinding-res-ok hu Bool.not_true Bool.false_or e-res])
    (exact (rcl-all (res-of-quiet (:id q))
             (fn [z :- ResRow, b1 :- (= (res-of-quiet (:id q) z) true)]
               (quiet-f (:id q) z (res-cancel-row z) (cancel-row-owner z) (cancel-row-quiet z) b1))
             (:resources r) (:res w) a1)))
  (have p3 := (tbl-all-upd RunRow run-id (:id r) run-cancel-row (unwinding-res-ok w) (unwinding-res-ok (cancel-mid w r)) hin hout
                (:runs w) (And.right (And.right hr))))
  (have hr2 (= (i9-res-rest (cancel-mid w r)) true))
  (simp only [i9-res-rest lit-i9-res Bool.and_eq_true e-runs e-res e-next])
  (exact (And.intro p1 (And.intro p2 p3)))
  (exact (i9-res-intro _ (cancel-mid-well-formed w r hs) hr2)))

;; ---- T15 ack: the resource row goes and leaves its owner's list

(a/theorem nat-mem-del [y :- Nat, x :- Nat, xs :- (List Nat)]
  (=> (= (Nat.beq y x) false) (= (nat-mem y (nat-del x xs)) (nat-mem y xs)))
  (intro hne)
  (induction xs)
  (case [nil] (simp only [nat-del nat-mem]))
  (case [cons h t ih]
    (cases hx (Nat.beq h x))
    (case [true]
      (have e (= h x)) (exact (Nat.eq_of_beq_eq_true hx))
      (have hy (= (Nat.beq h y) false)) (rw [e]) (rw [beq-comm]) (exact hne)
      (simp only [nat-del hx nat-mem hy ih]))
    (case [false] (simp only [nat-del hx nat-mem ih]))))

(a/theorem listed-unres [z :- Nat, zz :- ResRow, q :- RunRow]
  (=> (= (Nat.beq (resource-id zz) z) false) (= (listed-in zz (run-unres z q)) (listed-in zz q)))
  (intro h)
  (have h2 (= (Nat.beq (:id zz) z) false)) (exact h)
  (simp only [listed-in run-unres (nat-mem-del (:id zz) z (:resources q) h2)]))

(a/theorem i9-res-ack-raw-hand [w :- World, z :- Nat, owner :- Nat]
  (=> (= (tbl-all (no-debtor z) (:edges w)) true) (= (i9-res w) true) (= (i9-res (ack-raw w z owner)) true))
  (intros hu h)
  (have hr := (i9-res-rest-of w h))
  (simp only [i9-res-rest lit-i9-res Bool.and_eq_true] at hr)
  (have e1 (= (:runs (ack-raw w z owner)) (tbl-upd run-id owner (run-unres z) (:runs w)))) (rfl)
  (have e2 (= (:res (ack-raw w z owner)) (tbl-del resource-id z (:res w)))) (rfl)
  (have e3 (= (:next-id (ack-raw w z owner)) (:next-id w))) (rfl)
  (have p1 := (tbl-all-del ResRow resource-id z (res-good (:next-id w)) (res-good (:next-id w))
                (fn [zz :- ResRow, a1 :- (= (res-good (:next-id w) zz) true), a2 :- (= (Nat.beq (resource-id zz) z) false)] a1)
                (:res w) (And.left hr)))
  (have p2 := (tbl-all-del ResRow resource-id z (res-listed (:runs w)) (res-listed (tbl-upd run-id owner (run-unres z) (:runs w)))
                (fn [zz :- ResRow, a1 :- (= (res-listed (:runs w) zz) true), a2 :- (= (Nat.beq (resource-id zz) z) false)]
                  (Eq.trans (tbl-all-upd-same RunRow run-id owner (run-unres z) (listed-in zz) (fn [q :- RunRow] (listed-unres z zz q a2)) (:runs w)) a1))
                (:res w) (And.left (And.right hr))))
  (have hq (forall [q :- RunRow] (=> (= (unwinding-res-ok w q) true) (= (unwinding-res-ok (ack-raw w z owner) q) true))))
  (intros q a1)
  (cases hm (Nat.beq (:mode q) mode-unwinding))
  (case [false] (simp only [unwinding-res-ok hm Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [unwinding-res-ok hm Bool.not_true Bool.false_or] at a1)
    (simp only [unwinding-res-ok hm Bool.not_true Bool.false_or e2])
    (exact (tbl-all-del ResRow resource-id z (res-of-quiet (:id q)) (res-of-quiet (:id q))
             (fn [zz :- ResRow, b1 :- (= (res-of-quiet (:id q) zz) true), b2 :- (= (Nat.beq (resource-id zz) z) false)] b1) (:res w) a1)))
  (have hq2 (forall [q :- RunRow] (= (unwinding-res-ok (ack-raw w z owner) (run-unres z q)) (unwinding-res-ok (ack-raw w z owner) q))))
  (intro q) (rfl)
  (have p3 (= (tbl-all (unwinding-res-ok (ack-raw w z owner)) (tbl-upd run-id owner (run-unres z) (:runs w))) true))
  (rw [(tbl-all-upd-same RunRow run-id owner (run-unres z) (unwinding-res-ok (ack-raw w z owner)) hq2 (:runs w))])
  (exact (tbl-all-mono RunRow (unwinding-res-ok w) (unwinding-res-ok (ack-raw w z owner)) hq (:runs w) (And.right (And.right hr))))
  (have hr2 (= (i9-res-rest (ack-raw w z owner)) true))
  (simp only [i9-res-rest lit-i9-res Bool.and_eq_true e1 e2 e3])
  (exact (And.intro p1 (And.intro p2 p3)))
  (exact (i9-res-intro _ (well-formed-ack-raw w z owner hu (i9-res-well-formed w h)) hr2)))

;; ---- T17 arm (not in a cleanup slice, Z#40): a new armed resource of a normal run

(a/defn not-unw [b :- RunRow] Bool (Bool.not (run-unwinding b)))
(a/defn tt-run [q :- RunRow] Bool true)
(a/theorem all-tt [rs :- (List RunRow)] (= (tbl-all tt-run rs) true)
  (induction rs) (case [nil] (simp only [tbl-all])) (case [cons h t ih] (simp only [tbl-all tt-run ih Bool.and_self])))

(a/theorem listed-arm [n :- Nat, zz :- ResRow, q :- RunRow]
  (=> (= (listed-in zz q) true) (= (listed-in zz (run-arm n q)) true))
  (intro h)
  (cases ho (Nat.beq (:id q) (:owner zz)))
  (case [false] (simp only [listed-in run-arm ho Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [listed-in ho Bool.not_true Bool.false_or] at h)
    (cases hn (Nat.beq n (:id zz)))
    (all_goals (simp only [listed-in run-arm ho nat-mem hn h Bool.not_true Bool.false_or]))))

(a/theorem listed-new [n :- Nat, o :- Nat, kind :- Nat, ei :- Nat, q :- RunRow]
  (=> (= (Nat.beq (run-id q) o) true) (= (listed-in (ResRow.mk n o kind ei rp-armed) (run-arm n q)) true))
  (intro h) (simp only [listed-in run-arm nat-mem Nat.beq_refl Bool.or_true]))
(a/theorem listed-other [n :- Nat, o :- Nat, kind :- Nat, ei :- Nat, q :- RunRow]
  (=> (= (Nat.beq (run-id q) o) false) (= (listed-in (ResRow.mk n o kind ei rp-armed) q) true))
  (intro h) (have h2 (= (Nat.beq (:id q) o) false)) (exact h) (simp only [listed-in h2 Bool.not_false Bool.true_or]))
(a/theorem well-formed-arm-raw-of [w :- World, r :- RunRow, kind :- Nat]
  (=> (= (well-formed w) true) (= (well-formed (arm-raw w r kind)) true))
  (intro h)
  (simp only [arm-raw])
  (exact (well-formed-run-upd _ (:id r) (run-arm (:next-id w)) (run-arm-run-id _)
           (well-formed-resource-ins-fresh w (ResRow.mk (:next-id w) (:id r) kind (:effect-index r) rp-armed) (rfl) h))))

(a/theorem arm-good [n :- Nat, o :- Nat, kind :- Nat, ei :- Nat]
  (=> (< o (+ n 1)) (= (res-good (+ n 1) (ResRow.mk n o kind ei rp-armed)) true))
  (intro h)
  (have h2 (= (Nat.blt o (+ n 1)) true)) (simp only [Nat.blt_eq]) (exact h)
  (simp only [res-good res-below-z phase-ok h2 Bool.true_and]))

(a/theorem i9-res-arm-hand [w :- World, r :- RunRow, kind :- Nat]
  (=> (List.Mem r (:runs w)) (= (run-unwinding r) false) (= (i9-res w) true) (= (i9-res (arm-raw w r kind)) true))
  (intros hm hu h)
  (have hs := (i9-res-well-formed w h))
  (have hr := (i9-res-rest-of w h))
  (simp only [i9-res-rest lit-i9-res Bool.and_eq_true] at hr)
  (have hlt := (run-below w r hs hm))
  (have hnu (= (not-unw r) true)) (simp only [not-unw hu Bool.not_false])
  (have u := (uniq-all RunRow run-id not-unw r (:runs w) (lit-runs-nodup w hs) hm hnu))
  (have e1 (= (:runs (arm-raw w r kind)) (tbl-upd run-id (:id r) (run-arm (:next-id w)) (:runs w)))) (rfl)
  (have e2 (= (:res (arm-raw w r kind))
              (List.cons ResRow (ResRow.mk (:next-id w) (:id r) kind (:effect-index r) rp-armed) (:res w)))) (rfl)
  (have e3 (= (:next-id (arm-raw w r kind)) (+ (:next-id w) 1))) (rfl)
  ;; part 1
  (have g0 (= (res-good (+ (:next-id w) 1) (ResRow.mk (:next-id w) (:id r) kind (:effect-index r) rp-armed)) true))
  (have lt2 (< (:id r) (+ (:next-id w) 1))) (omega)
  (exact (arm-good (:next-id w) (:id r) kind (:effect-index r) lt2))
  (have le (<= (:next-id w) (+ (:next-id w) 1))) (omega)
  (have p1 (= (tbl-all (res-good (+ (:next-id w) 1)) (List.cons ResRow (ResRow.mk (:next-id w) (:id r) kind (:effect-index r) rp-armed) (:res w))) true))
  (simp only [tbl-all g0 Bool.true_and])
  (exact (tbl-all-mono ResRow (res-good (:next-id w)) (res-good (+ (:next-id w) 1))
           (fn [zz :- ResRow, a1 :- (= (res-good (:next-id w) zz) true)] (res-good-one (:next-id w) (+ (:next-id w) 1) zz le a1)) (:res w) (And.left hr)))
  ;; part 2
  (have pz (= (res-listed (tbl-upd run-id (:id r) (run-arm (:next-id w)) (:runs w)) (ResRow.mk (:next-id w) (:id r) kind (:effect-index r) rp-armed)) true))
  (simp only [res-listed])
  (exact (tbl-all-upd RunRow run-id (:id r) (run-arm (:next-id w)) tt-run (listed-in (ResRow.mk (:next-id w) (:id r) kind (:effect-index r) rp-armed))
           (fn [q :- RunRow, a1 :- (= (tt-run q) true), a2 :- (= (Nat.beq (run-id q) (:id r)) true)] (listed-new (:next-id w) (:id r) kind (:effect-index r) q a2))
           (fn [q :- RunRow, a1 :- (= (tt-run q) true), a2 :- (= (Nat.beq (run-id q) (:id r)) false)] (listed-other (:next-id w) (:id r) kind (:effect-index r) q a2))
           (:runs w) (all-tt (:runs w))))
  (have p2 (= (tbl-all (res-listed (tbl-upd run-id (:id r) (run-arm (:next-id w)) (:runs w)))
                       (List.cons ResRow (ResRow.mk (:next-id w) (:id r) kind (:effect-index r) rp-armed) (:res w))) true))
  (simp only [tbl-all pz Bool.true_and])
  (exact (tbl-all-mono ResRow (res-listed (:runs w)) (res-listed (tbl-upd run-id (:id r) (run-arm (:next-id w)) (:runs w)))
           (fn [zz :- ResRow, a1 :- (= (res-listed (:runs w) zz) true)]
             (tbl-all-upd RunRow run-id (:id r) (run-arm (:next-id w)) (listed-in zz) (listed-in zz)
               (fn [q :- RunRow, b1 :- (= (listed-in zz q) true), b2 :- (= (Nat.beq (run-id q) (:id r)) true)] (listed-arm (:next-id w) zz q b1))
               (fn [q :- RunRow, b1 :- (= (listed-in zz q) true), b2 :- (= (Nat.beq (run-id q) (:id r)) false)] b1)
               (:runs w) a1))
           (:res w) (And.left (And.right hr))))
  ;; part 3
  (have hin (forall [q :- RunRow] (=> (= (unwinding-res-ok w q) true) (= (same-id-then run-id (run-id r) not-unw q) true)
                                      (= (Nat.beq (run-id q) (:id r)) true)
                                      (= (unwinding-res-ok (arm-raw w r kind) (run-arm (:next-id w) q)) true))))
  (intros q a1 a2 a3)
  (have a3b (= (Nat.beq (run-id q) (run-id r)) true)) (exact a3)
  (simp only [same-id-then a3b Bool.not_true Bool.false_or not-unw run-unwinding] at a2)
  (simp only [unwinding-res-ok run-arm a2 Bool.true_or])
  (have hout (forall [q :- RunRow] (=> (= (unwinding-res-ok w q) true) (= (same-id-then run-id (run-id r) not-unw q) true)
                                       (= (Nat.beq (run-id q) (:id r)) false)
                                       (= (unwinding-res-ok (arm-raw w r kind) q) true))))
  (intros q a1 a2 a3)
  (cases hmq (Nat.beq (:mode q) mode-unwinding))
  (case [false] (simp only [unwinding-res-ok hmq Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [unwinding-res-ok hmq Bool.not_true Bool.false_or] at a1)
    (have a4 (= (Nat.beq (:id r) (:id q)) false)) (rw [beq-comm]) (exact a3)
    (simp only [unwinding-res-ok hmq Bool.not_true Bool.false_or e2 tbl-all res-of-quiet a4 Bool.not_false Bool.true_or Bool.true_and])
    (exact a1))
  (have p3 := (all-upd2 RunRow run-id (:id r) (run-arm (:next-id w)) (unwinding-res-ok w) (same-id-then run-id (run-id r) not-unw)
                (unwinding-res-ok (arm-raw w r kind)) hin hout (:runs w) (And.right (And.right hr)) u))
  (have hr2 (= (i9-res-rest (arm-raw w r kind)) true))
  (simp only [i9-res-rest lit-i9-res Bool.and_eq_true e1 e2 e3])
  (exact (And.intro p1 (And.intro p2 p3)))
  (exact (i9-res-intro _ (well-formed-arm-raw-of w r kind hs) hr2)))

;; ---- the G9 cells (its table in the generic tree and its step: spindel.v2.inv.i9-res)

(defpart G9 :reads '[next-id res runs])
(frames/frame-theorem! 'i9-res-rest-mark-edge 'i9-res-rest 'well-formed-mark-edge)
(frames/frame-theorem! 'i9-res-rest-unmark-edge 'i9-res-rest 'well-formed-unmark-edge)
(frames/frame-theorem! 'i9-res-rest-remove-edge 'i9-res-rest 'well-formed-remove-edge)
(doseq [o '[well-formed-source-ins-fresh well-formed-fork-ins-fresh well-formed-scope-ins-fresh well-formed-comp-ins-fresh well-formed-act-ins-fresh well-formed-task-ins-fresh]]
  (prim! G9 o (list 'i9-res-rest-bump (list (symbol (str/replace (subs (name o) 12) "-fresh" "")) 'w 'r)
                    (list 'Eq.trans '(rfl) 'R))))
(prim! G9 'well-formed-bump '(i9-res-rest-bump w R))
(prim! G9 'well-formed-insert-edge-fresh '(i9-res-rest-bump (insert-edge w (edge-set-id (:next-id w) e)) (Eq.trans (rfl) R)))
(prim! G9 'well-formed-run-ins-fresh '(i9-res-run-ins w r h0 R))
(prim! G9 'well-formed-run-del '(i9-res-rest-run-del w x R))
(prim! G9 'well-formed-resource-del '(i9-res-rest-resource-del w x R))
(prim! G9 'well-formed-filter-world '(i9-res-filter w K R))
(swap! (:renames G9) assoc 'well-formed-run-upd 'i9-res-run-upd)

;; a token outside a cleanup slice holds a run that is not unwinding (the tree's pass at T17's arm-park,
;; from transition's guard arm-refused)
(a/theorem cleanup-not-unw [w :- World, st :- Nat, r :- RunRow]
  (=> (= (in-cleanup w st) false) (= (tok-run w st) (Option.some RunRow r)) (= (run-unwinding r) false))
  (intros hc ht) (simp only [in-cleanup ht opt-test] at hc) (exact hc))

;; ===========================================================================
;; Part E. P3, the core: the Rule R filter is edge-safe in a normalized world with the
;; reference invariants below (no transition reasoning here; their preservation through the step
;; is spindel.v2.inv.base's `round-facts` bundle, `step-rule-r-safe`)
;;
;;   dep-active   the creditor of a dep edge is a computation that is not idle (I7's edge part)
;;   acts-run     every activation's run row exists (with acts-alive: it is not done)
;;   marked-dep   a marked edge is a dep edge
;;   edge-sep     no edge id is a cleanup row or a storage ref (kind separation)
;; ===========================================================================

(a/defn not-idle-if-id [x :- Nat, c :- CompRow] Bool (Bool.or (Bool.not (Nat.beq (:id c) x)) (Bool.not (:idle c))))
(a/defn dep-active [cs :- (List CompRow), e :- EdgeRow] Bool
  (Bool.or (Bool.not (Nat.beq (:kind e) ek-dep)) (tbl-all (not-idle-if-id (:creditor e)) cs)))
(a/defn act-run-has [rs :- (List RunRow), a :- ActRow] Bool (tbl-has run-id (:run a) rs))
;; C1 Q6: a dep edge's creditor is no tombstone (spindel.v2.inv.tomb carries it through the step), so a
;; normalized world has it live
(a/defn nt-if-id [x :- Nat, c :- CompRow] Bool (Bool.or (Bool.not (Nat.beq (:id c) x)) (Bool.not (:tomb c))))
(a/defn untomb [cs :- (List CompRow), x :- Nat] Bool (tbl-all (nt-if-id x) cs))
(a/defn dep-untomb [cs :- (List CompRow), e :- EdgeRow] Bool
  (Bool.or (Bool.not (Nat.beq (:kind e) ek-dep)) (untomb cs (:creditor e))))
(a/defn refs-untomb [w :- World] Bool (tbl-all (dep-untomb (:comps w)) (:edges w)))
(a/defn marked-dep [e :- EdgeRow] Bool (Bool.or (Bool.not (:marked e)) (Nat.beq (:kind e) ek-dep)))
(a/defn edge-sep [w :- World, e :- EdgeRow] Bool
  (Bool.and (Bool.not (reach-mem (:id e) (cleanup-rows w))) (Bool.not (reach-mem (:id e) (storage w)))))
(a/defn p3-refs [w :- World] Bool
  (Bool.and (tbl-all (dep-active (:comps w)) (:edges w))
  (Bool.and (tbl-all (act-run-has (:runs w)) (:acts w))
  (Bool.and (tbl-all marked-dep (:edges w)) (tbl-all (edge-sep w) (:edges w))))))

;; ---- live is closed under the §3.2 successors

(a/theorem live-close [w :- World, x :- Nat, y :- Nat]
  (=> (= (in-live w x) true) (= (reach-mem y (retain-succ w x)) true) (= (in-live w y) true))
  (intros hx hy)
  (have hc := (live-converged-all w))
  (have rx := (Iff.mp (in-live-iff w x hc) hx))
  (exact (Iff.mpr (in-live-iff w y hc) (Reach.step x y rx (Iff.mp (reach-mem-iff y (retain-succ w x)) hy)))))

(a/theorem rm-app-l [x :- Nat, a :- (List Nat), b :- (List Nat)]
  (=> (= (reach-mem x a) true) (= (reach-mem x (List.append Nat a b)) true))
  (intro h) (simp only [reach-mem-append h Bool.true_or]))
(a/theorem rm-app-r [x :- Nat, a :- (List Nat), b :- (List Nat)]
  (=> (= (reach-mem x b) true) (= (reach-mem x (List.append Nat a b)) true))
  (intro h) (simp only [reach-mem-append h Bool.or_true]))
(a/theorem rm-nz [x :- Nat] (=> (= (Nat.beq x 0) false) (= (reach-mem x (nz x)) true))
  (intro h) (simp only [nz h reach-mem Nat.beq_refl]))

(a/theorem succ-edge [w :- World, e :- EdgeRow]
  (=> (List.Mem e (:edges w)) (= (Nat.beq (:debtor e) 0) false) (= (reach-mem (:debtor e) (retain-succ w (:id e))) true))
  (intros hm hd)
  (simp only [retain-succ])
  (apply rm-app-r) (apply rm-app-r) (apply rm-app-r) (apply rm-app-r) (apply rm-app-r) (apply rm-app-l)
  (exact (gather-mem EdgeRow (id-is edge-id (:id e)) edge-contrib e (:debtor e) (:edges w) hm
           (Nat.beq_refl (:id e)) (rm-nz (:debtor e) hd))))

(a/theorem succ-act [w :- World, r :- RunRow, a :- ActRow]
  (=> (List.Mem r (:runs w)) (= (run-alive r) true) (List.Mem a (:acts w)) (= (Nat.beq (:run a) (:id r)) true)
      (= (reach-mem (:id a) (retain-succ w (:id r))) true))
  (intros hr ha hm he)
  (simp only [retain-succ])
  (apply rm-app-r) (apply rm-app-r) (apply rm-app-r) (apply rm-app-l)
  (apply (gather-mem RunRow (id-is run-id (:id r)) (run-contrib w) r (:id a) (:runs w) hr (Nat.beq_refl (:id r))))
  (simp only [run-contrib ha])
  (apply rm-app-r) (apply rm-app-r) (apply rm-app-l)
  (exact (scan-mem ActRow act-id (act-of-run (:id r)) a (:acts w) hm he)))

(a/theorem succ-dep [w :- World, c :- CompRow, e :- EdgeRow]
  (=> (List.Mem c (:comps w)) (= (:idle c) false) (List.Mem e (:edges w)) (= (dep-of (:id c) e) true)
      (= (reach-mem (:id e) (retain-succ w (:id c))) true))
  (intros hc hi hm hd)
  (simp only [retain-succ])
  (apply rm-app-r) (apply rm-app-l)
  (apply (gather-mem CompRow (id-is comp-id (:id c)) (comp-contrib w) c (:id e) (:comps w) hc (Nat.beq_refl (:id c))))
  (simp only [comp-contrib hi])
  (apply rm-app-r) (apply rm-app-l)
  (exact (scan-mem EdgeRow edge-id (dep-of (:id c)) e (:edges w) hm hd)))

;; ---- ids: an edge's debtor is a row id (> 0); an edge id is admitted by nothing

(a/theorem has-pos [A :- Type, idf :- (=> A Nat), d :- Nat, n :- Nat, xs :- (List A)]
  (=> (= (tbl-all (id-in-range n) (tbl-ids idf xs)) true) (= (tbl-has idf d xs) true) (= (Nat.beq d 0) false))
  (intros hr hh)
  (have hm (= (nat-mem d (tbl-ids idf xs)) true)) (rw [nat-mem-ids]) (exact hh)
  (have r := (all-nat-mem (id-in-range n) d _ hr hm))
  (simp only [id-in-range Bool.and_eq_true Nat.blt_eq] at r)
  (cases hb (Nat.beq d 0))
  (case [false] (rfl))
  (case [true] (have e (= d 0)) (exact (Nat.eq_of_beq_eq_true hb)) (rw [e] at r) (omega)))

(a/theorem deb-nz [w :- World, e :- EdgeRow]
  (=> (= (well-formed w) true) (List.Mem e (:edges w)) (= (Nat.beq (:debtor e) 0) false))
  (intros h hm)
  (have ho := (tbl-all-mem EdgeRow (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w)) e (:edges w)
                (And.left (And.right (well-formed-parts w h))) hm))
  (simp only [edge-ok deb-ok Bool.and_eq_true Bool.or_eq_true] at ho)
  (have hb := (ids-below-of w h))
  (simp only [all-ids tbl-all-nat-app Bool.and_eq_true] at hb)
  (have hdo := (And.right ho))
  (cases hdo)
  (case [inl h1] (exact (has-pos CompRow comp-id (:debtor e) (:next-id w) (:comps w) (And.left (And.right hb)) h1)))
  (case [inr h2]
    (cases h2)
    (case [inl h3] (exact (has-pos TaskRow task-id (:debtor e) (:next-id w) (:tasks w) (And.left (And.right (And.right hb))) h3)))
    (case [inr h4]
      (cases h4)
      (case [inl h5] (exact (has-pos SourceRow source-id (:debtor e) (:next-id w) (:sources w)
                              (And.left (And.right (And.right (And.right (And.right hb))))) h5)))
      (case [inr h6] (exact (has-pos ResRow resource-id (:debtor e) (:next-id w) (:res w)
                              (And.left (And.right (And.right (And.right (And.right (And.right (And.right (And.right hb)))))))) (And.right h6)))))))

(a/theorem any-has-id [A :- Type, idf :- (=> A Nat), p :- (=> A Bool), y :- Nat,
                       h :- (forall [a :- A] (=> (= (p a) true) (= (Nat.beq (idf a) y) true))), xs :- (List A)]
  (=> (= (tbl-any p xs) true) (= (nat-mem y (tbl-ids idf xs)) true))
  (induction xs)
  (case [nil] (intro ha) (simp [tbl-any] at ha))
  (case [cons hd t ih]
    (intro ha)
    (cases hp (p hd))
    (case [true] (simp only [tbl-ids nat-mem (h hd hp)]))
    (case [false]
      (simp only [tbl-any hp Bool.false_or] at ha)
      (cases hx (Nat.beq (idf hd) y))
      (all_goals (simp only [tbl-ids nat-mem hx (ih ha)])))))

(a/theorem and-beq [b :- Nat, y :- Nat, c :- Bool] (=> (= (Bool.and (Nat.beq b y) c) true) (= (Nat.beq b y) true))
  (intro h) (simp only [Bool.and_eq_true] at h) (exact (And.left h)))

(a/theorem mem-app-l [x :- Nat, xs :- (List Nat), ys :- (List Nat)]
  (=> (= (nat-mem x xs) true) (= (nat-mem x (nat-app xs ys)) true))
  (intro h) (simp only [nat-mem-app h Bool.true_or]))
(a/theorem mem-app-r [x :- Nat, xs :- (List Nat), ys :- (List Nat)]
  (=> (= (nat-mem x ys) true) (= (nat-mem x (nat-app xs ys)) true))
  (intro h) (simp only [nat-mem-app h Bool.or_true]))

(a/theorem not-both [x :- Nat, xs :- (List Nat), ys :- (List Nat)]
  (=> (= (nat-nodup (nat-app xs ys)) true) (= (nat-mem x xs) true) (= (nat-mem x ys) true) False)
  (intros hn h1 h2)
  (have d := (nodup-app-disj x xs ys hn h1))
  (rw [h2] at d) (cases d))

(a/theorem edge-not-admitted [w :- World, e :- EdgeRow]
  (=> (= (well-formed w) true) (List.Mem e (:edges w)) (= (admitted w (:id e)) false))
  (intros h hm)
  (have he := (mem-ids-has EdgeRow edge-id e (:edges w) hm))
  (have u := (ids-unique-of w h))
  (simp only [all-ids] at u)
  (have u1 := (nat-nodup-app-right _ _ u))
  (have u2 := (nat-nodup-app-right _ _ u1))
  (have u3 := (nat-nodup-app-right _ _ u2))
  (have u4 := (nat-nodup-app-right _ _ u3))
  (have u5 := (nat-nodup-app-right _ _ u4))
  (cases a1 (tbl-any (adm-comp (:id e)) (:comps w)))
  (case [true]
    (have m := (any-has-id CompRow comp-id (adm-comp (:id e)) (:id e)
                 (fn [c :- CompRow, hc :- (= (adm-comp (:id e) c) true)] (and-beq (:id c) (:id e) _ hc)) (:comps w) a1))
    (exact (False.elim (not-both (edge-id e) _ _ u1 m (mem-app-r _ _ _ (mem-app-r _ _ _ (mem-app-r _ _ _ (mem-app-l _ _ _ he))))))))
  (case [false]
    (cases a2 (tbl-any (adm-source (:id e)) (:sources w)))
    (case [true]
      (have m := (any-has-id SourceRow source-id (adm-source (:id e)) (:id e)
                   (fn [c :- SourceRow, hc :- (= (adm-source (:id e) c) true)] (and-beq (:id c) (:id e) _ hc)) (:sources w) a2))
      (exact (False.elim (not-both (edge-id e) _ _ u4 m (mem-app-l _ _ _ he)))))
    (case [false]
      (cases a3 (tbl-any (adm-task (:id e)) (:tasks w)))
      (case [true]
        (have m := (any-has-id TaskRow task-id (adm-task (:id e)) (:id e)
                     (fn [c :- TaskRow, hc :- (= (adm-task (:id e) c) true)] (and-beq (:id c) (:id e) _ hc)) (:tasks w) a3))
        (exact (False.elim (not-both (edge-id e) _ _ u2 m (mem-app-r _ _ _ (mem-app-r _ _ _ (mem-app-l _ _ _ he)))))))
      (case [false]
        (cases a4 (tbl-any (adm-pub (:id e)) (:pubs w)))
        (case [true]
          (have m := (any-has-id PubRow pub-id (adm-pub (:id e)) (:id e)
                       (fn [c :- PubRow, hc :- (= (adm-pub (:id e) c) true)] (and-beq (:id c) (:id e) _ hc)) (:pubs w) a4))
          (exact (False.elim (not-both (edge-id e) _ _ u5 he (mem-app-r _ _ _ (mem-app-r _ _ _ (mem-app-l _ _ _ m)))))))
        (case [false] (simp only [admitted a1 a2 a3 a4 Bool.or_self]))))))

(a/theorem p3-parts [w :- World]
  (=> (= (p3-refs w) true)
      (And (= (tbl-all (dep-active (:comps w)) (:edges w)) true)
      (And (= (tbl-all (act-run-has (:runs w)) (:acts w)) true)
      (And (= (tbl-all marked-dep (:edges w)) true) (= (tbl-all (edge-sep w) (:edges w)) true)))))
  (intro h) (simp only [p3-refs Bool.and_eq_true] at h) (exact h))

;; a dep edge's creditor is live
(a/theorem bool-contra [b :- Bool] (=> (= b true) (= b false) False)
  (intros h1 h2) (rw [h1] at h2) (cases h2))

(a/theorem dep-cred-live [w :- World, e :- EdgeRow]
  (=> (= (well-formed w) true) (= (normalized w) true) (= (p3-refs w) true) (= (refs-untomb w) true) (List.Mem e (:edges w))
      (= (Nat.beq (:kind e) ek-dep) true)
      (And (= (in-live w (:creditor e)) true)
           (forall [c :- CompRow] (=> (= (tbl-find comp-id (:creditor e) (:comps w)) (Option.some CompRow c))
                                      (And (List.Mem c (:comps w)) (And (= (:idle c) false) (= (:id c) (:creditor e))))))))
  (intros h hn hp hu hm hk)
  (have ho := (tbl-all-mem EdgeRow (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w)) e (:edges w)
                (And.left (And.right (well-formed-parts w h))) hm))
  (simp only [edge-ok cred-ok hk Bool.and_eq_true] at ho)
  (have hut := (tbl-all-mem EdgeRow (dep-untomb (:comps w)) e (:edges w) hu hm))
  (simp only [dep-untomb hk Bool.not_true Bool.false_or] at hut)
  (have hda := (tbl-all-mem EdgeRow (dep-active (:comps w)) e (:edges w) (And.left (p3-parts w hp)) hm))
  (simp only [dep-active hk Bool.not_true Bool.false_or] at hda)
  (have hc (forall [c :- CompRow] (=> (= (tbl-find comp-id (:creditor e) (:comps w)) (Option.some CompRow c))
                                      (And (List.Mem c (:comps w)) (And (= (:idle c) false) (= (:id c) (:creditor e)))))))
  (intros c hf)
  (have cm := (tbl-find-mem CompRow comp-id (:creditor e) c (:comps w) hf))
  (have ci (= (:id c) (:creditor e))) (exact (tbl-find-id CompRow comp-id (:creditor e) c (:comps w) hf))
  (have cn := (tbl-all-mem CompRow (not-idle-if-id (:creditor e)) c (:comps w) hda cm))
  (have ci2 (= (Nat.beq (:id c) (:creditor e)) true)) (rw [ci]) (exact (Nat.beq_refl (:creditor e)))
  (simp only [not-idle-if-id ci2 Bool.not_true Bool.false_or] at cn)
  (exact (And.intro cm (And.intro (bnot-true _ cn) ci)))
  (have hlive (= (in-live w (:creditor e)) true))
  (cases hf (tbl-find comp-id (:creditor e) (:comps w)))
  (case [none] (have hn2 := (tbl-find-none-has CompRow comp-id (:creditor e) (:comps w) hf)) (exact (False.elim (bool-contra _ (And.left ho) hn2))))
  (case [some c]
    (have p := (hc c hf))
    (have nt := (tbl-all-mem CompRow (nt-if-id (:creditor e)) c (:comps w) hut (And.left p)))
    (have ci3 (= (Nat.beq (:id c) (:creditor e)) true)) (rw [(And.right (And.right p))]) (exact (Nat.beq_refl (:creditor e)))
    (simp only [nt-if-id ci3 Bool.not_true Bool.false_or] at nt)
    (have hl := (normalized-comps w c hn (And.left p) (And.left (And.right p)) (bnot-true _ nt)))
    (exact (Eq.trans (congrArg (fn [x :- Nat] (in-live w x)) (Eq.symm (And.right (And.right p)))) hl)))
  (exact (And.intro hlive hc)))

(a/theorem cred-kept [w :- World, e :- EdgeRow]
  (=> (= (well-formed w) true) (= (acts-alive w) true) (= (normalized w) true) (= (p3-refs w) true) (= (refs-untomb w) true) (List.Mem e (:edges w))
      (= (Bool.or (host-cred e) (keep-fn w (:creditor e))) true))
  (intros h ha hn hp hu hm)
  (cases hk (Nat.beq (:kind e) ek-dep))
  (case [true]
    (simp only [(keep-of-live w (:creditor e) (And.left (dep-cred-live w e h hn hp hu hm hk))) Bool.or_true]))
  (case [false]
    (cases hh (host-cred e))
    (case [true] (simp only [Bool.true_or]))
    (case [false]
      (have ho := (tbl-all-mem EdgeRow (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w)) e (:edges w)
                    (And.left (And.right (well-formed-parts w h))) hm))
      (simp only [edge-ok cred-ok hk hh Bool.and_eq_true] at ho)
      (cases hf (tbl-find act-id (:creditor e) (:acts w)))
      (case [none] (have hn2 := (tbl-find-none-has ActRow act-id (:creditor e) (:acts w) hf)) (exact (False.elim (bool-contra _ (And.left ho) hn2))))
      (case [some a]
        (have am := (tbl-find-mem ActRow act-id (:creditor e) a (:acts w) hf))
        (have ai (= (:id a) (:creditor e))) (exact (tbl-find-id ActRow act-id (:creditor e) a (:acts w) hf))
        (have hrh := (tbl-all-mem ActRow (act-run-has (:runs w)) a (:acts w) (And.left (And.right (p3-parts w hp))) am))
        (simp only [act-run-has] at hrh)
        (cases hr (tbl-find run-id (:run a) (:runs w)))
        (case [none] (have hn3 := (tbl-find-none-has RunRow run-id (:run a) (:runs w) hr)) (exact (False.elim (bool-contra _ hrh hn3))))
        (case [some r]
          (have rm := (tbl-find-mem RunRow run-id (:run a) r (:runs w) hr))
          (have ri (= (:id r) (:run a))) (exact (tbl-find-id RunRow run-id (:run a) r (:runs w) hr))
          (have hok := (tbl-all-mem RunRow (run-ok-for (:run a)) r (:runs w) (tbl-all-mem ActRow (act-run-ok (:runs w)) a (:acts w) ha am) rm))
          (have ri2 (= (Nat.beq (:id r) (:run a)) true)) (rw [ri]) (exact (Nat.beq_refl (:run a)))
          (simp only [run-ok-for ri2 Bool.not_true Bool.false_or] at hok)
          (have rl := (normalized-runs w r hn rm hok))
          (have ar (= (Nat.beq (:run a) (:id r)) true)) (rw [ri]) (exact (Nat.beq_refl (:run a)))
          (have al := (live-close w (:id r) (:id a) rl (succ-act w r a rm hok am ar)))
          (have al2 := (Eq.trans (congrArg (fn [x :- Nat] (in-live w x)) (Eq.symm ai)) al))
          (simp only [(keep-of-live w (:creditor e) al2) Bool.or_true]))))))

(a/theorem filter-keeps-ends-ok [w :- World, e :- EdgeRow]
  (=> (= (well-formed w) true) (= (acts-alive w) true) (= (normalized w) true) (= (p3-refs w) true) (= (refs-untomb w) true) (List.Mem e (:edges w))
      (= (filter-keeps-ends (keep-fn w) e) true))
  (intros h ha hn hp hu hm)
  (cases hl (in-live w (:id e)))
  (case [true]
    (have dl := (live-close w (:id e) (:debtor e) hl (succ-edge w e hm (deb-nz w e h hm))))
    (simp only [filter-keeps-ends (cred-kept w e h ha hn hp hu hm) (keep-of-live w (:debtor e) dl) Bool.and_self Bool.or_true]))
  (case [false]
    (have hs := (tbl-all-mem EdgeRow (edge-sep w) e (:edges w) (And.right (And.right (And.right (p3-parts w hp)))) hm))
    (simp only [edge-sep Bool.and_eq_true] at hs)
    (have hl2 (= (reach-mem (:id e) (live-list w)) false)) (exact hl)
    (have k0 (= (keep-fn w (:id e)) false))
    (simp only [keep-fn keep-with hl2 (bnot-true _ (And.left hs)) (bnot-true _ (And.right hs)) (edge-not-admitted w e h hm) Bool.or_self])
    (simp only [filter-keeps-ends k0 Bool.not_false Bool.true_or])))

(a/theorem filter-keeps-marked-ok [w :- World, e :- EdgeRow]
  (=> (= (well-formed w) true) (= (normalized w) true) (= (p3-refs w) true) (= (refs-untomb w) true) (List.Mem e (:edges w))
      (= (filter-keeps-marked (keep-fn w) e) true))
  (intros h hn hp hu hm)
  (cases hk (:marked e))
  (case [false] (simp only [filter-keeps-marked hk Bool.false_and Bool.not_false Bool.true_or]))
  (case [true]
    (have hd := (tbl-all-mem EdgeRow marked-dep e (:edges w) (And.left (And.right (And.right (p3-parts w hp)))) hm))
    (simp only [marked-dep hk Bool.not_true Bool.false_or] at hd)
    (have q := (dep-cred-live w e h hn hp hu hm hd))
    (cases hf (tbl-find comp-id (:creditor e) (:comps w)))
    (case [none]
      (have ho := (tbl-all-mem EdgeRow (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w)) e (:edges w)
                    (And.left (And.right (well-formed-parts w h))) hm))
      (simp only [edge-ok cred-ok hd Bool.and_eq_true] at ho)
      (have hn2 := (tbl-find-none-has CompRow comp-id (:creditor e) (:comps w) hf)) (exact (False.elim (bool-contra _ (And.left ho) hn2))))
    (case [some c]
      (have p := ((And.right q) c hf))
      (have cl := (Eq.trans (congrArg (fn [x :- Nat] (in-live w x)) (And.right (And.right p))) (And.left q)))
      (have dep (= (dep-of (:id c) e) true)) (simp only [dep-of hd (And.right (And.right p)) Nat.beq_refl Bool.and_self])
      (have el := (live-close w (:id c) (:id e) cl (succ-dep w c e (And.left p) (And.left (And.right p)) hm dep)))
      (simp only [filter-keeps-marked (keep-of-live w (:id e) el) Bool.or_true]))))

;; Theorem (P3 core): in a normalized world with the reference invariants, the filter is edge-safe
(a/theorem filter-safe-of-refs [w :- World]
  (=> (= (well-formed w) true) (= (acts-alive w) true) (= (normalized w) true) (= (p3-refs w) true) (= (refs-untomb w) true)
      (= (filter-safe w) true))
  (intros h ha hn hp hu)
  (simp only [filter-safe filter-safe-for Bool.and_eq_true])
  (exact (And.intro
           (all-of-mem EdgeRow (filter-keeps-ends (keep-fn w)) (:edges w) (fn [e :- EdgeRow, hm :- (List.Mem e (:edges w))] (filter-keeps-ends-ok w e h ha hn hp hu hm)))
           (all-of-mem EdgeRow (filter-keeps-marked (keep-fn w)) (:edges w) (fn [e :- EdgeRow, hm :- (List.Mem e (:edges w))] (filter-keeps-marked-ok w e h hn hp hu hm))))))

;; ===========================================================================
;; C1 Q6: the demotion's row is the idle row or the tombstone row (unique ids pick the one row)
;; ===========================================================================

(a/theorem tbl-upd-congr [A :- Type, idf :- (=> A Nat), x :- Nat, f :- (=> A A), g :- (=> A A), P :- (=> A Bool),
                          hfg :- (forall [r :- A] (=> (= (P r) true) (= (f r) (g r)))), xs :- (List A)]
  (=> (= (tbl-all (same-id-then idf x P) xs) true) (= (tbl-upd idf x f xs) (tbl-upd idf x g xs)))
  (induction xs)
  (case [nil] (intro hp) (rfl))
  (case [cons h t ih]
    (intro hp)
    (simp only [tbl-all Bool.and_eq_true] at hp)
    (have e := (ih (And.right hp)))
    (cases hx (Nat.beq (idf h) x))
    (case [false] (simp only [tbl-upd hx]) (rw [e]))
    (case [true]
      (have hq := (And.left hp))
      (simp only [same-id-then hx Bool.not_true Bool.false_or] at hq)
      (simp only [tbl-upd hx]) (rw [e (hfg h hq)]))))

(a/theorem demote-row-idle-upd [w :- World, cid :- Nat, c :- CompRow, vs :- (List Valid)]
  (=> (= (well-formed w) true) (= (comp-find w cid) (Option.some CompRow c)) (= (demote-idle c) true)
      (= (comp-upd w cid (comp-demote-row vs)) (comp-upd w cid (comp-make-idle vs))))
  (intros h hf hd)
  (have hm := (tbl-find-mem CompRow comp-id cid c (:comps w) hf))
  (have ei (= (comp-id c) cid)) (exact (tbl-find-id CompRow comp-id cid c (:comps w) hf))
  (have u := (uniq-all CompRow comp-id demote-idle c (:comps w) (comps-nodup w h) hm hd))
  (rw [ei] at u)
  (simp only [comp-upd])
  (rw [(tbl-upd-congr CompRow comp-id cid (comp-demote-row vs) (comp-make-idle vs) demote-idle
         (fn [r :- CompRow, hr :- (= (demote-idle r) true)] (comp-demote-row-idle vs r hr)) (:comps w) u)]))

(a/defn demote-tomb [c :- CompRow] Bool (Bool.not (demote-idle c)))
(a/theorem demote-row-tomb-upd [w :- World, cid :- Nat, c :- CompRow, vs :- (List Valid)]
  (=> (= (well-formed w) true) (= (comp-find w cid) (Option.some CompRow c)) (= (demote-idle c) false)
      (= (comp-upd w cid (comp-demote-row vs)) (comp-upd w cid comp-tomb-row)))
  (intros h hf hd)
  (have hm := (tbl-find-mem CompRow comp-id cid c (:comps w) hf))
  (have ei (= (comp-id c) cid)) (exact (tbl-find-id CompRow comp-id cid c (:comps w) hf))
  (have hd2 (= (demote-tomb c) true)) (simp only [demote-tomb hd Bool.not_false])
  (have u := (uniq-all CompRow comp-id demote-tomb c (:comps w) (comps-nodup w h) hm hd2))
  (rw [ei] at u)
  (simp only [comp-upd])
  (rw [(tbl-upd-congr CompRow comp-id cid (comp-demote-row vs) comp-tomb-row demote-tomb
         (fn [r :- CompRow, hr :- (= (demote-tomb r) true)] (comp-demote-row-tomb vs r (bnot-true _ hr))) (:comps w) u)]))
