(ns spindel.v2.inv.i10
  "Literal I10, computation part (`lit-i10-current`: a computation has at most one current run,
  R.epoch = C.epoch) through the step, kernel-checked (Init only).

  Bundle i10-current-exempt gxz gkz = well-formed and, over the key lists of runs (id, of, epoch, alive),
  computations (id, epoch, done-epoch, run, idle) and tasks (id, run):
    E1   a run's epoch is at most its computation's epoch;
    E2   a current run is C.run, C is not idle, and the run is alive or C.done-epoch = C.epoch
         (`cur-fin`, exempt for the computations in gxz: those demoted later in the same
         normalization round, whose current run the round's stray cancel ended);
    rof  C.run / K.run name a run of C / K; run `of` and run pointers are below the allocator,
         computation epochs are >= 1.
  The runs in gkz are exempt from E1/E2/rof (a run being retired: C.run is cleared before the
  row goes). The bundle goes through the generic step tree (spindel.v2.pres.tree; its table is in
  Part B); its own proofs:
    cascade  a cancel job needs `job-ok` (the run is no current run of a computation outside gxz),
             kept through every job (transport bundle i10-current-transport, pair predicates over (id, of, epoch) x
             (id, epoch, idle) that an epoch step keeps) and met by every caller: task runs (T14 host,
             T6 losers, T12 children), the stale predecessor (T11), the demotion's own cancels, the
             round's stray cancels (a computation outside the strays is idle or keeps its current run
             live, `stray-pair`);
    T12      the current run sets done-epoch := epoch (computation exempt in between); stale and task
             runs are no current runs;
    T13      C.run cleared with the run exempt until run-del;
    T4/T5/T11  the new run (`i10-current-exempt-keys-ok-new-run`): T11 carries `kcq` (C keeps an epoch >= its old one,
             stays awake, has no run at it) through the predecessor's cancel, the cut and the entry;
             T5 at gxz = gkz = [] (bundle i10-current, every other raw lemma is G10's instantiated):
             a current run would be alive or completed, against `startable` (`start-cur`);
    demote   ends with no current run of C (epoch step, or none was current) and drops C from gxz.
  Theorems: step-i10-current (i10-current w, rule-r-safe raw -> i10-current (world-step w it)), i10-current-lit-i10,
  step-lit-i10-current; chain-to-i10-current = chain-start && i10-current with step-chain-to-i10-current, chain-to-i10-current-empty and step-lit-i10-current-total
  (no honest hypothesis)."
  (:require [ansatz.core :as a]
            [spindel.v2.pres.exempt :as exempt]
            [spindel.v2.pres.tree :as tree]
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
            [spindel.v2.inv.copier :refer :all]
            [spindel.v2.inv.idle :refer :all]
            [spindel.v2.inv.base :refer :all]
            [spindel.v2.inv.tomb :refer :all]))

;; ===========================================================================
;; Part A. Keys and the invariant
;; ===========================================================================

(a/structure I10CurrentRunKey [] (id Nat) (of Nat) (epoch Nat) (alive Bool))
(a/defn i10-current-run-key [r :- RunRow] I10CurrentRunKey (I10CurrentRunKey.mk (:id r) (:of r) (:epoch r) (run-alive r)))
(a/defn i10-current-run-key-id [k :- I10CurrentRunKey] Nat (:id k))
(a/structure I10CurrentCompKey [] (id Nat) (epoch Nat) (done Nat) (run Nat) (idle Bool))
(a/defn i10-current-comp-key [c :- CompRow] I10CurrentCompKey (I10CurrentCompKey.mk (:id c) (:epoch c) (:done-epoch c) (:run c) (:idle c)))
(a/defn i10-current-comp-key-id [k :- I10CurrentCompKey] Nat (:id k))
(a/structure I10CurrentTaskKey [] (id Nat) (run Nat))
(a/defn i10-current-task-key [t :- TaskRow] I10CurrentTaskKey (I10CurrentTaskKey.mk (:id t) (:run t)))
(a/defn i10-current-task-key-id [k :- I10CurrentTaskKey] Nat (:id k))
(a/defn i10-current-run-keys [rs :- (List RunRow)] (List I10CurrentRunKey)
  (match rs [nil (List.nil I10CurrentRunKey)] [(cons h t) (List.cons I10CurrentRunKey (i10-current-run-key h) (i10-current-run-keys t))]))
(a/defn i10-current-comp-keys [cs :- (List CompRow)] (List I10CurrentCompKey)
  (match cs [nil (List.nil I10CurrentCompKey)] [(cons h t) (List.cons I10CurrentCompKey (i10-current-comp-key h) (i10-current-comp-keys t))]))
(a/defn i10-current-task-keys [ts :- (List TaskRow)] (List I10CurrentTaskKey)
  (match ts [nil (List.nil I10CurrentTaskKey)] [(cons h t) (List.cons I10CurrentTaskKey (i10-current-task-key h) (i10-current-task-keys t))]))

;; a run r of computation c: its epoch is at most C.epoch; a current run (R.epoch = C.epoch) is
;; C.run, C is not idle, and (`cur-fin`) the run is alive or C's result is of this epoch, unless C
;; is in the exempt list gxz (a computation demoted later in the same normalization round)
(a/defn cur-core [r :- I10CurrentRunKey, c :- I10CurrentCompKey, x :- Bool] Bool
  (Bool.or (Bool.not (Nat.beq (:of r) (:id c)))
   (Bool.and (Nat.ble (:epoch r) (:epoch c))
    (Bool.or (Bool.not (Nat.beq (:epoch r) (:epoch c)))
     (Bool.and (Nat.beq (:run c) (:id r)) (Bool.and (Bool.not (:idle c)) x))))))
(a/defn cur-fin [gxz :- (List Nat), r :- I10CurrentRunKey, c :- I10CurrentCompKey] Bool
  (Bool.or (reach-mem (:id c) gxz) (Bool.or (:alive r) (Nat.beq (:done c) (:epoch c)))))
(a/defn cur-pair [gxz :- (List Nat), r :- I10CurrentRunKey, c :- I10CurrentCompKey] Bool (cur-core r c (cur-fin gxz r c)))
;; C.run names a run of C
(a/defn rof-pair [r :- I10CurrentRunKey, c :- I10CurrentCompKey] Bool
  (Bool.or (Nat.beq (:id r) 0) (Bool.or (Bool.not (Nat.beq (:id r) (:run c))) (Nat.beq (:of r) (:id c)))))
;; the runs in gkz are exempt (a run being retired: C.run is cleared before the row goes)
(a/defn rc-ok [gxz :- (List Nat), gkz :- (List Nat), r :- I10CurrentRunKey, c :- I10CurrentCompKey] Bool
  (Bool.or (reach-mem (:id r) gkz) (Bool.and (cur-pair gxz r c) (rof-pair r c))))
;; K.run names a run of K
(a/defn tof-pair [r :- I10CurrentRunKey, t :- I10CurrentTaskKey] Bool
  (Bool.or (Nat.beq (:id r) 0) (Bool.or (Bool.not (Nat.beq (:id r) (:run t))) (Nat.beq (:of r) (:id t)))))
(a/defn i10-current-run-ok [gxz :- (List Nat), gkz :- (List Nat), cks :- (List I10CurrentCompKey), tks :- (List I10CurrentTaskKey), n :- Nat, r :- I10CurrentRunKey] Bool
  (Bool.and (tbl-all (rc-ok gxz gkz r) cks) (Bool.and (tbl-all (tof-pair r) tks) (Nat.blt (:of r) n))))
(a/defn below0 [n :- Nat, x :- Nat] Bool (Bool.or (Nat.beq x 0) (Nat.blt x n)))
(a/defn i10-current-comp-ok [n :- Nat, c :- I10CurrentCompKey] Bool (Bool.and (Nat.ble 1 (:epoch c)) (below0 n (:run c))))
(a/defn i10-current-task-ok [n :- Nat, t :- I10CurrentTaskKey] Bool (below0 n (:run t)))
(a/defn i10-current-exempt-keys-ok [gxz :- (List Nat), gkz :- (List Nat), rks :- (List I10CurrentRunKey), cks :- (List I10CurrentCompKey), tks :- (List I10CurrentTaskKey), n :- Nat] Bool
  (Bool.and (tbl-all (i10-current-run-ok gxz gkz cks tks n) rks) (Bool.and (tbl-all (i10-current-comp-ok n) cks) (tbl-all (i10-current-task-ok n) tks))))
(a/defn i10-current-exempt-rest [gxz :- (List Nat), gkz :- (List Nat), w :- World] Bool
  (i10-current-exempt-keys-ok gxz gkz (i10-current-run-keys (:runs w)) (i10-current-comp-keys (:comps w)) (i10-current-task-keys (:tasks w)) (:next-id w)))
(a/defn i10-current-exempt [gxz :- (List Nat), gkz :- (List Nat), w :- World] Bool (Bool.and (well-formed w) (i10-current-exempt-rest gxz gkz w)))

(a/theorem i10-current-exempt-well-formed [gxz :- (List Nat), gkz :- (List Nat), w :- World] (=> (= (i10-current-exempt gxz gkz w) true) (= (well-formed w) true))
  (intro h) (simp only [i10-current-exempt Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem i10-current-exempt-rest-of [gxz :- (List Nat), gkz :- (List Nat), w :- World] (=> (= (i10-current-exempt gxz gkz w) true) (= (i10-current-exempt-rest gxz gkz w) true))
  (intro h) (simp only [i10-current-exempt Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem i10-current-exempt-intro [gxz :- (List Nat), gkz :- (List Nat), w :- World]
  (=> (= (well-formed w) true) (= (i10-current-exempt-rest gxz gkz w) true) (= (i10-current-exempt gxz gkz w) true))
  (intros h1 h2) (simp only [i10-current-exempt h1 h2 Bool.and_self]))
(a/theorem i10-current-exempt-parts [gxz :- (List Nat), gkz :- (List Nat), w :- World]
  (=> (= (i10-current-exempt gxz gkz w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (i10-current-exempt-well-formed gxz gkz w h))))

;; ---- key lists under the table edits

(a/theorem i10-current-run-keys-upd [x :- Nat, f :- (=> RunRow RunRow), g :- (=> I10CurrentRunKey I10CurrentRunKey),
                      hc :- (forall [r :- RunRow] (= (i10-current-run-key (f r)) (g (i10-current-run-key r)))), rs :- (List RunRow)]
  (= (i10-current-run-keys (tbl-upd run-id x f rs)) (tbl-upd i10-current-run-key-id x g (i10-current-run-keys rs)))
  (induction rs)
  (case [nil] (simp only [tbl-upd i10-current-run-keys]))
  (case [cons h t ih]
    (cases hx (Nat.beq (run-id h) x))
    (case [false]
      (have hx2 (= (Nat.beq (i10-current-run-key-id (i10-current-run-key h)) x) false)) (exact hx)
      (simp only [tbl-upd hx i10-current-run-keys hx2 ih]))
    (case [true]
      (have hx2 (= (Nat.beq (i10-current-run-key-id (i10-current-run-key h)) x) true)) (exact hx)
      (simp only [tbl-upd hx i10-current-run-keys hx2 ih (hc h)]))))

(a/theorem i10-current-comp-keys-upd [x :- Nat, f :- (=> CompRow CompRow), g :- (=> I10CurrentCompKey I10CurrentCompKey),
                      hc :- (forall [c :- CompRow] (= (i10-current-comp-key (f c)) (g (i10-current-comp-key c)))), cs :- (List CompRow)]
  (= (i10-current-comp-keys (tbl-upd comp-id x f cs)) (tbl-upd i10-current-comp-key-id x g (i10-current-comp-keys cs)))
  (induction cs)
  (case [nil] (simp only [tbl-upd i10-current-comp-keys]))
  (case [cons h t ih]
    (cases hx (Nat.beq (comp-id h) x))
    (case [false]
      (have hx2 (= (Nat.beq (i10-current-comp-key-id (i10-current-comp-key h)) x) false)) (exact hx)
      (simp only [tbl-upd hx i10-current-comp-keys hx2 ih]))
    (case [true]
      (have hx2 (= (Nat.beq (i10-current-comp-key-id (i10-current-comp-key h)) x) true)) (exact hx)
      (simp only [tbl-upd hx i10-current-comp-keys hx2 ih (hc h)]))))

(a/theorem i10-current-task-keys-upd [x :- Nat, f :- (=> TaskRow TaskRow), g :- (=> I10CurrentTaskKey I10CurrentTaskKey),
                      hc :- (forall [t :- TaskRow] (= (i10-current-task-key (f t)) (g (i10-current-task-key t)))), ts :- (List TaskRow)]
  (= (i10-current-task-keys (tbl-upd task-id x f ts)) (tbl-upd i10-current-task-key-id x g (i10-current-task-keys ts)))
  (induction ts)
  (case [nil] (simp only [tbl-upd i10-current-task-keys]))
  (case [cons h t ih]
    (cases hx (Nat.beq (task-id h) x))
    (case [false]
      (have hx2 (= (Nat.beq (i10-current-task-key-id (i10-current-task-key h)) x) false)) (exact hx)
      (simp only [tbl-upd hx i10-current-task-keys hx2 ih]))
    (case [true]
      (have hx2 (= (Nat.beq (i10-current-task-key-id (i10-current-task-key h)) x) true)) (exact hx)
      (simp only [tbl-upd hx i10-current-task-keys hx2 ih (hc h)]))))

(a/theorem upd-id-same [A :- Type, idf :- (=> A Nat), x :- Nat, xs :- (List A)]
  (= (tbl-upd idf x (fn [a :- A] a) xs) xs)
  (induction xs)
  (case [nil] (simp only [tbl-upd]))
  (case [cons h t ih] (cases hx (Nat.beq (idf h) x)) (all_goals (simp only [tbl-upd hx ih]))))

(a/theorem i10-current-run-keys-same [x :- Nat, f :- (=> RunRow RunRow), hk :- (forall [r :- RunRow] (= (i10-current-run-key (f r)) (i10-current-run-key r))), rs :- (List RunRow)]
  (= (i10-current-run-keys (tbl-upd run-id x f rs)) (i10-current-run-keys rs))
  (exact (Eq.trans (i10-current-run-keys-upd x f (fn [k :- I10CurrentRunKey] k) hk rs) (upd-id-same I10CurrentRunKey i10-current-run-key-id x (i10-current-run-keys rs)))))
(a/theorem i10-current-comp-keys-same [x :- Nat, f :- (=> CompRow CompRow), hk :- (forall [c :- CompRow] (= (i10-current-comp-key (f c)) (i10-current-comp-key c))), cs :- (List CompRow)]
  (= (i10-current-comp-keys (tbl-upd comp-id x f cs)) (i10-current-comp-keys cs))
  (exact (Eq.trans (i10-current-comp-keys-upd x f (fn [k :- I10CurrentCompKey] k) hk cs) (upd-id-same I10CurrentCompKey i10-current-comp-key-id x (i10-current-comp-keys cs)))))
(a/theorem i10-current-task-keys-same [x :- Nat, f :- (=> TaskRow TaskRow), hk :- (forall [t :- TaskRow] (= (i10-current-task-key (f t)) (i10-current-task-key t))), ts :- (List TaskRow)]
  (= (i10-current-task-keys (tbl-upd task-id x f ts)) (i10-current-task-keys ts))
  (exact (Eq.trans (i10-current-task-keys-upd x f (fn [k :- I10CurrentTaskKey] k) hk ts) (upd-id-same I10CurrentTaskKey i10-current-task-key-id x (i10-current-task-keys ts)))))

(a/theorem i10-current-run-keys-del [x :- Nat, rs :- (List RunRow)] (= (i10-current-run-keys (tbl-del run-id x rs)) (tbl-del i10-current-run-key-id x (i10-current-run-keys rs)))
  (induction rs)
  (case [nil] (simp only [tbl-del i10-current-run-keys]))
  (case [cons h t ih]
    (have e (= (Nat.beq (i10-current-run-key-id (i10-current-run-key h)) x) (Nat.beq (run-id h) x))) (rfl)
    (cases hx (Nat.beq (run-id h) x)) (all_goals (simp only [tbl-del hx i10-current-run-keys e ih]))))
(a/theorem i10-current-comp-keys-del [x :- Nat, cs :- (List CompRow)] (= (i10-current-comp-keys (tbl-del comp-id x cs)) (tbl-del i10-current-comp-key-id x (i10-current-comp-keys cs)))
  (induction cs)
  (case [nil] (simp only [tbl-del i10-current-comp-keys]))
  (case [cons h t ih]
    (have e (= (Nat.beq (i10-current-comp-key-id (i10-current-comp-key h)) x) (Nat.beq (comp-id h) x))) (rfl)
    (cases hx (Nat.beq (comp-id h) x)) (all_goals (simp only [tbl-del hx i10-current-comp-keys e ih]))))
(a/theorem i10-current-run-keys-keep [K :- (=> Nat Bool), rs :- (List RunRow)] (= (i10-current-run-keys (tbl-keep K run-id rs)) (tbl-keep K i10-current-run-key-id (i10-current-run-keys rs)))
  (induction rs)
  (case [nil] (simp only [tbl-keep i10-current-run-keys]))
  (case [cons h t ih]
    (have e (= (K (i10-current-run-key-id (i10-current-run-key h))) (K (run-id h)))) (rfl)
    (cases hk (K (run-id h))) (all_goals (simp only [tbl-keep i10-current-run-keys e hk ih]))))
(a/theorem i10-current-comp-keys-keep [K :- (=> Nat Bool), cs :- (List CompRow)] (= (i10-current-comp-keys (tbl-keep K comp-id cs)) (tbl-keep K i10-current-comp-key-id (i10-current-comp-keys cs)))
  (induction cs)
  (case [nil] (simp only [tbl-keep i10-current-comp-keys]))
  (case [cons h t ih]
    (have e (= (K (i10-current-comp-key-id (i10-current-comp-key h))) (K (comp-id h)))) (rfl)
    (cases hk (K (comp-id h))) (all_goals (simp only [tbl-keep i10-current-comp-keys e hk ih]))))
(a/theorem i10-current-task-keys-keep [K :- (=> Nat Bool), ts :- (List TaskRow)] (= (i10-current-task-keys (tbl-keep K task-id ts)) (tbl-keep K i10-current-task-key-id (i10-current-task-keys ts)))
  (induction ts)
  (case [nil] (simp only [tbl-keep i10-current-task-keys]))
  (case [cons h t ih]
    (have e (= (K (i10-current-task-key-id (i10-current-task-key h))) (K (task-id h)))) (rfl)
    (cases hk (K (task-id h))) (all_goals (simp only [tbl-keep i10-current-task-keys e hk ih]))))

;; ---- the pair predicates under key changes

(a/theorem core-mono [r :- I10CurrentRunKey, c :- I10CurrentCompKey, x :- Bool, y :- Bool]
  (=> (= (cur-core r c x) true) (=> (= x true) (= y true)) (= (cur-core r c y) true))
  (intros h hxy)
  (cases y)
  (case [true]
    (cases x)
    (case [true] (exact h))
    (case [false]
      (simp only [cur-core Bool.and_false Bool.or_false] at h)
      (simp only [cur-core Bool.and_true])
      (cases ha (Nat.beq (:of r) (:id c)))
      (case [false] (simp only [ha Bool.not_false Bool.true_or]))
      (case [true]
        (simp only [ha Bool.not_true Bool.false_or Bool.and_eq_true] at h)
        (simp only [ha Bool.not_true Bool.false_or (And.left h) (And.right h) Bool.true_or Bool.true_and]))))
  (case [false]
    (cases x)
    (case [true] (have z := (hxy (rfl))) (cases z))
    (case [false] (exact h))))

(a/theorem fin-up [gxz :- (List Nat), r :- I10CurrentRunKey, c :- I10CurrentCompKey]
  (= (cur-fin gxz (I10CurrentRunKey.mk (:id r) (:of r) (:epoch r) true) c) true)
  (simp only [cur-fin Bool.true_or Bool.or_true]))

(a/defn i10-current-run-key-up [k :- I10CurrentRunKey] I10CurrentRunKey (I10CurrentRunKey.mk (:id k) (:of k) (:epoch k) true))
(a/defn i10-current-run-key-down [k :- I10CurrentRunKey] I10CurrentRunKey (I10CurrentRunKey.mk (:id k) (:of k) (:epoch k) false))

(a/theorem rc-up [gxz :- (List Nat), gkz :- (List Nat), r :- I10CurrentRunKey, c :- I10CurrentCompKey]
  (=> (= (rc-ok gxz gkz r c) true) (= (rc-ok gxz gkz (i10-current-run-key-up r) c) true))
  (intro h)
  (have e1 (= (rof-pair (i10-current-run-key-up r) c) (rof-pair r c))) (rfl)
  (have e2 (= (reach-mem (:id (i10-current-run-key-up r)) gkz) (reach-mem (:id r) gkz))) (rfl)
  (have e3 (= (cur-core (i10-current-run-key-up r) c true) (cur-core r c true))) (rfl)
  (have e4 (= (cur-fin gxz (i10-current-run-key-up r) c) true)) (exact (fin-up gxz r c))
  (simp only [rc-ok cur-pair e1 e2 e4 e3])
  (simp only [rc-ok cur-pair] at h)
  (cases hk (reach-mem (:id r) gkz))
  (case [true] (simp only [Bool.true_or]))
  (case [false]
    (simp only [hk Bool.false_or Bool.and_eq_true] at h)
    (simp only [Bool.false_or (And.right h) Bool.and_true])
    (exact (core-mono r c _ true (And.left h) (fn [z :- (= (cur-fin gxz r c) true)] (rfl))))))

;; a run made done: harmless when it is no current run of a computation outside gxz
(a/defn nc-c [gxz :- (List Nat), r :- I10CurrentRunKey, c :- I10CurrentCompKey] Bool
  (Bool.or (reach-mem (:id c) gxz) (Bool.or (Bool.not (Nat.beq (:of r) (:id c))) (Bool.not (Nat.beq (:epoch r) (:epoch c))))))

(a/theorem rc-down [gxz :- (List Nat), gkz :- (List Nat), r :- I10CurrentRunKey, c :- I10CurrentCompKey]
  (=> (= (rc-ok gxz gkz r c) true) (= (nc-c gxz r c) true) (= (rc-ok gxz gkz (i10-current-run-key-down r) c) true))
  (intros h hn)
  (have e1 (= (rof-pair (i10-current-run-key-down r) c) (rof-pair r c))) (rfl)
  (have e2 (= (reach-mem (:id (i10-current-run-key-down r)) gkz) (reach-mem (:id r) gkz))) (rfl)
  (simp only [rc-ok cur-pair] at h)
  (simp only [rc-ok cur-pair e1 e2])
  (cases hk (reach-mem (:id r) gkz))
  (case [true] (simp only [Bool.true_or]))
  (case [false]
    (simp only [hk Bool.false_or Bool.and_eq_true] at h)
    (simp only [Bool.false_or (And.right h) Bool.and_true])
    (have hc := (And.left h))
    (cases hg (reach-mem (:id c) gxz))
    (case [true]
      (have z (= (cur-fin gxz (i10-current-run-key-down r) c) true)) (simp only [cur-fin hg Bool.true_or])
      (have e3 (= (cur-core (i10-current-run-key-down r) c (cur-fin gxz (i10-current-run-key-down r) c)) (cur-core r c (cur-fin gxz (i10-current-run-key-down r) c)))) (rfl)
      (rw [e3])
      (exact (core-mono r c _ _ hc (fn [q :- (= (cur-fin gxz r c) true)] z))))
    (case [false]
      (simp only [nc-c hg Bool.false_or] at hn)
      (cases ho (Nat.beq (:of r) (:id c)))
      (case [false] (simp only [cur-core i10-current-run-key-down ho Bool.not_false Bool.true_or]))
      (case [true]
        (simp only [ho Bool.not_true Bool.false_or] at hn)
        (simp only [cur-core Bool.not_true Bool.false_or Bool.and_eq_true ho] at hc)
        (have he (= (Nat.beq (:epoch r) (:epoch c)) false)) (exact (bnot-true _ hn))
        (simp only [cur-core i10-current-run-key-down ho he (And.left hc) Bool.not_true Bool.not_false Bool.false_or Bool.true_or Bool.true_and])))))

;; ---- generic list facts

(a/theorem below0-mono [n :- Nat, m :- Nat, x :- Nat] (=> (<= n m) (= (below0 n x) true) (= (below0 m x) true))
  (intros hn h)
  (cases hz (Nat.beq x 0))
  (case [true] (simp only [below0 hz Bool.true_or]))
  (case [false] (simp only [below0 hz Bool.false_or Nat.blt_eq] at h) (simp only [below0 hz Bool.false_or Nat.blt_eq]) (omega)))

(a/theorem i10-current-run-ok-next [gxz :- (List Nat), gkz :- (List Nat), cks :- (List I10CurrentCompKey), tks :- (List I10CurrentTaskKey), n :- Nat, m :- Nat, r :- I10CurrentRunKey]
  (=> (<= n m) (= (i10-current-run-ok gxz gkz cks tks n r) true) (= (i10-current-run-ok gxz gkz cks tks m r) true))
  (intros hn h)
  (simp only [i10-current-run-ok Bool.and_eq_true Nat.blt_eq] at h)
  (simp only [i10-current-run-ok Bool.and_eq_true Nat.blt_eq (And.left h) (And.left (And.right h)) true_and])
  (have z := (And.right (And.right h))) (omega))
(a/theorem i10-current-comp-ok-next [n :- Nat, m :- Nat, c :- I10CurrentCompKey] (=> (<= n m) (= (i10-current-comp-ok n c) true) (= (i10-current-comp-ok m c) true))
  (intros hn h)
  (simp only [i10-current-comp-ok Bool.and_eq_true] at h)
  (simp only [i10-current-comp-ok Bool.and_eq_true (And.left h) true_and])
  (exact (below0-mono n m _ hn (And.right h))))
(a/theorem i10-current-task-ok-next [n :- Nat, m :- Nat, t :- I10CurrentTaskKey] (=> (<= n m) (= (i10-current-task-ok n t) true) (= (i10-current-task-ok m t) true))
  (intros hn h) (simp only [i10-current-task-ok] at h) (simp only [i10-current-task-ok]) (exact (below0-mono n m _ hn h)))

(a/theorem i10-current-exempt-keys-ok-next [gxz :- (List Nat), gkz :- (List Nat), rks :- (List I10CurrentRunKey), cks :- (List I10CurrentCompKey), tks :- (List I10CurrentTaskKey), n :- Nat, m :- Nat]
  (=> (<= n m) (= (i10-current-exempt-keys-ok gxz gkz rks cks tks n) true) (= (i10-current-exempt-keys-ok gxz gkz rks cks tks m) true))
  (intros hn h)
  (simp only [i10-current-exempt-keys-ok Bool.and_eq_true] at h)
  (simp only [i10-current-exempt-keys-ok Bool.and_eq_true])
  (exact (And.intro (tbl-all-mono I10CurrentRunKey _ _ (fn [r :- I10CurrentRunKey] (i10-current-run-ok-next gxz gkz cks tks n m r hn)) rks (And.left h))
           (And.intro (tbl-all-mono I10CurrentCompKey _ _ (fn [c :- I10CurrentCompKey] (i10-current-comp-ok-next n m c hn)) cks (And.left (And.right h)))
                      (tbl-all-mono I10CurrentTaskKey _ _ (fn [t :- I10CurrentTaskKey] (i10-current-task-ok-next n m t hn)) tks (And.right (And.right h)))))))

;; ---- the invariant under key-list edits

(a/theorem i10-current-run-ok-up [gxz :- (List Nat), gkz :- (List Nat), cks :- (List I10CurrentCompKey), tks :- (List I10CurrentTaskKey), n :- Nat, r :- I10CurrentRunKey]
  (=> (= (i10-current-run-ok gxz gkz cks tks n r) true) (= (i10-current-run-ok gxz gkz cks tks n (i10-current-run-key-up r)) true))
  (intro h)
  (simp only [i10-current-run-ok Bool.and_eq_true] at h)
  (have e1 (= (tbl-all (tof-pair (i10-current-run-key-up r)) tks) (tbl-all (tof-pair r) tks))) (rfl)
  (have e2 (= (Nat.blt (:of (i10-current-run-key-up r)) n) (Nat.blt (:of r) n))) (rfl)
  (simp only [i10-current-run-ok Bool.and_eq_true e1 e2 (And.left (And.right h)) (And.right (And.right h)) and_true])
  (exact (tbl-all-mono I10CurrentCompKey _ _ (fn [c :- I10CurrentCompKey] (rc-up gxz gkz r c)) cks (And.left h))))

(a/theorem i10-current-exempt-keys-ok-run-up [gxz :- (List Nat), gkz :- (List Nat), rks :- (List I10CurrentRunKey), cks :- (List I10CurrentCompKey), tks :- (List I10CurrentTaskKey), n :- Nat, x :- Nat]
  (=> (= (i10-current-exempt-keys-ok gxz gkz rks cks tks n) true) (= (i10-current-exempt-keys-ok gxz gkz (tbl-upd i10-current-run-key-id x i10-current-run-key-up rks) cks tks n) true))
  (intro h)
  (simp only [i10-current-exempt-keys-ok Bool.and_eq_true] at h)
  (simp only [i10-current-exempt-keys-ok Bool.and_eq_true (And.right h) and_true])
  (apply (tbl-all-upd I10CurrentRunKey i10-current-run-key-id x i10-current-run-key-up _ _ _ _ rks (And.left h)))
  (intros r hr hx) (exact (i10-current-run-ok-up gxz gkz cks tks n r hr))
  (intros r hr hx) (exact hr))

(a/defn dn-ok [gxz :- (List Nat), x :- Nat, cks :- (List I10CurrentCompKey), r :- I10CurrentRunKey] Bool
  (Bool.or (Bool.not (Nat.beq (:id r) x)) (tbl-all (nc-c gxz r) cks)))

(a/theorem i10-current-run-ok-down [gxz :- (List Nat), gkz :- (List Nat), cks :- (List I10CurrentCompKey), tks :- (List I10CurrentTaskKey), n :- Nat, r :- I10CurrentRunKey]
  (=> (= (i10-current-run-ok gxz gkz cks tks n r) true) (= (tbl-all (nc-c gxz r) cks) true) (= (i10-current-run-ok gxz gkz cks tks n (i10-current-run-key-down r)) true))
  (intros h hn)
  (simp only [i10-current-run-ok Bool.and_eq_true] at h)
  (have e1 (= (tbl-all (tof-pair (i10-current-run-key-down r)) tks) (tbl-all (tof-pair r) tks))) (rfl)
  (have e2 (= (Nat.blt (:of (i10-current-run-key-down r)) n) (Nat.blt (:of r) n))) (rfl)
  (simp only [i10-current-run-ok Bool.and_eq_true e1 e2 (And.left (And.right h)) (And.right (And.right h)) and_true])
  (exact (tbl-all-mono2 I10CurrentCompKey _ _ _ (fn [c :- I10CurrentCompKey] (rc-down gxz gkz r c)) cks (And.left h) hn)))

(a/theorem both-mk [A :- Type, p :- (=> A Bool), q :- (=> A Bool), a :- A]
  (=> (= (p a) true) (= (q a) true) (= (both p q a) true))
  (intros h1 h2) (simp only [both h1 h2 Bool.and_self]))

(a/theorem i10-current-exempt-keys-ok-run-down [gxz :- (List Nat), gkz :- (List Nat), rks :- (List I10CurrentRunKey), cks :- (List I10CurrentCompKey), tks :- (List I10CurrentTaskKey), n :- Nat, x :- Nat]
  (=> (= (i10-current-exempt-keys-ok gxz gkz rks cks tks n) true) (= (tbl-all (dn-ok gxz x cks) rks) true)
      (= (i10-current-exempt-keys-ok gxz gkz (tbl-upd i10-current-run-key-id x i10-current-run-key-down rks) cks tks n) true))
  (intros h hd)
  (simp only [i10-current-exempt-keys-ok Bool.and_eq_true] at h)
  (simp only [i10-current-exempt-keys-ok Bool.and_eq_true (And.right h) and_true])
  (have hb (forall [r :- I10CurrentRunKey] (=> (= (i10-current-run-ok gxz gkz cks tks n r) true) (= (dn-ok gxz x cks r) true)
                                   (= (Nat.beq (i10-current-run-key-id r) x) true) (= (i10-current-run-ok gxz gkz cks tks n (i10-current-run-key-down r)) true))))
  (intros r hr hdn hx)
  (have hx2 (= (Nat.beq (:id r) x) true)) (exact hx)
  (simp only [dn-ok hx2 Bool.not_true Bool.false_or] at hdn)
  (exact (i10-current-run-ok-down gxz gkz cks tks n r hr hdn))
  (exact (tbl-all-upd I10CurrentRunKey i10-current-run-key-id x i10-current-run-key-down (both (i10-current-run-ok gxz gkz cks tks n) (dn-ok gxz x cks)) (i10-current-run-ok gxz gkz cks tks n)
           (fn [r :- I10CurrentRunKey, hp :- (= (both (i10-current-run-ok gxz gkz cks tks n) (dn-ok gxz x cks) r) true), hx :- (= (Nat.beq (i10-current-run-key-id r) x) true)]
             (hb r (both-left _ _ _ _ hp) (both-right _ _ _ _ hp) hx))
           (fn [r :- I10CurrentRunKey, hp :- (= (both (i10-current-run-ok gxz gkz cks tks n) (dn-ok gxz x cks) r) true), hx :- (= (Nat.beq (i10-current-run-key-id r) x) false)]
             (both-left _ _ _ _ hp))
           rks (tbl-all-mono2 I10CurrentRunKey _ _ _ (fn [r :- I10CurrentRunKey, a1 :- (= (i10-current-run-ok gxz gkz cks tks n r) true), a2 :- (= (dn-ok gxz x cks r) true)]
                                            (both-mk _ _ _ _ a1 a2)) rks (And.left h) hd))))

(a/theorem i10-current-exempt-keys-ok-comp-up [gxz :- (List Nat), gkz :- (List Nat), rks :- (List I10CurrentRunKey), cks :- (List I10CurrentCompKey), tks :- (List I10CurrentTaskKey), n :- Nat,
                         x :- Nat, g :- (=> I10CurrentCompKey I10CurrentCompKey),
                         hup :- (forall [r :- I10CurrentRunKey, c :- I10CurrentCompKey] (=> (= (rc-ok gxz gkz r c) true) (= (rc-ok gxz gkz r (g c)) true))),
                         hc :- (forall [c :- I10CurrentCompKey] (=> (= (i10-current-comp-ok n c) true) (= (i10-current-comp-ok n (g c)) true)))]
  (=> (= (i10-current-exempt-keys-ok gxz gkz rks cks tks n) true) (= (i10-current-exempt-keys-ok gxz gkz rks (tbl-upd i10-current-comp-key-id x g cks) tks n) true))
  (intro h)
  (simp only [i10-current-exempt-keys-ok Bool.and_eq_true] at h)
  (have h1 (forall [r :- I10CurrentRunKey] (=> (= (i10-current-run-ok gxz gkz cks tks n r) true) (= (i10-current-run-ok gxz gkz (tbl-upd i10-current-comp-key-id x g cks) tks n r) true))))
  (intros r hr)
  (simp only [i10-current-run-ok Bool.and_eq_true] at hr)
  (simp only [i10-current-run-ok Bool.and_eq_true (And.right hr) and_true])
  (exact (tbl-all-upd I10CurrentCompKey i10-current-comp-key-id x g (rc-ok gxz gkz r) (rc-ok gxz gkz r)
           (fn [c :- I10CurrentCompKey, hp :- (= (rc-ok gxz gkz r c) true), hx :- (= (Nat.beq (i10-current-comp-key-id c) x) true)] (hup r c hp))
           (fn [c :- I10CurrentCompKey, hp :- (= (rc-ok gxz gkz r c) true), hx :- (= (Nat.beq (i10-current-comp-key-id c) x) false)] hp) cks (And.left hr)))
  (simp only [i10-current-exempt-keys-ok Bool.and_eq_true (And.right (And.right h)) and_true])
  (exact (And.intro (tbl-all-mono I10CurrentRunKey _ _ h1 rks (And.left h))
           (tbl-all-upd I10CurrentCompKey i10-current-comp-key-id x g (i10-current-comp-ok n) (i10-current-comp-ok n)
             (fn [c :- I10CurrentCompKey, hp :- (= (i10-current-comp-ok n c) true), hx :- (= (Nat.beq (i10-current-comp-key-id c) x) true)] (hc c hp))
             (fn [c :- I10CurrentCompKey, hp :- (= (i10-current-comp-ok n c) true), hx :- (= (Nat.beq (i10-current-comp-key-id c) x) false)] hp) cks (And.left (And.right h))))))

(a/theorem i10-current-exempt-keys-ok-task-up [gxz :- (List Nat), gkz :- (List Nat), rks :- (List I10CurrentRunKey), cks :- (List I10CurrentCompKey), tks :- (List I10CurrentTaskKey), n :- Nat,
                         x :- Nat, g :- (=> I10CurrentTaskKey I10CurrentTaskKey),
                         hup :- (forall [r :- I10CurrentRunKey, t :- I10CurrentTaskKey] (=> (= (tof-pair r t) true) (= (tof-pair r (g t)) true))),
                         hc :- (forall [t :- I10CurrentTaskKey] (=> (= (i10-current-task-ok n t) true) (= (i10-current-task-ok n (g t)) true)))]
  (=> (= (i10-current-exempt-keys-ok gxz gkz rks cks tks n) true) (= (i10-current-exempt-keys-ok gxz gkz rks cks (tbl-upd i10-current-task-key-id x g tks) n) true))
  (intro h)
  (simp only [i10-current-exempt-keys-ok Bool.and_eq_true] at h)
  (have h1 (forall [r :- I10CurrentRunKey] (=> (= (i10-current-run-ok gxz gkz cks tks n r) true) (= (i10-current-run-ok gxz gkz cks (tbl-upd i10-current-task-key-id x g tks) n r) true))))
  (intros r hr)
  (simp only [i10-current-run-ok Bool.and_eq_true] at hr)
  (simp only [i10-current-run-ok Bool.and_eq_true (And.left hr) (And.right (And.right hr)) and_true true_and])
  (exact (tbl-all-upd I10CurrentTaskKey i10-current-task-key-id x g (tof-pair r) (tof-pair r)
           (fn [t :- I10CurrentTaskKey, hp :- (= (tof-pair r t) true), hx :- (= (Nat.beq (i10-current-task-key-id t) x) true)] (hup r t hp))
           (fn [t :- I10CurrentTaskKey, hp :- (= (tof-pair r t) true), hx :- (= (Nat.beq (i10-current-task-key-id t) x) false)] hp) tks (And.left (And.right hr))))
  (simp only [i10-current-exempt-keys-ok Bool.and_eq_true (And.left (And.right h)) true_and])
  (exact (And.intro (tbl-all-mono I10CurrentRunKey _ _ h1 rks (And.left h))
           (tbl-all-upd I10CurrentTaskKey i10-current-task-key-id x g (i10-current-task-ok n) (i10-current-task-ok n)
             (fn [t :- I10CurrentTaskKey, hp :- (= (i10-current-task-ok n t) true), hx :- (= (Nat.beq (i10-current-task-key-id t) x) true)] (hc t hp))
             (fn [t :- I10CurrentTaskKey, hp :- (= (i10-current-task-ok n t) true), hx :- (= (Nat.beq (i10-current-task-key-id t) x) false)] hp) tks (And.right (And.right h))))))

;; deletions and the Rule R filter: sublists
(a/theorem i10-current-exempt-keys-ok-run-del [gxz :- (List Nat), gkz :- (List Nat), rks :- (List I10CurrentRunKey), cks :- (List I10CurrentCompKey), tks :- (List I10CurrentTaskKey), n :- Nat, x :- Nat]
  (=> (= (i10-current-exempt-keys-ok gxz gkz rks cks tks n) true) (= (i10-current-exempt-keys-ok gxz gkz (tbl-del i10-current-run-key-id x rks) cks tks n) true))
  (intro h)
  (simp only [i10-current-exempt-keys-ok Bool.and_eq_true] at h)
  (simp only [i10-current-exempt-keys-ok Bool.and_eq_true (And.right h) and_true])
  (exact (tbl-all-del I10CurrentRunKey i10-current-run-key-id x _ _ (fn [r :- I10CurrentRunKey, hp :- (= (i10-current-run-ok gxz gkz cks tks n r) true), hx :- (= (Nat.beq (i10-current-run-key-id r) x) false)] hp)
           rks (And.left h))))

(a/theorem rc-unexempt [gxz :- (List Nat), gkz :- (List Nat), x :- Nat, r :- I10CurrentRunKey, c :- I10CurrentCompKey]
  (=> (= (rc-ok gxz (List.cons Nat x gkz) r c) true) (= (Nat.beq (:id r) x) false) (= (rc-ok gxz gkz r c) true))
  (intros h hx) (simp only [rc-ok reach-mem-cons hx Bool.false_or] at h) (simp only [rc-ok]) (exact h))

(a/theorem i10-current-exempt-keys-ok-run-del-x [gxz :- (List Nat), gkz :- (List Nat), rks :- (List I10CurrentRunKey), cks :- (List I10CurrentCompKey), tks :- (List I10CurrentTaskKey), n :- Nat, x :- Nat]
  (=> (= (i10-current-exempt-keys-ok gxz (List.cons Nat x gkz) rks cks tks n) true) (= (i10-current-exempt-keys-ok gxz gkz (tbl-del i10-current-run-key-id x rks) cks tks n) true))
  (intro h)
  (simp only [i10-current-exempt-keys-ok Bool.and_eq_true] at h)
  (simp only [i10-current-exempt-keys-ok Bool.and_eq_true (And.right h) and_true])
  (apply (tbl-all-del I10CurrentRunKey i10-current-run-key-id x (i10-current-run-ok gxz (List.cons Nat x gkz) cks tks n) (i10-current-run-ok gxz gkz cks tks n) _ rks (And.left h)))
  (intros r hp hx)
  (simp only [i10-current-run-ok Bool.and_eq_true] at hp)
  (simp only [i10-current-run-ok Bool.and_eq_true (And.right hp) and_true])
  (have hx2 (= (Nat.beq (:id r) x) false)) (exact hx)
  (exact (tbl-all-mono I10CurrentCompKey _ _ (fn [c :- I10CurrentCompKey, q :- (= (rc-ok gxz (List.cons Nat x gkz) r c) true)] (rc-unexempt gxz gkz x r c q hx2))
           cks (And.left hp))))

(a/theorem i10-current-run-ok-sub [gxz :- (List Nat), gkz :- (List Nat), cks :- (List I10CurrentCompKey), cks2 :- (List I10CurrentCompKey), tks :- (List I10CurrentTaskKey), tks2 :- (List I10CurrentTaskKey), n :- Nat,
                    hc :- (forall [p :- (=> I10CurrentCompKey Bool)] (=> (= (tbl-all p cks) true) (= (tbl-all p cks2) true))),
                    ht :- (forall [p :- (=> I10CurrentTaskKey Bool)] (=> (= (tbl-all p tks) true) (= (tbl-all p tks2) true))), r :- I10CurrentRunKey]
  (=> (= (i10-current-run-ok gxz gkz cks tks n r) true) (= (i10-current-run-ok gxz gkz cks2 tks2 n r) true))
  (intro h)
  (simp only [i10-current-run-ok Bool.and_eq_true] at h)
  (simp only [i10-current-run-ok Bool.and_eq_true (hc _ (And.left h)) (ht _ (And.left (And.right h))) (And.right (And.right h)) and_self]))

(a/theorem i10-current-exempt-keys-ok-sub [gxz :- (List Nat), gkz :- (List Nat), rks :- (List I10CurrentRunKey), rks2 :- (List I10CurrentRunKey), cks :- (List I10CurrentCompKey), cks2 :- (List I10CurrentCompKey),
                     tks :- (List I10CurrentTaskKey), tks2 :- (List I10CurrentTaskKey), n :- Nat,
                     hr :- (forall [p :- (=> I10CurrentRunKey Bool)] (=> (= (tbl-all p rks) true) (= (tbl-all p rks2) true))),
                     hc :- (forall [p :- (=> I10CurrentCompKey Bool)] (=> (= (tbl-all p cks) true) (= (tbl-all p cks2) true))),
                     ht :- (forall [p :- (=> I10CurrentTaskKey Bool)] (=> (= (tbl-all p tks) true) (= (tbl-all p tks2) true)))]
  (=> (= (i10-current-exempt-keys-ok gxz gkz rks cks tks n) true) (= (i10-current-exempt-keys-ok gxz gkz rks2 cks2 tks2 n) true))
  (intro h)
  (simp only [i10-current-exempt-keys-ok Bool.and_eq_true] at h)
  (simp only [i10-current-exempt-keys-ok Bool.and_eq_true (hc _ (And.left (And.right h))) (ht _ (And.right (And.right h))) and_true])
  (exact (hr _ (tbl-all-mono I10CurrentRunKey _ _ (i10-current-run-ok-sub gxz gkz cks cks2 tks tks2 n hc ht) rks (And.left h)))))

(a/theorem i10-current-exempt-keys-ok-comp-del [gxz :- (List Nat), gkz :- (List Nat), rks :- (List I10CurrentRunKey), cks :- (List I10CurrentCompKey), tks :- (List I10CurrentTaskKey), n :- Nat, x :- Nat]
  (=> (= (i10-current-exempt-keys-ok gxz gkz rks cks tks n) true) (= (i10-current-exempt-keys-ok gxz gkz rks (tbl-del i10-current-comp-key-id x cks) tks n) true))
  (exact (i10-current-exempt-keys-ok-sub gxz gkz rks rks cks _ tks tks n (fn [p :- (=> I10CurrentRunKey Bool), q :- (= (tbl-all p rks) true)] q)
           (fn [p :- (=> I10CurrentCompKey Bool), q :- (= (tbl-all p cks) true)]
             (tbl-all-del I10CurrentCompKey i10-current-comp-key-id x p p (fn [c :- I10CurrentCompKey, a1 :- (= (p c) true), a2 :- (= (Nat.beq (i10-current-comp-key-id c) x) false)] a1) cks q))
           (fn [p :- (=> I10CurrentTaskKey Bool), q :- (= (tbl-all p tks) true)] q))))

(a/theorem i10-current-exempt-keys-ok-keep [gxz :- (List Nat), gkz :- (List Nat), rks :- (List I10CurrentRunKey), cks :- (List I10CurrentCompKey), tks :- (List I10CurrentTaskKey), n :- Nat, K :- (=> Nat Bool)]
  (=> (= (i10-current-exempt-keys-ok gxz gkz rks cks tks n) true)
      (= (i10-current-exempt-keys-ok gxz gkz (tbl-keep K i10-current-run-key-id rks) (tbl-keep K i10-current-comp-key-id cks) (tbl-keep K i10-current-task-key-id tks) n) true))
  (exact (i10-current-exempt-keys-ok-sub gxz gkz rks _ cks _ tks _ n
           (fn [p :- (=> I10CurrentRunKey Bool), q :- (= (tbl-all p rks) true)] (tbl-all-keep-same I10CurrentRunKey K i10-current-run-key-id p rks q))
           (fn [p :- (=> I10CurrentCompKey Bool), q :- (= (tbl-all p cks) true)] (tbl-all-keep-same I10CurrentCompKey K i10-current-comp-key-id p cks q))
           (fn [p :- (=> I10CurrentTaskKey Bool), q :- (= (tbl-all p tks) true)] (tbl-all-keep-same I10CurrentTaskKey K i10-current-task-key-id p tks q)))))

;; more exemptions
(a/theorem rc-gx-cons [gxz :- (List Nat), gkz :- (List Nat), y :- Nat, r :- I10CurrentRunKey, c :- I10CurrentCompKey]
  (=> (= (rc-ok gxz gkz r c) true) (= (rc-ok (List.cons Nat y gxz) gkz r c) true))
  (intro h)
  (simp only [rc-ok cur-pair] at h)
  (simp only [rc-ok cur-pair])
  (cases hk (reach-mem (:id r) gkz))
  (case [true] (simp only [Bool.true_or]))
  (case [false]
    (simp only [hk Bool.false_or Bool.and_eq_true] at h)
    (simp only [Bool.false_or (And.right h) Bool.and_true])
    (apply (core-mono r c _ _ (And.left h)))
    (intro q)
    (simp only [cur-fin Bool.or_eq_true] at q)
    (simp only [cur-fin reach-mem-cons Bool.or_eq_true])
    (cases q)
    (case [inl a] (exact (Or.inl (Or.inr a))))
    (case [inr b] (exact (Or.inr b)))))

;; ---- the world keys

(a/structure I10CurrentView [] (rks (List I10CurrentRunKey)) (cks (List I10CurrentCompKey)) (tks (List I10CurrentTaskKey)) (n Nat))
(a/defn i10-current-view [w :- World] I10CurrentView (I10CurrentView.mk (i10-current-run-keys (:runs w)) (i10-current-comp-keys (:comps w)) (i10-current-task-keys (:tasks w)) (:next-id w)))

(a/theorem i10-current-exempt-rest-frame [gxz :- (List Nat), gkz :- (List Nat), w :- World, w2 :- World]
  (=> (= (i10-current-view w2) (i10-current-view w)) (= (i10-current-exempt-rest gxz gkz w2) (i10-current-exempt-rest gxz gkz w)))
  (intro e)
  (have e1 (= (i10-current-run-keys (:runs w2)) (i10-current-run-keys (:runs w)))) (exact (congrArg (fn [k :- I10CurrentView] (:rks k)) e))
  (have e2 (= (i10-current-comp-keys (:comps w2)) (i10-current-comp-keys (:comps w)))) (exact (congrArg (fn [k :- I10CurrentView] (:cks k)) e))
  (have e3 (= (i10-current-task-keys (:tasks w2)) (i10-current-task-keys (:tasks w)))) (exact (congrArg (fn [k :- I10CurrentView] (:tks k)) e))
  (have e4 (= (:next-id w2) (:next-id w))) (exact (congrArg (fn [k :- I10CurrentView] (:n k)) e))
  (simp only [i10-current-exempt-rest e1 e2 e3 e4]))

(a/theorem i10-current-exempt-frame [gxz :- (List Nat), gkz :- (List Nat), w :- World, w2 :- World]
  (=> (= (i10-current-view w2) (i10-current-view w)) (= (well-formed w2) true) (= (i10-current-exempt gxz gkz w) true) (= (i10-current-exempt gxz gkz w2) true))
  (intros e hs h) (exact (i10-current-exempt-intro gxz gkz w2 hs (Eq.trans (i10-current-exempt-rest-frame gxz gkz w w2 e) (i10-current-exempt-rest-of gxz gkz w h)))))

(a/theorem i10-current-view-comp-same [w :- World, x :- Nat, f :- (=> CompRow CompRow), hk :- (forall [c :- CompRow] (= (i10-current-comp-key (f c)) (i10-current-comp-key c)))]
  (= (i10-current-view (comp-upd w x f)) (i10-current-view w))
  (simp only [i10-current-view comp-upd set-comps (i10-current-comp-keys-same x f hk (:comps w))]))

(a/theorem i10-current-view-mark-edge [w :- World, x :- Nat] (= (i10-current-view (mark-edge w x)) (i10-current-view w))
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]))
  (case [some e]
    (cases hm (:marked e))
    (case [true] (simp only [mark-edge hf hm]))
    (case [false] (simp only [mark-edge hf hm])
      (exact (Eq.trans (i10-current-view-comp-same _ (:creditor e) comp-inc-pending (fn [c :- CompRow] (Eq.refl (i10-current-comp-key c)))) (rfl))))))
(a/theorem i10-current-view-unmark-edge [w :- World, x :- Nat] (= (i10-current-view (unmark-edge w x)) (i10-current-view w))
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [unmark-edge hf hm]))
    (case [true] (simp only [unmark-edge hf hm])
      (exact (Eq.trans (i10-current-view-comp-same _ (:creditor e) comp-dec-pending (fn [c :- CompRow] (Eq.refl (i10-current-comp-key c)))) (rfl))))))
(a/theorem i10-current-view-remove-edge [w :- World, x :- Nat] (= (i10-current-view (remove-edge w x)) (i10-current-view w))
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [remove-edge hf hm]))
    (case [true] (simp only [remove-edge hf hm])
      (exact (Eq.trans (i10-current-view-comp-same _ (:creditor e) comp-dec-pending (fn [c :- CompRow] (Eq.refl (i10-current-comp-key c)))) (rfl))))))
(a/theorem i10-current-view-drop-cred [w :- World, a :- Nat] (= (i10-current-view (drop-cred-edges w a)) (i10-current-view w))
  (simp only [drop-cred-edges])
  (exact (Eq.trans (i10-current-view-comp-same _ a (comp-set-pending 0) (fn [c :- CompRow] (Eq.refl (i10-current-comp-key c)))) (rfl))))
(a/theorem i10-current-view-drop-act [w :- World, a :- Nat] (= (i10-current-view (drop-act w a)) (i10-current-view w))
  (simp only [drop-act]) (exact (Eq.trans (rfl) (i10-current-view-drop-cred w a))))
(a/theorem i10-current-comp-keys-resync [es :- (List EdgeRow), cs :- (List CompRow)] (= (i10-current-comp-keys (comps-resync es cs)) (i10-current-comp-keys cs))
  (induction cs)
  (case [nil] (simp only [comps-resync i10-current-comp-keys]))
  (case [cons h t ih]
    (have e (= (i10-current-comp-key (comp-resync es h)) (i10-current-comp-key h))) (rfl)
    (simp only [comps-resync i10-current-comp-keys e ih])))
(a/theorem i10-current-view-drop-edges [w :- World, p :- (=> EdgeRow Bool)] (= (i10-current-view (drop-edges w p)) (i10-current-view w))
  (simp only [i10-current-view drop-edges set-comps set-edges i10-current-comp-keys-resync]))

;; ---- primitives

(a/theorem i10-current-exempt-run-upd [gxz :- (List Nat), gkz :- (List Nat), w :- World, x :- Nat, f :- (=> RunRow RunRow),
                        hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                        hk :- (forall [r :- RunRow] (= (i10-current-run-key (f r)) (i10-current-run-key r)))]
  (=> (= (i10-current-exempt gxz gkz w) true) (= (i10-current-exempt gxz gkz (run-upd w x f)) true))
  (intro h)
  (have e (= (i10-current-view (run-upd w x f)) (i10-current-view w))) (simp only [i10-current-view run-upd set-runs (i10-current-run-keys-same x f hk (:runs w))])
  (exact (i10-current-exempt-frame gxz gkz w _ e (well-formed-run-upd w x f hf (i10-current-exempt-well-formed gxz gkz w h)) h)))

(a/theorem i10-current-exempt-comp-upd [gxz :- (List Nat), gkz :- (List Nat), w :- World, x :- Nat, f :- (=> CompRow CompRow),
                         hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                         hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                         hk :- (forall [c :- CompRow] (= (i10-current-comp-key (f c)) (i10-current-comp-key c)))]
  (=> (= (i10-current-exempt gxz gkz w) true) (= (i10-current-exempt gxz gkz (comp-upd w x f)) true))
  (intro h)
  (exact (i10-current-exempt-frame gxz gkz w _ (i10-current-view-comp-same w x f hk) (well-formed-comp-upd w x f hid hp (i10-current-exempt-well-formed gxz gkz w h)) h)))

(a/theorem i10-current-exempt-task-upd [gxz :- (List Nat), gkz :- (List Nat), w :- World, x :- Nat, f :- (=> TaskRow TaskRow),
                         hf :- (forall [t :- TaskRow] (= (task-id (f t)) (task-id t))),
                         hk :- (forall [t :- TaskRow] (= (i10-current-task-key (f t)) (i10-current-task-key t)))]
  (=> (= (i10-current-exempt gxz gkz w) true) (= (i10-current-exempt gxz gkz (task-upd w x f)) true))
  (intro h)
  (have e (= (i10-current-view (task-upd w x f)) (i10-current-view w))) (simp only [i10-current-view task-upd set-tasks (i10-current-task-keys-same x f hk (:tasks w))])
  (exact (i10-current-exempt-frame gxz gkz w _ e (well-formed-task-upd w x f hf (i10-current-exempt-well-formed gxz gkz w h)) h)))

(a/theorem i10-current-exempt-run-upd-up [gxz :- (List Nat), gkz :- (List Nat), w :- World, x :- Nat, f :- (=> RunRow RunRow),
                           hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                           hk :- (forall [r :- RunRow] (= (i10-current-run-key (f r)) (i10-current-run-key-up (i10-current-run-key r))))]
  (=> (= (i10-current-exempt gxz gkz w) true) (= (i10-current-exempt gxz gkz (run-upd w x f)) true))
  (intro h)
  (have hr (= (i10-current-exempt-rest gxz gkz (run-upd w x f)) true))
  (simp only [i10-current-exempt-rest run-upd set-runs (i10-current-run-keys-upd x f i10-current-run-key-up hk (:runs w))])
  (exact (i10-current-exempt-keys-ok-run-up gxz gkz _ _ _ _ x (i10-current-exempt-rest-of gxz gkz w h)))
  (exact (i10-current-exempt-intro gxz gkz _ (well-formed-run-upd w x f hf (i10-current-exempt-well-formed gxz gkz w h)) hr)))

(a/theorem i10-current-exempt-comp-upd-g [gxz :- (List Nat), gkz :- (List Nat), w :- World, x :- Nat, f :- (=> CompRow CompRow),
                           hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                           hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                           g :- (=> I10CurrentCompKey I10CurrentCompKey), hk :- (forall [c :- CompRow] (= (i10-current-comp-key (f c)) (g (i10-current-comp-key c)))),
                           hup :- (forall [r :- I10CurrentRunKey, c :- I10CurrentCompKey] (=> (= (rc-ok gxz gkz r c) true) (= (rc-ok gxz gkz r (g c)) true))),
                           hc :- (forall [c :- I10CurrentCompKey] (=> (= (i10-current-comp-ok (:next-id w) c) true) (= (i10-current-comp-ok (:next-id w) (g c)) true)))]
  (=> (= (i10-current-exempt gxz gkz w) true) (= (i10-current-exempt gxz gkz (comp-upd w x f)) true))
  (intro h)
  (have hr (= (i10-current-exempt-rest gxz gkz (comp-upd w x f)) true))
  (simp only [i10-current-exempt-rest comp-upd set-comps (i10-current-comp-keys-upd x f g hk (:comps w))])
  (exact (i10-current-exempt-keys-ok-comp-up gxz gkz _ _ _ _ x g hup hc (i10-current-exempt-rest-of gxz gkz w h)))
  (exact (i10-current-exempt-intro gxz gkz _ (well-formed-comp-upd w x f hid hp (i10-current-exempt-well-formed gxz gkz w h)) hr)))

(a/theorem i10-current-exempt-task-upd-g [gxz :- (List Nat), gkz :- (List Nat), w :- World, x :- Nat, f :- (=> TaskRow TaskRow),
                           hf :- (forall [t :- TaskRow] (= (task-id (f t)) (task-id t))),
                           g :- (=> I10CurrentTaskKey I10CurrentTaskKey), hk :- (forall [t :- TaskRow] (= (i10-current-task-key (f t)) (g (i10-current-task-key t)))),
                           hup :- (forall [r :- I10CurrentRunKey, t :- I10CurrentTaskKey] (=> (= (tof-pair r t) true) (= (tof-pair r (g t)) true))),
                           hc :- (forall [t :- I10CurrentTaskKey] (=> (= (i10-current-task-ok (:next-id w) t) true) (= (i10-current-task-ok (:next-id w) (g t)) true)))]
  (=> (= (i10-current-exempt gxz gkz w) true) (= (i10-current-exempt gxz gkz (task-upd w x f)) true))
  (intro h)
  (have hr (= (i10-current-exempt-rest gxz gkz (task-upd w x f)) true))
  (simp only [i10-current-exempt-rest task-upd set-tasks (i10-current-task-keys-upd x f g hk (:tasks w))])
  (exact (i10-current-exempt-keys-ok-task-up gxz gkz _ _ _ _ x g hup hc (i10-current-exempt-rest-of gxz gkz w h)))
  (exact (i10-current-exempt-intro gxz gkz _ (well-formed-task-upd w x f hf (i10-current-exempt-well-formed gxz gkz w h)) hr)))

(a/theorem i10-current-exempt-rest-next [gxz :- (List Nat), gkz :- (List Nat), w :- World, v :- Nat]
  (=> (= (i10-current-exempt-rest gxz gkz w) true) (<= (:next-id w) v) (= (i10-current-exempt-rest gxz gkz (set-next-id w v)) true))
  (intros h hv)
  (simp only [i10-current-exempt-rest] at h)
  (have e1 (= (:runs (set-next-id w v)) (:runs w))) (rfl)
  (have e2 (= (:comps (set-next-id w v)) (:comps w))) (rfl)
  (have e3 (= (:tasks (set-next-id w v)) (:tasks w))) (rfl)
  (have e4 (= (:next-id (set-next-id w v)) v)) (rfl)
  (simp only [i10-current-exempt-rest e1 e2 e3 e4])
  (exact (i10-current-exempt-keys-ok-next gxz gkz _ _ _ (:next-id w) v hv h)))
(a/theorem i10-current-exempt-rest-bump [gxz :- (List Nat), gkz :- (List Nat), w :- World]
  (=> (= (i10-current-exempt-rest gxz gkz w) true) (= (i10-current-exempt-rest gxz gkz (bump w)) true))
  (intro h) (simp only [bump]) (exact (i10-current-exempt-rest-next gxz gkz w (+ (:next-id w) 1) h (Nat.le_succ (:next-id w)))))

(a/theorem i10-current-exempt-rest-run-del [gxz :- (List Nat), gkz :- (List Nat), w :- World, x :- Nat]
  (=> (= (i10-current-exempt-rest gxz gkz w) true) (= (i10-current-exempt-rest gxz gkz (run-del w x)) true))
  (intro h) (simp only [i10-current-exempt-rest] at h) (simp only [i10-current-exempt-rest run-del set-runs i10-current-run-keys-del])
  (exact (i10-current-exempt-keys-ok-run-del gxz gkz _ _ _ _ x h)))
(a/theorem i10-current-exempt-rest-run-del-x [gxz :- (List Nat), gkz :- (List Nat), w :- World, x :- Nat]
  (=> (= (i10-current-exempt-rest gxz (List.cons Nat x gkz) w) true) (= (i10-current-exempt-rest gxz gkz (run-del w x)) true))
  (intro h) (simp only [i10-current-exempt-rest] at h) (simp only [i10-current-exempt-rest run-del set-runs i10-current-run-keys-del])
  (exact (i10-current-exempt-keys-ok-run-del-x gxz gkz _ _ _ _ x h)))
(a/theorem i10-current-exempt-rest-comp-del [gxz :- (List Nat), gkz :- (List Nat), w :- World, x :- Nat]
  (=> (= (i10-current-exempt-rest gxz gkz w) true) (= (i10-current-exempt-rest gxz gkz (comp-del w x)) true))
  (intro h) (simp only [i10-current-exempt-rest] at h) (simp only [i10-current-exempt-rest comp-del set-comps i10-current-comp-keys-del])
  (exact (i10-current-exempt-keys-ok-comp-del gxz gkz _ _ _ _ x h)))
(a/theorem i10-current-exempt-rest-filter [gxz :- (List Nat), gkz :- (List Nat), w :- World, K :- (=> Nat Bool)]
  (=> (= (i10-current-exempt-rest gxz gkz w) true) (= (i10-current-exempt-rest gxz gkz (filter-world K w)) true))
  (intro h) (simp only [i10-current-exempt-rest] at h) (simp only [i10-current-exempt-rest filter-world i10-current-run-keys-keep i10-current-comp-keys-keep i10-current-task-keys-keep])
  (exact (i10-current-exempt-keys-ok-keep gxz gkz _ _ _ _ K h)))

;; a fresh computation (id = next-id) has epoch >= 1 and no run (T3: epoch 1, run none)
(a/defn fresh-ck [c :- CompRow] Bool (Bool.and (Nat.beq (:run c) 0) (Nat.ble 1 (:epoch c))))
(a/theorem i10-current-run-ok-comp-ins [gxz :- (List Nat), gkz :- (List Nat), cks :- (List I10CurrentCompKey), tks :- (List I10CurrentTaskKey), n :- Nat, c :- I10CurrentCompKey, r :- I10CurrentRunKey]
  (=> (= (i10-current-run-ok gxz gkz cks tks n r) true) (= (:id c) n) (= (:run c) 0)
      (= (i10-current-run-ok gxz gkz (List.cons I10CurrentCompKey c cks) tks (+ n 1) r) true))
  (intros a0 hi hr)
  (have a1 := (i10-current-run-ok-next gxz gkz cks tks n (+ n 1) r (Nat.le_succ n) a0))
  (simp only [i10-current-run-ok Bool.and_eq_true Nat.blt_eq] at a0)
  (have hne (= (Nat.beq (:of r) (:id c)) false))
  (cases hb (Nat.beq (:of r) (:id c)))
  (rfl)
  (have z (= (:of r) (:id c))) (exact (Nat.eq_of_beq_eq_true hb))
  (have z2 := (And.right (And.right a0))) (rw [z hi] at z2) (omega)
  (have hrr (= (rof-pair r c) true))
  (cases hz (Nat.beq (:id r) 0))
  (case [true] (simp only [rof-pair hz Bool.true_or]))
  (case [false]
    (have hrne (= (Nat.beq (:id r) (:run c)) false)) (rw [hr]) (exact hz)
    (simp only [rof-pair hz hrne Bool.not_false Bool.true_or Bool.or_true Bool.false_or]))
  (have hpc (= (rc-ok gxz gkz r c) true))
  (simp only [rc-ok cur-pair cur-core hne hrr Bool.not_false Bool.true_or Bool.and_true Bool.or_true])
  (simp only [i10-current-run-ok Bool.and_eq_true] at a1)
  (simp only [i10-current-run-ok tbl-all hpc (And.left a1) (And.right a1) Bool.true_and Bool.and_self]))

(a/theorem i10-current-exempt-keys-ok-comp-ins [gxz :- (List Nat), gkz :- (List Nat), rks :- (List I10CurrentRunKey), cks :- (List I10CurrentCompKey), tks :- (List I10CurrentTaskKey), n :- Nat, c :- I10CurrentCompKey]
  (=> (= (i10-current-exempt-keys-ok gxz gkz rks cks tks n) true) (= (:id c) n) (= (:run c) 0) (<= 1 (:epoch c))
      (= (i10-current-exempt-keys-ok gxz gkz rks (List.cons I10CurrentCompKey c cks) tks (+ n 1)) true))
  (intros h hi hr he)
  (have h0 := h) (simp only [i10-current-exempt-keys-ok Bool.and_eq_true] at h0)
  (have h2 := (i10-current-exempt-keys-ok-next gxz gkz rks cks tks n (+ n 1) (Nat.le_succ n) h))
  (simp only [i10-current-exempt-keys-ok Bool.and_eq_true] at h2)
  (have hc (= (i10-current-comp-ok (+ n 1) c) true)) (simp only [i10-current-comp-ok below0 hr Nat.beq_refl Bool.true_or Bool.and_true Nat.ble_eq]) (exact he)
  (simp only [i10-current-exempt-keys-ok Bool.and_eq_true tbl-all hc (And.left (And.right h2)) (And.right (And.right h2)) Bool.true_and and_true])
  (exact (tbl-all-mono I10CurrentRunKey _ _ (fn [r :- I10CurrentRunKey, a0 :- (= (i10-current-run-ok gxz gkz cks tks n r) true)] (i10-current-run-ok-comp-ins gxz gkz cks tks n c r a0 hi hr))
           rks (And.left h0))))

;; ---- computation rows that wake, react or step the epoch: the pair facts

(a/theorem rc-step [gxz :- (List Nat), gkz :- (List Nat), r :- I10CurrentRunKey, c :- I10CurrentCompKey, d :- Nat, i :- Bool]
  (=> (= (rc-ok gxz gkz r c) true) (= (rc-ok gxz gkz r (I10CurrentCompKey.mk (:id c) (+ (:epoch c) 1) d (:run c) i)) true))
  (intro h)
  (simp only [rc-ok] at h)
  (have e1 (= (rof-pair r (I10CurrentCompKey.mk (:id c) (+ (:epoch c) 1) d (:run c) i)) (rof-pair r c))) (rfl)
  (simp only [rc-ok e1])
  (cases hk (reach-mem (:id r) gkz))
  (case [true] (simp only [Bool.true_or]))
  (case [false]
    (simp only [hk Bool.false_or Bool.and_eq_true] at h)
    (simp only [Bool.false_or (And.right h) Bool.and_true])
    (have hc := (And.left h))
    (simp only [cur-pair] at hc)
    (simp only [cur-pair cur-core])
    (cases ho (Nat.beq (:of r) (:id c)))
    (case [false] (simp only [ho Bool.not_false Bool.true_or]))
    (case [true]
      (simp only [cur-core ho Bool.not_true Bool.false_or Bool.and_eq_true Nat.ble_eq] at hc)
      (have le := (And.left hc))
      (have b1 (= (Nat.ble (:epoch r) (+ (:epoch c) 1)) true)) (simp only [Nat.ble_eq]) (omega)
      (have b2 (= (Nat.beq (:epoch r) (+ (:epoch c) 1)) false))
      (cases hb (Nat.beq (:epoch r) (+ (:epoch c) 1)))
      (rfl)
      (have z := (Nat.eq_of_beq_eq_true hb)) (omega)
      (simp only [ho b1 b2 Bool.not_true Bool.not_false Bool.false_or Bool.true_or Bool.true_and]))))

(a/theorem rc-wake [gxz :- (List Nat), gkz :- (List Nat), r :- I10CurrentRunKey, c :- I10CurrentCompKey, d :- Nat]
  (=> (= (rc-ok gxz gkz r c) true) (=> (= (cur-fin gxz r c) true) (= (cur-fin gxz r (I10CurrentCompKey.mk (:id c) (:epoch c) d (:run c) false)) true))
      (= (rc-ok gxz gkz r (I10CurrentCompKey.mk (:id c) (:epoch c) d (:run c) false)) true))
  (intros h hf)
  (simp only [rc-ok] at h)
  (have e1 (= (rof-pair r (I10CurrentCompKey.mk (:id c) (:epoch c) d (:run c) false)) (rof-pair r c))) (rfl)
  (simp only [rc-ok e1])
  (cases hk (reach-mem (:id r) gkz))
  (case [true] (simp only [Bool.true_or]))
  (case [false]
    (simp only [hk Bool.false_or Bool.and_eq_true] at h)
    (simp only [Bool.false_or (And.right h) Bool.and_true])
    (have hc := (And.left h))
    (simp only [cur-pair] at hc)
    (simp only [cur-pair cur-core])
    (cases ho (Nat.beq (:of r) (:id c)))
    (case [false] (simp only [ho Bool.not_false Bool.true_or]))
    (case [true]
      (simp only [cur-core ho Bool.not_true Bool.false_or Bool.and_eq_true] at hc)
      (cases he (Nat.beq (:epoch r) (:epoch c)))
      (case [false] (simp only [ho he (And.left hc) Bool.not_true Bool.not_false Bool.false_or Bool.true_or Bool.true_and]))
      (case [true]
        (simp only [he Bool.not_true Bool.false_or Bool.and_eq_true] at hc)
        (simp only [ho he (And.left hc) (And.left (And.right hc)) (hf (And.right (And.right (And.right hc))))
                    Bool.not_true Bool.not_false Bool.false_or Bool.true_and Bool.and_self])))))

(a/theorem fin-wake [gxz :- (List Nat), r :- I10CurrentRunKey, c :- I10CurrentCompKey]
  (=> (= (cur-fin gxz r c) true) (= (cur-fin gxz r (I10CurrentCompKey.mk (:id c) (:epoch c) (:done c) (:run c) false)) true))
  (intro h) (exact h))
(a/theorem fin-react [gxz :- (List Nat), r :- I10CurrentRunKey, c :- I10CurrentCompKey]
  (=> (= (cur-fin gxz r c) true) (= (cur-fin gxz r (I10CurrentCompKey.mk (:id c) (:epoch c) (:epoch c) (:run c) false)) true))
  (intro h) (simp only [cur-fin Nat.beq_refl Bool.or_true]))

(a/theorem i10-current-comp-ok-step [n :- Nat, c :- I10CurrentCompKey, d :- Nat, i :- Bool]
  (=> (= (i10-current-comp-ok n c) true) (= (i10-current-comp-ok n (I10CurrentCompKey.mk (:id c) (+ (:epoch c) 1) d (:run c) i)) true))
  (intro h) (simp only [i10-current-comp-ok Bool.and_eq_true Nat.ble_eq] at h) (simp only [i10-current-comp-ok Bool.and_eq_true Nat.ble_eq (And.right h) and_true]) (try (omega)))
(a/theorem i10-current-comp-ok-wake [n :- Nat, c :- I10CurrentCompKey, d :- Nat]
  (=> (= (i10-current-comp-ok n c) true) (= (i10-current-comp-ok n (I10CurrentCompKey.mk (:id c) (:epoch c) d (:run c) false)) true))
  (intro h) (exact h))

(a/theorem i10-current-exempt-up-react [gxz :- (List Nat), gkz :- (List Nat), w :- World, x :- Nat]
  (=> (= (i10-current-exempt gxz gkz w) true) (= (i10-current-exempt gxz gkz (comp-upd w x comp-react-row)) true))
  (exact (i10-current-exempt-comp-upd-g gxz gkz w x comp-react-row comp-react-row-id comp-react-row-pending
           (fn [k :- I10CurrentCompKey] (I10CurrentCompKey.mk (:id k) (:epoch k) (:epoch k) (:run k) false)) (fn [c :- CompRow] (Eq.refl (i10-current-comp-key (comp-react-row c))))
           (fn [r :- I10CurrentRunKey, k :- I10CurrentCompKey, q :- (= (rc-ok gxz gkz r k) true)] (rc-wake gxz gkz r k (:epoch k) q (fin-react gxz r k)))
           (fn [k :- I10CurrentCompKey, q :- (= (i10-current-comp-ok (:next-id w) k) true)] (i10-current-comp-ok-wake (:next-id w) k (:epoch k) q)))))

(a/theorem i10-current-exempt-up-inc-epoch [gxz :- (List Nat), gkz :- (List Nat), w :- World, x :- Nat]
  (=> (= (i10-current-exempt gxz gkz w) true) (= (i10-current-exempt gxz gkz (comp-upd w x comp-inc-epoch)) true))
  (exact (i10-current-exempt-comp-upd-g gxz gkz w x comp-inc-epoch comp-inc-epoch-comp-id comp-inc-epoch-pending
           (fn [k :- I10CurrentCompKey] (I10CurrentCompKey.mk (:id k) (+ (:epoch k) 1) (:done k) (:run k) (:idle k))) (fn [c :- CompRow] (Eq.refl (i10-current-comp-key (comp-inc-epoch c))))
           (fn [r :- I10CurrentRunKey, k :- I10CurrentCompKey, q :- (= (rc-ok gxz gkz r k) true)] (rc-step gxz gkz r k (:done k) (:idle k) q))
           (fn [k :- I10CurrentCompKey, q :- (= (i10-current-comp-ok (:next-id w) k) true)] (i10-current-comp-ok-step (:next-id w) k (:done k) (:idle k) q)))))

(a/theorem i10-current-exempt-up-replace [gxz :- (List Nat), gkz :- (List Nat), w :- World, x :- Nat, i :- (List Nat), b :- Nat]
  (=> (= (i10-current-exempt gxz gkz w) true) (= (i10-current-exempt gxz gkz (comp-upd w x (comp-replace-row i b))) true))
  (exact (i10-current-exempt-comp-upd-g gxz gkz w x (comp-replace-row i b) (comp-replace-row-id i b) (comp-replace-row-pending i b)
           (fn [k :- I10CurrentCompKey] (I10CurrentCompKey.mk (:id k) (+ (:epoch k) 1) (if (:idle k) 0 (:done k)) (:run k) false))
           (fn [c :- CompRow] (Eq.refl (i10-current-comp-key (comp-replace-row i b c))))
           (fn [r :- I10CurrentRunKey, k :- I10CurrentCompKey, q :- (= (rc-ok gxz gkz r k) true)] (rc-step gxz gkz r k (if (:idle k) 0 (:done k)) false q))
           (fn [k :- I10CurrentCompKey, q :- (= (i10-current-comp-ok (:next-id w) k) true)] (i10-current-comp-ok-step (:next-id w) k (if (:idle k) 0 (:done k)) false q)))))

(a/defn demand-ck [k :- I10CurrentCompKey] I10CurrentCompKey
  (I10CurrentCompKey.mk (:id k) (if (Nat.beq (:done k) 0) (:epoch k) (+ (:epoch k) 1)) (:done k) (:run k) false))
(a/theorem rc-demand [gxz :- (List Nat), gkz :- (List Nat), r :- I10CurrentRunKey, k :- I10CurrentCompKey]
  (=> (= (rc-ok gxz gkz r k) true) (= (rc-ok gxz gkz r (demand-ck k)) true))
  (intro q)
  (cases hd (Nat.beq (:done k) 0))
  (case [true] (simp only [demand-ck hd]) (exact (rc-wake gxz gkz r k (:done k) q (fin-wake gxz r k))))
  (case [false] (simp only [demand-ck hd]) (exact (rc-step gxz gkz r k (:done k) false q))))
(a/theorem i10-current-comp-ok-demand [n :- Nat, k :- I10CurrentCompKey] (=> (= (i10-current-comp-ok n k) true) (= (i10-current-comp-ok n (demand-ck k)) true))
  (intro q)
  (cases hd (Nat.beq (:done k) 0))
  (case [true] (simp only [demand-ck hd]) (exact (i10-current-comp-ok-wake n k (:done k) q)))
  (case [false] (simp only [demand-ck hd]) (exact (i10-current-comp-ok-step n k (:done k) false q))))
(a/theorem i10-current-exempt-up-demand [gxz :- (List Nat), gkz :- (List Nat), w :- World, x :- Nat]
  (=> (= (i10-current-exempt gxz gkz w) true) (= (i10-current-exempt gxz gkz (comp-upd w x comp-demand-row)) true))
  (exact (i10-current-exempt-comp-upd-g gxz gkz w x comp-demand-row comp-demand-row-id comp-demand-row-pending demand-ck
           (fn [c :- CompRow] (Eq.refl (i10-current-comp-key (comp-demand-row c))))
           (rc-demand gxz gkz) (i10-current-comp-ok-demand (:next-id w)))))

(a/theorem run-park-i10-current-run-key [r :- RunRow] (= (i10-current-run-key (run-park-row r)) (i10-current-run-key-up (i10-current-run-key r))) (rfl))
(a/theorem run-wake-i10-current-run-key [r :- RunRow] (= (i10-current-run-key (run-wake r)) (i10-current-run-key r)) (simp only [i10-current-run-key run-wake-alive]))

(a/theorem run-tick-park-i10-current-run-key [r :- RunRow] (= (i10-current-run-key (run-tick-park r)) (i10-current-run-key-up (i10-current-run-key r))) (rfl))
(a/theorem i10-current-task-key-cancel-result [t :- TaskRow] (= (i10-current-task-key (task-cancel-result t)) (i10-current-task-key t))
  (cases hn (Nat.beq (:tag (:result t)) res-none))
  (case [true] (simp only [task-cancel-result hn i10-current-task-key]))
  (case [false] (simp only [task-cancel-result hn])))
(a/theorem tof-clear [r :- I10CurrentRunKey, t :- I10CurrentTaskKey] (=> (= (tof-pair r t) true) (= (tof-pair r (I10CurrentTaskKey.mk (:id t) 0)) true))
  (intro h)
  (cases hz (Nat.beq (:id r) 0))
  (case [true] (simp only [tof-pair hz Bool.true_or]))
  (case [false] (simp only [tof-pair hz Bool.not_false Bool.false_or Bool.true_or])))
(a/theorem i10-current-task-ok-clear [n :- Nat, t :- I10CurrentTaskKey] (=> (= (i10-current-task-ok n t) true) (= (i10-current-task-ok n (I10CurrentTaskKey.mk (:id t) 0)) true))
  (intro h) (simp only [i10-current-task-ok below0 Nat.beq_refl Bool.true_or]))
(a/theorem i10-current-exempt-task-clear [gxz :- (List Nat), gkz :- (List Nat), w :- World, x :- Nat]
  (=> (= (i10-current-exempt gxz gkz w) true) (= (i10-current-exempt gxz gkz (task-upd w x task-clear-run)) true))
  (exact (i10-current-exempt-task-upd-g gxz gkz w x task-clear-run task-clear-run-id (fn [k :- I10CurrentTaskKey] (I10CurrentTaskKey.mk (:id k) 0))
           (fn [t :- TaskRow] (Eq.refl (i10-current-task-key (task-clear-run t)))) tof-clear (i10-current-task-ok-clear (:next-id w)))))

(a/theorem i10-current-exempt-comp-ins-fresh [gxz :- (List Nat), gkz :- (List Nat), w :- World, r :- CompRow, hf :- (= (fresh-ck r) true)]
  (=> (= (comp-id r) (:next-id w)) (= (:pending r) (marked-in (:id r) (:edges w))) (= (i10-current-exempt gxz gkz w) true)
      (= (i10-current-exempt gxz gkz (bump (comp-ins w r))) true))
  (intros hr hp h)
  (simp only [fresh-ck Bool.and_eq_true Nat.ble_eq] at hf)
  (have e0 (= (:run r) 0)) (exact (Nat.eq_of_beq_eq_true (And.left hf)))
  (have hi (= (:id (i10-current-comp-key r)) (:next-id w))) (exact hr)
  (have hrest (= (i10-current-exempt-rest gxz gkz (bump (comp-ins w r))) true))
  (simp only [i10-current-exempt-rest bump comp-ins set-next-id set-comps tbl-ins i10-current-comp-keys])
  (exact (i10-current-exempt-keys-ok-comp-ins gxz gkz _ _ _ _ (i10-current-comp-key r) (i10-current-exempt-rest-of gxz gkz w h) hi e0 (And.right hf)))
  (exact (i10-current-exempt-intro gxz gkz _ (well-formed-comp-ins-fresh w r hr hp (i10-current-exempt-well-formed gxz gkz w h)) hrest)))

;; ===========================================================================
;; Part B. The bundle copy
;; ===========================================================================

;; g10's exempt form (spindel.v2.pres.exempt; recorded, no aliases yet)
(exempt/defexempt 'i10-current
  :form "i10-current-exempt gxz gkz w"
  :ids "gxz computation ids (demoted later in the same normalization round: E2 waived); gkz run ids (being retired: E1, E2, rof waived)"
  :commit "i10-current-exempt [] [] = i10-current (chain-to-i10-current)")
(def G10 (mk-bundle 'i10-current-exempt '[gxz :- (List Nat), gkz :- (List Nat)] "i10-current-exempt-"
           {'well-formed-run-upd ['(fn [r :- RunRow] (Eq.refl (i10-current-run-key r))) 4]
            'well-formed-comp-upd ['(fn [c :- CompRow] (Eq.refl (i10-current-comp-key c))) 5]
            'well-formed-task-upd ['(fn [t :- TaskRow] (Eq.refl (i10-current-task-key t))) 4]
            'well-formed-comp-ins-fresh ['(Eq.refl true) 2]}))
(swap! (:renames G10) assoc 'well-formed-parts 'i10-current-exempt-parts 'well-formed-run-upd 'i10-current-exempt-run-upd 'well-formed-comp-upd 'i10-current-exempt-comp-upd
       'well-formed-task-upd 'i10-current-exempt-task-upd 'well-formed-comp-ins-fresh 'i10-current-exempt-comp-ins-fresh)

(defpart G10 :reads '[comps next-id runs tasks])
(doseq [o '[well-formed-source-ins-fresh well-formed-fork-ins-fresh well-formed-resource-ins-fresh well-formed-scope-ins-fresh well-formed-act-ins-fresh]]
  (prim! G10 o (list 'i10-current-exempt-rest-bump 'gxz 'gkz (list (symbol (str/replace (subs (name o) 12) "-fresh" "")) 'w 'r)
                     (list 'Eq.trans '(rfl) 'R))))
(prim! G10 'well-formed-bump '(i10-current-exempt-rest-bump gxz gkz w R))
(prim! G10 'well-formed-mark-edge '(Eq.trans (i10-current-exempt-rest-frame gxz gkz w (mark-edge w x) (i10-current-view-mark-edge w x)) R))
(prim! G10 'well-formed-unmark-edge '(Eq.trans (i10-current-exempt-rest-frame gxz gkz w (unmark-edge w x) (i10-current-view-unmark-edge w x)) R))
(prim! G10 'well-formed-remove-edge '(Eq.trans (i10-current-exempt-rest-frame gxz gkz w (remove-edge w x) (i10-current-view-remove-edge w x)) R))
(prim! G10 'well-formed-drop-cred-edges '(Eq.trans (i10-current-exempt-rest-frame gxz gkz w (drop-cred-edges w a) (i10-current-view-drop-cred w a)) R))
(prim! G10 'well-formed-drop-act '(Eq.trans (i10-current-exempt-rest-frame gxz gkz w (drop-act w a) (i10-current-view-drop-act w a)) R))
(prim! G10 'well-formed-drop-edges '(Eq.trans (i10-current-exempt-rest-frame gxz gkz w (drop-edges w p) (i10-current-view-drop-edges w p)) R))
(prim! G10 'well-formed-comp-del-unref '(i10-current-exempt-rest-comp-del gxz gkz w x R))
(prim! G10 'well-formed-run-del '(i10-current-exempt-rest-run-del gxz gkz w x R))
(prim! G10 'well-formed-filter-world '(i10-current-exempt-rest-filter gxz gkz w K R))
(prim! G10 'well-formed-insert-edge-fresh '(i10-current-exempt-rest-bump gxz gkz (insert-edge w (edge-set-id (:next-id w) e)) (Eq.trans (rfl) R)))

;; i10-current-exempt on the generic tree (spindel.v2.pres.tree): its table. Its own proofs are in Parts D to H.
(def ^:private up-comp-fns   ; computation row functions that change a key, with g10's lemma
  '{comp-react-row i10-current-exempt-up-react comp-demand-row i10-current-exempt-up-demand comp-inc-epoch i10-current-exempt-up-inc-epoch comp-replace-row i10-current-exempt-up-replace})
(tree/part! G10
  ;; ---- the part's own proofs (content)
  :over '{well-formed-t13-retire-with-subtree      i10-current-exempt-t13-retire-with-subtree       ; T13: the retired run is exempt (gkz) until its row goes
          well-formed-cancel-run-local i10-current-exempt-cancel-run-local  ; T14 local: the run is made done under the job condition
          well-formed-job-apply        i10-current-exempt-job-apply         ; the cascade under the job condition (job-ok) ...
          well-formed-cascade          i10-current-exempt-cascade           ;   ... which every job's successors keep (jl-step)
          well-formed-run-cascade      i10-current-exempt-run-cascade
          well-formed-t14-cancel              i10-current-exempt-t14-cancel               ; T14: the cancelled run is no current run of a kept computation
          well-formed-t14-host-cancel         i10-current-exempt-t14-host-cancel          ; T-cancel: a task's run (found-task-ncw)
          well-formed-cancel-losers    i10-current-exempt-cancel-losers     ; the losers of an accepted await
          well-formed-cancel-pred      i10-current-exempt-cancel-pred       ; T11: the predecessor run
          well-formed-dispatch-raw     i10-current-exempt-dispatch-raw      ; T11: C.run := the new run (i10-current-transport and comp-exists carry the keys)
          well-formed-spawn-rows       i10-current-exempt-spawn-rows        ; T4: a task's run
          well-formed-complete-raw     i10-current-exempt-complete-raw      ; T12: the run is done; a current run sets done-epoch
          well-formed-demote           i10-current-exempt-demote            ; demotion: cid leaves the exempt list with no current run
          well-formed-normalize-round       i10-current-exempt-normalize-round        ; a round: the stray computations are exempt until demoted
          well-formed-normalize-loop        i10-current-exempt-normalize-loop
          well-formed-normalize        i10-current-exempt-normalize}
  ;; ---- sites: a computation, run or task edit by a row function that changes a key, by its lemma
  :sites (merge (tree/row-sites 'well-formed-comp-upd up-comp-fns
                  (fn [F] (concat (list (up-comp-fns (if (seq? F) (first F) F)) 'gxz 'gkz 'w 'x) (when (seq? F) (rest F)) '(h0))))
                '{[well-formed-run-upd run-park-row]        (i10-current-exempt-run-upd-up gxz gkz w x run-park-row hf run-park-i10-current-run-key h0)
                  [well-formed-run-upd run-tick-park]       (i10-current-exempt-run-upd-up gxz gkz w x run-tick-park hf run-tick-park-i10-current-run-key h0)
                  [well-formed-run-upd run-wake]            (i10-current-exempt-run-upd gxz gkz w x run-wake hf run-wake-i10-current-run-key h0)
                  [well-formed-task-upd task-cancel-result] (i10-current-exempt-task-upd gxz gkz w x task-cancel-result hf i10-current-task-key-cancel-result h0)
                  [well-formed-task-upd task-clear-run]     (i10-current-exempt-task-clear gxz gkz w x h0)})
  ;; ---- facts from the path. The cascade's job condition names the exempt lists (the part's
  ;; parameters): a cancel job's run is no current run of a kept computation (ncw).
  :ctx '{well-formed-cancel-run-local [(= (ncw gxz gkz (:id r) w) true)]
         well-formed-job-apply        [(= (job-ok gxz gkz w j) true)]
         well-formed-run-cascade      [(= (tbl-all (job-ok gxz gkz w) js) true)]
         well-formed-t14-cancel              [(= (ncw gxz gkz rid w) true)]
         well-formed-cancel-pred      [(List.Mem c (:comps w)) (= (needs-run w c) true)]
         well-formed-dispatch-raw     [(List.Mem c (:comps w)) (= (:idle c) false) (= (needs-run w c) true)]
         well-formed-complete-raw     [(List.Mem r (:runs w))]
         well-formed-normalize-round       [(= (tbl-all (ta-one (:comps w)) (:runs w)) true)]
         well-formed-normalize        [(= (acts-alive w) true) (= (tombs-dormant 0 w) true)]}
  :pass '{;; cascades of retire and close jobs: the job condition holds by computation
          well-formed-t16-close-scope             {well-formed-run-cascade [(Eq.refl true)]}
          well-formed-t15-resource-ack        {well-formed-run-cascade [(Eq.refl true)]}
          well-formed-t-slice-exit    {well-formed-run-cascade [(Eq.refl true)]}
          well-formed-t21-release-world {well-formed-run-cascade [(Eq.refl true)]}
          well-formed-retire-one      {well-formed-run-cascade  [(Eq.refl true)]
                               well-formed-complete-raw [(retire-r1-mem w r r1 rid hf1)]}                    ; run-find found it
          well-formed-t12-complete             {well-formed-complete-raw [(And.left (tok-facts w st r ht))]}                  ; the token's run
          well-formed-t11-dispatch             {well-formed-dispatch-raw [(tbl-find-mem CompRow comp-id cid c (:comps w) hc)  ; comp-find found it;
                                                 (t11-dispatch-g-idle fresh (:next-id w) w c hg)              ;   T11's guard
                                                 (t11-dispatch-g-nr fresh (:next-id w) w c hg)]}})

;; ===========================================================================
;; Part C. Transport: pair predicates over (id, of, epoch) of runs and (id, epoch, idle) of
;; computations, kept by every edit of the cascade, the cut and the entry (no run or computation
;; is created there, epochs and idleness do not change)
;; ===========================================================================

(a/structure RS10 [] (id Nat) (of Nat) (epoch Nat))
(a/defn rs10 [r :- RunRow] RS10 (RS10.mk (:id r) (:of r) (:epoch r)))
(a/defn rs10-id [k :- RS10] Nat (:id k))
(a/structure CS10 [] (id Nat) (epoch Nat) (idle Bool))
(a/defn cs10 [c :- CompRow] CS10 (CS10.mk (:id c) (:epoch c) (:idle c)))
(a/defn cs10-id [k :- CS10] Nat (:id k))
(a/defn rs10s [rs :- (List RunRow)] (List RS10)
  (match rs [nil (List.nil RS10)] [(cons h t) (List.cons RS10 (rs10 h) (rs10s t))]))
(a/defn cs10s [cs :- (List CompRow)] (List CS10)
  (match cs [nil (List.nil CS10)] [(cons h t) (List.cons CS10 (cs10 h) (cs10s t))]))

(a/defn cs-step [c :- CS10] CS10 (CS10.mk (:id c) (+ (:epoch c) 1) (:idle c)))
(a/defn i10-current-transport-row [nqr :- (=> RS10 CS10 Bool), cks :- (List CS10), r :- RS10] Bool (tbl-all (nqr r) cks))
(a/defn nqk [nqr :- (=> RS10 CS10 Bool), nqc :- (=> CS10 Bool), rks :- (List RS10), cks :- (List CS10)] Bool
  (Bool.and (tbl-all (i10-current-transport-row nqr cks) rks) (tbl-all nqc cks)))
(a/defn i10-current-transport-rest [nqr :- (=> RS10 CS10 Bool), nqc :- (=> CS10 Bool),
                 nqm :- (forall [r :- RS10, c :- CS10] (=> (= (nqr r c) true) (= (nqr r (cs-step c)) true))),
                       nqcm :- (forall [c :- CS10] (=> (= (nqc c) true) (= (nqc (cs-step c)) true))), w :- World] Bool
  (nqk nqr nqc (rs10s (:runs w)) (cs10s (:comps w))))
(a/defn i10-current-transport [nqr :- (=> RS10 CS10 Bool), nqc :- (=> CS10 Bool),
         nqm :- (forall [r :- RS10, c :- CS10] (=> (= (nqr r c) true) (= (nqr r (cs-step c)) true))),
         nqcm :- (forall [c :- CS10] (=> (= (nqc c) true) (= (nqc (cs-step c)) true))), w :- World] Bool
  (Bool.and (well-formed w) (i10-current-transport-rest nqr nqc nqm nqcm w)))

(a/theorem i10-current-transport-well-formed [nqr :- (=> RS10 CS10 Bool), nqc :- (=> CS10 Bool),
                     nqm :- (forall [r :- RS10, c :- CS10] (=> (= (nqr r c) true) (= (nqr r (cs-step c)) true))),
                     nqcm :- (forall [c :- CS10] (=> (= (nqc c) true) (= (nqc (cs-step c)) true))), w :- World] (=> (= (i10-current-transport nqr nqc nqm nqcm w) true) (= (well-formed w) true))
  (intro h) (simp only [i10-current-transport Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem i10-current-transport-rest-of [nqr :- (=> RS10 CS10 Bool), nqc :- (=> CS10 Bool),
                     nqm :- (forall [r :- RS10, c :- CS10] (=> (= (nqr r c) true) (= (nqr r (cs-step c)) true))),
                     nqcm :- (forall [c :- CS10] (=> (= (nqc c) true) (= (nqc (cs-step c)) true))), w :- World] (=> (= (i10-current-transport nqr nqc nqm nqcm w) true) (= (i10-current-transport-rest nqr nqc nqm nqcm w) true))
  (intro h) (simp only [i10-current-transport Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem i10-current-transport-intro [nqr :- (=> RS10 CS10 Bool), nqc :- (=> CS10 Bool),
                     nqm :- (forall [r :- RS10, c :- CS10] (=> (= (nqr r c) true) (= (nqr r (cs-step c)) true))),
                     nqcm :- (forall [c :- CS10] (=> (= (nqc c) true) (= (nqc (cs-step c)) true))), w :- World]
  (=> (= (well-formed w) true) (= (i10-current-transport-rest nqr nqc nqm nqcm w) true) (= (i10-current-transport nqr nqc nqm nqcm w) true))
  (intros h1 h2) (simp only [i10-current-transport h1 h2 Bool.and_self]))
(a/theorem i10-current-transport-parts [nqr :- (=> RS10 CS10 Bool), nqc :- (=> CS10 Bool),
                     nqm :- (forall [r :- RS10, c :- CS10] (=> (= (nqr r c) true) (= (nqr r (cs-step c)) true))),
                     nqcm :- (forall [c :- CS10] (=> (= (nqc c) true) (= (nqc (cs-step c)) true))), w :- World]
  (=> (= (i10-current-transport nqr nqc nqm nqcm w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (i10-current-transport-well-formed nqr nqc nqm nqcm w h))))

(a/theorem rs10s-same [x :- Nat, f :- (=> RunRow RunRow), hk :- (forall [r :- RunRow] (= (rs10 (f r)) (rs10 r))), rs :- (List RunRow)]
  (= (rs10s (tbl-upd run-id x f rs)) (rs10s rs))
  (induction rs)
  (case [nil] (simp only [tbl-upd rs10s]))
  (case [cons h t ih] (cases hx (Nat.beq (run-id h) x)) (all_goals (simp only [tbl-upd hx rs10s ih (hk h)]))))
(a/theorem cs10s-same [x :- Nat, f :- (=> CompRow CompRow), hk :- (forall [c :- CompRow] (= (cs10 (f c)) (cs10 c))), cs :- (List CompRow)]
  (= (cs10s (tbl-upd comp-id x f cs)) (cs10s cs))
  (induction cs)
  (case [nil] (simp only [tbl-upd cs10s]))
  (case [cons h t ih] (cases hx (Nat.beq (comp-id h) x)) (all_goals (simp only [tbl-upd hx cs10s ih (hk h)]))))
(a/theorem rs10s-del [x :- Nat, rs :- (List RunRow)] (= (rs10s (tbl-del run-id x rs)) (tbl-del rs10-id x (rs10s rs)))
  (induction rs)
  (case [nil] (simp only [tbl-del rs10s]))
  (case [cons h t ih]
    (have e (= (Nat.beq (rs10-id (rs10 h)) x) (Nat.beq (run-id h) x))) (rfl)
    (cases hx (Nat.beq (run-id h) x)) (all_goals (simp only [tbl-del hx rs10s e ih]))))
(a/theorem cs10s-del [x :- Nat, cs :- (List CompRow)] (= (cs10s (tbl-del comp-id x cs)) (tbl-del cs10-id x (cs10s cs)))
  (induction cs)
  (case [nil] (simp only [tbl-del cs10s]))
  (case [cons h t ih]
    (have e (= (Nat.beq (cs10-id (cs10 h)) x) (Nat.beq (comp-id h) x))) (rfl)
    (cases hx (Nat.beq (comp-id h) x)) (all_goals (simp only [tbl-del hx cs10s e ih]))))
(a/theorem rs10s-keep [K :- (=> Nat Bool), rs :- (List RunRow)] (= (rs10s (tbl-keep K run-id rs)) (tbl-keep K rs10-id (rs10s rs)))
  (induction rs)
  (case [nil] (simp only [tbl-keep rs10s]))
  (case [cons h t ih]
    (have e (= (K (rs10-id (rs10 h))) (K (run-id h)))) (rfl)
    (cases hk (K (run-id h))) (all_goals (simp only [tbl-keep rs10s e hk ih]))))
(a/theorem cs10s-keep [K :- (=> Nat Bool), cs :- (List CompRow)] (= (cs10s (tbl-keep K comp-id cs)) (tbl-keep K cs10-id (cs10s cs)))
  (induction cs)
  (case [nil] (simp only [tbl-keep cs10s]))
  (case [cons h t ih]
    (have e (= (K (cs10-id (cs10 h))) (K (comp-id h)))) (rfl)
    (cases hk (K (comp-id h))) (all_goals (simp only [tbl-keep cs10s e hk ih]))))
(a/theorem cs10s-upd [x :- Nat, f :- (=> CompRow CompRow), g :- (=> CS10 CS10),
                      hc :- (forall [c :- CompRow] (= (cs10 (f c)) (g (cs10 c)))), cs :- (List CompRow)]
  (= (cs10s (tbl-upd comp-id x f cs)) (tbl-upd cs10-id x g (cs10s cs)))
  (induction cs)
  (case [nil] (simp only [tbl-upd cs10s]))
  (case [cons h t ih]
    (cases hx (Nat.beq (comp-id h) x))
    (case [false]
      (have hx2 (= (Nat.beq (cs10-id (cs10 h)) x) false)) (exact hx)
      (simp only [tbl-upd hx cs10s hx2 ih]))
    (case [true]
      (have hx2 (= (Nat.beq (cs10-id (cs10 h)) x) true)) (exact hx)
      (simp only [tbl-upd hx cs10s hx2 ih (hc h)]))))
(a/theorem cs10s-resync [es :- (List EdgeRow), cs :- (List CompRow)] (= (cs10s (comps-resync es cs)) (cs10s cs))
  (induction cs)
  (case [nil] (simp only [comps-resync cs10s]))
  (case [cons h t ih] (have e (= (cs10 (comp-resync es h)) (cs10 h))) (rfl) (simp only [comps-resync cs10s e ih])))

(a/theorem nqk-sub [nqr :- (=> RS10 CS10 Bool), nqc :- (=> CS10 Bool), rks :- (List RS10), rks2 :- (List RS10), cks :- (List CS10), cks2 :- (List CS10),
                    hr :- (forall [p :- (=> RS10 Bool)] (=> (= (tbl-all p rks) true) (= (tbl-all p rks2) true))),
                    hc :- (forall [p :- (=> CS10 Bool)] (=> (= (tbl-all p cks) true) (= (tbl-all p cks2) true)))]
  (=> (= (nqk nqr nqc rks cks) true) (= (nqk nqr nqc rks2 cks2) true))
  (intro h)
  (simp only [nqk Bool.and_eq_true] at h)
  (simp only [nqk Bool.and_eq_true (hc _ (And.right h)) and_true])
  (exact (hr _ (tbl-all-mono RS10 _ _ (fn [r :- RS10, q :- (= (i10-current-transport-row nqr cks r) true)] (hc (nqr r) q)) rks (And.left h)))))

(a/structure KS10 [] (rks (List RS10)) (cks (List CS10)))
(a/defn ks10 [w :- World] KS10 (KS10.mk (rs10s (:runs w)) (cs10s (:comps w))))
(a/theorem i10-current-transport-ks [nqr :- (=> RS10 CS10 Bool), nqc :- (=> CS10 Bool), nqm :- (forall [r :- RS10, c :- CS10] (=> (= (nqr r c) true) (= (nqr r (cs-step c)) true))),
                       nqcm :- (forall [c :- CS10] (=> (= (nqc c) true) (= (nqc (cs-step c)) true))), w :- World, w2 :- World]
  (=> (= (ks10 w2) (ks10 w)) (= (i10-current-transport-rest nqr nqc nqm nqcm w2) (i10-current-transport-rest nqr nqc nqm nqcm w)))
  (intro e)
  (have e1 (= (rs10s (:runs w2)) (rs10s (:runs w)))) (exact (congrArg (fn [k :- KS10] (:rks k)) e))
  (have e2 (= (cs10s (:comps w2)) (cs10s (:comps w)))) (exact (congrArg (fn [k :- KS10] (:cks k)) e))
  (simp only [i10-current-transport-rest e1 e2]))
(a/theorem ks10-comp-same [w :- World, x :- Nat, f :- (=> CompRow CompRow), hk :- (forall [c :- CompRow] (= (cs10 (f c)) (cs10 c)))]
  (= (ks10 (comp-upd w x f)) (ks10 w))
  (simp only [ks10 comp-upd set-comps (cs10s-same x f hk (:comps w))]))
(a/theorem ks10-mark-edge [w :- World, x :- Nat] (= (ks10 (mark-edge w x)) (ks10 w))
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]))
  (case [some e]
    (cases hm (:marked e))
    (case [true] (simp only [mark-edge hf hm]))
    (case [false] (simp only [mark-edge hf hm])
      (exact (Eq.trans (ks10-comp-same _ (:creditor e) comp-inc-pending (fn [c :- CompRow] (Eq.refl (cs10 c)))) (rfl))))))
(a/theorem ks10-unmark-edge [w :- World, x :- Nat] (= (ks10 (unmark-edge w x)) (ks10 w))
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [unmark-edge hf hm]))
    (case [true] (simp only [unmark-edge hf hm])
      (exact (Eq.trans (ks10-comp-same _ (:creditor e) comp-dec-pending (fn [c :- CompRow] (Eq.refl (cs10 c)))) (rfl))))))
(a/theorem ks10-remove-edge [w :- World, x :- Nat] (= (ks10 (remove-edge w x)) (ks10 w))
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [remove-edge hf hm]))
    (case [true] (simp only [remove-edge hf hm])
      (exact (Eq.trans (ks10-comp-same _ (:creditor e) comp-dec-pending (fn [c :- CompRow] (Eq.refl (cs10 c)))) (rfl))))))
(a/theorem ks10-drop-cred [w :- World, a :- Nat] (= (ks10 (drop-cred-edges w a)) (ks10 w))
  (simp only [drop-cred-edges])
  (exact (Eq.trans (ks10-comp-same _ a (comp-set-pending 0) (fn [c :- CompRow] (Eq.refl (cs10 c)))) (rfl))))
(a/theorem ks10-drop-act [w :- World, a :- Nat] (= (ks10 (drop-act w a)) (ks10 w))
  (simp only [drop-act]) (exact (Eq.trans (rfl) (ks10-drop-cred w a))))
(a/theorem ks10-drop-edges [w :- World, p :- (=> EdgeRow Bool)] (= (ks10 (drop-edges w p)) (ks10 w))
  (simp only [ks10 drop-edges set-comps set-edges cs10s-resync]))

(a/theorem i10-current-transport-run-upd [nqr :- (=> RS10 CS10 Bool), nqc :- (=> CS10 Bool),
                     nqm :- (forall [r :- RS10, c :- CS10] (=> (= (nqr r c) true) (= (nqr r (cs-step c)) true))),
                     nqcm :- (forall [c :- CS10] (=> (= (nqc c) true) (= (nqc (cs-step c)) true))), w :- World, x :- Nat, f :- (=> RunRow RunRow),
                       hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                       hk :- (forall [r :- RunRow] (= (rs10 (f r)) (rs10 r)))]
  (=> (= (i10-current-transport nqr nqc nqm nqcm w) true) (= (i10-current-transport nqr nqc nqm nqcm (run-upd w x f)) true))
  (intro h)
  (have e (= (ks10 (run-upd w x f)) (ks10 w))) (simp only [ks10 run-upd set-runs (rs10s-same x f hk (:runs w))])
  (exact (i10-current-transport-intro nqr nqc nqm nqcm _ (well-formed-run-upd w x f hf (i10-current-transport-well-formed nqr nqc nqm nqcm w h)) (Eq.trans (i10-current-transport-ks nqr nqc nqm nqcm w _ e) (i10-current-transport-rest-of nqr nqc nqm nqcm w h)))))
(a/theorem i10-current-transport-comp-upd [nqr :- (=> RS10 CS10 Bool), nqc :- (=> CS10 Bool),
                     nqm :- (forall [r :- RS10, c :- CS10] (=> (= (nqr r c) true) (= (nqr r (cs-step c)) true))),
                     nqcm :- (forall [c :- CS10] (=> (= (nqc c) true) (= (nqc (cs-step c)) true))), w :- World, x :- Nat, f :- (=> CompRow CompRow),
                        hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                        hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                        hk :- (forall [c :- CompRow] (= (cs10 (f c)) (cs10 c)))]
  (=> (= (i10-current-transport nqr nqc nqm nqcm w) true) (= (i10-current-transport nqr nqc nqm nqcm (comp-upd w x f)) true))
  (intro h)
  (exact (i10-current-transport-intro nqr nqc nqm nqcm _ (well-formed-comp-upd w x f hid hp (i10-current-transport-well-formed nqr nqc nqm nqcm w h))
           (Eq.trans (i10-current-transport-ks nqr nqc nqm nqcm w _ (ks10-comp-same w x f hk)) (i10-current-transport-rest-of nqr nqc nqm nqcm w h)))))
(a/theorem i10-current-transport-rest-run-del [nqr :- (=> RS10 CS10 Bool), nqc :- (=> CS10 Bool), nqm :- (forall [r :- RS10, c :- CS10] (=> (= (nqr r c) true) (= (nqr r (cs-step c)) true))),
                       nqcm :- (forall [c :- CS10] (=> (= (nqc c) true) (= (nqc (cs-step c)) true))), w :- World, x :- Nat]
  (=> (= (i10-current-transport-rest nqr nqc nqm nqcm w) true) (= (i10-current-transport-rest nqr nqc nqm nqcm (run-del w x)) true))
  (intro h) (simp only [i10-current-transport-rest] at h) (simp only [i10-current-transport-rest run-del set-runs rs10s-del])
  (exact (nqk-sub nqr nqc _ _ _ _
           (fn [p :- (=> RS10 Bool), q :- (= (tbl-all p (rs10s (:runs w))) true)]
             (tbl-all-del RS10 rs10-id x p p (fn [c :- RS10, a1 :- (= (p c) true), a2 :- (= (Nat.beq (rs10-id c) x) false)] a1) _ q))
           (fn [p :- (=> CS10 Bool), q :- (= (tbl-all p (cs10s (:comps w))) true)] q) h)))
(a/theorem i10-current-transport-rest-comp-del [nqr :- (=> RS10 CS10 Bool), nqc :- (=> CS10 Bool), nqm :- (forall [r :- RS10, c :- CS10] (=> (= (nqr r c) true) (= (nqr r (cs-step c)) true))),
                       nqcm :- (forall [c :- CS10] (=> (= (nqc c) true) (= (nqc (cs-step c)) true))), w :- World, x :- Nat]
  (=> (= (i10-current-transport-rest nqr nqc nqm nqcm w) true) (= (i10-current-transport-rest nqr nqc nqm nqcm (comp-del w x)) true))
  (intro h) (simp only [i10-current-transport-rest] at h) (simp only [i10-current-transport-rest comp-del set-comps cs10s-del])
  (exact (nqk-sub nqr nqc _ _ _ _
           (fn [p :- (=> RS10 Bool), q :- (= (tbl-all p (rs10s (:runs w))) true)] q)
           (fn [p :- (=> CS10 Bool), q :- (= (tbl-all p (cs10s (:comps w))) true)]
             (tbl-all-del CS10 cs10-id x p p (fn [c :- CS10, a1 :- (= (p c) true), a2 :- (= (Nat.beq (cs10-id c) x) false)] a1) _ q)) h)))
(a/theorem i10-current-transport-rest-filter [nqr :- (=> RS10 CS10 Bool), nqc :- (=> CS10 Bool), nqm :- (forall [r :- RS10, c :- CS10] (=> (= (nqr r c) true) (= (nqr r (cs-step c)) true))),
                       nqcm :- (forall [c :- CS10] (=> (= (nqc c) true) (= (nqc (cs-step c)) true))), w :- World, K :- (=> Nat Bool)]
  (=> (= (i10-current-transport-rest nqr nqc nqm nqcm w) true) (= (i10-current-transport-rest nqr nqc nqm nqcm (filter-world K w)) true))
  (intro h) (simp only [i10-current-transport-rest] at h) (simp only [i10-current-transport-rest filter-world rs10s-keep cs10s-keep])
  (exact (nqk-sub nqr nqc _ _ _ _
           (fn [p :- (=> RS10 Bool), q :- (= (tbl-all p (rs10s (:runs w))) true)] (tbl-all-keep-same RS10 K rs10-id p _ q))
           (fn [p :- (=> CS10 Bool), q :- (= (tbl-all p (cs10s (:comps w))) true)] (tbl-all-keep-same CS10 K cs10-id p _ q)) h)))

(def NQ (mk-bundle 'i10-current-transport '[nqr :- (=> RS10 CS10 Bool), nqc :- (=> CS10 Bool),
                         nqm :- (forall [r :- RS10, c :- CS10] (=> (= (nqr r c) true) (= (nqr r (cs-step c)) true))),
                         nqcm :- (forall [c :- CS10] (=> (= (nqc c) true) (= (nqc (cs-step c)) true)))] "i10-current-transport-"
          {'well-formed-run-upd ['(fn [r :- RunRow] (Eq.refl (rs10 r))) 4]
           'well-formed-comp-upd ['(fn [c :- CompRow] (Eq.refl (cs10 c))) 5]}))
(swap! (:renames NQ) assoc 'well-formed-parts 'i10-current-transport-parts 'well-formed-run-upd 'i10-current-transport-run-upd 'well-formed-comp-upd 'i10-current-transport-comp-upd)
(doseq [o '[well-formed-scope-upd well-formed-pub-upd well-formed-source-upd well-formed-resource-upd well-formed-cleanup-upd well-formed-cleanup-del well-formed-task-upd
            well-formed-set-pins well-formed-resource-del well-formed-scope-del well-formed-cleanup-ins well-formed-act-upd well-formed-edge-upd well-formed-bump
            well-formed-source-ins-fresh well-formed-fork-ins-fresh well-formed-resource-ins-fresh well-formed-scope-ins-fresh well-formed-act-ins-fresh well-formed-insert-edge-fresh well-formed-fork-del]]
  (prim! NQ o nil))
(prim! NQ 'well-formed-mark-edge '(Eq.trans (i10-current-transport-ks nqr nqc nqm nqcm w (mark-edge w x) (ks10-mark-edge w x)) R))
(prim! NQ 'well-formed-unmark-edge '(Eq.trans (i10-current-transport-ks nqr nqc nqm nqcm w (unmark-edge w x) (ks10-unmark-edge w x)) R))
(prim! NQ 'well-formed-remove-edge '(Eq.trans (i10-current-transport-ks nqr nqc nqm nqcm w (remove-edge w x) (ks10-remove-edge w x)) R))
(prim! NQ 'well-formed-drop-cred-edges '(Eq.trans (i10-current-transport-ks nqr nqc nqm nqcm w (drop-cred-edges w a) (ks10-drop-cred w a)) R))
(prim! NQ 'well-formed-drop-act '(Eq.trans (i10-current-transport-ks nqr nqc nqm nqcm w (drop-act w a) (ks10-drop-act w a)) R))
(prim! NQ 'well-formed-drop-edges '(Eq.trans (i10-current-transport-ks nqr nqc nqm nqcm w (drop-edges w p) (ks10-drop-edges w p)) R))
(prim! NQ 'well-formed-comp-del-unref '(i10-current-transport-rest-comp-del nqr nqc nqm nqcm w x R))
(prim! NQ 'well-formed-run-del '(i10-current-transport-rest-run-del nqr nqc nqm nqcm w x R))
(prim! NQ 'well-formed-filter-world '(i10-current-transport-rest-filter nqr nqc nqm nqcm w K R))
(a/theorem i10-current-transport-inc-epoch [nqr :- (=> RS10 CS10 Bool), nqc :- (=> CS10 Bool),
                          nqm :- (forall [r :- RS10, c :- CS10] (=> (= (nqr r c) true) (= (nqr r (cs-step c)) true))),
                          nqcm :- (forall [c :- CS10] (=> (= (nqc c) true) (= (nqc (cs-step c)) true))), w :- World, x :- Nat]
  (=> (= (i10-current-transport nqr nqc nqm nqcm w) true) (= (i10-current-transport nqr nqc nqm nqcm (comp-upd w x comp-inc-epoch)) true))
  (intro h)
  (have hs := (well-formed-comp-upd w x comp-inc-epoch comp-inc-epoch-comp-id comp-inc-epoch-pending (i10-current-transport-well-formed nqr nqc nqm nqcm w h)))
  (have hr := (i10-current-transport-rest-of nqr nqc nqm nqcm w h))
  (have ec (= (cs10s (tbl-upd comp-id x comp-inc-epoch (:comps w))) (tbl-upd cs10-id x cs-step (cs10s (:comps w)))))
  (exact (cs10s-upd x comp-inc-epoch cs-step (fn [c :- CompRow] (Eq.refl (cs10 (comp-inc-epoch c)))) (:comps w)))
  (simp only [i10-current-transport-rest nqk Bool.and_eq_true] at hr)
  (have h1 (forall [r :- RS10] (=> (= (i10-current-transport-row nqr (cs10s (:comps w)) r) true) (= (i10-current-transport-row nqr (tbl-upd cs10-id x cs-step (cs10s (:comps w))) r) true))))
  (intros r q) (simp only [i10-current-transport-row] at q) (simp only [i10-current-transport-row])
  (exact (tbl-all-upd CS10 cs10-id x cs-step (nqr r) (nqr r) (fn [c :- CS10, a1 :- (= (nqr r c) true), a2 :- (= (Nat.beq (cs10-id c) x) true)] (nqm r c a1))
           (fn [c :- CS10, a1 :- (= (nqr r c) true), a2 :- (= (Nat.beq (cs10-id c) x) false)] a1) _ q))
  (have hr2 (= (i10-current-transport-rest nqr nqc nqm nqcm (comp-upd w x comp-inc-epoch)) true))
  (simp only [i10-current-transport-rest nqk comp-upd set-comps ec Bool.and_eq_true])
  (exact (And.intro (tbl-all-mono RS10 _ _ h1 _ (And.left hr))
           (tbl-all-upd CS10 cs10-id x cs-step nqc nqc (fn [c :- CS10, a1 :- (= (nqc c) true), a2 :- (= (Nat.beq (cs10-id c) x) true)] (nqcm c a1))
             (fn [c :- CS10, a1 :- (= (nqc c) true), a2 :- (= (Nat.beq (cs10-id c) x) false)] a1) _ (And.right hr))))
  (exact (i10-current-transport-intro nqr nqc nqm nqcm _ hs hr2)))
;; i10-current-transport on the generic tree: one site, the epoch step (nqm and nqcm: both predicates survive cs-step)
(tree/part! NQ :sites '{[well-formed-comp-upd comp-inc-epoch] (i10-current-transport-inc-epoch nqr nqc nqm nqcm w x h0)})

(tree/restate! NQ '[well-formed-job-apply well-formed-run-cascade well-formed-cancel-pred well-formed-cut-suffix well-formed-consume-entry])

;; ---- key lists as maps

(a/theorem all-i10-current-run-keys [P :- (=> I10CurrentRunKey Bool), rs :- (List RunRow)] (= (tbl-all P (i10-current-run-keys rs)) (tbl-all (fn [r :- RunRow] (P (i10-current-run-key r))) rs))
  (induction rs) (case [nil] (simp only [i10-current-run-keys tbl-all])) (case [cons h t ih] (simp only [i10-current-run-keys tbl-all ih])))
(a/theorem all-i10-current-comp-keys [P :- (=> I10CurrentCompKey Bool), cs :- (List CompRow)] (= (tbl-all P (i10-current-comp-keys cs)) (tbl-all (fn [c :- CompRow] (P (i10-current-comp-key c))) cs))
  (induction cs) (case [nil] (simp only [i10-current-comp-keys tbl-all])) (case [cons h t ih] (simp only [i10-current-comp-keys tbl-all ih])))
(a/theorem all-i10-current-task-keys [P :- (=> I10CurrentTaskKey Bool), ts :- (List TaskRow)] (= (tbl-all P (i10-current-task-keys ts)) (tbl-all (fn [t :- TaskRow] (P (i10-current-task-key t))) ts))
  (induction ts) (case [nil] (simp only [i10-current-task-keys tbl-all])) (case [cons h t ih] (simp only [i10-current-task-keys tbl-all ih])))
(a/theorem all-rs10s [P :- (=> RS10 Bool), rs :- (List RunRow)] (= (tbl-all P (rs10s rs)) (tbl-all (fn [r :- RunRow] (P (rs10 r))) rs))
  (induction rs) (case [nil] (simp only [rs10s tbl-all])) (case [cons h t ih] (simp only [rs10s tbl-all ih])))
(a/theorem all-cs10s [P :- (=> CS10 Bool), cs :- (List CompRow)] (= (tbl-all P (cs10s cs)) (tbl-all (fn [c :- CompRow] (P (cs10 c))) cs))
  (induction cs) (case [nil] (simp only [cs10s tbl-all])) (case [cons h t ih] (simp only [cs10s tbl-all ih])))

;; ===========================================================================
;; Part D. Runs made done (cancel, complete): the cascade with its job condition
;; ===========================================================================

;; job condition: run x is no current run of a computation outside gxz (stated with `<`, which an
;; epoch step keeps)
(a/defn nc-cs [gxz :- (List Nat), r :- RS10, c :- CS10] Bool
  (Bool.or (reach-mem (:id c) gxz) (Bool.or (Bool.not (Nat.beq (:of r) (:id c))) (Nat.blt (:epoch r) (:epoch c)))))
(a/defn nc-run [gxz :- (List Nat), gkz :- (List Nat), x :- Nat, r :- RS10, c :- CS10] Bool
  (Bool.or (Bool.not (Nat.beq (:id r) x)) (Bool.or (reach-mem (:id r) gkz) (nc-cs gxz r c))))
(a/defn tt-c [c :- CS10] Bool true)
(a/theorem nc-run-m [gxz :- (List Nat), gkz :- (List Nat), x :- Nat, r :- RS10, c :- CS10]
  (=> (= (nc-run gxz gkz x r c) true) (= (nc-run gxz gkz x r (cs-step c)) true))
  (intro h)
  (simp only [nc-run nc-cs Bool.or_eq_true Nat.blt_eq] at h)
  (simp only [nc-run nc-cs cs-step Bool.or_eq_true Nat.blt_eq])
  (cases h)
  (case [inl a] (exact (Or.inl a)))
  (case [inr b]
    (cases b)
    (case [inl a] (exact (Or.inr (Or.inl a))))
    (case [inr b1]
      (cases b1)
      (case [inl a] (exact (Or.inr (Or.inr (Or.inl a)))))
      (case [inr b2]
        (cases b2)
        (case [inl a] (exact (Or.inr (Or.inr (Or.inr (Or.inl a))))))
        (case [inr a] (have a2 (< (:epoch r) (+ (:epoch c) 1))) (omega) (exact (Or.inr (Or.inr (Or.inr (Or.inr a2))))))))))
(a/theorem tt-m [c :- CS10] (=> (= (tt-c c) true) (= (tt-c (cs-step c)) true)) (intro h) (rfl))

(a/defn ncw [gxz :- (List Nat), gkz :- (List Nat), x :- Nat, w :- World] Bool (nqk (nc-run gxz gkz x) tt-c (rs10s (:runs w)) (cs10s (:comps w))))
(a/theorem ncw-i10-current-transport [gxz :- (List Nat), gkz :- (List Nat), x :- Nat, w :- World]
  (=> (= (well-formed w) true) (= (ncw gxz gkz x w) true) (= (i10-current-transport (nc-run gxz gkz x) tt-c (nc-run-m gxz gkz x) tt-m w) true))
  (intros hs h) (exact (i10-current-transport-intro _ _ _ _ w hs h)))
(a/theorem ncw-of-i10-current-transport [gxz :- (List Nat), gkz :- (List Nat), x :- Nat, w :- World]
  (=> (= (i10-current-transport (nc-run gxz gkz x) tt-c (nc-run-m gxz gkz x) tt-m w) true) (= (ncw gxz gkz x w) true))
  (intro h) (exact (i10-current-transport-rest-of _ _ _ _ w h)))

;; a run made done whose rows (id x) are exempt or no current run outside gxz
(a/defn dn2-ok [gxz :- (List Nat), gkz :- (List Nat), x :- Nat, cks :- (List I10CurrentCompKey), r :- I10CurrentRunKey] Bool
  (Bool.or (reach-mem (:id r) gkz) (dn-ok gxz x cks r)))
(a/theorem rc-exempt [gxz :- (List Nat), gkz :- (List Nat), r :- I10CurrentRunKey, c :- I10CurrentCompKey]
  (=> (= (reach-mem (:id r) gkz) true) (= (rc-ok gxz gkz r c) true))
  (intro h) (simp only [rc-ok h Bool.true_or]))
(a/theorem i10-current-run-ok-down-x [gxz :- (List Nat), gkz :- (List Nat), cks :- (List I10CurrentCompKey), tks :- (List I10CurrentTaskKey), n :- Nat, r :- I10CurrentRunKey]
  (=> (= (i10-current-run-ok gxz gkz cks tks n r) true) (= (reach-mem (:id r) gkz) true) (= (i10-current-run-ok gxz gkz cks tks n (i10-current-run-key-down r)) true))
  (intros h hk)
  (simp only [i10-current-run-ok Bool.and_eq_true] at h)
  (have e1 (= (tbl-all (tof-pair (i10-current-run-key-down r)) tks) (tbl-all (tof-pair r) tks))) (rfl)
  (have e2 (= (Nat.blt (:of (i10-current-run-key-down r)) n) (Nat.blt (:of r) n))) (rfl)
  (have e3 (= (reach-mem (:id (i10-current-run-key-down r)) gkz) true)) (exact hk)
  (have hc (= (tbl-all (rc-ok gxz gkz (i10-current-run-key-down r)) cks) true))
  (exact (all-of-mem I10CurrentCompKey _ cks (fn [c :- I10CurrentCompKey, m :- (List.Mem c cks)] (rc-exempt gxz gkz (i10-current-run-key-down r) c e3))))
  (simp only [i10-current-run-ok Bool.and_eq_true e1 e2 hc (And.left (And.right h)) (And.right (And.right h)) and_self]))

(a/theorem i10-current-exempt-keys-ok-run-down2 [gxz :- (List Nat), gkz :- (List Nat), rks :- (List I10CurrentRunKey), cks :- (List I10CurrentCompKey), tks :- (List I10CurrentTaskKey), n :- Nat, x :- Nat]
  (=> (= (i10-current-exempt-keys-ok gxz gkz rks cks tks n) true) (= (tbl-all (dn2-ok gxz gkz x cks) rks) true)
      (= (i10-current-exempt-keys-ok gxz gkz (tbl-upd i10-current-run-key-id x i10-current-run-key-down rks) cks tks n) true))
  (intros h hd)
  (simp only [i10-current-exempt-keys-ok Bool.and_eq_true] at h)
  (simp only [i10-current-exempt-keys-ok Bool.and_eq_true (And.right h) and_true])
  (have hb (forall [r :- I10CurrentRunKey] (=> (= (both (i10-current-run-ok gxz gkz cks tks n) (dn2-ok gxz gkz x cks) r) true)
                                   (= (Nat.beq (i10-current-run-key-id r) x) true) (= (i10-current-run-ok gxz gkz cks tks n (i10-current-run-key-down r)) true))))
  (intros r hp hx)
  (have hr := (both-left _ _ _ _ hp))
  (have hdn := (both-right _ _ _ _ hp))
  (have hx2 (= (Nat.beq (:id r) x) true)) (exact hx)
  (cases hk (reach-mem (:id r) gkz))
  (case [true] (exact (i10-current-run-ok-down-x gxz gkz cks tks n r hr hk)))
  (case [false]
    (simp only [dn2-ok dn-ok hk hx2 Bool.not_true Bool.false_or] at hdn)
    (exact (i10-current-run-ok-down gxz gkz cks tks n r hr hdn)))
  (exact (tbl-all-upd I10CurrentRunKey i10-current-run-key-id x i10-current-run-key-down (both (i10-current-run-ok gxz gkz cks tks n) (dn2-ok gxz gkz x cks)) (i10-current-run-ok gxz gkz cks tks n)
           hb
           (fn [r :- I10CurrentRunKey, hp :- (= (both (i10-current-run-ok gxz gkz cks tks n) (dn2-ok gxz gkz x cks) r) true), hx :- (= (Nat.beq (i10-current-run-key-id r) x) false)]
             (both-left _ _ _ _ hp))
           rks (tbl-all-mono2 I10CurrentRunKey _ _ _ (fn [r :- I10CurrentRunKey, a1 :- (= (i10-current-run-ok gxz gkz cks tks n r) true), a2 :- (= (dn2-ok gxz gkz x cks r) true)]
                                            (both-mk _ _ _ _ a1 a2)) rks (And.left h) hd))))

(a/theorem nc-c-of-cs [gxz :- (List Nat), r :- RunRow, c :- CompRow]
  (=> (= (nc-cs gxz (rs10 r) (cs10 c)) true) (= (nc-c gxz (i10-current-run-key r) (i10-current-comp-key c)) true))
  (intro h)
  (simp only [nc-cs nc-c rs10 cs10 i10-current-run-key i10-current-comp-key Bool.or_eq_true Nat.blt_eq] at h)
  (simp only [nc-c i10-current-run-key i10-current-comp-key Bool.or_eq_true])
  (cases h)
  (case [inl a] (exact (Or.inl a)))
  (case [inr b]
    (cases b)
    (case [inl a] (exact (Or.inr (Or.inl a))))
    (case [inr a]
      (have z (= (Nat.beq (:epoch r) (:epoch c)) false))
      (cases hb (Nat.beq (:epoch r) (:epoch c))) (rfl)
      (have z2 := (Nat.eq_of_beq_eq_true hb)) (omega)
      (exact (Or.inr (Or.inr (Eq.trans (congrArg Bool.not z) (rfl))))))))

(a/theorem ncrun-cs [gxz :- (List Nat), gkz :- (List Nat), x :- Nat, r :- RS10, c :- CS10]
  (=> (= (Nat.beq (:id r) x) true) (= (reach-mem (:id r) gkz) false) (= (nc-run gxz gkz x r c) true) (= (nc-cs gxz r c) true))
  (intros h1 h2 h) (simp only [nc-run h1 h2 Bool.not_true Bool.false_or] at h) (exact h))

(a/theorem dn2-of-ncw [gxz :- (List Nat), gkz :- (List Nat), x :- Nat, w :- World]
  (=> (= (ncw gxz gkz x w) true) (= (tbl-all (dn2-ok gxz gkz x (i10-current-comp-keys (:comps w))) (i10-current-run-keys (:runs w))) true))
  (intro h)
  (simp only [ncw nqk Bool.and_eq_true] at h)
  (have h1 := (And.left h))
  (rw [all-rs10s] at h1)
  (rw [all-i10-current-run-keys])
  (apply (tbl-all-mono RunRow _ _ _ (:runs w) h1))
  (intros r q)
  (simp only [i10-current-transport-row] at q)
  (cases hx (Nat.beq (:id r) x))
  (case [false] (simp only [dn2-ok dn-ok i10-current-run-key hx Bool.not_false Bool.true_or Bool.or_true]))
  (case [true]
    (have hx2 (= (Nat.beq (:id (rs10 r)) x) true)) (exact hx)
    (have hx3 (= (Nat.beq (:id (i10-current-run-key r)) x) true)) (exact hx)
    (cases hk (reach-mem (:id r) gkz))
    (case [true] (have hk3 (= (reach-mem (:id (i10-current-run-key r)) gkz) true)) (exact hk) (simp only [dn2-ok hk3 Bool.true_or]))
    (case [false]
      (have hk2 (= (reach-mem (:id (rs10 r)) gkz) false)) (exact hk)
      (have hk3 (= (reach-mem (:id (i10-current-run-key r)) gkz) false)) (exact hk)
      (simp only [dn2-ok dn-ok hx3 hk3 Bool.not_true Bool.false_or])
      (have q2 := (tbl-all-mono CS10 (nc-run gxz gkz x (rs10 r)) (nc-cs gxz (rs10 r))
                    (fn [c :- CS10, a :- (= (nc-run gxz gkz x (rs10 r) c) true)] (ncrun-cs gxz gkz x (rs10 r) c hx2 hk2 a)) _ q))
      (rw [all-cs10s] at q2)
      (rw [all-i10-current-comp-keys])
      (exact (tbl-all-mono CompRow _ _ (fn [c :- CompRow, a :- (= (nc-cs gxz (rs10 r) (cs10 c)) true)] (nc-c-of-cs gxz r c a)) _ q2)))))

(a/theorem i10-current-exempt-kill [gxz :- (List Nat), gkz :- (List Nat), w :- World, x :- Nat, f :- (=> RunRow RunRow),
                     hf :- (forall [r :- RunRow] (= (run-id (f r)) (run-id r))),
                     hk :- (forall [r :- RunRow] (= (i10-current-run-key (f r)) (i10-current-run-key-down (i10-current-run-key r))))]
  (=> (= (tbl-all (dn2-ok gxz gkz x (i10-current-comp-keys (:comps w))) (i10-current-run-keys (:runs w))) true) (= (i10-current-exempt gxz gkz w) true)
      (= (i10-current-exempt gxz gkz (run-upd w x f)) true))
  (intros hd h)
  (have hr (= (i10-current-exempt-rest gxz gkz (run-upd w x f)) true))
  (simp only [i10-current-exempt-rest run-upd set-runs (i10-current-run-keys-upd x f i10-current-run-key-down hk (:runs w))])
  (exact (i10-current-exempt-keys-ok-run-down2 gxz gkz _ _ _ _ x (i10-current-exempt-rest-of gxz gkz w h) hd))
  (exact (i10-current-exempt-intro gxz gkz _ (well-formed-run-upd w x f hf (i10-current-exempt-well-formed gxz gkz w h)) hr)))

(a/theorem run-cancel-i10-current-run-key [r :- RunRow] (= (i10-current-run-key (run-cancel-row r)) (i10-current-run-key-down (i10-current-run-key r))) (rfl))
(a/theorem run-complete-i10-current-run-key [r :- RunRow] (= (i10-current-run-key (run-complete-row r)) (i10-current-run-key-down (i10-current-run-key r))) (rfl))

;; ---- facts from well-formed

(a/theorem all-true-of [A :- Type, P :- (=> A Bool), h :- (forall [a :- A] (= (P a) true)), xs :- (List A)] (= (tbl-all P xs) true)
  (induction xs) (case [nil] (simp only [tbl-all])) (case [cons hd t ih] (simp only [tbl-all (h hd) ih Bool.and_self])))
(a/theorem comp-mem-has [w :- World, c :- CompRow] (=> (List.Mem c (:comps w)) (= (comp-has w (:id c)) true))
  (intros m) (have hm := (mem-ids-has CompRow comp-id c (:comps w) m)) (rw [nat-mem-ids] at hm) (exact hm))

(a/theorem comp-task-ne [w :- World, c :- CompRow, y :- Nat]
  (=> (= (well-formed w) true) (List.Mem c (:comps w)) (= (task-has w y) true) (= (Nat.beq y (:id c)) false))
  (intros hs m ht)
  (have hc := (comp-mem-has w c m))
  (have hn := (comp-not-task w (:id c) hs hc))
  (rw [nat-mem-ids] at hn)
  (cases hb (Nat.beq y (:id c)))
  (case [false] (rfl))
  (case [true]
    (have e := (Nat.eq_of_beq_eq_true hb))
    (have ht2 (= (tbl-has task-id (:id c) (:tasks w)) true)) (rw [← e]) (exact ht)
    (rw [ht2] at hn) (cases hn)))

(a/theorem nc-run-off [gxz :- (List Nat), gkz :- (List Nat), x :- Nat, r :- RS10, c :- CS10]
  (=> (= (Nat.beq (:id r) x) false) (= (nc-run gxz gkz x r c) true))
  (intro h) (simp only [nc-run h Bool.not_false Bool.true_or]))
(a/theorem nc-run-of [gxz :- (List Nat), gkz :- (List Nat), x :- Nat, r :- RS10, c :- CS10]
  (=> (= (Nat.beq (:of r) (:id c)) false) (= (nc-run gxz gkz x r c) true))
  (intro h) (simp only [nc-run nc-cs h Bool.not_false Bool.true_or Bool.or_true]))

(a/theorem tr-one [gxz :- (List Nat), gkz :- (List Nat), x :- Nat, w :- World, r :- RunRow]
  (=> (= (well-formed w) true) (= (same-id-then run-id x (fn [q :- RunRow] (task-has w (:of q))) r) true)
      (= (i10-current-transport-row (nc-run gxz gkz x) (cs10s (:comps w)) (rs10 r)) true))
  (intros hs h)
  (simp only [i10-current-transport-row])
  (rw [all-cs10s])
  (cases hx (Nat.beq (:id r) x))
  (case [false]
    (have hx2 (= (Nat.beq (:id (rs10 r)) x) false)) (exact hx)
    (exact (all-true-of CompRow _ (fn [c :- CompRow] (nc-run-off gxz gkz x (rs10 r) (cs10 c) hx2)) _)))
  (case [true]
    (have hx2 (= (Nat.beq (run-id r) x) true)) (exact hx)
    (simp only [same-id-then hx2 Bool.not_true Bool.false_or] at h)
    (exact (all-of-mem CompRow _ _ (fn [c :- CompRow, m :- (List.Mem c (:comps w))]
             (nc-run-of gxz gkz x (rs10 r) (cs10 c) (comp-task-ne w c (:of r) hs m h)))))))

(a/theorem task-run-ncw [gxz :- (List Nat), gkz :- (List Nat), x :- Nat, w :- World]
  (=> (= (well-formed w) true) (= (tbl-all (same-id-then run-id x (fn [q :- RunRow] (task-has w (:of q)))) (:runs w)) true)
      (= (ncw gxz gkz x w) true))
  (intros hs h)
  (have a1 (= (tbl-all (i10-current-transport-row (nc-run gxz gkz x) (cs10s (:comps w))) (rs10s (:runs w))) true))
  (rw [all-rs10s])
  (exact (tbl-all-mono RunRow _ _ (fn [r :- RunRow, q :- (= (same-id-then run-id x (fn [q :- RunRow] (task-has w (:of q))) r) true)]
                                    (tr-one gxz gkz x w r hs q)) _ h))
  (have a2 (= (tbl-all tt-c (cs10s (:comps w))) true)) (exact (all-true-of CS10 tt-c (fn [c :- CS10] (Eq.refl true)) _))
  (simp only [ncw nqk a1 a2 Bool.and_self]))

;; a scan: every listed id has the property of its row
(a/theorem scan-all [A :- Type, idf :- (=> A Nat), p :- (=> A Bool), q :- (=> Nat Bool), xs :- (List A)]
  (=> (forall [a :- A] (=> (List.Mem a xs) (= (p a) true) (= (q (idf a)) true))) (= (tbl-all q (tbl-scan idf p xs)) true))
  (induction xs)
  (case [nil] (intro h) (simp only [tbl-scan tbl-all]))
  (case [cons hd t ih]
    (intro h)
    (have ht (forall [a :- A] (=> (List.Mem a t) (= (p a) true) (= (q (idf a)) true))))
    (intros a m pa) (exact (h a (List.Mem.tail hd m) pa))
    (cases hp (p hd))
    (case [false] (simp only [tbl-scan hp]) (exact (ih ht)))
    (case [true] (simp only [tbl-scan hp tbl-all (h hd (List.Mem.head t) hp) (ih ht) Bool.and_self]))))

(a/theorem owned-ncw [gxz :- (List Nat), gkz :- (List Nat), w :- World, sub :- (List Nat)]
  (=> (= (well-formed w) true) (= (tbl-all (fn [x :- Nat] (ncw gxz gkz x w)) (owned-runs w sub)) true))
  (intro hs)
  (simp only [owned-runs])
  (apply (scan-all RunRow run-id (run-owned-by w sub) (fn [x :- Nat] (ncw gxz gkz x w)) (:runs w)))
  (intros r m p)
  (simp only [run-owned-by Bool.and_eq_true] at p)
  (have hq (= (task-has w (:of r)) true))
  (cases hf (task-find w (:of r)))
  (case [none] (simp only [opt-test hf] at p) (have z := (And.right p)) (cases z))
  (case [some t] (exact (tbl-find-has TaskRow task-id (:of r) t (:tasks w) hf)))
  (exact (task-run-ncw gxz gkz (run-id r) w hs
           (uniq-all RunRow run-id (fn [q :- RunRow] (task-has w (:of q))) r (:runs w) (lit-runs-nodup w hs) m hq))))

;; ---- the job list condition

(a/defn job-ok [gxz :- (List Nat), gkz :- (List Nat), w :- World, j :- Job] Bool
  (match j [(jcancel x rep) (ncw gxz gkz x w)] [(jretire x) true] [(jclose s) true]))

(a/theorem all-append [A :- Type, P :- (=> A Bool), a :- (List A), b :- (List A)]
  (= (tbl-all P (List.append A a b)) (Bool.and (tbl-all P a) (tbl-all P b)))
  (induction a)
  (case [nil] (simp only [List.append tbl-all Bool.true_and]))
  (case [cons h t ih] (simp only [List.append tbl-all ih Bool.and_assoc])))

(a/theorem jl-cancel-jobs [gxz :- (List Nat), gkz :- (List Nat), w :- World, xs :- (List Nat)]
  (= (tbl-all (job-ok gxz gkz w) (cancel-jobs xs)) (tbl-all (fn [x :- Nat] (ncw gxz gkz x w)) xs))
  (induction xs)
  (case [nil] (simp only [cancel-jobs tbl-all]))
  (case [cons h t ih] (simp only [cancel-jobs tbl-all job-ok ih])))

(a/theorem job-next-ok [gxz :- (List Nat), gkz :- (List Nat), w :- World, j :- Job]
  (=> (= (well-formed w) true) (= (tbl-all (job-ok gxz gkz w) (job-next w j)) true))
  (intro hs)
  (cases j)
  (case [jcancel rid rep]
    (cases hf (run-find w rid))
    (case [none] (simp only [job-next hf tbl-all]))
    (case [some r]
      (cases ha (run-alive r))
      (case [false] (simp only [job-next hf ha tbl-all]))
      (case [true]
        (simp only [job-next hf ha all-append jl-cancel-jobs (owned-ncw gxz gkz w (scope-subtree w (:scope r)) hs) tbl-all job-ok Bool.and_self]))))
  (case [jretire rid]
    (cases hf (run-find w rid))
    (case [none] (simp only [job-next hf tbl-all]))
    (case [some r]
      (cases ha (retirable r))
      (case [false] (simp only [job-next hf ha tbl-all]))
      (case [true] (simp only [job-next hf ha jl-cancel-jobs (owned-ncw gxz gkz w (scope-subtree w (:scope r)) hs)]))))
  (case [jclose s]
    (cases hc (scope-has w s))
    (case [false] (simp only [job-next hc tbl-all]))
    (case [true] (simp only [job-next hc jl-cancel-jobs (owned-ncw gxz gkz w (scope-subtree w s) hs)]))))

(a/theorem job-ok-tr [gxz :- (List Nat), gkz :- (List Nat), w :- World, j :- Job, j2 :- Job]
  (=> (= (well-formed w) true) (= (job-ok gxz gkz w j2) true) (= (job-ok gxz gkz (job-apply w j) j2) true))
  (intros hs h)
  (cases j2)
  (case [jcancel x rep]
    (simp only [job-ok] at h) (simp only [job-ok])
    (exact (ncw-of-i10-current-transport gxz gkz x _ (i10-current-transport-job-apply (nc-run gxz gkz x) tt-c (nc-run-m gxz gkz x) tt-m w j (ncw-i10-current-transport gxz gkz x w hs h)))))
  (case [jretire x] (simp only [job-ok]))
  (case [jclose s] (simp only [job-ok])))

(a/theorem jl-step [gxz :- (List Nat), gkz :- (List Nat), w :- World, j :- Job, t :- (List Job)]
  (=> (= (well-formed w) true) (= (tbl-all (job-ok gxz gkz w) (List.cons Job j t)) true)
      (= (tbl-all (job-ok gxz gkz (job-apply w j)) (List.append Job t (job-next w j))) true))
  (intros hs h)
  (simp only [tbl-all Bool.and_eq_true] at h)
  (have a1 := (tbl-all-mono Job (job-ok gxz gkz w) (job-ok gxz gkz (job-apply w j)) (fn [j2 :- Job, q :- (= (job-ok gxz gkz w j2) true)] (job-ok-tr gxz gkz w j j2 hs q)) t (And.right h)))
  (have a2 := (tbl-all-mono Job (job-ok gxz gkz w) (job-ok gxz gkz (job-apply w j)) (fn [j2 :- Job, q :- (= (job-ok gxz gkz w j2) true)] (job-ok-tr gxz gkz w j j2 hs q)) _ (job-next-ok gxz gkz w j hs)))
  (simp only [all-append a1 a2 Bool.and_self]))

(a/theorem comps-nodup10 [w :- World]
  (=> (= (well-formed w) true) (= (nat-nodup (tbl-ids comp-id (:comps w))) true))
  (intro h)
  (have u := (ids-unique-of w h))
  (simp only [all-ids] at u)
  (exact (nat-nodup-app-left _ _ (nat-nodup-app-right _ _ u))))

;; ---- T13 retire: C.run cleared before the row goes (the run is exempt in between)

(a/defn idq [x :- Nat, Q :- (=> I10CurrentCompKey Bool), k :- I10CurrentCompKey] Bool (Bool.or (Bool.not (Nat.beq (:id k) x)) (Q k)))

(a/theorem i10-current-exempt-keys-ok-comp-up-q [gxz :- (List Nat), gkz :- (List Nat), rks :- (List I10CurrentRunKey), cks :- (List I10CurrentCompKey), tks :- (List I10CurrentTaskKey), n :- Nat,
                           x :- Nat, g :- (=> I10CurrentCompKey I10CurrentCompKey), Q :- (=> I10CurrentCompKey Bool),
                           hup :- (forall [r :- I10CurrentRunKey, c :- I10CurrentCompKey] (=> (= (Q c) true) (= (rc-ok gxz gkz r c) true) (= (rc-ok gxz gkz r (g c)) true))),
                           hc :- (forall [c :- I10CurrentCompKey] (=> (= (i10-current-comp-ok n c) true) (= (i10-current-comp-ok n (g c)) true)))]
  (=> (= (tbl-all (idq x Q) cks) true) (= (i10-current-exempt-keys-ok gxz gkz rks cks tks n) true) (= (i10-current-exempt-keys-ok gxz gkz rks (tbl-upd i10-current-comp-key-id x g cks) tks n) true))
  (intros hq h)
  (simp only [i10-current-exempt-keys-ok Bool.and_eq_true] at h)
  (have hin (forall [r :- I10CurrentRunKey, c :- I10CurrentCompKey] (=> (= (both (rc-ok gxz gkz r) (idq x Q) c) true) (= (Nat.beq (i10-current-comp-key-id c) x) true)
                                               (= (rc-ok gxz gkz r (g c)) true))))
  (intros r c p hx)
  (have p2 := (both-right _ _ _ _ p))
  (have hx2 (= (Nat.beq (:id c) x) true)) (exact hx)
  (simp only [idq hx2 Bool.not_true Bool.false_or] at p2)
  (exact (hup r c p2 (both-left _ _ _ _ p)))
  (have h1 (forall [r :- I10CurrentRunKey] (=> (= (i10-current-run-ok gxz gkz cks tks n r) true) (= (i10-current-run-ok gxz gkz (tbl-upd i10-current-comp-key-id x g cks) tks n r) true))))
  (intros r hr)
  (simp only [i10-current-run-ok Bool.and_eq_true] at hr)
  (simp only [i10-current-run-ok Bool.and_eq_true (And.right hr) and_true])
  (exact (tbl-all-upd I10CurrentCompKey i10-current-comp-key-id x g (both (rc-ok gxz gkz r) (idq x Q)) (rc-ok gxz gkz r) (hin r)
           (fn [c :- I10CurrentCompKey, hp :- (= (both (rc-ok gxz gkz r) (idq x Q) c) true), hx :- (= (Nat.beq (i10-current-comp-key-id c) x) false)] (both-left _ _ _ _ hp))
           cks (tbl-all-mono2 I10CurrentCompKey _ _ _ (fn [c :- I10CurrentCompKey, a1 :- (= (rc-ok gxz gkz r c) true), a2 :- (= (idq x Q c) true)] (both-mk _ _ _ _ a1 a2))
                 cks (And.left hr) hq)))
  (simp only [i10-current-exempt-keys-ok Bool.and_eq_true (And.right (And.right h)) and_true])
  (exact (And.intro (tbl-all-mono I10CurrentRunKey _ _ h1 rks (And.left h))
           (tbl-all-upd I10CurrentCompKey i10-current-comp-key-id x g (i10-current-comp-ok n) (i10-current-comp-ok n)
             (fn [c :- I10CurrentCompKey, hp :- (= (i10-current-comp-ok n c) true), hx :- (= (Nat.beq (i10-current-comp-key-id c) x) true)] (hc c hp))
             (fn [c :- I10CurrentCompKey, hp :- (= (i10-current-comp-ok n c) true), hx :- (= (Nat.beq (i10-current-comp-key-id c) x) false)] hp) cks (And.left (And.right h))))))

(a/theorem rc-ks-cons [gxz :- (List Nat), gkz :- (List Nat), y :- Nat, r :- I10CurrentRunKey, c :- I10CurrentCompKey]
  (=> (= (rc-ok gxz gkz r c) true) (= (rc-ok gxz (List.cons Nat y gkz) r c) true))
  (intro h)
  (simp only [rc-ok Bool.or_eq_true] at h)
  (simp only [rc-ok reach-mem-cons Bool.or_eq_true])
  (cases h) (case [inl a] (exact (Or.inl (Or.inr a)))) (case [inr b] (exact (Or.inr b))))

(a/theorem i10-current-run-ok-sub2 [gxz :- (List Nat), gkz :- (List Nat), y :- Nat, cks :- (List I10CurrentCompKey), tks :- (List I10CurrentTaskKey), n :- Nat, r :- I10CurrentRunKey]
  (=> (= (i10-current-run-ok gxz gkz cks tks n r) true) (= (i10-current-run-ok gxz (List.cons Nat y gkz) cks tks n r) true))
  (intro h)
  (simp only [i10-current-run-ok Bool.and_eq_true] at h)
  (simp only [i10-current-run-ok Bool.and_eq_true (And.right h) and_true])
  (exact (tbl-all-mono I10CurrentCompKey _ _ (fn [c :- I10CurrentCompKey, q :- (= (rc-ok gxz gkz r c) true)] (rc-ks-cons gxz gkz y r c q)) cks (And.left h))))
(a/theorem i10-current-exempt-keys-ok-ks-cons [gxz :- (List Nat), gkz :- (List Nat), y :- Nat, rks :- (List I10CurrentRunKey), cks :- (List I10CurrentCompKey), tks :- (List I10CurrentTaskKey), n :- Nat]
  (=> (= (i10-current-exempt-keys-ok gxz gkz rks cks tks n) true) (= (i10-current-exempt-keys-ok gxz (List.cons Nat y gkz) rks cks tks n) true))
  (intro h)
  (simp only [i10-current-exempt-keys-ok Bool.and_eq_true] at h)
  (simp only [i10-current-exempt-keys-ok Bool.and_eq_true (And.right h) and_true])
  (exact (tbl-all-mono I10CurrentRunKey _ _ (fn [r :- I10CurrentRunKey, q :- (= (i10-current-run-ok gxz gkz cks tks n r) true)]
    (i10-current-run-ok-sub2 gxz gkz y cks tks n r q)) rks (And.left h))))

(a/defn ck-clear [k :- I10CurrentCompKey] I10CurrentCompKey (I10CurrentCompKey.mk (:id k) (:epoch k) (:done k) 0 (:idle k)))
(a/theorem rc-clear [gxz :- (List Nat), gkz :- (List Nat), rid :- Nat, r :- I10CurrentRunKey, c :- I10CurrentCompKey]
  (=> (= (Nat.beq (:run c) rid) true) (= (rc-ok gxz (List.cons Nat rid gkz) r c) true)
      (= (rc-ok gxz (List.cons Nat rid gkz) r (ck-clear c)) true))
  (intros hq h)
  (cases hk (reach-mem (:id r) (List.cons Nat rid gkz)))
  (case [true] (exact (rc-exempt gxz _ r _ hk)))
  (case [false]
    (have hk2 := hk)
    (simp only [reach-mem-cons Bool.or_eq_false_iff] at hk2)
    (simp only [rc-ok hk Bool.false_or Bool.and_eq_true] at h)
    (have hrof (= (rof-pair r (ck-clear c)) true))
    (cases hz (Nat.beq (:id r) 0))
    (simp only [rof-pair hz Bool.true_or])
    (simp only [rof-pair ck-clear hz Bool.not_false Bool.false_or Bool.true_or])
    (have hf (= (cur-fin gxz r (ck-clear c)) (cur-fin gxz r c))) (rfl)
    (have hc := (And.left h))
    (simp only [cur-pair] at hc)
    (simp only [rc-ok hk hrof cur-pair hf Bool.false_or Bool.and_true])
    (cases ho (Nat.beq (:of r) (:id c)))
    (case [false] (simp only [cur-core ho Bool.not_false Bool.true_or]))
    (case [true]
      (simp only [cur-core ho Bool.not_true Bool.false_or Bool.and_eq_true] at hc)
      (cases he (Nat.beq (:epoch r) (:epoch c)))
      (case [false] (simp only [cur-core ck-clear ho he (And.left hc) Bool.not_true Bool.not_false Bool.false_or Bool.true_or Bool.true_and]))
      (case [true]
        (simp only [he Bool.not_true Bool.false_or Bool.and_eq_true] at hc)
        (have e1 := (Nat.eq_of_beq_eq_true (And.left (And.right hc))))
        (have e2 := (Nat.eq_of_beq_eq_true hq))
        (have z := (And.left hk2))
        (have e3 (= (:id r) rid)) (rw [← e1 e2])
        (simp [e3] at z)))))

(a/theorem i10-current-comp-ok-clear [n :- Nat, c :- I10CurrentCompKey] (=> (= (i10-current-comp-ok n c) true) (= (i10-current-comp-ok n (ck-clear c)) true))
  (intro h) (simp only [i10-current-comp-ok Bool.and_eq_true] at h) (simp only [i10-current-comp-ok ck-clear below0 Nat.beq_refl Bool.true_or (And.left h) Bool.and_self]))

(a/theorem i10-current-exempt-ks-cons [gxz :- (List Nat), gkz :- (List Nat), y :- Nat, w :- World]
  (=> (= (i10-current-exempt gxz gkz w) true) (= (i10-current-exempt gxz (List.cons Nat y gkz) w) true))
  (intro h)
  (have hr := (i10-current-exempt-rest-of gxz gkz w h)) (simp only [i10-current-exempt-rest] at hr)
  (have hr2 (= (i10-current-exempt-rest gxz (List.cons Nat y gkz) w) true)) (simp only [i10-current-exempt-rest]) (exact (i10-current-exempt-keys-ok-ks-cons gxz gkz y _ _ _ _ hr))
  (exact (i10-current-exempt-intro gxz _ w (i10-current-exempt-well-formed gxz gkz w h) hr2)))

(tree/restate! G10 '[well-formed-clear-task-run])

(a/theorem i10-current-exempt-clear-comp-run-x [gxz :- (List Nat), gkz :- (List Nat), w :- World, r :- RunRow]
  (=> (= (i10-current-exempt gxz gkz w) true) (= (i10-current-exempt gxz (List.cons Nat (:id r) gkz) (clear-comp-run w r)) true))
  (intro h)
  (have h1 := (i10-current-exempt-ks-cons gxz gkz (:id r) w h))
  (have hs := (i10-current-exempt-well-formed gxz gkz w h))
  (cases hc (comp-find w (:of r)))
  (case [none] (simp only [clear-comp-run hc]) (exact (i10-current-exempt-clear-task-run gxz _ w r h1)))
  (case [some c]
    (cases hr (Nat.beq (:run c) (:id r)))
    (case [false] (simp only [clear-comp-run hc hr]) (exact h1))
    (case [true]
      (simp only [clear-comp-run hc hr])
      (have u := (uniq-all CompRow comp-id (fn [k :- CompRow] (Nat.beq (:run k) (:id r))) c (:comps w) (comps-nodup10 w hs)
                   (tbl-find-mem CompRow comp-id (:of r) c (:comps w) hc) hr))
      (have ek (= (comp-id c) (:of r))) (exact (tbl-find-id CompRow comp-id (:of r) c (:comps w) hc))
      (rw [ek] at u)
      (have hq (= (tbl-all (idq (:of r) (fn [k :- I10CurrentCompKey] (Nat.beq (:run k) (:id r)))) (i10-current-comp-keys (:comps w))) true))
      (rw [all-i10-current-comp-keys])
      (exact u)
      (have hrest (= (i10-current-exempt-rest gxz (List.cons Nat (:id r) gkz) (comp-upd w (:of r) comp-clear-run)) true))
      (have hr1 := (i10-current-exempt-rest-of gxz _ w h1))
      (simp only [i10-current-exempt-rest] at hr1)
      (simp only [i10-current-exempt-rest comp-upd set-comps (i10-current-comp-keys-upd (:of r) comp-clear-run ck-clear (fn [k :- CompRow] (Eq.refl (i10-current-comp-key (comp-clear-run k)))) (:comps w))])
      (exact (i10-current-exempt-keys-ok-comp-up-q gxz _ _ _ _ _ (:of r) ck-clear (fn [k :- I10CurrentCompKey] (Nat.beq (:run k) (:id r)))
               (fn [q :- I10CurrentRunKey, k :- I10CurrentCompKey, a1 :- (= (Nat.beq (:run k) (:id r)) true), a2 :- (= (rc-ok gxz (List.cons Nat (:id r) gkz) q k) true)]
                 (rc-clear gxz gkz (:id r) q k a1 a2))
               (i10-current-comp-ok-clear (:next-id w)) hq hr1))
      (exact (i10-current-exempt-intro gxz _ _ (well-formed-comp-upd w (:of r) comp-clear-run comp-clear-run-id comp-clear-run-pending hs) hrest)))))

(a/theorem i10-current-exempt-run-del-x [gxz :- (List Nat), gkz :- (List Nat), w :- World, x :- Nat]
  (=> (= (i10-current-exempt gxz (List.cons Nat x gkz) w) true) (= (i10-current-exempt gxz gkz (run-del w x)) true))
  (intro h)
  (exact (i10-current-exempt-intro gxz gkz _ (well-formed-run-del w x (i10-current-exempt-well-formed gxz _ w h)) (i10-current-exempt-rest-run-del-x gxz gkz w x (i10-current-exempt-rest-of gxz _ w h)))))

(tree/restate! G10 '[well-formed-close-local well-formed-cleanup-del well-formed-remove-if-empty])
(a/theorem i10-current-exempt-t13-retire-with-subtree [gxz :- (List Nat), gkz :- (List Nat), w :- World, r :- RunRow, sub :- (List Nat)]
  (=> (= (i10-current-exempt gxz gkz w) true) (= (i10-current-exempt gxz gkz (t13-retire-with-subtree w r sub)) true))
  (intro h) (simp only [t13-retire-with-subtree])
  (exact (i10-current-exempt-remove-if-empty gxz gkz _ sub (i10-current-exempt-cleanup-del gxz gkz _ (:id r) (i10-current-exempt-run-del-x gxz gkz _ (:id r)
           (i10-current-exempt-close-local gxz (List.cons Nat (:id r) gkz) _ sub (i10-current-exempt-clear-comp-run-x gxz gkz w r h)))))))
(tree/restate! G10 '[well-formed-retire-run])

;; ---- the cascade under the job condition

(tree/restate! G10 '[well-formed-cancel-debtor well-formed-cleanup-set well-formed-cancel-res well-formed-cancel-acts])
(a/theorem i10-current-exempt-cancel-run-local [gxz :- (List Nat), gkz :- (List Nat), w :- World, r :- RunRow, rep :- Bool]
  (=> (= (ncw gxz gkz (:id r) w) true) (= (i10-current-exempt gxz gkz w) true) (= (i10-current-exempt gxz gkz (cancel-run-local w r rep)) true))
  (intros hn h) (simp only [cancel-run-local])
  (exact (i10-current-exempt-cancel-debtor gxz gkz rep _ r (i10-current-exempt-cleanup-set gxz gkz _ (:id r) (cleanup-rows-of w r)
           (i10-current-exempt-cancel-res gxz gkz _ r (i10-current-exempt-cancel-acts gxz gkz _ (:id r)
             (i10-current-exempt-kill gxz gkz w (:id r) run-cancel-row run-cancel-row-id run-cancel-i10-current-run-key (dn2-of-ncw gxz gkz (:id r) w hn) h)))))))

(tree/restate! G10 '[well-formed-close-scope-local])
(a/theorem i10-current-exempt-job-apply [gxz :- (List Nat), gkz :- (List Nat), w :- World, j :- Job]
  (=> (= (job-ok gxz gkz w j) true) (= (i10-current-exempt gxz gkz w) true) (= (i10-current-exempt gxz gkz (job-apply w j)) true))
  (intros hj h)
  (cases j)
  (case [jcancel rid rep]
    (cases hf (run-find w rid))
    (case [none] (simp only [job-apply hf]) (exact h))
    (case [some r]
      (cases ha (run-alive r))
      (case [false] (simp only [job-apply hf ha]) (exact h))
      (case [true]
        (simp only [job-apply hf ha])
        (have e (= (:id r) rid)) (exact (tbl-find-id RunRow run-id rid r (:runs w) hf))
        (simp only [job-ok] at hj)
        (rw [← e] at hj)
        (exact (i10-current-exempt-cancel-run-local gxz gkz w r rep hj h)))))
  (case [jretire rid]
    (cases hf (run-find w rid))
    (case [none] (simp only [job-apply hf]) (exact h))
    (case [some r]
      (cases ha (retirable r))
      (case [false] (simp only [job-apply hf ha]) (exact h))
      (case [true] (simp only [job-apply hf ha]) (exact (i10-current-exempt-retire-run gxz gkz w r h)))))
  (case [jclose s]
    (cases hs (scope-has w s))
    (case [false] (simp only [job-apply hs]) (exact h))
    (case [true] (simp only [job-apply hs]) (exact (i10-current-exempt-close-scope-local gxz gkz w s h)))))

(a/theorem i10-current-exempt-cascade [gxz :- (List Nat), gkz :- (List Nat), fuel :- (List Nat)]
  (forall [w :- World, js :- (List Job)]
    (=> (= (tbl-all (job-ok gxz gkz w) js) true) (= (i10-current-exempt gxz gkz w) true) (= (i10-current-exempt gxz gkz (:world (cascade fuel w js))) true)))
  (induction fuel)
  (case [nil] (intros w js hj hw) (simp only [cascade]) (exact hw))
  (case [cons h f ih]
    (intros w js hj hw)
    (cases js)
    (case [nil] (simp only [cascade]) (exact hw))
    (case [cons j t]
      (simp only [cascade])
      (have hj1 := hj) (simp only [tbl-all Bool.and_eq_true] at hj1)
      (exact (ih (job-apply w j) (List.append Job t (job-next w j)) (jl-step gxz gkz w j t (i10-current-exempt-well-formed gxz gkz w hw) hj)
               (i10-current-exempt-job-apply gxz gkz w j (And.left hj1) hw))))))

(a/theorem i10-current-exempt-run-cascade [gxz :- (List Nat), gkz :- (List Nat), w :- World, js :- (List Job)]
  (=> (= (tbl-all (job-ok gxz gkz w) js) true) (= (i10-current-exempt gxz gkz w) true) (= (i10-current-exempt gxz gkz (run-cascade w js)) true))
  (intros hj h) (exact (i10-current-exempt-cascade gxz gkz (cascade-fuel w js) w js hj h)))

(tree/restate! G10 '[well-formed-t16-close-scope well-formed-t15-resource-ack well-formed-t-slice-exit well-formed-t21-release-world])

;; ===========================================================================
;; Part E. Run creation: T4 (a task's run), T5 and T11 (a computation's new run, C.run := R)
;; ===========================================================================

(a/theorem all-ids-map [A :- Type, idf :- (=> A Nat), p :- (=> Nat Bool), xs :- (List A)]
  (= (tbl-all p (tbl-ids idf xs)) (tbl-all (fn [a :- A] (p (idf a))) xs))
  (induction xs) (case [nil] (simp only [tbl-ids tbl-all])) (case [cons h t ih] (simp only [tbl-ids tbl-all ih])))

(a/defn id-lt [n :- Nat, k :- I10CurrentRunKey] Bool (Nat.blt (:id k) n))
(a/theorem rir [n :- Nat, x :- Nat] (=> (= (id-in-range n x) true) (= (Nat.blt x n) true))
  (intro h) (simp only [id-in-range Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem runs-below [w :- World] (=> (= (well-formed w) true) (= (tbl-all (id-lt (:next-id w)) (i10-current-run-keys (:runs w))) true))
  (intro hs)
  (have hb := (ids-below-of w hs))
  (simp only [all-ids tbl-all-nat-app Bool.and_eq_true] at hb)
  (have h1 := (And.left (And.right (And.right (And.right hb)))))
  (rw [all-ids-map] at h1)
  (rw [all-i10-current-run-keys])
  (exact (tbl-all-mono RunRow _ _ (fn [r :- RunRow, q :- (= (id-in-range (:next-id w) (run-id r)) true)]
    (Eq.trans (Eq.symm (Eq.refl (id-lt (:next-id w) (i10-current-run-key r)))) (rir (:next-id w) (:id r) q))) _ h1)))

(a/theorem below0-ne [n :- Nat, x :- Nat] (=> (= (below0 n x) true) (= (Bool.or (Nat.beq n 0) (Bool.not (Nat.beq n x))) true))
  (intro h)
  (cases hz (Nat.beq n 0))
  (case [true] (simp only [Bool.true_or]))
  (case [false]
    (simp only [Bool.false_or])
    (cases hx (Nat.beq n x))
    (case [false] (rfl))
    (case [true]
      (have e := (Nat.eq_of_beq_eq_true hx))
      (simp only [below0 Bool.or_eq_true Nat.blt_eq] at h)
      (cases h)
      (case [inl a] (have e2 := (Nat.eq_of_beq_eq_true a)) (rw [← e] at e2) (rw [e2] at hz) (simp at hz))
      (case [inr a] (rw [← e] at a) (omega)))))

;; the new run N = (n, cid, ep, alive) against a computation row of cid updated by g
(a/theorem rc-new-new [gxz :- (List Nat), gkz :- (List Nat), n :- Nat, cid :- Nat, ep :- Nat, gc :- I10CurrentCompKey]
  (=> (= (:id gc) cid) (= (:run gc) n) (= (:idle gc) false) (<= ep (:epoch gc))
      (= (rc-ok gxz gkz (I10CurrentRunKey.mk n cid ep true) gc) true))
  (intros hi hr hd he)
  (have b1 (= (Nat.beq cid (:id gc)) true)) (rw [hi]) (exact (Nat.beq_refl cid))
  (have b2 (= (Nat.beq (:run gc) n) true)) (rw [hr]) (exact (Nat.beq_refl n))
  (have b3 (= (Nat.ble ep (:epoch gc)) true)) (simp only [Nat.ble_eq]) (exact he)
  (simp only [rc-ok cur-pair cur-core cur-fin rof-pair b1 b2 b3 hd Bool.not_true Bool.not_false Bool.false_or Bool.true_or
              Bool.or_true Bool.true_and Bool.and_true Bool.or_self]))

(a/theorem rc-new-other [gxz :- (List Nat), gkz :- (List Nat), n :- Nat, cid :- Nat, ep :- Nat, c :- I10CurrentCompKey]
  (=> (= (Nat.beq (:id c) cid) false) (= (i10-current-comp-ok n c) true) (= (rc-ok gxz gkz (I10CurrentRunKey.mk n cid ep true) c) true))
  (intros hi hc)
  (have b1 (= (Nat.beq cid (:id c)) false))
  (cases hb (Nat.beq cid (:id c))) (rfl)
  (have e := (Nat.eq_of_beq_eq_true hb)) (rw [e Nat.beq_refl] at hi) (cases hi)
  (simp only [i10-current-comp-ok Bool.and_eq_true] at hc)
  (have b2 := (below0-ne n (:run c) (And.right hc)))
  (have e2 (= (rof-pair (I10CurrentRunKey.mk n cid ep true) c) (Bool.or (Nat.beq n 0) (Bool.or (Bool.not (Nat.beq n (:run c))) (Nat.beq cid (:id c)))))) (rfl)
  (have b3 (= (rof-pair (I10CurrentRunKey.mk n cid ep true) c) true))
  (rw [e2])
  (simp only [Bool.or_eq_true] at b2)
  (simp only [Bool.or_eq_true])
  (cases b2) (case [inl a] (exact (Or.inl a))) (case [inr a] (exact (Or.inr (Or.inl a))))
  (simp only [rc-ok cur-pair cur-core b1 b3 Bool.not_false Bool.true_or Bool.or_true Bool.and_true]))

(a/theorem tof-new [n :- Nat, cid :- Nat, ep :- Nat, t :- I10CurrentTaskKey]
  (=> (= (i10-current-task-ok n t) true) (= (tof-pair (I10CurrentRunKey.mk n cid ep true) t) true))
  (intro h)
  (have b2 := (below0-ne n (:run t) h))
  (simp only [Bool.or_eq_true] at b2)
  (simp only [tof-pair Bool.or_eq_true])
  (cases b2) (case [inl a] (exact (Or.inl a))) (case [inr a] (exact (Or.inr (Or.inl a)))))

;; an existing run against an updated row of cid: it is not current there (its epoch is below)
(a/defn old-below [cid :- Nat, ep :- Nat, r :- I10CurrentRunKey] Bool
  (Bool.or (Bool.not (Nat.beq (:of r) cid)) (Nat.blt (:epoch r) ep)))
(a/theorem rc-new-old [gxz :- (List Nat), gkz :- (List Nat), n :- Nat, cid :- Nat, r :- I10CurrentRunKey, gc :- I10CurrentCompKey]
  (=> (= (Nat.blt (:id r) n) true) (= (:id gc) cid) (= (:run gc) n) (= (old-below cid (:epoch gc) r) true)
      (= (rc-ok gxz gkz r gc) true))
  (intros hid hi hr hb)
  (have b0 (= (Nat.beq (:id r) (:run gc)) false))
  (cases hb0 (Nat.beq (:id r) (:run gc))) (rfl)
  (have e := (Nat.eq_of_beq_eq_true hb0)) (rw [hr] at e) (simp only [Nat.blt_eq] at hid) (omega)
  (have hrof (= (rof-pair r gc) true)) (simp only [rof-pair b0 Bool.not_false Bool.true_or Bool.or_true])
  (have hcur (= (cur-pair gxz r gc) true))
  (simp only [cur-pair cur-core])
  (cases ho (Nat.beq (:of r) (:id gc)))
  (simp only [Bool.not_false Bool.true_or])
  (have ho2 (= (Nat.beq (:of r) cid) true)) (rw [← hi]) (exact ho)
  (simp only [old-below ho2 Bool.not_true Bool.false_or Nat.blt_eq] at hb)
  (have b3 (= (Nat.ble (:epoch r) (:epoch gc)) true)) (simp only [Nat.ble_eq]) (omega)
  (have b4 (= (Nat.beq (:epoch r) (:epoch gc)) false))
  (cases hb4 (Nat.beq (:epoch r) (:epoch gc))) (rfl)
  (have e4 := (Nat.eq_of_beq_eq_true hb4)) (omega)
  (simp only [b3 b4 Bool.not_true Bool.not_false Bool.false_or Bool.true_or Bool.true_and])
  (simp only [rc-ok hcur hrof Bool.and_self Bool.or_true]))


(a/defn newok [cid :- Nat, n :- Nat, ep :- Nat, g :- (=> I10CurrentCompKey I10CurrentCompKey), k :- I10CurrentCompKey] Bool
  (Bool.or (Bool.not (Nat.beq (:id k) cid))
   (Bool.and (Nat.beq (:run (g k)) n) (Bool.and (Bool.not (:idle (g k)))
    (Bool.and (Nat.ble ep (:epoch (g k))) (Nat.ble (:epoch k) (:epoch (g k))))))))
(a/theorem newok-on [cid :- Nat, n :- Nat, ep :- Nat, g :- (=> I10CurrentCompKey I10CurrentCompKey), k :- I10CurrentCompKey]
  (=> (= (Nat.beq (i10-current-comp-key-id k) cid) true) (= (newok cid n ep g k) true)
      (And (= (:run (g k)) n) (And (= (:idle (g k)) false) (And (<= ep (:epoch (g k))) (<= (:epoch k) (:epoch (g k)))))))
  (intros hx h)
  (have hx2 (= (Nat.beq (:id k) cid) true)) (exact hx)
  (simp only [newok hx2 Bool.not_true Bool.false_or Bool.and_eq_true Nat.ble_eq] at h)
  (exact (And.intro (Nat.eq_of_beq_eq_true (And.left h)) (And.intro (bnot-true _ (And.left (And.right h))) (And.right (And.right h))))))

(a/theorem i10-current-comp-ok-new [n :- Nat, m :- Nat, cid :- Nat, ep :- Nat, g :- (=> I10CurrentCompKey I10CurrentCompKey), k :- I10CurrentCompKey, hnm :- (< n m)]
  (=> (= (Nat.beq (i10-current-comp-key-id k) cid) true) (= (newok cid n ep g k) true) (= (i10-current-comp-ok n k) true) (= (i10-current-comp-ok m (g k)) true))
  (intros hx hn h)
  (have q := (newok-on cid n ep g k hx hn))
  (simp only [i10-current-comp-ok Bool.and_eq_true Nat.ble_eq] at h)
  (have e1 := (And.right (And.right (And.right q))))
  (have e2 := (And.left q))
  (have b1 (= (Nat.ble 1 (:epoch (g k))) true)) (simp only [Nat.ble_eq]) (omega)
  (have b2 (= (Nat.blt (:run (g k)) m) true)) (rw [e2]) (simp only [Nat.blt_eq]) (exact hnm)
  (simp only [i10-current-comp-ok below0 b1 b2 Bool.or_true Bool.and_self]))

(a/defn old-k [cid :- Nat, n :- Nat, ep :- Nat, g :- (=> I10CurrentCompKey I10CurrentCompKey), r :- I10CurrentRunKey, k :- I10CurrentCompKey] Bool
  (Bool.and (newok cid n ep g k) (Bool.or (Bool.not (Nat.beq (:id k) cid)) (old-below cid (:epoch (g k)) r))))
(a/defn old-row [gkz :- (List Nat), cid :- Nat, n :- Nat, ep :- Nat, g :- (=> I10CurrentCompKey I10CurrentCompKey), cks :- (List I10CurrentCompKey), r :- I10CurrentRunKey] Bool
  (Bool.or (reach-mem (:id r) gkz) (tbl-all (old-k cid n ep g r) cks)))

(a/theorem old-k-on [cid :- Nat, n :- Nat, ep :- Nat, g :- (=> I10CurrentCompKey I10CurrentCompKey), r :- I10CurrentRunKey, k :- I10CurrentCompKey]
  (=> (= (Nat.beq (i10-current-comp-key-id k) cid) true) (= (old-k cid n ep g r k) true) (= (old-below cid (:epoch (g k)) r) true))
  (intros hx h) (have hx2 (= (Nat.beq (:id k) cid) true)) (exact hx)
  (simp only [old-k hx2 Bool.not_true Bool.false_or Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem old-k-new [cid :- Nat, n :- Nat, ep :- Nat, g :- (=> I10CurrentCompKey I10CurrentCompKey), r :- I10CurrentRunKey, k :- I10CurrentCompKey]
  (=> (= (old-k cid n ep g r k) true) (= (newok cid n ep g k) true))
  (intro h) (simp only [old-k Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem rc-new-new-k [gxz :- (List Nat), gkz :- (List Nat), n :- Nat, cid :- Nat, ep :- Nat, g :- (=> I10CurrentCompKey I10CurrentCompKey), k :- I10CurrentCompKey,
                         hgid :- (forall [k :- I10CurrentCompKey] (= (:id (g k)) (:id k)))]
  (=> (= (Nat.beq (i10-current-comp-key-id k) cid) true) (= (newok cid n ep g k) true) (= (rc-ok gxz gkz (I10CurrentRunKey.mk n cid ep true) (g k)) true))
  (intros hx hn)
  (have q := (newok-on cid n ep g k hx hn))
  (exact (rc-new-new gxz gkz n cid ep (g k) (Eq.trans (hgid k) (Nat.eq_of_beq_eq_true hx)) (And.left q) (And.left (And.right q))
           (And.left (And.right (And.right q))))))
(a/theorem i10-current-run-ok-new-old [gxz :- (List Nat), gkz :- (List Nat), cks :- (List I10CurrentCompKey), tks :- (List I10CurrentTaskKey), n :- Nat, m :- Nat,
                        cid :- Nat, ep :- Nat, g :- (=> I10CurrentCompKey I10CurrentCompKey),
                        hgid :- (forall [k :- I10CurrentCompKey] (= (:id (g k)) (:id k))), r :- I10CurrentRunKey]
  (=> (<= n m) (= (i10-current-run-ok gxz gkz cks tks n r) true) (= (old-row gkz cid n ep g cks r) true) (= (id-lt n r) true)
      (= (i10-current-run-ok gxz gkz (tbl-upd i10-current-comp-key-id cid g cks) tks m r) true))
  (intros hnm h ho hi)
  (simp only [i10-current-run-ok Bool.and_eq_true Nat.blt_eq] at h)
  (simp only [id-lt] at hi)
  (have hof (= (Nat.blt (:of r) m) true)) (simp only [Nat.blt_eq]) (omega)
  (have hrc (= (tbl-all (rc-ok gxz gkz r) (tbl-upd i10-current-comp-key-id cid g cks)) true))
  (cases hk (reach-mem (:id r) gkz))
  (case [true] (exact (all-true-of I10CurrentCompKey _ (fn [k :- I10CurrentCompKey] (rc-exempt gxz gkz r k hk)) _)))
  (case [false]
    (simp only [old-row hk Bool.false_or] at ho)
    (exact (tbl-all-upd I10CurrentCompKey i10-current-comp-key-id cid g (both (rc-ok gxz gkz r) (old-k cid n ep g r)) (rc-ok gxz gkz r)
             (fn [k :- I10CurrentCompKey, p :- (= (both (rc-ok gxz gkz r) (old-k cid n ep g r) k) true), hx :- (= (Nat.beq (i10-current-comp-key-id k) cid) true)]
               (rc-new-old gxz gkz n cid r (g k) hi (Eq.trans (hgid k) (Nat.eq_of_beq_eq_true hx))
                 (And.left (newok-on cid n ep g k hx (old-k-new cid n ep g r k (both-right _ _ _ _ p))))
                 (old-k-on cid n ep g r k hx (both-right _ _ _ _ p))))
             (fn [k :- I10CurrentCompKey, p :- (= (both (rc-ok gxz gkz r) (old-k cid n ep g r) k) true), hx :- (= (Nat.beq (i10-current-comp-key-id k) cid) false)]
               (both-left _ _ _ _ p))
             cks (tbl-all-mono2 I10CurrentCompKey _ _ _ (fn [k :- I10CurrentCompKey, a1 :- (= (rc-ok gxz gkz r k) true), a2 :- (= (old-k cid n ep g r k) true)] (both-mk _ _ _ _ a1 a2))
                   cks (And.left h) ho))))
  (simp only [i10-current-run-ok Bool.and_eq_true hrc (And.left (And.right h)) hof and_self]))

;; T5/T11: the new run (n, cid, ep) with C.run := n on every row of cid (updated by g)
(a/theorem i10-current-exempt-keys-ok-new-run [gxz :- (List Nat), gkz :- (List Nat), rks :- (List I10CurrentRunKey), cks :- (List I10CurrentCompKey), tks :- (List I10CurrentTaskKey),
                         n :- Nat, m :- Nat, cid :- Nat, ep :- Nat, g :- (=> I10CurrentCompKey I10CurrentCompKey),
                         hgid :- (forall [k :- I10CurrentCompKey] (= (:id (g k)) (:id k)))]
  (=> (= (i10-current-exempt-keys-ok gxz gkz rks cks tks n) true) (= (tbl-all (newok cid n ep g) cks) true)
      (= (tbl-all (old-row gkz cid n ep g cks) rks) true) (= (tbl-all (id-lt n) rks) true)
      (< n m) (< cid m)
      (= (i10-current-exempt-keys-ok gxz gkz (List.cons I10CurrentRunKey (I10CurrentRunKey.mk n cid ep true) rks) (tbl-upd i10-current-comp-key-id cid g cks) tks m) true))
  (intros h hnw ho hi hnm hcm)
  (simp only [i10-current-exempt-keys-ok Bool.and_eq_true] at h)
  (have hnm2 (<= n m)) (omega)
  (have hcn := (tbl-all-mono2 I10CurrentCompKey (i10-current-comp-ok n) (newok cid n ep g) (both (i10-current-comp-ok n) (newok cid n ep g))
                 (fn [k :- I10CurrentCompKey, a1 :- (= (i10-current-comp-ok n k) true), a2 :- (= (newok cid n ep g k) true)] (both-mk _ _ _ _ a1 a2))
                 cks (And.left (And.right h)) hnw))
  (have hc' (= (tbl-all (i10-current-comp-ok m) (tbl-upd i10-current-comp-key-id cid g cks)) true))
  (exact (tbl-all-upd I10CurrentCompKey i10-current-comp-key-id cid g (both (i10-current-comp-ok n) (newok cid n ep g)) (i10-current-comp-ok m)
           (fn [k :- I10CurrentCompKey, p :- (= (both (i10-current-comp-ok n) (newok cid n ep g) k) true), hx :- (= (Nat.beq (i10-current-comp-key-id k) cid) true)]
             (i10-current-comp-ok-new n m cid ep g k hnm hx (both-right _ _ _ _ p) (both-left _ _ _ _ p)))
           (fn [k :- I10CurrentCompKey, p :- (= (both (i10-current-comp-ok n) (newok cid n ep g) k) true), hx :- (= (Nat.beq (i10-current-comp-key-id k) cid) false)]
             (i10-current-comp-ok-next n m k hnm2 (both-left _ _ _ _ p)))
           cks hcn))
  (have ht' := (tbl-all-mono I10CurrentTaskKey (i10-current-task-ok n) (i10-current-task-ok m) (fn [t :- I10CurrentTaskKey, p :- (= (i10-current-task-ok n t) true)] (i10-current-task-ok-next n m t hnm2 p)) tks (And.right (And.right h))))
  (have hN1 (= (tbl-all (rc-ok gxz gkz (I10CurrentRunKey.mk n cid ep true)) (tbl-upd i10-current-comp-key-id cid g cks)) true))
  (exact (tbl-all-upd I10CurrentCompKey i10-current-comp-key-id cid g (both (i10-current-comp-ok n) (newok cid n ep g)) (rc-ok gxz gkz (I10CurrentRunKey.mk n cid ep true))
           (fn [k :- I10CurrentCompKey, p :- (= (both (i10-current-comp-ok n) (newok cid n ep g) k) true), hx :- (= (Nat.beq (i10-current-comp-key-id k) cid) true)]
             (rc-new-new-k gxz gkz n cid ep g k hgid hx (both-right _ _ _ _ p)))
           (fn [k :- I10CurrentCompKey, p :- (= (both (i10-current-comp-ok n) (newok cid n ep g) k) true), hx :- (= (Nat.beq (i10-current-comp-key-id k) cid) false)]
             (rc-new-other gxz gkz n cid ep k hx (both-left _ _ _ _ p)))
           cks hcn))
  (have hN2 := (tbl-all-mono I10CurrentTaskKey (i10-current-task-ok n) (tof-pair (I10CurrentRunKey.mk n cid ep true)) (fn [t :- I10CurrentTaskKey, p :- (= (i10-current-task-ok n t) true)] (tof-new n cid ep t p)) tks (And.right (And.right h))))
  (have hN3 (= (Nat.blt cid m) true)) (simp only [Nat.blt_eq]) (exact hcm)
  (have hN (= (i10-current-run-ok gxz gkz (tbl-upd i10-current-comp-key-id cid g cks) tks m (I10CurrentRunKey.mk n cid ep true)) true))
  (simp only [i10-current-run-ok hN1 hN2 hN3 Bool.and_self])
  (have hold := (tbl-all-mono2 I10CurrentRunKey (i10-current-run-ok gxz gkz cks tks n) (old-row gkz cid n ep g cks) (both (i10-current-run-ok gxz gkz cks tks n) (old-row gkz cid n ep g cks))
                  (fn [r :- I10CurrentRunKey, a1 :- (= (i10-current-run-ok gxz gkz cks tks n r) true), a2 :- (= (old-row gkz cid n ep g cks r) true)] (both-mk _ _ _ _ a1 a2))
                  rks (And.left h) ho))
  (have hR := (tbl-all-mono2 I10CurrentRunKey (both (i10-current-run-ok gxz gkz cks tks n) (old-row gkz cid n ep g cks)) (id-lt n) (i10-current-run-ok gxz gkz (tbl-upd i10-current-comp-key-id cid g cks) tks m)
                (fn [r :- I10CurrentRunKey, a1 :- (= (both (i10-current-run-ok gxz gkz cks tks n) (old-row gkz cid n ep g cks) r) true), a2 :- (= (id-lt n r) true)]
                  (i10-current-run-ok-new-old gxz gkz cks tks n m cid ep g hgid r hnm2 (both-left _ _ _ _ a1) (both-right _ _ _ _ a1) a2))
                rks hold hi))
  (simp only [i10-current-exempt-keys-ok tbl-all hN hR hc' ht' Bool.and_self]))

;; ---- T14 from the host (a task's run) and the T6 losers (tasks' runs): the job condition

(a/theorem i10-current-exempt-t14-cancel [gxz :- (List Nat), gkz :- (List Nat), w :- World, rid :- Nat, rep :- Bool]
  (=> (= (ncw gxz gkz rid w) true) (= (i10-current-exempt gxz gkz w) true) (= (i10-current-exempt gxz gkz (:world (t14-cancel w rid rep))) true))
  (intros hn h)
  (cases hf (run-find w rid))
  (case [none] (simp only [t14-cancel hf refuse]) (exact h))
  (case [some r]
    (cases ha (run-alive r))
    (case [false] (simp only [t14-cancel hf ha refuse]) (exact h))
    (case [true]
      (simp only [t14-cancel hf ha accept])
      (have hj (= (tbl-all (job-ok gxz gkz w) (List.cons Job (Job.jcancel rid rep) (List.nil Job))) true))
      (simp only [tbl-all job-ok hn Bool.and_self])
      (exact (i10-current-exempt-run-cascade gxz gkz w _ hj h)))))

(a/theorem found-task-ncw [gxz :- (List Nat), gkz :- (List Nat), w :- World, rid :- Nat, r :- RunRow]
  (=> (= (well-formed w) true) (= (run-find w rid) (Option.some RunRow r)) (= (task-has w (:of r)) true) (= (ncw gxz gkz rid w) true))
  (intros hs hf ht)
  (have m := (tbl-find-mem RunRow run-id rid r (:runs w) hf))
  (have e (= (run-id r) rid)) (exact (tbl-find-id RunRow run-id rid r (:runs w) hf))
  (have u := (uniq-all RunRow run-id (fn [q :- RunRow] (task-has w (:of q))) r (:runs w) (lit-runs-nodup w hs) m ht))
  (rw [e] at u)
  (exact (task-run-ncw gxz gkz rid w hs u)))

(a/theorem i10-current-exempt-t14-host-cancel [gxz :- (List Nat), gkz :- (List Nat), w :- World, rid :- Nat]
  (=> (= (i10-current-exempt gxz gkz w) true) (= (i10-current-exempt gxz gkz (:world (t14-host-cancel w rid))) true))
  (intro h)
  (cases hf (run-find w rid))
  (case [none] (simp only [t14-host-cancel hf refuse]) (exact h))
  (case [some r]
    (cases hg (host-cancel-ok w r))
    (case [false]
      ;; C1: a done task run's cancel reaches its scope subtree (its owned task runs)
      (cases hd (host-cancel-done w r))
      (case [false] (simp only [t14-host-cancel hf hg cancel-done hd refuse]) (exact h))
      (case [true]
        (have hj (= (tbl-all (job-ok gxz gkz w) (cancel-jobs (owned-runs w (scope-subtree w (:scope r))))) true))
        (rw [jl-cancel-jobs]) (exact (owned-ncw gxz gkz w _ (i10-current-exempt-well-formed gxz gkz w h)))
        (simp only [t14-host-cancel hf hg cancel-done hd accept])
        (exact (i10-current-exempt-run-cascade gxz gkz w _ hj h))))
    (case [true]
      (simp only [t14-host-cancel hf hg])
      (have hg2 := hg) (simp only [host-cancel-ok Bool.and_eq_true] at hg2)
      (exact (i10-current-exempt-t14-cancel gxz gkz w rid false (found-task-ncw gxz gkz w rid r (i10-current-exempt-well-formed gxz gkz w h) hf (And.right (And.right hg2))) h)))))

(a/theorem i10-current-exempt-tof [gxz :- (List Nat), gkz :- (List Nat), w :- World, r :- RunRow, t :- TaskRow]
  (=> (= (i10-current-exempt gxz gkz w) true) (List.Mem r (:runs w)) (List.Mem t (:tasks w)) (= (tof-pair (i10-current-run-key r) (i10-current-task-key t)) true))
  (intros h mr mt)
  (have hr := (i10-current-exempt-rest-of gxz gkz w h))
  (simp only [i10-current-exempt-rest i10-current-exempt-keys-ok Bool.and_eq_true] at hr)
  (have a1 := (And.left hr)) (rw [all-i10-current-run-keys] at a1)
  (have a2 := (tbl-all-mem RunRow _ r _ a1 mr))
  (simp only [i10-current-run-ok Bool.and_eq_true] at a2)
  (have a3 := (And.left (And.right a2))) (rw [all-i10-current-task-keys] at a3)
  (exact (tbl-all-mem TaskRow _ t _ a3 mt)))

(a/theorem run-id-pos [w :- World, r :- RunRow]
  (=> (= (well-formed w) true) (List.Mem r (:runs w)) (= (Nat.beq (:id r) 0) false))
  (intros hs m)
  (have hb := (ids-below-of w hs))
  (simp only [all-ids tbl-all-nat-app Bool.and_eq_true] at hb)
  (have h1 := (And.left (And.right (And.right (And.right hb)))))
  (rw [all-ids-map] at h1)
  (have q := (tbl-all-mem RunRow _ r _ h1 m))
  (simp only [id-in-range run-id Bool.and_eq_true Nat.blt_eq] at q)
  (cases hb0 (Nat.beq (:id r) 0)) (rfl)
  (have e := (Nat.eq_of_beq_eq_true hb0)) (omega))

(a/theorem task-mem-has [w :- World, t :- TaskRow] (=> (List.Mem t (:tasks w)) (= (task-has w (:id t)) true))
  (intros m) (have hm := (mem-ids-has TaskRow task-id t (:tasks w) m)) (rw [nat-mem-ids] at hm) (exact hm))
(a/theorem task-run-tasks [gxz :- (List Nat), gkz :- (List Nat), w :- World, x :- Nat]
  (=> (= (i10-current-exempt gxz gkz w) true)
      (= (tbl-all (same-id-then run-id (task-run-of w x) (fn [q :- RunRow] (task-has w (:of q)))) (:runs w)) true))
  (intro h)
  (have hs := (i10-current-exempt-well-formed gxz gkz w h))
  (apply (all-of-mem RunRow _ (:runs w)))
  (intros r m)
  (have hz := (run-id-pos w r hs m))
  (cases hf (task-find w x))
  (case [none]
    (have hz2 (= (Nat.beq (run-id r) 0) false)) (exact hz)
    (simp only [same-id-then task-run-of hf hz2 Bool.not_false Bool.true_or]))
  (case [some t]
    (cases hx (Nat.beq (run-id r) (:run t)))
    (case [false] (simp only [same-id-then task-run-of hf hx Bool.not_false Bool.true_or]))
    (case [true]
      (have mt := (tbl-find-mem TaskRow task-id x t (:tasks w) hf))
      (have tp := (i10-current-exempt-tof gxz gkz w r t h m mt))
      (have hx2 (= (Nat.beq (:id r) (:run t)) true)) (exact hx)
      (simp only [tof-pair i10-current-run-key i10-current-task-key hz hx2 Bool.not_true Bool.false_or] at tp)
      (have e := (Nat.eq_of_beq_eq_true tp))
      (have ht (= (task-has w (:of r)) true)) (rw [e])
      (exact (Eq.trans (Eq.refl (tbl-has task-id (:id t) (:tasks w))) (task-mem-has w t mt)))
      (simp only [same-id-then task-run-of hf hx ht Bool.or_true]))))

(a/theorem task-runs-ncw [gxz :- (List Nat), gkz :- (List Nat), w :- World, xs :- (List Nat)]
  (=> (= (i10-current-exempt gxz gkz w) true) (= (tbl-all (fn [x :- Nat] (ncw gxz gkz x w)) (task-runs w xs)) true))
  (intro h)
  (induction xs)
  (case [nil] (simp only [task-runs tbl-all]))
  (case [cons hd t ih]
    (simp only [task-runs tbl-all ih Bool.and_true])
    (exact (task-run-ncw gxz gkz _ w (i10-current-exempt-well-formed gxz gkz w h) (task-run-tasks gxz gkz w hd h)))))

(a/theorem gather-all10 [A :- Type, p :- (=> A Bool), f :- (=> A (List Nat)), q :- (=> Nat Bool),
                       hf :- (forall [a :- A] (= (tbl-all q (f a)) true)), xs :- (List A)]
  (= (tbl-all q (tbl-gather p f xs)) true)
  (induction xs)
  (case [nil] (simp only [tbl-gather tbl-all]))
  (case [cons hd t ih]
    (cases hp (p hd))
    (case [false] (simp only [tbl-gather hp]) (exact ih))
    (case [true] (simp only [tbl-gather hp all-append (hf hd) ih Bool.and_self]))))

(a/theorem loser-ncw [gxz :- (List Nat), gkz :- (List Nat), w :- World, a :- ActRow]
  (=> (= (i10-current-exempt gxz gkz w) true) (= (tbl-all (fn [x :- Nat] (ncw gxz gkz x w)) (loser-runs w a)) true))
  (intro h) (simp only [loser-runs])
  (exact (task-runs-ncw gxz gkz w (tbl-filter (loser-task w (run-scope-of w (:run a))) (:spawned a)) h)))

(a/theorem i10-current-exempt-cancel-losers [gxz :- (List Nat), gkz :- (List Nat), w0 :- World, w1 :- World]
  (=> (= (i10-current-exempt gxz gkz w1) true) (= (i10-current-exempt gxz gkz (cancel-losers w0 w1)) true))
  (intro h)
  (simp only [cancel-losers])
  (have hj (= (tbl-all (job-ok gxz gkz w1) (cancel-jobs (tbl-gather (any-resolved w1) (loser-runs w1) (:acts w0)))) true))
  (rw [jl-cancel-jobs])
  (exact (gather-all10 ActRow (any-resolved w1) (loser-runs w1) (fn [x :- Nat] (ncw gxz gkz x w1))
           (fn [a :- ActRow] (loser-ncw gxz gkz w1 a h)) (:acts w0)))
  (exact (i10-current-exempt-run-cascade gxz gkz w1 (cancel-jobs (tbl-gather (any-resolved w1) (loser-runs w1) (:acts w0))) hj h)))

;; ---- facts about rows of the world

(a/theorem i10-current-exempt-rc [gxz :- (List Nat), gkz :- (List Nat), w :- World, q :- RunRow, k :- CompRow]
  (=> (= (i10-current-exempt gxz gkz w) true) (List.Mem q (:runs w)) (List.Mem k (:comps w)) (= (rc-ok gxz gkz (i10-current-run-key q) (i10-current-comp-key k)) true))
  (intros h mr mk)
  (have hr := (i10-current-exempt-rest-of gxz gkz w h))
  (simp only [i10-current-exempt-rest i10-current-exempt-keys-ok Bool.and_eq_true] at hr)
  (have a1 := (And.left hr)) (rw [all-i10-current-run-keys] at a1)
  (have a2 := (tbl-all-mem RunRow _ q _ a1 mr))
  (simp only [i10-current-run-ok Bool.and_eq_true] at a2)
  (have a3 := (And.left a2)) (rw [all-i10-current-comp-keys] at a3)
  (exact (tbl-all-mem CompRow _ k _ a3 mk)))

(a/defn bool-eq [a :- Bool, b :- Bool] Bool (Bool.and (Bool.or (Bool.not a) b) (Bool.or (Bool.not b) a)))
(a/defn ck-eq [a :- CompRow, b :- CompRow] Bool
  (Bool.and (Nat.beq (:epoch a) (:epoch b)) (Bool.and (Nat.beq (:done-epoch a) (:done-epoch b))
   (Bool.and (Nat.beq (:run a) (:run b)) (bool-eq (:idle a) (:idle b))))))
(a/theorem bool-eq-refl [a :- Bool] (= (bool-eq a a) true) (cases a) (all_goals (rfl)))
(a/theorem bool-eq-eq [a :- Bool, b :- Bool] (=> (= (bool-eq a b) true) (= a b))
  (intro h) (cases a) (all_goals (cases b)) (all_goals (try (simp [bool-eq] at h))) (all_goals (try (rfl))))
(a/theorem ck-eq-refl [a :- CompRow] (= (ck-eq a a) true)
  (simp only [ck-eq Nat.beq_refl bool-eq-refl Bool.and_self]))
(a/theorem ck-eq-parts [a :- CompRow, b :- CompRow]
  (=> (= (ck-eq a b) true)
      (And (= (:epoch a) (:epoch b)) (And (= (:done-epoch a) (:done-epoch b)) (And (= (:run a) (:run b)) (= (:idle a) (:idle b))))))
  (intro h)
  (simp only [ck-eq Bool.and_eq_true] at h)
  (exact (And.intro (Nat.eq_of_beq_eq_true (And.left h)) (And.intro (Nat.eq_of_beq_eq_true (And.left (And.right h)))
           (And.intro (Nat.eq_of_beq_eq_true (And.left (And.right (And.right h)))) (bool-eq-eq _ _ (And.right (And.right (And.right h)))))))))

;; every computation row with c's id has c's epoch, result epoch, run and idleness
(a/theorem comp-same [w :- World, c :- CompRow, k :- CompRow]
  (=> (= (well-formed w) true) (List.Mem c (:comps w)) (List.Mem k (:comps w)) (= (:id k) (:id c))
      (And (= (:epoch k) (:epoch c)) (And (= (:done-epoch k) (:done-epoch c)) (And (= (:run k) (:run c)) (= (:idle k) (:idle c))))))
  (intros hs mc mk e)
  (have u := (uniq-all CompRow comp-id (fn [q :- CompRow] (ck-eq q c)) c (:comps w) (comps-nodup10 w hs) mc (ck-eq-refl c)))
  (have q := (tbl-all-mem CompRow _ k _ u mk))
  (have e2 (= (Nat.beq (comp-id k) (comp-id c)) true)) (have e3 (= (comp-id k) (comp-id c))) (exact e) (rw [e3]) (exact (Nat.beq_refl _))
  (simp only [same-id-then e2 Bool.not_true Bool.false_or] at q)
  (exact (ck-eq-parts k c q)))

(a/theorem by-refl2 [a :- Nat, b :- Nat] (= (Bool.and (Nat.beq a a) (Nat.beq b b)) true) (simp only [Nat.beq_refl Bool.and_self]))
(a/theorem run-same-ep [w :- World, r :- RunRow, q :- RunRow]
  (=> (= (well-formed w) true) (List.Mem r (:runs w)) (List.Mem q (:runs w)) (= (:id q) (:id r))
      (And (= (:epoch q) (:epoch r)) (= (:of q) (:of r))))
  (intros hs mr mq e)
  (have u := (uniq-all RunRow run-id (fn [x :- RunRow] (Bool.and (Nat.beq (:epoch x) (:epoch r)) (Nat.beq (:of x) (:of r)))) r (:runs w)
               (lit-runs-nodup w hs) mr (by-refl2 (:epoch r) (:of r))))
  (have v := (tbl-all-mem RunRow _ q _ u mq))
  (have e2 (= (Nat.beq (run-id q) (run-id r)) true)) (have e3 (= (run-id q) (run-id r))) (exact e) (rw [e3]) (exact (Nat.beq_refl _))
  (simp only [same-id-then e2 Bool.not_true Bool.false_or Bool.and_eq_true] at v)
  (exact (And.intro (Nat.eq_of_beq_eq_true (And.left v)) (Nat.eq_of_beq_eq_true (And.right v)))))

;; ---- a non-exempt pair, unpacked
(a/theorem rc-parts [gxz :- (List Nat), gkz :- (List Nat), r :- I10CurrentRunKey, c :- I10CurrentCompKey]
  (=> (= (rc-ok gxz gkz r c) true) (= (reach-mem (:id r) gkz) false) (And (= (cur-pair gxz r c) true) (= (rof-pair r c) true)))
  (intros h hk) (simp only [rc-ok hk Bool.false_or Bool.and_eq_true] at h) (exact h))
(a/theorem cur-le [gxz :- (List Nat), r :- I10CurrentRunKey, c :- I10CurrentCompKey]
  (=> (= (cur-pair gxz r c) true) (= (Nat.beq (:of r) (:id c)) true) (<= (:epoch r) (:epoch c)))
  (intros h ho)
  (simp only [cur-pair cur-core ho Bool.not_true Bool.false_or Bool.and_eq_true Nat.ble_eq] at h) (exact (And.left h)))
(a/theorem cur-eq [gxz :- (List Nat), r :- I10CurrentRunKey, c :- I10CurrentCompKey]
  (=> (= (cur-pair gxz r c) true) (= (Nat.beq (:of r) (:id c)) true) (= (Nat.beq (:epoch r) (:epoch c)) true)
      (And (= (:run c) (:id r)) (And (= (:idle c) false) (= (cur-fin gxz r c) true))))
  (intros h ho he)
  (simp only [cur-pair cur-core ho he Bool.not_true Bool.false_or Bool.and_eq_true] at h)
  (have h2 := (And.right h))
  (exact (And.intro (Nat.eq_of_beq_eq_true (And.left h2)) (And.intro (bnot-true _ (And.left (And.right h2))) (And.right (And.right h2))))))
(a/theorem rof-is [r :- I10CurrentRunKey, c :- I10CurrentCompKey]
  (=> (= (rof-pair r c) true) (= (Nat.beq (:id r) 0) false) (= (:id r) (:run c)) (= (:of r) (:id c)))
  (intros h hz e)
  (have e2 (= (Nat.beq (:id r) (:run c)) true)) (rw [e]) (exact (Nat.beq_refl _))
  (simp only [rof-pair hz e2 Bool.not_true Bool.false_or] at h)
  (exact (Nat.eq_of_beq_eq_true h)))

(a/theorem i10-current-transport-row-of-mem [nqr :- (=> RS10 CS10 Bool), cs :- (List CompRow), x :- RS10,
                          h :- (forall [k :- CompRow] (=> (List.Mem k cs) (= (nqr x (cs10 k)) true)))]
  (= (i10-current-transport-row nqr (cs10s cs) x) true)
  (simp only [i10-current-transport-row]) (rw [all-cs10s]) (exact (all-of-mem CompRow _ cs h)))
(a/theorem nqk-of-mem [nqr :- (=> RS10 CS10 Bool), nqc :- (=> CS10 Bool), rs :- (List RunRow), cs :- (List CompRow),
                       hr :- (forall [q :- RunRow, k :- CompRow] (=> (List.Mem q rs) (List.Mem k cs) (= (nqr (rs10 q) (cs10 k)) true))),
                       hc :- (forall [k :- CompRow] (=> (List.Mem k cs) (= (nqc (cs10 k)) true)))]
  (= (nqk nqr nqc (rs10s rs) (cs10s cs)) true)
  (have a1 (= (tbl-all (i10-current-transport-row nqr (cs10s cs)) (rs10s rs)) true))
  (rw [all-rs10s])
  (exact (all-of-mem RunRow _ rs (fn [q :- RunRow, m :- (List.Mem q rs)] (i10-current-transport-row-of-mem nqr cs (rs10 q) (fn [k :- CompRow, mk :- (List.Mem k cs)] (hr q k m mk))))))
  (have a2 (= (tbl-all nqc (cs10s cs)) true)) (rw [all-cs10s]) (exact (all-of-mem CompRow _ cs hc))
  (simp only [nqk a1 a2 Bool.and_self]))

;; ---- T11: the predecessor C.run is stale (needs-run), so its cancel meets the job condition

(a/theorem pred-pair [gxz :- (List Nat), gkz :- (List Nat), w :- World, c :- CompRow, r :- RunRow, q :- RunRow, k :- CompRow]
  (=> (= (i10-current-exempt gxz gkz w) true) (List.Mem c (:comps w)) (= (needs-run w c) true) (= (run-find w (:run c)) (Option.some RunRow r))
      (List.Mem q (:runs w)) (List.Mem k (:comps w)) (= (nc-run gxz gkz (:id r) (rs10 q) (cs10 k)) true))
  (intros h mc hn hf mq mk)
  (have hs := (i10-current-exempt-well-formed gxz gkz w h))
  (cases hx (Nat.beq (:id q) (:id r)))
  (case [false] (exact (nc-run-off gxz gkz (:id r) (rs10 q) (cs10 k) hx)))
  (case [true]
    (cases hk (reach-mem (:id q) gkz))
    (case [true] (simp only [nc-run rs10 hk Bool.true_or Bool.or_true]))
    (case [false]
      (have mr := (tbl-find-mem RunRow run-id (:run c) r (:runs w) hf))
      (have er (= (:id r) (:run c))) (exact (tbl-find-id RunRow run-id (:run c) r (:runs w) hf))
      (have eq := (Nat.eq_of_beq_eq_true hx))
      (have sq := (run-same-ep w r q hs mr mq eq))
      (have pc := (rc-parts gxz gkz (i10-current-run-key q) (i10-current-comp-key c) (i10-current-exempt-rc gxz gkz w q c h mq mc) hk))
      (have ho := (rof-is (i10-current-run-key q) (i10-current-comp-key c) (And.right pc) (run-id-pos w q hs mq) (Eq.trans eq er)))
      (have ho2 (= (:of q) (:id c))) (exact ho)
      (cases hkc (Nat.beq (:of q) (:id k)))
      (case [false] (exact (nc-run-of gxz gkz (:id r) (rs10 q) (cs10 k) hkc)))
      (case [true]
        (have ek := (Nat.eq_of_beq_eq_true hkc))
        (have sk := (comp-same w c k hs mc mk (Eq.trans (Eq.symm ek) ho2)))
        (have ho3 (= (Nat.beq (:of (i10-current-run-key q)) (:id (i10-current-comp-key c))) true)) (exact (Eq.trans (congrArg (fn [x :- Nat] (Nat.beq x (:id c))) ho2) (Nat.beq_refl (:id c))))
        (have le := (cur-le gxz (i10-current-run-key q) (i10-current-comp-key c) (And.left pc) ho3))
        (have hne (= (Nat.beq (:epoch r) (:epoch c)) false))
        (simp only [needs-run run-current-of-comp hf Bool.and_eq_true] at hn)
        (exact (bnot-true _ (And.right hn)))
        (have hne2 (Not (= (:epoch q) (:epoch c))))
        (intro z) (rw [(And.left sq)] at z) (rw [z Nat.beq_refl] at hne) (cases hne)
        (have lt (< (:epoch q) (:epoch k))) (rw [(And.left sk)]) (have le2 (<= (:epoch q) (:epoch c))) (exact le) (omega)
        (have lt2 (= (Nat.blt (:epoch q) (:epoch k)) true)) (simp only [Nat.blt_eq]) (exact lt)
        (simp only [nc-run nc-cs rs10 cs10 lt2 Bool.or_true])))))

(a/theorem pred-ncw [gxz :- (List Nat), gkz :- (List Nat), w :- World, c :- CompRow, r :- RunRow]
  (=> (= (i10-current-exempt gxz gkz w) true) (List.Mem c (:comps w)) (= (needs-run w c) true) (= (run-find w (:run c)) (Option.some RunRow r))
      (= (ncw gxz gkz (:id r) w) true))
  (intros h mc hn hf)
  (simp only [ncw])
  (exact (nqk-of-mem (nc-run gxz gkz (:id r)) tt-c (:runs w) (:comps w) (fn [q :- RunRow, k :- CompRow, mq :- (List.Mem q (:runs w)), mk :- (List.Mem k (:comps w))]
                               (pred-pair gxz gkz w c r q k h mc hn hf mq mk))
           (fn [k :- CompRow, mk :- (List.Mem k (:comps w))] (Eq.refl true)))))

(a/theorem i10-current-exempt-cancel-pred [gxz :- (List Nat), gkz :- (List Nat), w :- World, c :- CompRow]
  (=> (List.Mem c (:comps w)) (= (needs-run w c) true) (= (i10-current-exempt gxz gkz w) true) (= (i10-current-exempt gxz gkz (cancel-pred w c)) true))
  (intros mc hn h)
  (cases hr (run-find w (:run c)))
  (case [none] (simp only [cancel-pred hr]) (exact h))
  (case [some r]
    (cases ha (run-alive r))
    (case [false] (simp only [cancel-pred hr ha]) (exact h))
    (case [true]
      (simp only [cancel-pred hr ha])
      (have hj (= (tbl-all (job-ok gxz gkz w) (List.cons Job (Job.jcancel (:id r) true) (List.nil Job))) true))
      (simp only [tbl-all job-ok (pred-ncw gxz gkz w c r h mc hn hr) Bool.and_self])
      (exact (i10-current-exempt-run-cascade gxz gkz w _ hj h)))))

;; ---- T11: computation C keeps its epoch (or a later one), stays awake, and has no run at its
;; epoch through the predecessor's cancel, the cut and the entry (transport bundle instance)

(a/defn kc-r [gkz :- (List Nat), cid :- Nat, ep :- Nat, r :- RS10, k :- CS10] Bool
  (Bool.or (Bool.not (Nat.beq (:id k) cid))
   (Bool.or (Bool.not (Nat.beq (:of r) cid)) (Bool.or (Nat.blt (:epoch r) ep) (reach-mem (:id r) gkz)))))
(a/defn kc-c [cid :- Nat, ep :- Nat, k :- CS10] Bool
  (Bool.or (Bool.not (Nat.beq (:id k) cid)) (Bool.and (Nat.ble ep (:epoch k)) (Bool.not (:idle k)))))
(a/theorem kc-r-m [gkz :- (List Nat), cid :- Nat, ep :- Nat, r :- RS10, k :- CS10]
  (=> (= (kc-r gkz cid ep r k) true) (= (kc-r gkz cid ep r (cs-step k)) true)) (intro h) (exact h))
(a/theorem kc-c-m [cid :- Nat, ep :- Nat, k :- CS10] (=> (= (kc-c cid ep k) true) (= (kc-c cid ep (cs-step k)) true))
  (intro h)
  (cases hx (Nat.beq (:id k) cid))
  (case [false] (simp only [kc-c cs-step hx Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [kc-c hx Bool.not_true Bool.false_or Bool.and_eq_true Nat.ble_eq] at h)
    (have b (= (Nat.ble ep (+ (:epoch k) 1)) true)) (simp only [Nat.ble_eq]) (have z := (And.left h)) (omega)
    (have hx2 (= (Nat.beq (:id (cs-step k)) cid) true)) (exact hx)
    (have hi (= (:idle (cs-step k)) (:idle k))) (rfl)
    (simp only [kc-c hx2 hi b (And.right h) Bool.not_true Bool.false_or Bool.and_self])))

(a/defn kcq [gkz :- (List Nat), cid :- Nat, ep :- Nat, w :- World] Bool
  (i10-current-transport (kc-r gkz cid ep) (kc-c cid ep) (kc-r-m gkz cid ep) (kc-c-m cid ep) w))

(a/theorem edge-kind-kept-pair [gxz :- (List Nat), gkz :- (List Nat), w :- World, c :- CompRow, q :- RunRow, k :- CompRow]
  (=> (= (i10-current-exempt gxz gkz w) true) (List.Mem c (:comps w)) (= (needs-run w c) true) (List.Mem q (:runs w)) (List.Mem k (:comps w))
      (= (kc-r gkz (:id c) (:epoch c) (rs10 q) (cs10 k)) true))
  (intros h mc hn mq mk)
  (have hs := (i10-current-exempt-well-formed gxz gkz w h))
  (cases hx (Nat.beq (:id k) (:id c)))
  (case [false] (simp only [kc-r cs10 hx Bool.not_false Bool.true_or]))
  (case [true]
    (cases ho (Nat.beq (:of q) (:id c)))
    (case [false] (simp only [kc-r cs10 rs10 hx ho Bool.not_false Bool.not_true Bool.true_or Bool.false_or]))
    (case [true]
      (cases hk (reach-mem (:id q) gkz))
      (case [true] (simp only [kc-r rs10 hk Bool.or_true]))
      (case [false]
        (have pc := (rc-parts gxz gkz (i10-current-run-key q) (i10-current-comp-key c) (i10-current-exempt-rc gxz gkz w q c h mq mc) hk))
        (have ho2 (= (Nat.beq (:of (i10-current-run-key q)) (:id (i10-current-comp-key c))) true)) (exact ho)
        (have le := (cur-le gxz (i10-current-run-key q) (i10-current-comp-key c) (And.left pc) ho2))
        (cases he (Nat.beq (:epoch q) (:epoch c)))
        (case [false]
          (have lt (= (Nat.blt (:epoch q) (:epoch c)) true)) (simp only [Nat.blt_eq]) (have z := (Nat.ne_of_beq_eq_false he)) (omega)
          (simp only [kc-r rs10 lt Bool.true_or Bool.or_true]))
        (case [true]
          (have ce := (cur-eq gxz (i10-current-run-key q) (i10-current-comp-key c) (And.left pc) ho2 he))
          (have erun (= (:run c) (:id q))) (exact (And.left ce))
          (cases hf (run-find w (:run c)))
          (case [none]
            (have z := (tbl-find-none-has RunRow run-id (:run c) (:runs w) hf))
            (have z2 (= (tbl-has run-id (:run c) (:runs w)) true)) (rw [erun])
            (have hm := (mem-ids-has RunRow run-id q (:runs w) mq)) (rw [nat-mem-ids] at hm) (exact hm)
            (rw [z2] at z) (cases z))
          (case [some r2]
            (have mr2 := (tbl-find-mem RunRow run-id (:run c) r2 (:runs w) hf))
            (have er2 (= (:id r2) (:run c))) (exact (tbl-find-id RunRow run-id (:run c) r2 (:runs w) hf))
            (have sq := (run-same-ep w q r2 hs mq mr2 (Eq.trans er2 erun)))
            (have e3 (= (Nat.beq (:epoch r2) (:epoch c)) true)) (rw [(And.left sq)]) (exact he)
            (simp [needs-run run-current-of-comp hf e3] at hn)))))))

(a/theorem edge-kind-kept-comp [w :- World, c :- CompRow, k :- CompRow]
  (=> (= (well-formed w) true) (List.Mem c (:comps w)) (= (:idle c) false) (List.Mem k (:comps w))
      (= (kc-c (:id c) (:epoch c) (cs10 k)) true))
  (intros hs mc hi mk)
  (cases hx (Nat.beq (:id k) (:id c)))
  (case [false] (simp only [kc-c cs10 hx Bool.not_false Bool.true_or]))
  (case [true]
    (have sk := (comp-same w c k hs mc mk (Nat.eq_of_beq_eq_true hx)))
    (have hx2 (= (Nat.beq (:id (cs10 k)) (:id c)) true)) (exact hx)
    (have b1 (= (Nat.ble (:epoch c) (:epoch (cs10 k))) true)) (simp only [Nat.ble_eq]) (have z := (And.left sk)) (simp only [cs10]) (omega)
    (have b2 (= (:idle (cs10 k)) false)) (exact (Eq.trans (And.right (And.right (And.right sk))) hi))
    (simp only [kc-c hx2 b1 b2 Bool.not_true Bool.not_false Bool.false_or Bool.and_self])))

(a/theorem edge-kind-kept-init [gxz :- (List Nat), gkz :- (List Nat), w :- World, c :- CompRow]
  (=> (= (i10-current-exempt gxz gkz w) true) (List.Mem c (:comps w)) (= (:idle c) false) (= (needs-run w c) true)
      (= (kcq gkz (:id c) (:epoch c) w) true))
  (intros h mc hi hn)
  (have hs := (i10-current-exempt-well-formed gxz gkz w h))
  (simp only [kcq])
  (exact (i10-current-transport-intro _ _ _ _ w hs
           (nqk-of-mem (kc-r gkz (:id c) (:epoch c)) (kc-c (:id c) (:epoch c)) (:runs w) (:comps w)
             (fn [q :- RunRow, k :- CompRow, mq :- (List.Mem q (:runs w)), mk :- (List.Mem k (:comps w))] (edge-kind-kept-pair gxz gkz w c q k h mc hn mq mk))
             (fn [k :- CompRow, mk :- (List.Mem k (:comps w))] (edge-kind-kept-comp w c k hs mc hi mk))))))

(a/defn ck-set-run [n :- Nat, x :- I10CurrentCompKey] I10CurrentCompKey (I10CurrentCompKey.mk (:id x) (:epoch x) (:done x) n (:idle x)))
(a/theorem edge-kind-kept-newok [cid :- Nat, n :- Nat, ep :- Nat, k :- CompRow]
  (=> (= (kc-c cid ep (cs10 k)) true) (= (newok cid n ep (ck-set-run n) (i10-current-comp-key k)) true))
  (intro h)
  (cases hx (Nat.beq (:id k) cid))
  (case [false] (simp only [newok i10-current-comp-key hx Bool.not_false Bool.true_or]))
  (case [true]
    (have hx2 (= (Nat.beq (:id (cs10 k)) cid) true)) (exact hx)
    (simp only [kc-c hx2 Bool.not_true Bool.false_or Bool.and_eq_true] at h)
    (have hx3 (= (Nat.beq (:id (i10-current-comp-key k)) cid) true)) (exact hx)
    (have e1 (= (Nat.ble ep (:epoch (ck-set-run n (i10-current-comp-key k)))) true)) (exact (And.left h))
    (have e2 (= (:idle (ck-set-run n (i10-current-comp-key k))) (:idle k))) (rfl)
    (have e3 (= (:idle (cs10 k)) (:idle k))) (rfl)
    (have e4 (= (:run (ck-set-run n (i10-current-comp-key k))) n)) (rfl)
    (have e5 (= (Nat.ble (:epoch (i10-current-comp-key k)) (:epoch (ck-set-run n (i10-current-comp-key k)))) true)) (simp only [ck-set-run i10-current-comp-key Nat.ble_eq]) (omega)
    (simp only [newok hx3 e1 e2 e4 e5 (And.right h) Nat.beq_refl Bool.not_true Bool.false_or Bool.and_self])))

(a/theorem edge-kind-kept-old [gkz :- (List Nat), cid :- Nat, n :- Nat, ep :- Nat, q :- RunRow, k :- CompRow]
  (=> (= (kc-r gkz cid ep (rs10 q) (cs10 k)) true) (= (kc-c cid ep (cs10 k)) true) (= (reach-mem (:id q) gkz) false)
      (= (old-k cid n ep (ck-set-run n) (i10-current-run-key q) (i10-current-comp-key k)) true))
  (intros hr hc hk)
  (have hn := (edge-kind-kept-newok cid n ep k hc))
  (cases hx (Nat.beq (:id k) cid))
  (case [false] (have hx2 (= (Nat.beq (:id (i10-current-comp-key k)) cid) false)) (exact hx) (simp only [old-k hn hx2 Bool.not_false Bool.true_or Bool.and_self]))
  (case [true]
    (have hx2 (= (Nat.beq (:id (cs10 k)) cid) true)) (exact hx)
    (have hx3 (= (Nat.beq (:id (i10-current-comp-key k)) cid) true)) (exact hx)
    (have hk2 (= (reach-mem (:id (rs10 q)) gkz) false)) (exact hk)
    (simp only [kc-r hx2 hk2 Bool.not_true Bool.false_or Bool.or_false] at hr)
    (simp only [kc-c hx2 Bool.not_true Bool.false_or Bool.and_eq_true Nat.ble_eq] at hc)
    (have hb (= (old-below cid (:epoch (ck-set-run n (i10-current-comp-key k))) (i10-current-run-key q)) true))
    (cases ho (Nat.beq (:of q) cid))
    (case [false] (have ho2 (= (Nat.beq (:of (i10-current-run-key q)) cid) false)) (exact ho) (simp only [old-below ho2 Bool.not_false Bool.true_or]))
    (case [true]
      (have ho2 (= (Nat.beq (:of (rs10 q)) cid) true)) (exact ho)
      (have ho3 (= (Nat.beq (:of (i10-current-run-key q)) cid) true)) (exact ho)
      (simp only [ho2 Bool.not_true Bool.false_or Nat.blt_eq] at hr)
      (have lt (= (Nat.blt (:epoch (i10-current-run-key q)) (:epoch (ck-set-run n (i10-current-comp-key k)))) true))
      (simp only [Nat.blt_eq i10-current-run-key ck-set-run i10-current-comp-key]) (have z1 := (And.left hc)) (try (simp only [rs10] at hr)) (try (simp only [cs10] at z1)) (omega)
      (simp only [old-below ho3 lt Bool.not_true Bool.false_or]))
    (simp only [old-k hn hb Bool.or_true Bool.and_self])))

(a/theorem old-row-of [gkz :- (List Nat), cid :- Nat, n :- Nat, ep :- Nat, rs :- (List RunRow), cs :- (List CompRow),
                       q :- RunRow,
                       h1 :- (= (i10-current-transport-row (kc-r gkz cid ep) (cs10s cs) (rs10 q)) true),
                       h2 :- (= (tbl-all (fn [k :- CompRow] (kc-c cid ep (cs10 k))) cs) true)]
  (= (old-row gkz cid n ep (ck-set-run n) (i10-current-comp-keys cs) (i10-current-run-key q)) true)
  (cases hk (reach-mem (:id q) gkz))
  (case [true] (have hk2 (= (reach-mem (:id (i10-current-run-key q)) gkz) true)) (exact hk) (simp only [old-row hk2 Bool.true_or]))
  (case [false]
    (have hk2 (= (reach-mem (:id (i10-current-run-key q)) gkz) false)) (exact hk)
    (simp only [old-row hk2 Bool.false_or])
    (simp only [i10-current-transport-row] at h1) (rw [all-cs10s] at h1)
    (rw [all-i10-current-comp-keys])
    (exact (tbl-all-mono2 CompRow (fn [k :- CompRow] (kc-r gkz cid ep (rs10 q) (cs10 k))) (fn [k :- CompRow] (kc-c cid ep (cs10 k)))
             (fn [k :- CompRow] (old-k cid n ep (ck-set-run n) (i10-current-run-key q) (i10-current-comp-key k)))
             (fn [k :- CompRow, a1 :- (= (kc-r gkz cid ep (rs10 q) (cs10 k)) true), a2 :- (= (kc-c cid ep (cs10 k)) true)] (edge-kind-kept-old gkz cid n ep q k a1 a2 hk))
             cs h1 h2))))

(a/theorem i10-current-exempt-new-run-of [gxz :- (List Nat), gkz :- (List Nat), w :- World, c :- CompRow, ei :- Nat]
  (=> (= (i10-current-exempt gxz gkz w) true) (= (kcq gkz (:id c) (:epoch c) w) true) (= (comp-has w (:id c)) true)
      (= (i10-current-exempt gxz gkz (new-run-of w c ei)) true))
  (intros h hq hc)
  (have hs := (i10-current-exempt-well-formed gxz gkz w h))
  (simp only [kcq] at hq)
  (have kq := (i10-current-transport-rest-of _ _ _ _ w hq))
  (simp only [i10-current-transport-rest nqk Bool.and_eq_true] at kq)
  (have kq1 := (And.left kq)) (rw [all-rs10s] at kq1)
  (have kq2 := (And.right kq)) (rw [all-cs10s] at kq2)
  (have hnew (= (tbl-all (newok (:id c) (:next-id w) (:epoch c) (ck-set-run (:next-id w))) (i10-current-comp-keys (:comps w))) true))
  (rw [all-i10-current-comp-keys])
  (exact (tbl-all-mono CompRow _ _ (fn [k :- CompRow, a :- (= (kc-c (:id c) (:epoch c) (cs10 k)) true)] (edge-kind-kept-newok (:id c) (:next-id w) (:epoch c) k a)) _ kq2))
  (have hold (= (tbl-all (old-row gkz (:id c) (:next-id w) (:epoch c) (ck-set-run (:next-id w)) (i10-current-comp-keys (:comps w))) (i10-current-run-keys (:runs w))) true))
  (rw [all-i10-current-run-keys])
  (exact (tbl-all-mono RunRow _ _ (fn [q :- RunRow, a :- (= (i10-current-transport-row (kc-r gkz (:id c) (:epoch c)) (cs10s (:comps w)) (rs10 q)) true)]
                                    (old-row-of gkz (:id c) (:next-id w) (:epoch c) (:runs w) (:comps w) q a kq2)) _ kq1))
  (have lt1 (< (:next-id w) (+ (:next-id w) 2))) (omega)
  (have lt2 (< (:id c) (+ (:next-id w) 2))) (have z := (comp-below w (:id c) hs hc)) (omega)
  (have hr := (i10-current-exempt-rest-of gxz gkz w h)) (simp only [i10-current-exempt-rest] at hr)
  (have k1 := (i10-current-exempt-keys-ok-new-run gxz gkz _ _ _ (:next-id w) (+ (:next-id w) 2) (:id c) (:epoch c) (ck-set-run (:next-id w))
                (fn [k :- I10CurrentCompKey] (Eq.refl (:id k))) hr hnew hold (runs-below w hs) lt1 lt2))
  (have e (= (i10-current-exempt-rest gxz gkz (new-run-of w c ei))
             (i10-current-exempt-keys-ok gxz gkz (List.cons I10CurrentRunKey (I10CurrentRunKey.mk (:next-id w) (:id c) (:epoch c) true) (i10-current-run-keys (:runs w)))
                   (i10-current-comp-keys (tbl-upd comp-id (:id c) (comp-set-run (:next-id w)) (:comps w))) (i10-current-task-keys (:tasks w)) (+ (:next-id w) 2))))
  (rfl)
  (rw [(i10-current-comp-keys-upd (:id c) (comp-set-run (:next-id w)) (ck-set-run (:next-id w)) (fn [k :- CompRow] (Eq.refl (i10-current-comp-key (comp-set-run (:next-id w) k)))) (:comps w))] at e)
  (have hsn := (well-formed-new-run-of w c ei hs))
  (exact (i10-current-exempt-intro gxz gkz _ hsn (Eq.trans e k1))))

(tree/restate! G10 '[well-formed-cut-suffix well-formed-consume-entry])

(a/theorem i10-current-exempt-dispatch-raw [gxz :- (List Nat), gkz :- (List Nat), w :- World, c :- CompRow]
  (=> (List.Mem c (:comps w)) (= (:idle c) false) (= (needs-run w c) true) (= (i10-current-exempt gxz gkz w) true)
      (= (i10-current-exempt gxz gkz (dispatch-raw w c)) true))
  (intros mc hi hn h)
  (have hs := (i10-current-exempt-well-formed gxz gkz w h))
  (have k0 := (edge-kind-kept-init gxz gkz w c h mc hi hn))
  (simp only [kcq] at k0)
  (have c0 := (comp-exists-intro (:id c) w hs (comp-mem-has w c mc)))
  (have h1 := (i10-current-exempt-cancel-pred gxz gkz w c mc hn h))
  (have k1 := (i10-current-transport-cancel-pred _ _ _ _ w c k0))
  (have c1 := (comp-exists-cancel-pred (:id c) w c c0))
  (cases he (entry-edge w (:id c)))
  (case [none]
    (simp only [dispatch-raw he])
    (have k2 := (i10-current-transport-cut-suffix _ _ _ _ _ (:id c) false 0 0 k1))
    (have c2 := (comp-exists-cut-suffix (:id c) _ (:id c) false 0 0 c1))
    (exact (i10-current-exempt-new-run-of gxz gkz _ c 0 (i10-current-exempt-cut-suffix gxz gkz _ (:id c) false 0 0 h1) k2 (comp-exists-rest-of (:id c) _ c2))))
  (case [some e]
    (simp only [dispatch-raw he])
    (have k2 := (i10-current-transport-consume-entry _ _ _ _ _ e (i10-current-transport-cut-suffix _ _ _ _ _ (:id c) true (:at e) (:id e) k1)))
    (have c2 := (comp-exists-consume-entry (:id c) _ e (comp-exists-cut-suffix (:id c) _ (:id c) true (:at e) (:id e) c1)))
    (exact (i10-current-exempt-new-run-of gxz gkz _ c (entry-ei e)
             (i10-current-exempt-consume-entry gxz gkz _ e (i10-current-exempt-cut-suffix gxz gkz _ (:id c) true (:at e) (:id e) h1)) k2 (comp-exists-rest-of (:id c) _ c2)))))

(a/theorem t11-dispatch-g-idle [fresh :- Nat, n :- Nat, w :- World, c :- CompRow]
  (=> (= (Bool.and (Nat.beq fresh n) (Bool.and (Bool.not (:idle c)) (Bool.and (needs-run w c) (eligible w c)))) true) (= (:idle c) false))
  (intro h) (simp only [Bool.and_eq_true] at h) (exact (bnot-true _ (And.left (And.right h)))))
(a/theorem t11-dispatch-g-nr [fresh :- Nat, n :- Nat, w :- World, c :- CompRow]
  (=> (= (Bool.and (Nat.beq fresh n) (Bool.and (Bool.not (:idle c)) (Bool.and (needs-run w c) (eligible w c)))) true) (= (needs-run w c) true))
  (intro h) (simp only [Bool.and_eq_true] at h) (exact (And.left (And.right (And.right h)))))
(tree/restate! G10 '[well-formed-t11-dispatch])

;; ---- T4: a new task n with its run n + 1 (no computation has id n)

(a/defn cid-lt [n :- Nat, k :- I10CurrentCompKey] Bool (Nat.blt (:id k) n))
(a/theorem comps-below [w :- World] (=> (= (well-formed w) true) (= (tbl-all (cid-lt (:next-id w)) (i10-current-comp-keys (:comps w))) true))
  (intro hs)
  (have hb := (ids-below-of w hs))
  (simp only [all-ids tbl-all-nat-app Bool.and_eq_true] at hb)
  (have h1 := (And.left (And.right hb)))
  (rw [all-ids-map] at h1)
  (rw [all-i10-current-comp-keys])
  (exact (tbl-all-mono CompRow _ _ (fn [c :- CompRow, q :- (= (id-in-range (:next-id w) (comp-id c)) true)] (rir (:next-id w) (:id c) q)) _ h1)))

(a/theorem lt-ne [x :- Nat, n :- Nat] (=> (= (Nat.blt x n) true) (= (Nat.beq x n) false))
  (intro h) (simp only [Nat.blt_eq] at h)
  (cases hb (Nat.beq x n)) (case [false] (rfl)) (case [true] (have e := (Nat.eq_of_beq_eq_true hb)) (omega)))

(a/theorem i10-current-run-ok-spawn-old [gxz :- (List Nat), gkz :- (List Nat), cks :- (List I10CurrentCompKey), tks :- (List I10CurrentTaskKey), n :- Nat, r :- I10CurrentRunKey]
  (=> (= (i10-current-run-ok gxz gkz cks tks n r) true) (= (id-lt n r) true)
      (= (i10-current-run-ok gxz gkz cks (List.cons I10CurrentTaskKey (I10CurrentTaskKey.mk n (+ n 1)) tks) (+ n 3) r) true))
  (intros h hi)
  (simp only [i10-current-run-ok Bool.and_eq_true Nat.blt_eq] at h)
  (simp only [id-lt] at hi)
  (have hne (= (Nat.beq (:id r) (+ n 1)) false)) (have z (= (Nat.blt (:id r) (+ n 1)) true)) (simp only [Nat.blt_eq] at hi) (simp only [Nat.blt_eq]) (omega)
  (exact (lt-ne _ _ z))
  (have ht (= (tof-pair r (I10CurrentTaskKey.mk n (+ n 1))) true)) (simp only [tof-pair hne Bool.not_false Bool.true_or Bool.or_true])
  (have hof (= (Nat.blt (:of r) (+ n 3)) true)) (simp only [Nat.blt_eq]) (have z := (And.right (And.right h))) (omega)
  (simp only [i10-current-run-ok tbl-all ht (And.left h) (And.left (And.right h)) hof Bool.and_self]))

(a/theorem i10-current-exempt-keys-ok-spawn [gxz :- (List Nat), gkz :- (List Nat), rks :- (List I10CurrentRunKey), cks :- (List I10CurrentCompKey), tks :- (List I10CurrentTaskKey), n :- Nat]
  (=> (= (i10-current-exempt-keys-ok gxz gkz rks cks tks n) true) (= (tbl-all (id-lt n) rks) true) (= (tbl-all (cid-lt n) cks) true)
      (= (i10-current-exempt-keys-ok gxz gkz (List.cons I10CurrentRunKey (I10CurrentRunKey.mk (+ n 1) n 0 true) rks) cks (List.cons I10CurrentTaskKey (I10CurrentTaskKey.mk n (+ n 1)) tks) (+ n 3)) true))
  (intros h hi hc)
  (simp only [i10-current-exempt-keys-ok Bool.and_eq_true] at h)
  (have le1 (<= (+ n 1) (+ n 3))) (omega)
  (have le0 (<= n (+ n 1))) (omega)
  (have le3 (<= n (+ n 3))) (omega)
  (have hN1 (= (tbl-all (rc-ok gxz gkz (I10CurrentRunKey.mk (+ n 1) n 0 true)) cks) true))
  (exact (tbl-all-mono2 I10CurrentCompKey (i10-current-comp-ok n) (cid-lt n) (rc-ok gxz gkz (I10CurrentRunKey.mk (+ n 1) n 0 true))
           (fn [k :- I10CurrentCompKey, a1 :- (= (i10-current-comp-ok n k) true), a2 :- (= (cid-lt n k) true)]
             (rc-new-other gxz gkz (+ n 1) n 0 k (lt-ne _ _ a2) (i10-current-comp-ok-next n (+ n 1) k le0 a1)))
           cks (And.left (And.right h)) hc))
  (have hN2a := (tbl-all-mono I10CurrentTaskKey (i10-current-task-ok n) (tof-pair (I10CurrentRunKey.mk (+ n 1) n 0 true))
                 (fn [t :- I10CurrentTaskKey, p :- (= (i10-current-task-ok n t) true)] (tof-new (+ n 1) n 0 t (i10-current-task-ok-next n (+ n 1) t le0 p))) tks (And.right (And.right h))))
  (have hN2b (= (tof-pair (I10CurrentRunKey.mk (+ n 1) n 0 true) (I10CurrentTaskKey.mk n (+ n 1))) true)) (simp only [tof-pair Nat.beq_refl Bool.or_true])
  (have hN3 (= (Nat.blt n (+ n 3)) true)) (simp only [Nat.blt_eq]) (omega)
  (have hN (= (i10-current-run-ok gxz gkz cks (List.cons I10CurrentTaskKey (I10CurrentTaskKey.mk n (+ n 1)) tks) (+ n 3) (I10CurrentRunKey.mk (+ n 1) n 0 true)) true))
  (simp only [i10-current-run-ok tbl-all hN1 hN2a hN2b hN3 Bool.and_self])
  (have hR := (tbl-all-mono2 I10CurrentRunKey (i10-current-run-ok gxz gkz cks tks n) (id-lt n) (i10-current-run-ok gxz gkz cks (List.cons I10CurrentTaskKey (I10CurrentTaskKey.mk n (+ n 1)) tks) (+ n 3))
                (fn [r :- I10CurrentRunKey, a1 :- (= (i10-current-run-ok gxz gkz cks tks n r) true), a2 :- (= (id-lt n r) true)] (i10-current-run-ok-spawn-old gxz gkz cks tks n r a1 a2))
                rks (And.left h) hi))
  (have hC := (tbl-all-mono I10CurrentCompKey (i10-current-comp-ok n) (i10-current-comp-ok (+ n 3)) (fn [k :- I10CurrentCompKey, p :- (= (i10-current-comp-ok n k) true)] (i10-current-comp-ok-next n (+ n 3) k le3 p)) cks (And.left (And.right h))))
  (have hT := (tbl-all-mono I10CurrentTaskKey (i10-current-task-ok n) (i10-current-task-ok (+ n 3)) (fn [t :- I10CurrentTaskKey, p :- (= (i10-current-task-ok n t) true)] (i10-current-task-ok-next n (+ n 3) t le3 p)) tks (And.right (And.right h))))
  (have hT1 (= (i10-current-task-ok (+ n 3) (I10CurrentTaskKey.mk n (+ n 1))) true)) (have lt1 (< (+ n 1) (+ n 3))) (omega) (simp only [i10-current-task-ok below0 Nat.blt_eq Bool.or_eq_true]) (exact (Or.inr lt1))
  (simp only [i10-current-exempt-keys-ok tbl-all hN hR hC hT hT1 Bool.and_self]))

(a/theorem i10-current-exempt-spawn-rows [gxz :- (List Nat), gkz :- (List Nat), w :- World, owner :- Nat, inputs :- (List Nat), loc :- Bool]
  (=> (= (i10-current-exempt gxz gkz w) true) (= (i10-current-exempt gxz gkz (spawn-rows w owner inputs loc)) true))
  (intro h)
  (have hs := (i10-current-exempt-well-formed gxz gkz w h))
  (have hr := (i10-current-exempt-rest-of gxz gkz w h)) (simp only [i10-current-exempt-rest] at hr)
  (have k1 := (i10-current-exempt-keys-ok-spawn gxz gkz _ _ _ _ hr (runs-below w hs) (comps-below w hs)))
  (have e (= (i10-current-exempt-rest gxz gkz (spawn-rows w owner inputs loc))
             (i10-current-exempt-keys-ok gxz gkz (List.cons I10CurrentRunKey (I10CurrentRunKey.mk (+ (:next-id w) 1) (:next-id w) 0 true) (i10-current-run-keys (:runs w))) (i10-current-comp-keys (:comps w))
                   (List.cons I10CurrentTaskKey (I10CurrentTaskKey.mk (:next-id w) (+ (:next-id w) 1)) (i10-current-task-keys (:tasks w))) (+ (:next-id w) 3))))
  (rfl)
  (exact (i10-current-exempt-intro gxz gkz _ (well-formed-spawn-rows w owner inputs loc hs) (Eq.trans e k1))))
(tree/restate! G10 '[well-formed-t4-spawn well-formed-t4-spawn-top])

;; ===========================================================================
;; Part F. T12 complete: the run is done; a current computation run sets done-epoch := epoch
;; (computation r.of exempt in between); a stale run or a task run is no current run
;; ===========================================================================

(a/theorem i10-current-run-ok-gx-cons [gxz :- (List Nat), gkz :- (List Nat), y :- Nat, cks :- (List I10CurrentCompKey), tks :- (List I10CurrentTaskKey), n :- Nat, r :- I10CurrentRunKey]
  (=> (= (i10-current-run-ok gxz gkz cks tks n r) true) (= (i10-current-run-ok (List.cons Nat y gxz) gkz cks tks n r) true))
  (intro h)
  (simp only [i10-current-run-ok Bool.and_eq_true] at h)
  (simp only [i10-current-run-ok Bool.and_eq_true (And.right h) and_true])
  (exact (tbl-all-mono I10CurrentCompKey _ _ (fn [c :- I10CurrentCompKey, q :- (= (rc-ok gxz gkz r c) true)] (rc-gx-cons gxz gkz y r c q)) cks (And.left h))))
(a/theorem idq-on [x :- Nat, Q :- (=> I10CurrentCompKey Bool), k :- I10CurrentCompKey]
  (=> (= (Nat.beq (i10-current-comp-key-id k) x) true) (= (idq x Q k) true) (= (Q k) true))
  (intros hx h) (have hx2 (= (Nat.beq (:id k) x) true)) (exact hx) (simp only [idq hx2 Bool.not_true Bool.false_or] at h) (exact h))
(a/theorem i10-current-exempt-gx-cons [gxz :- (List Nat), gkz :- (List Nat), y :- Nat, w :- World]
  (=> (= (i10-current-exempt gxz gkz w) true) (= (i10-current-exempt (List.cons Nat y gxz) gkz w) true))
  (intro h)
  (have hr := (i10-current-exempt-rest-of gxz gkz w h)) (simp only [i10-current-exempt-rest i10-current-exempt-keys-ok Bool.and_eq_true] at hr)
  (have a1 := (tbl-all-mono I10CurrentRunKey (i10-current-run-ok gxz gkz (i10-current-comp-keys (:comps w)) (i10-current-task-keys (:tasks w)) (:next-id w))
                (i10-current-run-ok (List.cons Nat y gxz) gkz (i10-current-comp-keys (:comps w)) (i10-current-task-keys (:tasks w)) (:next-id w))
                (fn [r :- I10CurrentRunKey, q :- (= (i10-current-run-ok gxz gkz (i10-current-comp-keys (:comps w)) (i10-current-task-keys (:tasks w)) (:next-id w) r) true)]
                  (i10-current-run-ok-gx-cons gxz gkz y _ _ _ r q)) _ (And.left hr)))
  (have hr2 (= (i10-current-exempt-rest (List.cons Nat y gxz) gkz w) true))
  (simp only [i10-current-exempt-rest i10-current-exempt-keys-ok a1 (And.left (And.right hr)) (And.right (And.right hr)) Bool.and_self])
  (exact (i10-current-exempt-intro _ gkz w (i10-current-exempt-well-formed gxz gkz w h) hr2)))

(a/defn ck-done [e :- Nat, k :- I10CurrentCompKey] I10CurrentCompKey (I10CurrentCompKey.mk (:id k) (:epoch k) e (:run k) (:idle k)))
(a/theorem rc-res-on [gxz :- (List Nat), gkz :- (List Nat), cid :- Nat, e :- Nat, r :- I10CurrentRunKey, k :- I10CurrentCompKey]
  (=> (= (rc-ok (List.cons Nat cid gxz) gkz r k) true) (= (Nat.beq (:epoch k) e) true) (= (rc-ok gxz gkz r (ck-done e k)) true))
  (intros h he)
  (cases hk (reach-mem (:id r) gkz))
  (case [true] (exact (rc-exempt gxz gkz r _ hk)))
  (case [false]
    (have pc := (rc-parts _ gkz r k h hk))
    (have e1 (= (rof-pair r (ck-done e k)) (rof-pair r k))) (rfl)
    (have hf (= (cur-fin gxz r (ck-done e k)) true))
    (have ee := (Nat.eq_of_beq_eq_true he))
    (have b (= (Nat.beq (:done (ck-done e k)) (:epoch (ck-done e k))) true)) (simp only [ck-done]) (rw [ee]) (exact (Nat.beq_refl _))
    (simp only [cur-fin b Bool.or_true])
    (have e2 (= (cur-core r (ck-done e k) (cur-fin gxz r (ck-done e k))) (cur-core r k (cur-fin gxz r (ck-done e k))))) (rfl)
    (have hc := (And.left pc)) (simp only [cur-pair] at hc)
    (simp only [rc-ok cur-pair e1 e2 (And.right pc) hk Bool.false_or Bool.and_true])
    (exact (core-mono r k _ _ hc (fn [q :- (= (cur-fin (List.cons Nat cid gxz) r k) true)] hf)))))
(a/theorem rc-res-off [gxz :- (List Nat), gkz :- (List Nat), cid :- Nat, r :- I10CurrentRunKey, k :- I10CurrentCompKey]
  (=> (= (rc-ok (List.cons Nat cid gxz) gkz r k) true) (= (Nat.beq (:id k) cid) false) (= (rc-ok gxz gkz r k) true))
  (intros h hx)
  (have e (= (cur-fin (List.cons Nat cid gxz) r k) (cur-fin gxz r k))) (simp only [cur-fin reach-mem-cons hx Bool.false_or])
  (simp only [rc-ok cur-pair e] at h) (simp only [rc-ok cur-pair]) (exact h))

(a/theorem i10-current-exempt-keys-ok-result [gxz :- (List Nat), gkz :- (List Nat), rks :- (List I10CurrentRunKey), cks :- (List I10CurrentCompKey), tks :- (List I10CurrentTaskKey), n :- Nat, cid :- Nat, e :- Nat]
  (=> (= (i10-current-exempt-keys-ok (List.cons Nat cid gxz) gkz rks cks tks n) true) (= (tbl-all (idq cid (fn [k :- I10CurrentCompKey] (Nat.beq (:epoch k) e))) cks) true)
      (= (i10-current-exempt-keys-ok gxz gkz rks (tbl-upd i10-current-comp-key-id cid (ck-done e) cks) tks n) true))
  (intros h hq)
  (simp only [i10-current-exempt-keys-ok Bool.and_eq_true] at h)
  (have h1 (forall [r :- I10CurrentRunKey] (=> (= (i10-current-run-ok (List.cons Nat cid gxz) gkz cks tks n r) true) (= (i10-current-run-ok gxz gkz (tbl-upd i10-current-comp-key-id cid (ck-done e) cks) tks n r) true))))
  (intros r hr)
  (simp only [i10-current-run-ok Bool.and_eq_true] at hr)
  (simp only [i10-current-run-ok Bool.and_eq_true (And.right hr) and_true])
  (exact (tbl-all-upd I10CurrentCompKey i10-current-comp-key-id cid (ck-done e) (both (rc-ok (List.cons Nat cid gxz) gkz r) (idq cid (fn [k :- I10CurrentCompKey] (Nat.beq (:epoch k) e))))
           (rc-ok gxz gkz r)
           (fn [k :- I10CurrentCompKey, p :- (= (both (rc-ok (List.cons Nat cid gxz) gkz r) (idq cid (fn [k :- I10CurrentCompKey] (Nat.beq (:epoch k) e))) k) true),
                hx :- (= (Nat.beq (i10-current-comp-key-id k) cid) true)]
             (rc-res-on gxz gkz cid e r k (both-left _ _ _ _ p) (idq-on cid _ k hx (both-right _ _ _ _ p))))
           (fn [k :- I10CurrentCompKey, p :- (= (both (rc-ok (List.cons Nat cid gxz) gkz r) (idq cid (fn [k :- I10CurrentCompKey] (Nat.beq (:epoch k) e))) k) true),
                hx :- (= (Nat.beq (i10-current-comp-key-id k) cid) false)]
             (rc-res-off gxz gkz cid r k (both-left _ _ _ _ p) hx))
           cks (tbl-all-mono2 I10CurrentCompKey _ _ _ (fn [k :- I10CurrentCompKey, a1 :- (= (rc-ok (List.cons Nat cid gxz) gkz r k) true),
                                             a2 :- (= (idq cid (fn [k :- I10CurrentCompKey] (Nat.beq (:epoch k) e)) k) true)] (both-mk _ _ _ _ a1 a2))
                 cks (And.left hr) hq)))
  (simp only [i10-current-exempt-keys-ok Bool.and_eq_true (And.right (And.right h)) and_true])
  (exact (And.intro (tbl-all-mono I10CurrentRunKey _ _ h1 rks (And.left h))
           (tbl-all-upd I10CurrentCompKey i10-current-comp-key-id cid (ck-done e) (i10-current-comp-ok n) (i10-current-comp-ok n)
             (fn [k :- I10CurrentCompKey, hp :- (= (i10-current-comp-ok n k) true), hx :- (= (Nat.beq (i10-current-comp-key-id k) cid) true)] hp)
             (fn [k :- I10CurrentCompKey, hp :- (= (i10-current-comp-ok n k) true), hx :- (= (Nat.beq (i10-current-comp-key-id k) cid) false)] hp) cks (And.left (And.right h))))))

(a/theorem i10-current-exempt-result [gxz :- (List Nat), gkz :- (List Nat), w :- World, c :- CompRow, res :- RunResult, e :- Nat]
  (=> (= (i10-current-exempt (List.cons Nat (:id c) gxz) gkz w) true) (List.Mem c (:comps w)) (= (:epoch c) e)
      (= (i10-current-exempt gxz gkz (comp-upd w (:id c) (comp-result-row res e))) true))
  (intros h mc ee)
  (have hs := (i10-current-exempt-well-formed _ gkz w h))
  (have hq (= (tbl-all (idq (:id c) (fn [k :- I10CurrentCompKey] (Nat.beq (:epoch k) e))) (i10-current-comp-keys (:comps w))) true))
  (rw [all-i10-current-comp-keys])
  (apply (all-of-mem CompRow _ (:comps w)))
  (intros k mk)
  (cases hx (Nat.beq (:id k) (:id c)))
  (case [false] (have hx2 (= (Nat.beq (:id (i10-current-comp-key k)) (:id c)) false)) (exact hx) (simp only [idq hx2 Bool.not_false Bool.true_or]))
  (case [true]
    (have hx2 (= (Nat.beq (:id (i10-current-comp-key k)) (:id c)) true)) (exact hx)
    (have sk := (comp-same w c k hs mc mk (Nat.eq_of_beq_eq_true hx)))
    (have b (= (Nat.beq (:epoch (i10-current-comp-key k)) e) true)) (simp only [i10-current-comp-key]) (rw [(And.left sk) ee]) (exact (Nat.beq_refl _))
    (simp only [idq hx2 b Bool.not_true Bool.false_or]))
  (have hr := (i10-current-exempt-rest-of _ gkz w h)) (simp only [i10-current-exempt-rest] at hr)
  (have hrest (= (i10-current-exempt-rest gxz gkz (comp-upd w (:id c) (comp-result-row res e))) true))
  (simp only [i10-current-exempt-rest comp-upd set-comps (i10-current-comp-keys-upd (:id c) (comp-result-row res e) (ck-done e) (fn [k :- CompRow] (Eq.refl (i10-current-comp-key (comp-result-row res e k)))) (:comps w))])
  (exact (i10-current-exempt-keys-ok-result gxz gkz _ _ _ _ (:id c) e hr hq))
  (exact (i10-current-exempt-intro gxz gkz _ (well-formed-comp-upd w (:id c) (comp-result-row res e) (comp-result-row-id res e) (comp-result-row-pending res e) hs) hrest)))

(a/theorem dn2-row [gxz :- (List Nat), gkz :- (List Nat), x :- Nat, w :- World, q :- RunRow,
                    hp :- (forall [k :- CompRow] (=> (List.Mem k (:comps w)) (= (Nat.beq (:id q) x) true) (= (reach-mem (:id q) gkz) false)
                                                    (= (nc-c gxz (i10-current-run-key q) (i10-current-comp-key k)) true)))]
  (= (dn2-ok gxz gkz x (i10-current-comp-keys (:comps w)) (i10-current-run-key q)) true)
  (cases hx (Nat.beq (:id q) x))
  (case [false] (simp only [dn2-ok dn-ok i10-current-run-key hx Bool.not_false Bool.true_or Bool.or_true]))
  (case [true]
    (cases hk (reach-mem (:id q) gkz))
    (case [true] (simp only [dn2-ok i10-current-run-key hk Bool.true_or]))
    (case [false]
      (have hx3 (= (Nat.beq (:id (i10-current-run-key q)) x) true)) (exact hx)
      (have hk3 (= (reach-mem (:id (i10-current-run-key q)) gkz) false)) (exact hk)
      (simp only [dn2-ok dn-ok hx3 hk3 Bool.not_true Bool.false_or])
      (rw [all-i10-current-comp-keys])
      (exact (all-of-mem CompRow _ (:comps w) (fn [k :- CompRow, mk :- (List.Mem k (:comps w))] (hp k mk hx hk)))))))

(a/theorem kill-cur [gxz :- (List Nat), gkz :- (List Nat), w :- World, r :- RunRow]
  (=> (= (well-formed w) true) (List.Mem r (:runs w))
      (= (tbl-all (dn2-ok (List.cons Nat (:of r) gxz) gkz (:id r) (i10-current-comp-keys (:comps w))) (i10-current-run-keys (:runs w))) true))
  (intros hs mr)
  (rw [all-i10-current-run-keys])
  (apply (all-of-mem RunRow _ (:runs w)))
  (intros q mq)
  (apply (dn2-row _ gkz (:id r) w q))
  (intros k mk hx hk)
  (have sq := (run-same-ep w r q hs mr mq (Nat.eq_of_beq_eq_true hx)))
  (cases ho (Nat.beq (:of q) (:id k)))
  (case [false] (have ho2 (= (Nat.beq (:of (i10-current-run-key q)) (:id (i10-current-comp-key k))) false)) (exact ho) (simp only [nc-c ho2 Bool.not_false Bool.true_or Bool.or_true]))
  (case [true]
    (have e := (Nat.eq_of_beq_eq_true ho))
    (have b (= (reach-mem (:id (i10-current-comp-key k)) (List.cons Nat (:of r) gxz)) true))
    (simp only [i10-current-comp-key reach-mem-cons Bool.or_eq_true]) (rw [← e (And.right sq)]) (exact (Or.inl (Nat.beq_refl _)))
    (simp only [nc-c b Bool.true_or])))

(a/theorem kill-stale [gxz :- (List Nat), gkz :- (List Nat), w :- World, r :- RunRow, c :- CompRow]
  (=> (= (well-formed w) true) (List.Mem r (:runs w)) (= (comp-find w (:of r)) (Option.some CompRow c)) (= (Nat.beq (:epoch r) (:epoch c)) false)
      (= (tbl-all (dn2-ok gxz gkz (:id r) (i10-current-comp-keys (:comps w))) (i10-current-run-keys (:runs w))) true))
  (intros hs mr hf he)
  (have mc := (tbl-find-mem CompRow comp-id (:of r) c (:comps w) hf))
  (have ec (= (:id c) (:of r))) (exact (tbl-find-id CompRow comp-id (:of r) c (:comps w) hf))
  (rw [all-i10-current-run-keys])
  (apply (all-of-mem RunRow _ (:runs w)))
  (intros q mq)
  (apply (dn2-row gxz gkz (:id r) w q))
  (intros k mk hx hk)
  (have sq := (run-same-ep w r q hs mr mq (Nat.eq_of_beq_eq_true hx)))
  (cases ho (Nat.beq (:of q) (:id k)))
  (case [false] (have ho2 (= (Nat.beq (:of (i10-current-run-key q)) (:id (i10-current-comp-key k))) false)) (exact ho) (simp only [nc-c ho2 Bool.not_false Bool.true_or Bool.or_true]))
  (case [true]
    (have e := (Nat.eq_of_beq_eq_true ho))
    (have sk := (comp-same w c k hs mc mk (Eq.trans (Eq.symm e) (Eq.trans (And.right sq) (Eq.symm ec)))))
    (have b (= (Nat.beq (:epoch (i10-current-run-key q)) (:epoch (i10-current-comp-key k))) false))
    (simp only [i10-current-run-key i10-current-comp-key]) (rw [(And.left sq) (And.left sk)]) (exact he)
    (simp only [nc-c b Bool.not_false Bool.or_true])))

(a/theorem kill-none [gxz :- (List Nat), gkz :- (List Nat), w :- World, r :- RunRow]
  (=> (= (well-formed w) true) (List.Mem r (:runs w)) (= (comp-find w (:of r)) (Option.none CompRow))
      (= (tbl-all (dn2-ok gxz gkz (:id r) (i10-current-comp-keys (:comps w))) (i10-current-run-keys (:runs w))) true))
  (intros hs mr hf)
  (have hn := (tbl-find-none-has CompRow comp-id (:of r) (:comps w) hf))
  (rw [all-i10-current-run-keys])
  (apply (all-of-mem RunRow _ (:runs w)))
  (intros q mq)
  (apply (dn2-row gxz gkz (:id r) w q))
  (intros k mk hx hk)
  (have sq := (run-same-ep w r q hs mr mq (Nat.eq_of_beq_eq_true hx)))
  (cases ho (Nat.beq (:of q) (:id k)))
  (case [false] (have ho2 (= (Nat.beq (:of (i10-current-run-key q)) (:id (i10-current-comp-key k))) false)) (exact ho) (simp only [nc-c ho2 Bool.not_false Bool.true_or Bool.or_true]))
  (case [true]
    (have e := (Nat.eq_of_beq_eq_true ho))
    (have hm := (comp-mem-has w k mk))
    (have z (= (tbl-has comp-id (:of r) (:comps w)) true)) (rw [← (And.right sq) e]) (exact hm)
    (rw [z] at hn) (cases hn)))

(a/theorem task-runs-ncw2 [gxz :- (List Nat), gy :- (List Nat), gkz :- (List Nat), w :- World, xs :- (List Nat)]
  (=> (= (i10-current-exempt gy gkz w) true) (= (tbl-all (fn [x :- Nat] (ncw gxz gkz x w)) (task-runs w xs)) true))
  (intro h)
  (induction xs)
  (case [nil] (simp only [task-runs tbl-all]))
  (case [cons hd t ih]
    (simp only [task-runs tbl-all ih Bool.and_true])
    (exact (task-run-ncw gxz gkz _ w (i10-current-exempt-well-formed gy gkz w h) (task-run-tasks gy gkz w hd h)))))

(a/theorem jl-tr [gxz :- (List Nat), gkz :- (List Nat), w :- World, w2 :- World,
                  hf :- (forall [x :- Nat] (=> (= (ncw gxz gkz x w) true) (= (ncw gxz gkz x w2) true))), js :- (List Job)]
  (=> (= (tbl-all (job-ok gxz gkz w) js) true) (= (tbl-all (job-ok gxz gkz w2) js) true))
  (intro h)
  (apply (tbl-all-mono Job _ _ _ js h))
  (intros j q)
  (cases j)
  (case [jcancel x rep] (simp only [job-ok] at q) (simp only [job-ok]) (exact (hf x q)))
  (case [jretire x] (simp only [job-ok]))
  (case [jclose s] (simp only [job-ok])))

(tree/restate! NQ '[well-formed-complete-body well-formed-retire-after])
(tree/restate! G10 '[well-formed-settle well-formed-cancel-res well-formed-fire-edge well-formed-nat-fold well-formed-retire-after well-formed-finalize-if-final])

(a/theorem rest-tr [gxz :- (List Nat), gkz :- (List Nat), w0 :- World, r :- RunRow, res :- RunResult, xs :- (List Nat)]
  (=> (= (well-formed w0) true) (= (tbl-all (fn [x :- Nat] (ncw gxz gkz x w0)) xs) true)
      (= (tbl-all (job-ok gxz gkz (retire-after (:world (complete-body w0 r res)) (:id r))) (cancel-jobs xs)) true))
  (intros hs h)
  (rw [jl-cancel-jobs])
  (exact (tbl-all-mono Nat (fn [x :- Nat] (ncw gxz gkz x w0)) (fn [x :- Nat] (ncw gxz gkz x (retire-after (:world (complete-body w0 r res)) (:id r))))
           (fn [x :- Nat, q :- (= (ncw gxz gkz x w0) true)]
             (ncw-of-i10-current-transport gxz gkz x _ (i10-current-transport-retire-after (nc-run gxz gkz x) tt-c (nc-run-m gxz gkz x) tt-m _ (:id r)
               (i10-current-transport-complete-body (nc-run gxz gkz x) tt-c (nc-run-m gxz gkz x) tt-m w0 r res (ncw-i10-current-transport gxz gkz x w0 hs q)))))
           xs h)))

(a/theorem complete-tail [gxz :- (List Nat), gkz :- (List Nat), cs :- Casc, rid :- Nat, d :- Nat]
  (=> (= (i10-current-exempt gxz gkz (:world cs)) true) (= (tbl-all (job-ok gxz gkz (retire-after (:world cs) rid)) (:rest cs)) true)
      (= (i10-current-exempt gxz gkz (finalize-if-final (run-cascade (retire-after (:world cs) rid)
                                                 (List.append Job (:rest cs) (List.cons Job (Job.jretire rid) (List.nil Job)))) d)) true))
  (intros h hj)
  (have hj2 (= (tbl-all (job-ok gxz gkz (retire-after (:world cs) rid)) (List.append Job (:rest cs) (List.cons Job (Job.jretire rid) (List.nil Job)))) true))
  (simp only [all-append hj tbl-all job-ok Bool.and_self])
  (exact (i10-current-exempt-finalize-if-final gxz gkz _ d (i10-current-exempt-run-cascade gxz gkz _ _ hj2 (i10-current-exempt-retire-after gxz gkz _ rid h)))))

;; the four cases of complete-body (the world after the run is made done)
(a/theorem cmp-none-none [gxz :- (List Nat), gkz :- (List Nat), w :- World, r :- RunRow, res :- RunResult]
  (=> (List.Mem r (:runs w)) (= (i10-current-exempt gxz gkz w) true) (= (comp-find w (:of r)) (Option.none CompRow))
      (= (task-find w (:of r)) (Option.none TaskRow)) (= (i10-current-exempt gxz gkz (finalize-if-final (run-cascade (retire-after (:world (complete-body (run-upd w (:id r) run-complete-row) r res)) (:id r)) (List.append Job (:rest (complete-body (run-upd w (:id r) run-complete-row) r res)) (List.cons Job (Job.jretire (:id r)) (List.nil Job)))) (:of r))) true))
  (intros mr h hc hk)
  (have hs := (i10-current-exempt-well-formed gxz gkz w h))
  (have h0 := (i10-current-exempt-kill gxz gkz w (:id r) run-complete-row run-complete-row-id run-complete-i10-current-run-key (kill-none gxz gkz w r hs mr hc) h))
  (have ef (= (comp-find (run-upd w (:id r) run-complete-row) (:of r)) (comp-find w (:of r)))) (rfl)
  (have et (= (task-find (run-upd w (:id r) run-complete-row) (:of r)) (task-find w (:of r)))) (rfl)
  (have eb (= (complete-body (run-upd w (:id r) run-complete-row) r res) (Casc.mk (run-upd w (:id r) run-complete-row) (List.nil Job))))
  (simp only [complete-body ef hc et hk])
  (simp only [eb])
  (have hj (= (tbl-all (job-ok gxz gkz (retire-after (:world (Casc.mk (run-upd w (:id r) run-complete-row) (List.nil Job))) (:id r))) (:rest (Casc.mk (run-upd w (:id r) run-complete-row) (List.nil Job)))) true))
  (simp only [tbl-all])
  (exact (complete-tail gxz gkz (Casc.mk (run-upd w (:id r) run-complete-row) (List.nil Job)) (:id r) (:of r) h0 hj)))

(a/theorem cmp-none-task [gxz :- (List Nat), gkz :- (List Nat), w :- World, r :- RunRow, res :- RunResult]
  (=> (List.Mem r (:runs w)) (= (i10-current-exempt gxz gkz w) true) (= (comp-find w (:of r)) (Option.none CompRow)) (= (i10-current-exempt gxz gkz (finalize-if-final (run-cascade (retire-after (:world (complete-body (run-upd w (:id r) run-complete-row) r res)) (:id r)) (List.append Job (:rest (complete-body (run-upd w (:id r) run-complete-row) r res)) (List.cons Job (Job.jretire (:id r)) (List.nil Job)))) (:of r))) true))
  (intros mr h hc)
  (have hs := (i10-current-exempt-well-formed gxz gkz w h))
  (have h0 := (i10-current-exempt-kill gxz gkz w (:id r) run-complete-row run-complete-row-id run-complete-i10-current-run-key (kill-none gxz gkz w r hs mr hc) h))
  (have hs0 := (i10-current-exempt-well-formed gxz gkz _ h0))
  (have ef (= (comp-find (run-upd w (:id r) run-complete-row) (:of r)) (comp-find w (:of r)))) (rfl)
  (have et (= (task-find (run-upd w (:id r) run-complete-row) (:of r)) (task-find w (:of r)))) (rfl)
  (cases hk (task-find w (:of r)))
  (case [none] (exact (cmp-none-none gxz gkz w r res mr h hc hk)))
  (case [some k]
    (have eb (= (complete-body (run-upd w (:id r) run-complete-row) r res) (complete-task (run-upd w (:id r) run-complete-row) r (:id k) res)))
    (simp only [complete-body ef hc et hk])
    (have hw (= (i10-current-exempt gxz gkz (:world (complete-body (run-upd w (:id r) run-complete-row) r res))) true))
    (simp only [eb complete-task])
    (exact (i10-current-exempt-nat-fold gxz gkz (fire-edge res) (i10-current-exempt-fire-edge gxz gkz res) _ _
             (i10-current-exempt-cancel-res gxz gkz _ r (i10-current-exempt-task-upd gxz gkz _ (:id k) (task-result-row res) (task-result-row-id res)
                                            (fn [t :- TaskRow] (Eq.refl (i10-current-task-key t))) h0))))
    (have er (= (:rest (complete-body (run-upd w (:id r) run-complete-row) r res)) (cancel-jobs (owned-runs (run-upd w (:id r) run-complete-row) (scope-subtree (run-upd w (:id r) run-complete-row) (:scope r))))))
    (simp only [eb complete-task])
    (have hj := (rest-tr gxz gkz (run-upd w (:id r) run-complete-row) r res _ hs0 (owned-ncw gxz gkz (run-upd w (:id r) run-complete-row) (scope-subtree (run-upd w (:id r) run-complete-row) (:scope r)) hs0)))
    (have hj2 (= (tbl-all (job-ok gxz gkz (retire-after (:world (complete-body (run-upd w (:id r) run-complete-row) r res)) (:id r)))
                          (:rest (complete-body (run-upd w (:id r) run-complete-row) r res))) true))
    (simp only [er]) (exact hj)
    (exact (complete-tail gxz gkz (complete-body (run-upd w (:id r) run-complete-row) r res) (:id r) (:of r) hw hj2))))

(a/theorem cmp-stale [gxz :- (List Nat), gkz :- (List Nat), w :- World, r :- RunRow, res :- RunResult, c :- CompRow]
  (=> (List.Mem r (:runs w)) (= (i10-current-exempt gxz gkz w) true) (= (comp-find w (:of r)) (Option.some CompRow c)) (= (Nat.beq (:epoch r) (:epoch c)) false) (= (i10-current-exempt gxz gkz (finalize-if-final (run-cascade (retire-after (:world (complete-body (run-upd w (:id r) run-complete-row) r res)) (:id r)) (List.append Job (:rest (complete-body (run-upd w (:id r) run-complete-row) r res)) (List.cons Job (Job.jretire (:id r)) (List.nil Job)))) (:of r))) true))
  (intros mr h hc he)
  (have hs := (i10-current-exempt-well-formed gxz gkz w h))
  (have h0 := (i10-current-exempt-kill gxz gkz w (:id r) run-complete-row run-complete-row-id run-complete-i10-current-run-key (kill-stale gxz gkz w r c hs mr hc he) h))
  (have ef (= (comp-find (run-upd w (:id r) run-complete-row) (:of r)) (comp-find w (:of r)))) (rfl)
  (have eb (= (complete-body (run-upd w (:id r) run-complete-row) r res) (Casc.mk (run-upd w (:id r) run-complete-row) (List.nil Job))))
  (simp only [complete-body ef hc he])
  (simp only [eb])
  (have hj (= (tbl-all (job-ok gxz gkz (retire-after (:world (Casc.mk (run-upd w (:id r) run-complete-row) (List.nil Job))) (:id r))) (:rest (Casc.mk (run-upd w (:id r) run-complete-row) (List.nil Job)))) true))
  (simp only [tbl-all])
  (exact (complete-tail gxz gkz (Casc.mk (run-upd w (:id r) run-complete-row) (List.nil Job)) (:id r) (:of r) h0 hj)))

(a/theorem cmp-cur [gxz :- (List Nat), gkz :- (List Nat), w :- World, r :- RunRow, res :- RunResult, c :- CompRow]
  (=> (List.Mem r (:runs w)) (= (i10-current-exempt gxz gkz w) true) (= (comp-find w (:of r)) (Option.some CompRow c)) (= (Nat.beq (:epoch r) (:epoch c)) true) (= (i10-current-exempt gxz gkz (finalize-if-final (run-cascade (retire-after (:world (complete-body (run-upd w (:id r) run-complete-row) r res)) (:id r)) (List.append Job (:rest (complete-body (run-upd w (:id r) run-complete-row) r res)) (List.cons Job (Job.jretire (:id r)) (List.nil Job)))) (:of r))) true))
  (intros mr h hc he)
  (have hs := (i10-current-exempt-well-formed gxz gkz w h))
  (have mc := (tbl-find-mem CompRow comp-id (:of r) c (:comps w) hc))
  (have ec (= (:id c) (:of r))) (exact (tbl-find-id CompRow comp-id (:of r) c (:comps w) hc))
  (have h0 := (i10-current-exempt-kill (List.cons Nat (:of r) gxz) gkz w (:id r) run-complete-row run-complete-row-id run-complete-i10-current-run-key
                (kill-cur gxz gkz w r hs mr) (i10-current-exempt-gx-cons gxz gkz (:of r) w h)))
  (have hs0 := (i10-current-exempt-well-formed _ gkz _ h0))
  (have h0c (= (i10-current-exempt (List.cons Nat (:id c) gxz) gkz (run-upd w (:id r) run-complete-row)) true)) (rw [ec]) (exact h0)
  (have ee (= (:epoch c) (:epoch r))) (exact (Eq.symm (Nat.eq_of_beq_eq_true he)))
  (have mc0 (List.Mem c (:comps (run-upd w (:id r) run-complete-row)))) (exact mc)
  (have ef (= (comp-find (run-upd w (:id r) run-complete-row) (:of r)) (comp-find w (:of r)))) (rfl)
  (have eb (= (complete-body (run-upd w (:id r) run-complete-row) r res) (complete-comp (run-upd w (:id r) run-complete-row) r c res)))
  (simp only [complete-body ef hc he])
  (have hw (= (i10-current-exempt gxz gkz (:world (complete-body (run-upd w (:id r) run-complete-row) r res))) true))
  (simp only [eb complete-comp])
  (exact (i10-current-exempt-settle gxz gkz _ (:id c) _ (i10-current-exempt-cancel-res gxz gkz _ r (i10-current-exempt-result gxz gkz (run-upd w (:id r) run-complete-row) c res (:epoch r) h0c mc0 ee))))
  (have er (= (:rest (complete-body (run-upd w (:id r) run-complete-row) r res)) (cancel-jobs (released-runs (run-upd w (:id r) run-complete-row) c))))
  (simp only [eb complete-comp])
  (have hj := (rest-tr gxz gkz (run-upd w (:id r) run-complete-row) r res (task-runs (run-upd w (:id r) run-complete-row) (tbl-filter (released-run (run-upd w (:id r) run-complete-row) (created-ids (:basis c))) (created-ids (:adopt-basis c)))) hs0 (task-runs-ncw2 gxz (List.cons Nat (:of r) gxz) gkz (run-upd w (:id r) run-complete-row) (tbl-filter (released-run (run-upd w (:id r) run-complete-row) (created-ids (:basis c))) (created-ids (:adopt-basis c))) h0)))
  (have hj2 (= (tbl-all (job-ok gxz gkz (retire-after (:world (complete-body (run-upd w (:id r) run-complete-row) r res)) (:id r))) (cancel-jobs (released-runs (run-upd w (:id r) run-complete-row) c))) true))
  (simp only [released-runs]) (exact hj)
  (have hj3 (= (tbl-all (job-ok gxz gkz (retire-after (:world (complete-body (run-upd w (:id r) run-complete-row) r res)) (:id r)))
                        (:rest (complete-body (run-upd w (:id r) run-complete-row) r res))) true))
  (simp only [er]) (exact hj2)
  (exact (complete-tail gxz gkz (complete-body (run-upd w (:id r) run-complete-row) r res) (:id r) (:of r) hw hj3)))

(a/theorem i10-current-exempt-complete-raw [gxz :- (List Nat), gkz :- (List Nat), w :- World, r :- RunRow, res :- RunResult]
  (=> (List.Mem r (:runs w)) (= (i10-current-exempt gxz gkz w) true) (= (i10-current-exempt gxz gkz (complete-raw w r res)) true))
  (intros mr h)
  (simp only [complete-raw])
  (cases hc (comp-find w (:of r)))
  (case [none] (exact (cmp-none-task gxz gkz w r res mr h hc)))
  (case [some c]
    (cases he (Nat.beq (:epoch r) (:epoch c)))
    (case [false] (exact (cmp-stale gxz gkz w r res c mr h hc he)))
    (case [true] (exact (cmp-cur gxz gkz w r res c mr h hc he)))))

(tree/restate! G10 '[well-formed-t12-complete])

;; ===========================================================================
;; Part G. T5 start (outside a normalization round: nothing exempt): the computation has no
;; current run (a current run is alive or C has its result; T5 needs `fresh` and no run in
;; progress, or no run at all)
;; ===========================================================================

(a/theorem run-same-alive [w :- World, r :- RunRow, q :- RunRow]
  (=> (= (well-formed w) true) (List.Mem r (:runs w)) (List.Mem q (:runs w)) (= (:id q) (:id r)) (= (run-alive q) (run-alive r)))
  (intros hs mr mq e)
  (have u := (uniq-all RunRow run-id (fn [x :- RunRow] (bool-eq (run-alive x) (run-alive r))) r (:runs w) (lit-runs-nodup w hs) mr (bool-eq-refl _)))
  (have v := (tbl-all-mem RunRow _ q _ u mq))
  (have e2 (= (Nat.beq (run-id q) (run-id r)) true)) (have e3 (= (run-id q) (run-id r))) (exact e) (rw [e3]) (exact (Nat.beq_refl _))
  (simp only [same-id-then e2 Bool.not_true Bool.false_or] at v)
  (exact (bool-eq-eq _ _ v)))

(a/theorem i10-current-exempt-i10-current-comp-ok [gxz :- (List Nat), gkz :- (List Nat), w :- World, c :- CompRow]
  (=> (= (i10-current-exempt gxz gkz w) true) (List.Mem c (:comps w)) (= (i10-current-comp-ok (:next-id w) (i10-current-comp-key c)) true))
  (intros h mc)
  (have hr := (i10-current-exempt-rest-of gxz gkz w h))
  (simp only [i10-current-exempt-rest i10-current-exempt-keys-ok Bool.and_eq_true] at hr)
  (have a1 := (And.left (And.right hr))) (rw [all-i10-current-comp-keys] at a1)
  (exact (tbl-all-mem CompRow _ c _ a1 mc)))

(a/theorem start-cur [w :- World, c :- CompRow, q :- RunRow]
  (=> (= (i10-current-exempt (List.nil Nat) (List.nil Nat) w) true) (List.Mem c (:comps w)) (= (startable w c) true) (List.Mem q (:runs w))
      (= (Nat.beq (:of q) (:id c)) true) (= (Nat.beq (:epoch q) (:epoch c)) true) False)
  (intros h mc hst mq ho he)
  (have hs := (i10-current-exempt-well-formed _ _ w h))
  (have hk0 (= (reach-mem (:id (i10-current-run-key q)) (List.nil Nat)) false)) (rfl)
  (have pc := (rc-parts _ _ (i10-current-run-key q) (i10-current-comp-key c) (i10-current-exempt-rc _ _ w q c h mq mc) hk0))
  (have ce := (cur-eq _ (i10-current-run-key q) (i10-current-comp-key c) (And.left pc) ho he))
  (have erun (= (:run c) (:id q))) (exact (And.left ce))
  (have hidle (= (:idle c) false)) (exact (And.left (And.right ce)))
  (have hfin := (And.right (And.right ce)))
  (have hz := (run-id-pos w q hs mq))
  (have hrun0 (= (Nat.beq (:run c) 0) false)) (rw [erun]) (exact hz)
  (have hc10 := (i10-current-exempt-i10-current-comp-ok _ _ w c h mc))
  (simp only [i10-current-comp-ok Bool.and_eq_true Nat.ble_eq] at hc10)
  (cases hd (Nat.beq (:done-epoch c) 0))
  (case [false] (simp [startable hidle hd hrun0] at hst))
  (case [true]
    (have hd2 := (Nat.eq_of_beq_eq_true hd))
    (have hde (= (Nat.beq (:done (i10-current-comp-key c)) (:epoch (i10-current-comp-key c))) false))
    (cases hb (Nat.beq (:done (i10-current-comp-key c)) (:epoch (i10-current-comp-key c)))) (rfl)
    (have z := (Nat.eq_of_beq_eq_true hb)) (simp only [i10-current-comp-key] at z) (rw [hd2] at z) (have z2 := (And.left hc10)) (omega)
    (have ha (= (run-alive q) true))
    (simp only [cur-fin hde Bool.or_false Bool.false_or i10-current-run-key] at hfin) (exact hfin)
    (cases hf (run-find w (:run c)))
    (case [none]
      (have z := (tbl-find-none-has RunRow run-id (:run c) (:runs w) hf))
      (have z2 (= (tbl-has run-id (:run c) (:runs w)) true)) (rw [erun])
      (have hm := (mem-ids-has RunRow run-id q (:runs w) mq)) (rw [nat-mem-ids] at hm) (exact hm)
      (rw [z2] at z) (cases z))
    (case [some r2]
      (have mr2 := (tbl-find-mem RunRow run-id (:run c) r2 (:runs w) hf))
      (have er2 (= (:id r2) (:run c))) (exact (tbl-find-id RunRow run-id (:run c) r2 (:runs w) hf))
      (have sa := (run-same-alive w q r2 hs mq mr2 (Eq.trans er2 erun)))
      (have hbusy (= (run-busy w c) true)) (simp only [run-busy hf]) (rw [sa]) (exact ha)
      (simp [startable hidle hd hrun0 hbusy] at hst))))

(a/defn ck-start [n :- Nat, k :- I10CurrentCompKey] I10CurrentCompKey
  (I10CurrentCompKey.mk (:id k) (if (Bool.and (:idle k) (Bool.not (Nat.beq (:done k) 0))) (+ (:epoch k) 1) (:epoch k)) (:done k) n false))

(a/theorem ck-start-ep [n :- Nat, w :- World, c :- CompRow, k :- CompRow]
  (=> (= (well-formed w) true) (List.Mem c (:comps w)) (List.Mem k (:comps w)) (= (:id k) (:id c))
      (= (:epoch (ck-start n (i10-current-comp-key k))) (start-epoch c)))
  (intros hs mc mk e)
  (have sk := (comp-same w c k hs mc mk e))
  (simp only [ck-start i10-current-comp-key start-epoch])
  (rw [(And.left sk) (And.left (And.right sk)) (And.right (And.right (And.right sk)))]))

(a/theorem ck-start-ge [n :- Nat, k :- I10CurrentCompKey] (<= (:epoch k) (:epoch (ck-start n k)))
  (simp only [ck-start])
  (cases hb (Bool.and (:idle k) (Bool.not (Nat.beq (:done k) 0))))
  (case [false] (simp only [hb]) (omega))
  (case [true] (simp only [hb]) (omega)))

(a/theorem start-newok [n :- Nat, w :- World, c :- CompRow, k :- CompRow]
  (=> (= (well-formed w) true) (List.Mem c (:comps w)) (List.Mem k (:comps w))
      (= (newok (:id c) n (start-epoch c) (ck-start n) (i10-current-comp-key k)) true))
  (intros hs mc mk)
  (cases hx (Nat.beq (:id k) (:id c)))
  (case [false] (have hx2 (= (Nat.beq (:id (i10-current-comp-key k)) (:id c)) false)) (exact hx) (simp only [newok hx2 Bool.not_false Bool.true_or]))
  (case [true]
    (have hx2 (= (Nat.beq (:id (i10-current-comp-key k)) (:id c)) true)) (exact hx)
    (have ee := (ck-start-ep n w c k hs mc mk (Nat.eq_of_beq_eq_true hx)))
    (have b1 (= (Nat.ble (start-epoch c) (:epoch (ck-start n (i10-current-comp-key k)))) true)) (rw [ee]) (simp only [Nat.ble_eq]) (omega)
    (have b2 (= (Nat.ble (:epoch (i10-current-comp-key k)) (:epoch (ck-start n (i10-current-comp-key k)))) true)) (simp only [Nat.ble_eq]) (exact (ck-start-ge n (i10-current-comp-key k)))
    (have b3 (= (:run (ck-start n (i10-current-comp-key k))) n)) (rfl)
    (have b4 (= (:idle (ck-start n (i10-current-comp-key k))) false)) (rfl)
    (simp only [newok hx2 b1 b2 b3 b4 Nat.beq_refl Bool.not_true Bool.not_false Bool.false_or Bool.and_self])))

(a/theorem start-old [n :- Nat, w :- World, c :- CompRow, q :- RunRow, k :- CompRow]
  (=> (= (i10-current-exempt (List.nil Nat) (List.nil Nat) w) true) (List.Mem c (:comps w)) (= (startable w c) true) (List.Mem q (:runs w)) (List.Mem k (:comps w))
      (= (old-k (:id c) n (start-epoch c) (ck-start n) (i10-current-run-key q) (i10-current-comp-key k)) true))
  (intros h mc hst mq mk)
  (have hs := (i10-current-exempt-well-formed _ _ w h))
  (have hn := (start-newok n w c k hs mc mk))
  (cases hx (Nat.beq (:id k) (:id c)))
  (case [false] (have hx2 (= (Nat.beq (:id (i10-current-comp-key k)) (:id c)) false)) (exact hx) (simp only [old-k hn hx2 Bool.not_false Bool.true_or Bool.and_self]))
  (case [true]
    (have hx2 (= (Nat.beq (:id (i10-current-comp-key k)) (:id c)) true)) (exact hx)
    (have ee := (ck-start-ep n w c k hs mc mk (Nat.eq_of_beq_eq_true hx)))
    (have hb (= (old-below (:id c) (:epoch (ck-start n (i10-current-comp-key k))) (i10-current-run-key q)) true))
    (cases ho (Nat.beq (:of q) (:id c)))
    (case [false] (have ho2 (= (Nat.beq (:of (i10-current-run-key q)) (:id c)) false)) (exact ho) (simp only [old-below ho2 Bool.not_false Bool.true_or]))
    (case [true]
      (have ho2 (= (Nat.beq (:of (i10-current-run-key q)) (:id c)) true)) (exact ho)
      (have hk0 (= (reach-mem (:id (i10-current-run-key q)) (List.nil Nat)) false)) (rfl)
      (have pc := (rc-parts _ _ (i10-current-run-key q) (i10-current-comp-key c) (i10-current-exempt-rc _ _ w q c h mq mc) hk0))
      (have le := (cur-le _ (i10-current-run-key q) (i10-current-comp-key c) (And.left pc) ho2))
      (have ne (Not (= (:epoch q) (:epoch c))))
      (intro z) (have z2 (= (Nat.beq (:epoch q) (:epoch c)) true)) (rw [z]) (exact (Nat.beq_refl _)) (exact (start-cur w c q h mc hst mq ho z2))
      (have ge := (ck-start-ge n (i10-current-comp-key c)))
      (have lt (= (Nat.blt (:epoch (i10-current-run-key q)) (:epoch (ck-start n (i10-current-comp-key k)))) true))
      (rw [ee]) (simp only [Nat.blt_eq i10-current-run-key]) (simp only [start-epoch])
      (cases hb2 (Bool.and (:idle c) (Bool.not (Nat.beq (:done-epoch c) 0))))
      (case [false] (simp only [hb2]) (simp only [i10-current-comp-key] at le) (omega))
      (case [true] (simp only [hb2]) (simp only [i10-current-comp-key] at le) (omega))
      (simp only [old-below ho2 lt Bool.not_true Bool.false_or]))
    (simp only [old-k hn hb Bool.or_true Bool.and_self])))

(a/theorem i10-current-start-raw [w :- World, c :- CompRow]
  (=> (List.Mem c (:comps w)) (= (startable w c) true) (= (i10-current-exempt (List.nil Nat) (List.nil Nat) w) true)
      (= (i10-current-exempt (List.nil Nat) (List.nil Nat) (start-raw w c)) true))
  (intros mc hst h)
  (have hs := (i10-current-exempt-well-formed _ _ w h))
  (have hnew (= (tbl-all (newok (:id c) (:next-id w) (start-epoch c) (ck-start (:next-id w))) (i10-current-comp-keys (:comps w))) true))
  (rw [all-i10-current-comp-keys])
  (exact (all-of-mem CompRow _ (:comps w) (fn [k :- CompRow, mk :- (List.Mem k (:comps w))] (start-newok (:next-id w) w c k hs mc mk))))
  (have hold (= (tbl-all (old-row (List.nil Nat) (:id c) (:next-id w) (start-epoch c) (ck-start (:next-id w)) (i10-current-comp-keys (:comps w))) (i10-current-run-keys (:runs w))) true))
  (rw [all-i10-current-run-keys])
  (apply (all-of-mem RunRow _ (:runs w)))
  (intros q mq)
  (have hk0 (= (reach-mem (:id (i10-current-run-key q)) (List.nil Nat)) false)) (rfl)
  (simp only [old-row hk0 Bool.false_or])
  (rw [all-i10-current-comp-keys])
  (exact (all-of-mem CompRow _ (:comps w) (fn [k :- CompRow, mk :- (List.Mem k (:comps w))] (start-old (:next-id w) w c q k h mc hst mq mk))))
  (have lt1 (< (:next-id w) (+ (:next-id w) 2))) (omega)
  (have lt2 (< (:id c) (+ (:next-id w) 2))) (have z := (comp-below w (:id c) hs (comp-mem-has w c mc))) (omega)
  (have hr := (i10-current-exempt-rest-of _ _ w h)) (simp only [i10-current-exempt-rest] at hr)
  (have k1 := (i10-current-exempt-keys-ok-new-run _ _ _ _ _ (:next-id w) (+ (:next-id w) 2) (:id c) (start-epoch c) (ck-start (:next-id w))
                (fn [k :- I10CurrentCompKey] (Eq.refl (:id k))) hr hnew hold (runs-below w hs) lt1 lt2))
  (have e (= (i10-current-exempt-rest (List.nil Nat) (List.nil Nat) (start-raw w c))
             (i10-current-exempt-keys-ok (List.nil Nat) (List.nil Nat) (List.cons I10CurrentRunKey (I10CurrentRunKey.mk (:next-id w) (:id c) (start-epoch c) true) (i10-current-run-keys (:runs w)))
                   (i10-current-comp-keys (tbl-upd comp-id (:id c) (comp-start-row (:next-id w)) (:comps w))) (i10-current-task-keys (:tasks w)) (+ (:next-id w) 2))))
  (rfl)
  (rw [(i10-current-comp-keys-upd (:id c) (comp-start-row (:next-id w)) (ck-start (:next-id w)) (fn [k :- CompRow] (Eq.refl (i10-current-comp-key (comp-start-row (:next-id w) k)))) (:comps w))] at e)
  (exact (i10-current-exempt-intro _ _ _ (well-formed-start-raw w c hs) (Eq.trans e k1))))

;; ---- the raw transition with nothing exempt: bundle i10-current = i10-current-exempt [] [] (T5 is proved there; every
;; other transition lemma is G10's, instantiated)

(a/defn i10-current [w :- World] Bool (i10-current-exempt (List.nil Nat) (List.nil Nat) w))
(a/theorem i10-current-parts [w :- World]
  (=> (= (i10-current w) true) (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (i10-current-exempt-parts (List.nil Nat) (List.nil Nat) w h)))

(def G10R (mk-bundle 'i10-current [] "i10-current-" {}))
(swap! (:renames G10R) assoc 'well-formed-parts 'i10-current-parts)

(defn- wrap-g10r! [n]
  (let [[_ _ binders stmt] (#'spindel.v2.pres.part/theorem-source n)
        L (get @(:renames G10) n)
        _ (assert L (str "no G10 lemma for " n))
        prems (butlast (rest stmt))
        hs (vec (map-indexed (fn [i _] (symbol (str "h" i))) prems))
        stmt' (clojure.walk/postwalk (fn [y] (if (and (seq? y) (= 'well-formed (first y))) (list 'i10-current (second y)) y)) stmt)
        nm (symbol (str (name L) "-r"))
        form (list 'a/theorem nm binders stmt' (cons 'intros hs)
                   (list 'exact (concat (list L '(List.nil Nat) '(List.nil Nat)) (take-nth 3 binders) hs)))]
    (#'spindel.v2.pres.part/eval-theorem! form)
    (swap! (:renames G10R) assoc n nm)))

(def ^:private raw-deps
  (let [S (set (map first @@#'spindel.v2.pres.part/source-theorems))
        deps (fn [n] (let [[_ _ _ _ & p] (#'spindel.v2.pres.part/theorem-source n)] (distinct (filter S (filter symbol? (flatten p))))))]
    (vec (remove '#{well-formed-t5-start well-formed-transition well-formed-host-guarded-transition} (distinct (concat (deps 'well-formed-transition) (deps 'well-formed-raw)))))))
(tree/restate! G10 raw-deps)
(doseq [n raw-deps] (wrap-g10r! n))

(a/theorem t5-start-g-st [fresh :- Nat, n :- Nat, w :- World, c :- CompRow]
  (=> (= (Bool.and (Nat.beq fresh n) (startable w c)) true) (= (startable w c) true))
  (intro h) (simp only [Bool.and_eq_true] at h) (exact (And.right h)))
;; g10r's rest part, for the tree (Q := i10-current-rest): g10's at empty exempt lists
(a/defn i10-current-rest [w :- World] Bool (i10-current-exempt-rest (List.nil Nat) (List.nil Nat) w))
;; i10-current on the generic tree: raw0's transitions are g10's at empty exempt lists (the wrappers above);
;; T5's start takes "the computation is a startable row" from T5's guard
(tree/part! G10R
  :over '{well-formed-start-raw i10-current-start-raw-hand}
  :ctx '{well-formed-start-raw [(List.Mem c (:comps w)) (= (startable w c) true)]}
  :pass '{well-formed-t5-start {well-formed-start-raw [(tbl-find-mem CompRow comp-id cid c (:comps w) hc) (t5-start-g-st fresh (:next-id w) w c hg)]}})
(a/theorem i10-current-start-raw-hand [w :- World, c :- CompRow]
  (=> (List.Mem c (:comps w)) (= (startable w c) true) (= (i10-current w) true) (= (i10-current (start-raw w c)) true))
  (intros mc hst h) (exact (i10-current-start-raw w c mc hst h)))
(tree/restate! G10R '[well-formed-raw])

;; ===========================================================================
;; Part H. Demotion: computation cid (exempt) ends with no current run (epoch step, or none
;; was current), then leaves the exempt list
;; ===========================================================================

(a/defn nc0 [gkz :- (List Nat), cid :- Nat, r :- I10CurrentRunKey, k :- I10CurrentCompKey] Bool
  (Bool.or (Bool.not (Nat.beq (:id k) cid)) (Bool.or (Bool.not (Nat.beq (:of r) (:id k)))
   (Bool.or (Nat.blt (:epoch r) (:epoch k)) (reach-mem (:id r) gkz)))))
(a/defn nc0s [gkz :- (List Nat), cid :- Nat, r :- RS10, k :- CS10] Bool
  (Bool.or (Bool.not (Nat.beq (:id k) cid)) (Bool.or (Bool.not (Nat.beq (:of r) (:id k)))
   (Bool.or (Nat.blt (:epoch r) (:epoch k)) (reach-mem (:id r) gkz)))))
(a/theorem nc0s-m [gkz :- (List Nat), cid :- Nat, r :- RS10, k :- CS10]
  (=> (= (nc0s gkz cid r k) true) (= (nc0s gkz cid r (cs-step k)) true))
  (intro h)
  (simp only [nc0s Bool.or_eq_true Nat.blt_eq] at h)
  (simp only [nc0s cs-step Bool.or_eq_true Nat.blt_eq])
  (cases h)
  (case [inl a] (exact (Or.inl a)))
  (case [inr b]
    (cases b)
    (case [inl a] (exact (Or.inr (Or.inl a))))
    (case [inr b2]
      (cases b2)
      (case [inl a] (have a2 (< (:epoch r) (+ (:epoch k) 1))) (omega) (exact (Or.inr (Or.inr (Or.inl a2)))))
      (case [inr a] (exact (Or.inr (Or.inr (Or.inr a))))))))
(a/defn ncq [gkz :- (List Nat), cid :- Nat, w :- World] Bool (i10-current-transport (nc0s gkz cid) tt-c (nc0s-m gkz cid) tt-m w))
(a/defn nck [gkz :- (List Nat), cid :- Nat, rks :- (List I10CurrentRunKey), cks :- (List I10CurrentCompKey)] Bool
  (tbl-all (fn [r :- I10CurrentRunKey] (tbl-all (nc0 gkz cid r) cks)) rks))

(a/theorem nck-of-ncq [gkz :- (List Nat), cid :- Nat, w :- World]
  (=> (= (ncq gkz cid w) true) (= (nck gkz cid (i10-current-run-keys (:runs w)) (i10-current-comp-keys (:comps w))) true))
  (intro h)
  (simp only [ncq] at h)
  (have h1 := (i10-current-transport-rest-of _ _ _ _ w h))
  (simp only [i10-current-transport-rest nqk Bool.and_eq_true] at h1)
  (have h2 := (And.left h1)) (rw [all-rs10s] at h2)
  (simp only [nck]) (rw [all-i10-current-run-keys])
  (apply (tbl-all-mono RunRow _ _ _ (:runs w) h2))
  (intros q a) (simp only [i10-current-transport-row] at a) (rw [all-cs10s] at a) (simp only [all-i10-current-comp-keys]) (exact a))

(a/theorem nqk-and [nqr :- (=> RS10 CS10 Bool), nqc :- (=> CS10 Bool), rks :- (List RS10), cks :- (List CS10)]
  (=> (= (tbl-all (i10-current-transport-row nqr cks) rks) true) (= (tbl-all nqc cks) true) (= (nqk nqr nqc rks cks) true))
  (intros a b) (simp only [nqk a b Bool.and_self]))
(a/theorem ncq-of-nck [gkz :- (List Nat), cid :- Nat, w :- World]
  (=> (= (well-formed w) true) (= (nck gkz cid (i10-current-run-keys (:runs w)) (i10-current-comp-keys (:comps w))) true) (= (ncq gkz cid w) true))
  (intros hs h)
  (simp only [nck] at h) (rw [all-i10-current-run-keys] at h)
  (have a1 (= (tbl-all (i10-current-transport-row (nc0s gkz cid) (cs10s (:comps w))) (rs10s (:runs w))) true))
  (rw [all-rs10s])
  (apply (tbl-all-mono RunRow _ _ _ (:runs w) h))
  (intros q a) (simp only [all-i10-current-comp-keys] at a) (simp only [i10-current-transport-row]) (rw [all-cs10s]) (exact a)
  (have a2 (= (tbl-all tt-c (cs10s (:comps w))) true)) (exact (all-true-of CS10 tt-c (fn [c :- CS10] (Eq.refl true)) _))
  (simp only [ncq])
  (exact (i10-current-transport-intro (nc0s gkz cid) tt-c (nc0s-m gkz cid) tt-m w hs (nqk-and (nc0s gkz cid) tt-c (rs10s (:runs w)) (cs10s (:comps w)) a1 a2))))

;; drop cid from the exempt list when no run is current for its rows
(a/theorem rc-drop [gxz :- (List Nat), gkz :- (List Nat), cid :- Nat, r :- I10CurrentRunKey, k :- I10CurrentCompKey]
  (=> (= (rc-ok (List.cons Nat cid gxz) gkz r k) true) (= (nc0 gkz cid r k) true) (= (rc-ok gxz gkz r k) true))
  (intros h hn)
  (cases hx (Nat.beq (:id k) cid))
  (case [false] (exact (rc-res-off gxz gkz cid r k h hx)))
  (case [true]
    (cases hk (reach-mem (:id r) gkz))
    (case [true] (exact (rc-exempt gxz gkz r k hk)))
    (case [false]
      (have pc := (rc-parts _ gkz r k h hk))
      (simp only [nc0 hx hk Bool.not_true Bool.false_or Bool.or_false] at hn)
      (cases ho (Nat.beq (:of r) (:id k)))
      (case [false] (simp only [rc-ok cur-pair cur-core ho (And.right pc) Bool.not_false Bool.true_or Bool.and_self Bool.or_true]))
      (case [true]
        (simp only [ho Bool.not_true Bool.false_or Nat.blt_eq] at hn)
        (have b1 (= (Nat.ble (:epoch r) (:epoch k)) true)) (simp only [Nat.ble_eq]) (omega)
        (have b2 (= (Nat.beq (:epoch r) (:epoch k)) false)) (cases hb (Nat.beq (:epoch r) (:epoch k))) (rfl) (have z := (Nat.eq_of_beq_eq_true hb)) (omega)
        (simp only [rc-ok cur-pair cur-core ho b1 b2 (And.right pc) Bool.not_true Bool.not_false Bool.false_or Bool.true_or Bool.true_and
                    Bool.and_self Bool.or_true])))))

(a/theorem i10-current-run-ok-drop [gxz :- (List Nat), gkz :- (List Nat), cid :- Nat, cks :- (List I10CurrentCompKey), tks :- (List I10CurrentTaskKey), n :- Nat, r :- I10CurrentRunKey]
  (=> (= (i10-current-run-ok (List.cons Nat cid gxz) gkz cks tks n r) true) (= (tbl-all (nc0 gkz cid r) cks) true) (= (i10-current-run-ok gxz gkz cks tks n r) true))
  (intros h hn)
  (simp only [i10-current-run-ok Bool.and_eq_true] at h)
  (simp only [i10-current-run-ok Bool.and_eq_true (And.right h) and_true])
  (exact (tbl-all-mono2 I10CurrentCompKey _ _ _ (fn [k :- I10CurrentCompKey, a1 :- (= (rc-ok (List.cons Nat cid gxz) gkz r k) true), a2 :- (= (nc0 gkz cid r k) true)]
    (rc-drop gxz gkz cid r k a1 a2)) cks (And.left h) hn)))
(a/theorem i10-current-exempt-keys-ok-drop [gxz :- (List Nat), gkz :- (List Nat), cid :- Nat, rks :- (List I10CurrentRunKey), cks :- (List I10CurrentCompKey), tks :- (List I10CurrentTaskKey), n :- Nat]
  (=> (= (i10-current-exempt-keys-ok (List.cons Nat cid gxz) gkz rks cks tks n) true) (= (nck gkz cid rks cks) true) (= (i10-current-exempt-keys-ok gxz gkz rks cks tks n) true))
  (intros h hn)
  (simp only [nck] at hn)
  (simp only [i10-current-exempt-keys-ok Bool.and_eq_true] at h)
  (simp only [i10-current-exempt-keys-ok Bool.and_eq_true (And.right h) and_true])
  (exact (tbl-all-mono2 I10CurrentRunKey _ _ (i10-current-run-ok gxz gkz cks tks n)
           (fn [r :- I10CurrentRunKey, a1 :- (= (i10-current-run-ok (List.cons Nat cid gxz) gkz cks tks n r) true), a2 :- (= (tbl-all (nc0 gkz cid r) cks) true)]
             (i10-current-run-ok-drop gxz gkz cid cks tks n r a1 a2))
           rks (And.left h) hn)))

(a/theorem i10-current-exempt-drop [gxz :- (List Nat), gkz :- (List Nat), cid :- Nat, w :- World]
  (=> (= (i10-current-exempt (List.cons Nat cid gxz) gkz w) true) (= (ncq gkz cid w) true) (= (i10-current-exempt gxz gkz w) true))
  (intros h hn)
  (have hr := (i10-current-exempt-rest-of _ gkz w h)) (simp only [i10-current-exempt-rest] at hr)
  (have hr2 (= (i10-current-exempt-rest gxz gkz w) true)) (simp only [i10-current-exempt-rest]) (exact (i10-current-exempt-keys-ok-drop gxz gkz cid _ _ _ _ hr (nck-of-ncq gkz cid w hn)))
  (exact (i10-current-exempt-intro gxz gkz w (i10-current-exempt-well-formed _ gkz w h) hr2)))

(a/theorem nck-of-mem [gkz :- (List Nat), cid :- Nat, w :- World,
                       hp :- (forall [q :- RunRow, k :- CompRow] (=> (List.Mem q (:runs w)) (List.Mem k (:comps w)) (= (nc0 gkz cid (i10-current-run-key q) (i10-current-comp-key k)) true)))]
  (= (nck gkz cid (i10-current-run-keys (:runs w)) (i10-current-comp-keys (:comps w))) true)
  (simp only [nck]) (rw [all-i10-current-run-keys])
  (apply (all-of-mem RunRow _ (:runs w)))
  (intros q mq) (simp only [all-i10-current-comp-keys])
  (exact (all-of-mem CompRow _ (:comps w) (fn [k :- CompRow, mk :- (List.Mem k (:comps w))] (hp q k mq mk)))))

(a/theorem nc0-off [gkz :- (List Nat), cid :- Nat, r :- I10CurrentRunKey, k :- I10CurrentCompKey] (=> (= (Nat.beq (:id k) cid) false) (= (nc0 gkz cid r k) true))
  (intro h) (simp only [nc0 h Bool.not_false Bool.true_or]))

;; no computation row with id cid
(a/theorem ncq-none [gkz :- (List Nat), w :- World, cid :- Nat]
  (=> (= (well-formed w) true) (= (comp-find w cid) (Option.none CompRow)) (= (ncq gkz cid w) true))
  (intros hs hf)
  (have hn := (tbl-find-none-has CompRow comp-id cid (:comps w) hf))
  (apply (ncq-of-nck gkz cid w hs))
  (apply (nck-of-mem gkz cid w))
  (intros q k mq mk)
  (apply (nc0-off gkz cid (i10-current-run-key q) (i10-current-comp-key k)))
  (cases hx (Nat.beq (:id k) cid)) (rfl)
  (have e := (Nat.eq_of_beq_eq_true hx))
  (have hm := (comp-mem-has w k mk)) (rw [e] at hm) (simp only [comp-has] at hm) (rw [hm] at hn) (cases hn))

;; the rows of computation c (c found under cid), with a lemma for one pair
(a/theorem nc-of-pair [gxz :- (List Nat), gkz :- (List Nat), w :- World, c :- CompRow, q :- RunRow, k :- CompRow,
                       hcur :- (=> (= (reach-mem (:id q) gkz) false) (= (Nat.beq (:of q) (:id c)) true) (= (Nat.beq (:epoch q) (:epoch c)) true) False)]
  (=> (= (i10-current-exempt gxz gkz w) true) (List.Mem c (:comps w)) (List.Mem q (:runs w)) (List.Mem k (:comps w))
      (= (nc0 gkz (:id c) (i10-current-run-key q) (i10-current-comp-key k)) true))
  (intros h mc mq mk)
  (have hs := (i10-current-exempt-well-formed gxz gkz w h))
  (cases hx (Nat.beq (:id k) (:id c)))
  (case [false] (exact (nc0-off gkz (:id c) (i10-current-run-key q) (i10-current-comp-key k) hx)))
  (case [true]
    (have sk := (comp-same w c k hs mc mk (Nat.eq_of_beq_eq_true hx)))
    (cases hk (reach-mem (:id q) gkz))
    (case [true] (have hk3 (= (reach-mem (:id (i10-current-run-key q)) gkz) true)) (exact hk) (simp only [nc0 hk3 Bool.or_true]))
    (case [false]
      (cases ho (Nat.beq (:of q) (:id k)))
      (case [false] (have ho3 (= (Nat.beq (:of (i10-current-run-key q)) (:id (i10-current-comp-key k))) false)) (exact ho) (simp only [nc0 ho3 Bool.not_false Bool.true_or Bool.or_true]))
      (case [true]
        (have ho2 (= (Nat.beq (:of q) (:id c)) true)) (rw [← (Nat.eq_of_beq_eq_true hx)]) (exact ho)
        (have pc := (rc-parts gxz gkz (i10-current-run-key q) (i10-current-comp-key c) (i10-current-exempt-rc gxz gkz w q c h mq mc) hk))
        (have le := (cur-le gxz (i10-current-run-key q) (i10-current-comp-key c) (And.left pc) ho2))
        (have ne (Not (= (:epoch q) (:epoch c))))
        (intro z) (have z2 (= (Nat.beq (:epoch q) (:epoch c)) true)) (rw [z]) (exact (Nat.beq_refl _)) (exact (hcur hk ho2 z2))
        (have le2 (<= (:epoch q) (:epoch c))) (exact le)
        (have lt0 (< (:epoch q) (:epoch k))) (rw [(And.left sk)]) (omega)
        (have lt (= (Nat.blt (:epoch (i10-current-run-key q)) (:epoch (i10-current-comp-key k))) true)) (simp only [Nat.blt_eq]) (exact lt0)
        (simp only [nc0 lt Bool.true_or Bool.or_true])))))

(a/theorem ncq-idle [gxz :- (List Nat), gkz :- (List Nat), w :- World, c :- CompRow]
  (=> (= (i10-current-exempt gxz gkz w) true) (List.Mem c (:comps w)) (= (:idle c) true) (= (ncq gkz (:id c) w) true))
  (intros h mc hi)
  (have hs := (i10-current-exempt-well-formed gxz gkz w h))
  (apply (ncq-of-nck gkz (:id c) w hs))
  (apply (nck-of-mem gkz (:id c) w))
  (intros q k mq mk)
  (apply (nc-of-pair gxz gkz w c q k _ h mc mq mk))
  (intros hk ho he)
  (have pc := (rc-parts gxz gkz (i10-current-run-key q) (i10-current-comp-key c) (i10-current-exempt-rc gxz gkz w q c h mq mc) hk))
  (have ce := (cur-eq gxz (i10-current-run-key q) (i10-current-comp-key c) (And.left pc) ho he))
  (have z := (And.left (And.right ce))) (simp only [i10-current-comp-key] at z) (rw [hi] at z) (cases z))

(a/theorem ncq-notcur [gxz :- (List Nat), gkz :- (List Nat), w :- World, c :- CompRow]
  (=> (= (i10-current-exempt gxz gkz w) true) (List.Mem c (:comps w)) (= (demote-cur w c) false) (= (ncq gkz (:id c) w) true))
  (intros h mc hd)
  (have hs := (i10-current-exempt-well-formed gxz gkz w h))
  (apply (ncq-of-nck gkz (:id c) w hs))
  (apply (nck-of-mem gkz (:id c) w))
  (intros q k mq mk)
  (apply (nc-of-pair gxz gkz w c q k _ h mc mq mk))
  (intros hk ho he)
  (have pc := (rc-parts gxz gkz (i10-current-run-key q) (i10-current-comp-key c) (i10-current-exempt-rc gxz gkz w q c h mq mc) hk))
  (have ce := (cur-eq gxz (i10-current-run-key q) (i10-current-comp-key c) (And.left pc) ho he))
  (have erun (= (:run c) (:id q))) (exact (And.left ce))
  (cases hf (run-find w (:run c)))
  (case [none]
    (have z := (tbl-find-none-has RunRow run-id (:run c) (:runs w) hf))
    (have z2 (= (tbl-has run-id (:run c) (:runs w)) true)) (rw [erun])
    (have hm := (mem-ids-has RunRow run-id q (:runs w) mq)) (rw [nat-mem-ids] at hm) (exact hm)
    (rw [z2] at z) (cases z))
  (case [some r2]
    (have mr2 := (tbl-find-mem RunRow run-id (:run c) r2 (:runs w) hf))
    (have er2 (= (:id r2) (:run c))) (exact (tbl-find-id RunRow run-id (:run c) r2 (:runs w) hf))
    (have sq := (run-same-ep w q r2 hs mq mr2 (Eq.trans er2 erun)))
    (have e3 (= (Nat.beq (:epoch r2) (:epoch c)) true)) (rw [(And.left sq)]) (exact he)
    (simp [demote-cur hf e3] at hd)))

;; after the epoch step of cid: no run is current for cid (run epochs are at most the old epoch)
(a/defn ck-step [k :- I10CurrentCompKey] I10CurrentCompKey (I10CurrentCompKey.mk (:id k) (+ (:epoch k) 1) (:done k) (:run k) (:idle k)))
(a/theorem nc0-step [gxz :- (List Nat), gkz :- (List Nat), cid :- Nat, r :- I10CurrentRunKey, k :- I10CurrentCompKey]
  (=> (= (rc-ok gxz gkz r k) true) (= (nc0 gkz cid r (ck-step k)) true))
  (intro h)
  (cases hk (reach-mem (:id r) gkz))
  (case [true] (simp only [nc0 hk Bool.or_true]))
  (case [false]
    (have pc := (rc-parts gxz gkz r k h hk))
    (cases ho (Nat.beq (:of r) (:id k)))
    (case [false] (have ho2 (= (Nat.beq (:of r) (:id (ck-step k))) false)) (exact ho) (simp only [nc0 ho2 Bool.not_false Bool.true_or Bool.or_true]))
    (case [true]
      (have le := (cur-le gxz r k (And.left pc) ho))
      (have lt (= (Nat.blt (:epoch r) (:epoch (ck-step k))) true)) (simp only [Nat.blt_eq ck-step]) (omega)
      (simp only [nc0 lt Bool.true_or Bool.or_true]))))
(a/theorem ncq-step [gxz :- (List Nat), gkz :- (List Nat), w :- World, cid :- Nat]
  (=> (= (i10-current-exempt gxz gkz w) true) (= (ncq gkz cid (comp-upd w cid comp-inc-epoch)) true))
  (intro h)
  (have hs := (i10-current-exempt-well-formed gxz gkz w h))
  (have hs2 := (well-formed-comp-upd w cid comp-inc-epoch comp-inc-epoch-comp-id comp-inc-epoch-pending hs))
  (apply (ncq-of-nck gkz cid _ hs2))
  (have hr := (i10-current-exempt-rest-of gxz gkz w h)) (simp only [i10-current-exempt-rest i10-current-exempt-keys-ok Bool.and_eq_true] at hr)
  (have e (= (i10-current-comp-keys (:comps (comp-upd w cid comp-inc-epoch))) (tbl-upd i10-current-comp-key-id cid ck-step (i10-current-comp-keys (:comps w)))))
  (exact (i10-current-comp-keys-upd cid comp-inc-epoch ck-step (fn [c :- CompRow] (Eq.refl (i10-current-comp-key (comp-inc-epoch c)))) (:comps w)))
  (have e2 (= (i10-current-run-keys (:runs (comp-upd w cid comp-inc-epoch))) (i10-current-run-keys (:runs w)))) (rfl)
  (rw [e e2])
  (simp only [nck])
  (apply (tbl-all-mono I10CurrentRunKey _ _ _ _ (And.left hr)))
  (intros r a)
  (simp only [i10-current-run-ok Bool.and_eq_true] at a)
  (exact (tbl-all-upd I10CurrentCompKey i10-current-comp-key-id cid ck-step (rc-ok gxz gkz r) (nc0 gkz cid r)
           (fn [k :- I10CurrentCompKey, p :- (= (rc-ok gxz gkz r k) true), hx :- (= (Nat.beq (i10-current-comp-key-id k) cid) true)] (nc0-step gxz gkz cid r k p))
           (fn [k :- I10CurrentCompKey, p :- (= (rc-ok gxz gkz r k) true), hx :- (= (Nat.beq (i10-current-comp-key-id k) cid) false)] (nc0-off gkz cid r k hx))
           _ (And.left a))))

;; demoted to idle: C.run := none, idle (no run is current for it)
(a/defn ck-idle [k :- I10CurrentCompKey] I10CurrentCompKey (I10CurrentCompKey.mk (:id k) (:epoch k) (:done k) 0 true))
(a/theorem rc-idle [gxz :- (List Nat), gkz :- (List Nat), cid :- Nat, r :- I10CurrentRunKey, k :- I10CurrentCompKey]
  (=> (= (rc-ok gxz gkz r k) true) (= (nc0 gkz cid r k) true) (= (Nat.beq (:id k) cid) true) (= (rc-ok gxz gkz r (ck-idle k)) true))
  (intros h hn hx)
  (cases hk (reach-mem (:id r) gkz))
  (case [true] (exact (rc-exempt gxz gkz r _ hk)))
  (case [false]
    (have hrof (= (rof-pair r (ck-idle k)) true))
    (cases hz (Nat.beq (:id r) 0))
    (simp only [rof-pair hz Bool.true_or])
    (simp only [rof-pair ck-idle hz Bool.not_false Bool.false_or Bool.true_or])
    (simp only [nc0 hx hk Bool.not_true Bool.false_or Bool.or_false] at hn)
    (have pc := (rc-parts gxz gkz r k h hk))
    (cases ho (Nat.beq (:of r) (:id k)))
    (case [false]
      (have ho2 (= (Nat.beq (:of r) (:id (ck-idle k))) false)) (exact ho)
      (simp only [rc-ok cur-pair cur-core ho2 hrof Bool.not_false Bool.true_or Bool.and_self Bool.or_true]))
    (case [true]
      (have ho2 (= (Nat.beq (:of r) (:id (ck-idle k))) true)) (exact ho)
      (simp only [ho Bool.not_true Bool.false_or Nat.blt_eq] at hn)
      (have b1 (= (Nat.ble (:epoch r) (:epoch (ck-idle k))) true)) (simp only [Nat.ble_eq ck-idle]) (omega)
      (have b2 (= (Nat.beq (:epoch r) (:epoch (ck-idle k))) false)) (cases hb (Nat.beq (:epoch r) (:epoch (ck-idle k)))) (rfl)
      (have z := (Nat.eq_of_beq_eq_true hb)) (simp only [ck-idle] at z) (omega)
      (simp only [rc-ok cur-pair cur-core ho2 b1 b2 hrof Bool.not_true Bool.not_false Bool.false_or Bool.true_or Bool.true_and Bool.and_self Bool.or_true]))))
(a/theorem i10-current-exempt-make-idle [gxz :- (List Nat), gkz :- (List Nat), w :- World, cid :- Nat, vs :- (List Valid)]
  (=> (= (i10-current-exempt gxz gkz w) true) (= (ncq gkz cid w) true) (= (i10-current-exempt gxz gkz (comp-upd w cid (comp-make-idle vs))) true))
  (intros h hn)
  (have hs := (i10-current-exempt-well-formed gxz gkz w h))
  (have nk := (nck-of-ncq gkz cid w hn)) (simp only [nck] at nk)
  (have hr := (i10-current-exempt-rest-of gxz gkz w h)) (simp only [i10-current-exempt-rest i10-current-exempt-keys-ok Bool.and_eq_true] at hr)
  (have h1 (forall [r :- I10CurrentRunKey] (=> (= (i10-current-run-ok gxz gkz (i10-current-comp-keys (:comps w)) (i10-current-task-keys (:tasks w)) (:next-id w) r) true) (= (tbl-all (nc0 gkz cid r) (i10-current-comp-keys (:comps w))) true)
                                   (= (i10-current-run-ok gxz gkz (tbl-upd i10-current-comp-key-id cid ck-idle (i10-current-comp-keys (:comps w))) (i10-current-task-keys (:tasks w)) (:next-id w) r) true))))
  (intros r a1 a2)
  (simp only [i10-current-run-ok Bool.and_eq_true] at a1)
  (simp only [i10-current-run-ok Bool.and_eq_true (And.right a1) and_true])
  (exact (tbl-all-upd I10CurrentCompKey i10-current-comp-key-id cid ck-idle (both (rc-ok gxz gkz r) (nc0 gkz cid r)) (rc-ok gxz gkz r)
           (fn [k :- I10CurrentCompKey, p :- (= (both (rc-ok gxz gkz r) (nc0 gkz cid r) k) true), hx :- (= (Nat.beq (i10-current-comp-key-id k) cid) true)]
             (rc-idle gxz gkz cid r k (both-left _ _ _ _ p) (both-right _ _ _ _ p) hx))
           (fn [k :- I10CurrentCompKey, p :- (= (both (rc-ok gxz gkz r) (nc0 gkz cid r) k) true), hx :- (= (Nat.beq (i10-current-comp-key-id k) cid) false)] (both-left _ _ _ _ p))
           _ (tbl-all-mono2 I10CurrentCompKey _ _ _ (fn [k :- I10CurrentCompKey, b1 :- (= (rc-ok gxz gkz r k) true), b2 :- (= (nc0 gkz cid r k) true)] (both-mk _ _ _ _ b1 b2))
               _ (And.left a1) a2)))
  (have hR := (tbl-all-mono2 I10CurrentRunKey _ _ (i10-current-run-ok gxz gkz (tbl-upd i10-current-comp-key-id cid ck-idle (i10-current-comp-keys (:comps w))) (i10-current-task-keys (:tasks w)) (:next-id w)) h1 _ (And.left hr) nk))
  (have hC (= (tbl-all (i10-current-comp-ok (:next-id w)) (tbl-upd i10-current-comp-key-id cid ck-idle (i10-current-comp-keys (:comps w)))) true))
  (exact (tbl-all-upd I10CurrentCompKey i10-current-comp-key-id cid ck-idle (i10-current-comp-ok (:next-id w)) (i10-current-comp-ok (:next-id w))
           (fn [k :- I10CurrentCompKey, p :- (= (i10-current-comp-ok (:next-id w) k) true), hx :- (= (Nat.beq (i10-current-comp-key-id k) cid) true)] (i10-current-comp-ok-clear (:next-id w) k p))
           (fn [k :- I10CurrentCompKey, p :- (= (i10-current-comp-ok (:next-id w) k) true), hx :- (= (Nat.beq (i10-current-comp-key-id k) cid) false)] p) _ (And.left (And.right hr))))
  (have hrest (= (i10-current-exempt-rest gxz gkz (comp-upd w cid (comp-make-idle vs))) true))
  (simp only [i10-current-exempt-rest comp-upd set-comps (i10-current-comp-keys-upd cid (comp-make-idle vs) ck-idle (fn [k :- CompRow] (Eq.refl (i10-current-comp-key (comp-make-idle vs k)))) (:comps w))])
  (simp only [i10-current-exempt-keys-ok hR hC (And.right (And.right hr)) Bool.and_self])
  (exact (i10-current-exempt-intro gxz gkz _ (well-formed-comp-upd w cid (comp-make-idle vs) (comp-make-idle-id vs) (comp-make-idle-pending vs) hs) hrest)))

;; C1 Q6: the tombstone keeps C.run (stale), epoch and done-epoch; it is not idle
(a/defn ck-tomb [k :- I10CurrentCompKey] I10CurrentCompKey (I10CurrentCompKey.mk (:id k) (:epoch k) (:done k) (:run k) false))
(a/theorem comp-tomb-row-id [c :- CompRow] (= (comp-id (comp-tomb-row c)) (comp-id c)) (rfl))
(a/theorem comp-tomb-row-pending [c :- CompRow] (= (:pending (comp-tomb-row c)) (:pending c)) (rfl))
(a/theorem i10-current-comp-ok-tomb [n :- Nat, c :- I10CurrentCompKey] (=> (= (i10-current-comp-ok n c) true) (= (i10-current-comp-ok n (ck-tomb c)) true))
  (intro h) (exact h))
(a/theorem rc-tomb [gxz :- (List Nat), gkz :- (List Nat), cid :- Nat, r :- I10CurrentRunKey, k :- I10CurrentCompKey]
  (=> (= (rc-ok gxz gkz r k) true) (= (nc0 gkz cid r k) true) (= (Nat.beq (:id k) cid) true) (= (rc-ok gxz gkz r (ck-tomb k)) true))
  (intros h hn hx)
  (cases hk (reach-mem (:id r) gkz))
  (case [true] (exact (rc-exempt gxz gkz r _ hk)))
  (case [false]
    (have pc := (rc-parts gxz gkz r k h hk))
    (have hrof (= (rof-pair r (ck-tomb k)) true)) (exact (And.right pc))
    (simp only [nc0 hx hk Bool.not_true Bool.false_or Bool.or_false] at hn)
    (cases ho (Nat.beq (:of r) (:id k)))
    (case [false]
      (have ho2 (= (Nat.beq (:of r) (:id (ck-tomb k))) false)) (exact ho)
      (simp only [rc-ok cur-pair cur-core ho2 hrof Bool.not_false Bool.true_or Bool.and_self Bool.or_true]))
    (case [true]
      (have ho2 (= (Nat.beq (:of r) (:id (ck-tomb k))) true)) (exact ho)
      (simp only [ho Bool.not_true Bool.false_or Nat.blt_eq] at hn)
      (have b1 (= (Nat.ble (:epoch r) (:epoch (ck-tomb k))) true)) (simp only [Nat.ble_eq ck-tomb]) (omega)
      (have b2 (= (Nat.beq (:epoch r) (:epoch (ck-tomb k))) false)) (cases hb (Nat.beq (:epoch r) (:epoch (ck-tomb k)))) (rfl)
      (have z := (Nat.eq_of_beq_eq_true hb)) (simp only [ck-tomb] at z) (omega)
      (simp only [rc-ok cur-pair cur-core ho2 b1 b2 hrof Bool.not_true Bool.not_false Bool.false_or Bool.true_or Bool.true_and Bool.and_self Bool.or_true]))))
(a/theorem i10-current-exempt-tomb [gxz :- (List Nat), gkz :- (List Nat), w :- World, cid :- Nat]
  (=> (= (i10-current-exempt gxz gkz w) true) (= (ncq gkz cid w) true) (= (i10-current-exempt gxz gkz (comp-upd w cid comp-tomb-row)) true))
  (intros h hn)
  (have hs := (i10-current-exempt-well-formed gxz gkz w h))
  (have nk := (nck-of-ncq gkz cid w hn)) (simp only [nck] at nk)
  (have hr := (i10-current-exempt-rest-of gxz gkz w h)) (simp only [i10-current-exempt-rest i10-current-exempt-keys-ok Bool.and_eq_true] at hr)
  (have h1 (forall [r :- I10CurrentRunKey] (=> (= (i10-current-run-ok gxz gkz (i10-current-comp-keys (:comps w)) (i10-current-task-keys (:tasks w)) (:next-id w) r) true) (= (tbl-all (nc0 gkz cid r) (i10-current-comp-keys (:comps w))) true)
                                   (= (i10-current-run-ok gxz gkz (tbl-upd i10-current-comp-key-id cid ck-tomb (i10-current-comp-keys (:comps w))) (i10-current-task-keys (:tasks w)) (:next-id w) r) true))))
  (intros r a1 a2)
  (simp only [i10-current-run-ok Bool.and_eq_true] at a1)
  (simp only [i10-current-run-ok Bool.and_eq_true (And.right a1) and_true])
  (exact (tbl-all-upd I10CurrentCompKey i10-current-comp-key-id cid ck-tomb (both (rc-ok gxz gkz r) (nc0 gkz cid r)) (rc-ok gxz gkz r)
           (fn [k :- I10CurrentCompKey, p :- (= (both (rc-ok gxz gkz r) (nc0 gkz cid r) k) true), hx :- (= (Nat.beq (i10-current-comp-key-id k) cid) true)]
             (rc-tomb gxz gkz cid r k (both-left _ _ _ _ p) (both-right _ _ _ _ p) hx))
           (fn [k :- I10CurrentCompKey, p :- (= (both (rc-ok gxz gkz r) (nc0 gkz cid r) k) true), hx :- (= (Nat.beq (i10-current-comp-key-id k) cid) false)] (both-left _ _ _ _ p))
           _ (tbl-all-mono2 I10CurrentCompKey _ _ _ (fn [k :- I10CurrentCompKey, b1 :- (= (rc-ok gxz gkz r k) true), b2 :- (= (nc0 gkz cid r k) true)] (both-mk _ _ _ _ b1 b2))
               _ (And.left a1) a2)))
  (have hR := (tbl-all-mono2 I10CurrentRunKey _ _ (i10-current-run-ok gxz gkz (tbl-upd i10-current-comp-key-id cid ck-tomb (i10-current-comp-keys (:comps w))) (i10-current-task-keys (:tasks w)) (:next-id w)) h1 _ (And.left hr) nk))
  (have hC (= (tbl-all (i10-current-comp-ok (:next-id w)) (tbl-upd i10-current-comp-key-id cid ck-tomb (i10-current-comp-keys (:comps w)))) true))
  (exact (tbl-all-upd I10CurrentCompKey i10-current-comp-key-id cid ck-tomb (i10-current-comp-ok (:next-id w)) (i10-current-comp-ok (:next-id w))
           (fn [k :- I10CurrentCompKey, p :- (= (i10-current-comp-ok (:next-id w) k) true), hx :- (= (Nat.beq (i10-current-comp-key-id k) cid) true)] (i10-current-comp-ok-tomb (:next-id w) k p))
           (fn [k :- I10CurrentCompKey, p :- (= (i10-current-comp-ok (:next-id w) k) true), hx :- (= (Nat.beq (i10-current-comp-key-id k) cid) false)] p) _ (And.left (And.right hr))))
  (have hrest (= (i10-current-exempt-rest gxz gkz (comp-upd w cid comp-tomb-row)) true))
  (simp only [i10-current-exempt-rest comp-upd set-comps (i10-current-comp-keys-upd cid comp-tomb-row ck-tomb (fn [k :- CompRow] (Eq.refl (i10-current-comp-key (comp-tomb-row k)))) (:comps w))])
  (simp only [i10-current-exempt-keys-ok hR hC (And.right (And.right hr)) Bool.and_self])
  (exact (i10-current-exempt-intro gxz gkz _ (well-formed-comp-upd w cid comp-tomb-row comp-tomb-row-id comp-tomb-row-pending hs) hrest)))

(a/theorem ncq-del [gkz :- (List Nat), w :- World, cid :- Nat]
  (=> (= (well-formed (comp-del w cid)) true) (= (ncq gkz cid (comp-del w cid)) true))
  (intro hs)
  (apply (ncq-of-nck gkz cid _ hs))
  (have e (= (i10-current-comp-keys (:comps (comp-del w cid))) (tbl-del i10-current-comp-key-id cid (i10-current-comp-keys (:comps w))))) (exact (i10-current-comp-keys-del cid (:comps w)))
  (rw [e])
  (simp only [nck])
  (apply (all-true-of I10CurrentRunKey _ _ _))
  (intro r)
  (exact (tbl-all-del I10CurrentCompKey i10-current-comp-key-id cid (fn [k :- I10CurrentCompKey] true) (nc0 gkz cid r)
           (fn [k :- I10CurrentCompKey, a1 :- (= true true), hx :- (= (Nat.beq (i10-current-comp-key-id k) cid) false)] (nc0-off gkz cid r k hx))
           _ (all-true-of I10CurrentCompKey (fn [k :- I10CurrentCompKey] true) (fn [k :- I10CurrentCompKey] (Eq.refl true)) _))))

(tree/restate! G10 '[well-formed-end-basis])
(tree/restate! NQ '[well-formed-end-basis])

(a/theorem demote-tail [gxz :- (List Nat), gkz :- (List Nat), w :- World, cid :- Nat]
  (=> (= (i10-current-exempt (List.cons Nat cid gxz) gkz w) true) (= (ncq gkz cid w) true) (= (i10-current-exempt gxz gkz (demote-edges w cid)) true))
  (intros h hn)
  (simp only [demote-edges])
  (have h2 := (i10-current-exempt-drop-edges (List.cons Nat cid gxz) gkz w (not-dep-of cid) h))
  (have h3 := (i10-current-exempt-end-basis (List.cons Nat cid gxz) gkz _ cid h2))
  (have n3 (= (ncq gkz cid (end-basis (drop-edges w (not-dep-of cid)) cid)) true))
  (simp only [ncq] at hn) (simp only [ncq]) (exact (i10-current-transport-end-basis _ _ _ _ _ cid (i10-current-transport-drop-edges _ _ _ _ w (not-dep-of cid) hn)))
  (cases hf (comp-find (end-basis (drop-edges w (not-dep-of cid)) cid) cid))
  (case [none] (simp only [demote-finish hf]) (exact (i10-current-exempt-drop gxz gkz cid _ h3 n3)))
  (case [some c3]
    (cases hk (demote-keep (end-basis (drop-edges w (not-dep-of cid)) cid) c3))
    (case [true]
      (simp only [demote-finish hf hk])
      (have s3 := (i10-current-exempt-well-formed _ gkz _ h3))
      (cases hd (demote-idle c3))
      (case [true] (rw [(demote-row-idle-upd _ cid c3 _ s3 hf hd)]) (exact (i10-current-exempt-make-idle gxz gkz _ cid _ (i10-current-exempt-drop gxz gkz cid _ h3 n3) n3)))
      (case [false] (rw [(demote-row-tomb-upd _ cid c3 _ s3 hf hd)]) (exact (i10-current-exempt-tomb gxz gkz _ cid (i10-current-exempt-drop gxz gkz cid _ h3 n3) n3))))
    (case [false]
      (simp only [demote-finish hf hk])
      (have h4 := (i10-current-exempt-comp-del-unref (List.cons Nat cid gxz) gkz _ cid (drop-edges-avoids (end-basis (drop-edges w (not-dep-of cid)) cid) cid)
                    (i10-current-exempt-drop-edges (List.cons Nat cid gxz) gkz _ (edge-avoids cid) h3)))
      (exact (i10-current-exempt-drop gxz gkz cid _ h4 (ncq-del gkz _ cid (i10-current-exempt-well-formed _ gkz _ h4)))))))

;; the demotion's own cancels: C's runs (exempt) and runs of tasks (no computation's runs)
(a/theorem demote-ncw1 [gxz :- (List Nat), gkz :- (List Nat), w :- World, c :- CompRow, r :- RunRow]
  (=> (= (well-formed w) true) (List.Mem r (:runs w)) (= (run-alive-of (:id c) r) true)
      (= (ncw (List.cons Nat (:id c) gxz) gkz (:id r) w) true))
  (intros hs mr hr)
  (simp only [run-alive-of Bool.and_eq_true] at hr)
  (have eo := (Nat.eq_of_beq_eq_true (And.right hr)))
  (simp only [ncw])
  (apply (nqk-of-mem (nc-run (List.cons Nat (:id c) gxz) gkz (:id r)) tt-c (:runs w) (:comps w) _ (fn [k :- CompRow, mk :- (List.Mem k (:comps w))] (Eq.refl true))))
  (intros q k mq mk)
  (cases hx (Nat.beq (:id q) (:id r)))
  (case [false] (exact (nc-run-off _ gkz (:id r) (rs10 q) (cs10 k) hx)))
  (case [true]
    (have sq := (run-same-ep w r q hs mr mq (Nat.eq_of_beq_eq_true hx)))
    (cases ho (Nat.beq (:of q) (:id k)))
    (case [false] (exact (nc-run-of _ gkz (:id r) (rs10 q) (cs10 k) ho)))
    (case [true]
      (have e := (Nat.eq_of_beq_eq_true ho))
      (have b (= (reach-mem (:id (cs10 k)) (List.cons Nat (:id c) gxz)) true))
      (simp only [cs10 reach-mem-cons Bool.or_eq_true]) (rw [← e (And.right sq) eo]) (exact (Or.inl (Nat.beq_refl _)))
      (simp only [nc-run nc-cs b Bool.true_or Bool.or_true]))))

(a/theorem demote-ncw2 [gxz :- (List Nat), gkz :- (List Nat), w :- World, ids :- (List Nat), r :- RunRow]
  (=> (= (well-formed w) true) (List.Mem r (:runs w)) (= (run-of-tasks w ids r) true) (= (ncw gxz gkz (:id r) w) true))
  (intros hs mr hr)
  (simp only [run-of-tasks Bool.and_eq_true] at hr)
  (exact (task-run-ncw gxz gkz (run-id r) w hs
           (uniq-all RunRow run-id (fn [q :- RunRow] (task-has w (:of q))) r (:runs w) (lit-runs-nodup w hs) mr (And.right (And.right hr))))))

(a/theorem demote-jl [gxz :- (List Nat), gkz :- (List Nat), w :- World, c :- CompRow]
  (=> (= (well-formed w) true)
      (= (tbl-all (job-ok (List.cons Nat (:id c) gxz) gkz w) (cancel-jobs (demote-cancels w c))) true))
  (intro hs)
  (rw [jl-cancel-jobs])
  (simp only [demote-cancels all-append Bool.and_eq_true])
  (exact (And.intro
           (scan-all RunRow run-id (run-alive-of (:id c)) (fn [x :- Nat] (ncw (List.cons Nat (:id c) gxz) gkz x w)) (:runs w)
             (fn [r :- RunRow, m :- (List.Mem r (:runs w)), p :- (= (run-alive-of (:id c) r) true)] (demote-ncw1 gxz gkz w c r hs m p)))
           (scan-all RunRow run-id (run-of-tasks w (created-ids (:basis c))) (fn [x :- Nat] (ncw (List.cons Nat (:id c) gxz) gkz x w)) (:runs w)
             (fn [r :- RunRow, m :- (List.Mem r (:runs w)), p :- (= (run-of-tasks w (created-ids (:basis c)) r) true)]
               (demote-ncw2 (List.cons Nat (:id c) gxz) gkz w (created-ids (:basis c)) r hs m p))))))

(a/theorem i10-current-exempt-demote [gxz :- (List Nat), gkz :- (List Nat), w :- World, cid :- Nat]
  (=> (= (i10-current-exempt (List.cons Nat cid gxz) gkz w) true) (= (i10-current-exempt gxz gkz (demote w cid)) true))
  (intro h)
  (have hs := (i10-current-exempt-well-formed _ gkz w h))
  (cases hc (comp-find w cid))
  (case [none] (simp only [demote hc]) (exact (i10-current-exempt-drop gxz gkz cid w h (ncq-none gkz w cid hs hc))))
  (case [some c]
    (have mc := (tbl-find-mem CompRow comp-id cid c (:comps w) hc))
    (have ec (= (:id c) cid)) (exact (tbl-find-id CompRow comp-id cid c (:comps w) hc))
    (cases hi (:idle c))
    (case [true]
      (simp only [demote hc hi])
      (have n1 := (ncq-idle _ gkz w c h mc hi)) (rw [ec] at n1)
      (exact (i10-current-exempt-drop gxz gkz cid w h n1)))
    (case [false]
      (simp only [demote hc hi])
      (have hj := (demote-jl gxz gkz w c hs)) (rw [ec] at hj)
      (have h1 := (i10-current-exempt-run-cascade (List.cons Nat cid gxz) gkz w _ hj h))
      (cases hd (demote-cur w c))
      (case [true]
        (simp only [demote-epoch])
        (exact (demote-tail gxz gkz _ cid (i10-current-exempt-up-inc-epoch (List.cons Nat cid gxz) gkz _ cid h1) (ncq-step (List.cons Nat cid gxz) gkz _ cid h1))))
      (case [false]
        (simp only [demote-epoch])
        (have n0 := (ncq-notcur (List.cons Nat cid gxz) gkz w c h mc hd)) (rw [ec] at n0)
        (simp only [ncq] at n0)
        (have n1 := (i10-current-transport-run-cascade (nc0s gkz cid) tt-c (nc0s-m gkz cid) tt-m w (cancel-jobs (demote-cancels w c)) n0))
        (have n2 (= (ncq gkz cid (run-cascade w (cancel-jobs (demote-cancels w c)))) true)) (simp only [ncq]) (exact n1)
        (exact (demote-tail gxz gkz _ cid h1 n2))))))

(a/theorem i10-current-exempt-gx-app [gkz :- (List Nat), ys :- (List Nat)]
  (forall [gxz :- (List Nat), w :- World] (=> (= (i10-current-exempt gxz gkz w) true) (= (i10-current-exempt (List.append Nat ys gxz) gkz w) true)))
  (induction ys)
  (case [nil] (intros gxz w h) (exact h))
  (case [cons y t ih] (intros gxz w h) (exact (i10-current-exempt-gx-cons _ gkz y w (ih gxz w h)))))

(a/theorem i10-current-exempt-fold-demote [gkz :- (List Nat), ys :- (List Nat)]
  (forall [gxz :- (List Nat), w :- World] (=> (= (i10-current-exempt (List.append Nat ys gxz) gkz w) true) (= (i10-current-exempt gxz gkz (nat-fold demote w ys)) true)))
  (induction ys)
  (case [nil] (intros gxz w h) (simp only [nat-fold]) (exact h))
  (case [cons y t ih] (intros gxz w h) (simp only [nat-fold]) (exact (ih gxz (demote w y) (i10-current-exempt-demote _ gkz w y h)))))

(a/theorem succ-run [w :- World, k :- CompRow, r2 :- RunRow]
  (=> (List.Mem k (:comps w)) (= (:idle k) false) (= (run-find w (:run k)) (Option.some RunRow r2)) (= (comp-run-ok k r2) true)
      (= (reach-mem (:run k) (retain-succ w (:id k))) true))
  (intros mk hi hf hok)
  (simp only [retain-succ])
  (apply rm-app-r) (apply rm-app-l)
  (apply (gather-mem CompRow (id-is comp-id (:id k)) (comp-contrib w) k (:run k) (:comps w) mk (Nat.beq_refl (:id k))))
  (simp only [comp-contrib hi])
  (apply rm-app-l)
  (simp only [comp-run-succ hf opt-test hok reach-mem Nat.beq_refl]))

;; a stray run is no current run of a computation outside the stray computations (a computation
;; kept by live keeps its current run live)
(a/theorem stray-pair [gxz :- (List Nat), gkz :- (List Nat), w :- World, r :- RunRow, q :- RunRow, k :- CompRow]
  (=> (= (tbl-all (ta-one (:comps w)) (:runs w)) true)
      (= (i10-current-exempt gxz gkz w) true) (List.Mem r (:runs w)) (= (run-stray (live-list w) r) true) (List.Mem q (:runs w)) (List.Mem k (:comps w))
      (= (nc-run (List.append Nat (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) gxz) gkz (:id r) (rs10 q) (cs10 k)) true))
  (intros hta h mr hr mq mk)
  (have hs := (i10-current-exempt-well-formed gxz gkz w h))
  (cases hx (Nat.beq (:id q) (:id r)))
  (case [false] (exact (nc-run-off _ gkz (:id r) (rs10 q) (cs10 k) hx)))
  (case [true]
    (cases hk (reach-mem (:id q) gkz))
    (case [true] (simp only [nc-run rs10 hk Bool.true_or Bool.or_true]))
    (case [false]
      (cases ho (Nat.beq (:of q) (:id k)))
      (case [false] (exact (nc-run-of _ gkz (:id r) (rs10 q) (cs10 k) ho)))
      (case [true]
        (cases hst (comp-stray (live-list w) k))
        (case [true]
          (have m1 := (scan-mem CompRow comp-id (comp-stray (live-list w)) k (:comps w) mk hst))
          (have b (= (reach-mem (:id (cs10 k)) (List.append Nat (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) gxz)) true))
          (exact (rm-app-l (:id k) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) gxz m1))
          (simp only [nc-run nc-cs b Bool.true_or Bool.or_true]))
        (case [false]
          (have pc := (rc-parts gxz gkz (i10-current-run-key q) (i10-current-comp-key k) (i10-current-exempt-rc gxz gkz w q k h mq mk) hk))
          (have le := (cur-le gxz (i10-current-run-key q) (i10-current-comp-key k) (And.left pc) ho))
          (cases he (Nat.beq (:epoch q) (:epoch k)))
          (case [false]
            (have lt (= (Nat.blt (:epoch (rs10 q)) (:epoch (cs10 k))) true))
            (simp only [Nat.blt_eq rs10 cs10]) (have z := (Nat.ne_of_beq_eq_false he)) (simp only [i10-current-run-key i10-current-comp-key] at le) (omega)
            (simp only [nc-run nc-cs lt Bool.true_or Bool.or_true]))
          (case [true]
            (have ce := (cur-eq gxz (i10-current-run-key q) (i10-current-comp-key k) (And.left pc) ho he))
            (have erun (= (:run k) (:id q))) (exact (And.left ce))
            (have hik (= (:idle k) false)) (exact (And.left (And.right ce)))
            (have hn2 (= (comp-normalized (live-list w) k) true))
            (cases hcn (comp-normalized (live-list w) k)) (simp [comp-stray hcn] at hst) (rfl)
            ;; C1 Q6: k is no tombstone, its alive run q (the stray run r) says so (ta-one)
            (have ua := (uniq-all RunRow run-id run-alive r (:runs w) (lit-runs-nodup w hs) mr (stray-run-alive _ r hr)))
            (have qa := (tbl-all-mem RunRow (same-id-then run-id (run-id r) run-alive) q (:runs w) ua mq))
            (have hx2 (= (Nat.beq (run-id q) (run-id r)) true)) (exact hx)
            (simp only [same-id-then hx2 Bool.not_true Bool.false_or] at qa)
            (have tq := (tbl-all-mem RunRow (ta-one (:comps w)) q (:runs w) hta mq))
            (simp only [ta-one qa Bool.not_true Bool.false_or] at tq)
            (have hkt := (untomb-mem (:comps w) k (:of q) tq mk (Eq.trans (beq-comm (:id k) (:of q)) ho)))
            (simp only [comp-normalized hik hkt Bool.false_or] at hn2)
            (cases hf (run-find w (:run k)))
            (case [none]
              (have z := (tbl-find-none-has RunRow run-id (:run k) (:runs w) hf))
              (have z2 (= (tbl-has run-id (:run k) (:runs w)) true)) (rw [erun])
              (have hm := (mem-ids-has RunRow run-id q (:runs w) mq)) (rw [nat-mem-ids] at hm) (exact hm)
              (rw [z2] at z) (cases z))
            (case [some r2]
              (have mr2 := (tbl-find-mem RunRow run-id (:run k) r2 (:runs w) hf))
              (have er2 (= (:id r2) (:run k))) (exact (tbl-find-id RunRow run-id (:run k) r2 (:runs w) hf))
              (have sq := (run-same-ep w q r2 hs mq mr2 (Eq.trans er2 erun)))
              (have hok (= (comp-run-ok k r2) true))
              (have e3 (= (Nat.beq (:epoch r2) (:epoch k)) true)) (rw [(And.left sq)]) (exact he)
              (simp only [comp-run-ok e3 Bool.true_or])
              (have hsucc := (succ-run w k r2 mk hik hf hok))
              (have hl := (live-close w (:id k) (:run k) hn2 hsucc))
              (rw [erun] at hl)
              (have eqr := (Nat.eq_of_beq_eq_true hx))
              (rw [eqr] at hl)
              (simp only [run-stray run-normalized in-live Bool.not_or Bool.and_eq_true] at hr)
              (have z := (And.right hr)) (simp only [in-live] at hl) (rw [hl] at z) (cases z))))))))

(a/theorem stray-ncw [gxz :- (List Nat), gkz :- (List Nat), w :- World, r :- RunRow]
  (=> (= (tbl-all (ta-one (:comps w)) (:runs w)) true)
      (= (i10-current-exempt gxz gkz w) true) (List.Mem r (:runs w)) (= (run-stray (live-list w) r) true)
      (= (ncw (List.append Nat (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) gxz) gkz (:id r) w) true))
  (intros hta h mr hr)
  (simp only [ncw])
  (exact (nqk-of-mem (nc-run (List.append Nat (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) gxz) gkz (:id r)) tt-c (:runs w) (:comps w)
           (fn [q :- RunRow, k :- CompRow, mq :- (List.Mem q (:runs w)), mk :- (List.Mem k (:comps w))] (stray-pair gxz gkz w r q k hta h mr hr mq mk))
           (fn [k :- CompRow, mk :- (List.Mem k (:comps w))] (Eq.refl true)))))

(tree/restate! G10 '[well-formed-detach])
(a/theorem i10-current-exempt-normalize-round [gxz :- (List Nat), gkz :- (List Nat), w :- World]
  (=> (= (tbl-all (ta-one (:comps w)) (:runs w)) true) (= (i10-current-exempt gxz gkz w) true) (= (i10-current-exempt gxz gkz (normalize-round w)) true))
  (intros hta h)
  (simp only [normalize-round normalize-round-with-live])
  (have h1 := (i10-current-exempt-gx-app gkz (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) gxz w h))
  (have hj (= (tbl-all (job-ok (List.append Nat (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) gxz) gkz w)
                       (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w)))) true))
  (rw [jl-cancel-jobs])
  (exact (scan-all RunRow run-id (run-stray (live-list w)) (fn [x :- Nat] (ncw (List.append Nat (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) gxz) gkz x w))
           (:runs w) (fn [r :- RunRow, m :- (List.Mem r (:runs w)), p :- (= (run-stray (live-list w) r) true)] (stray-ncw gxz gkz w r hta h m p))))
  (have h2 := (i10-current-exempt-run-cascade _ gkz w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w))) hj h1))
  (exact (i10-current-exempt-detach gxz gkz _ (i10-current-exempt-fold-demote gkz (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) gxz _ h2))))

;; C1 Q6: a round's stray runs are no current runs of tombstones (tombs-dormant 0: tombstones are dormant)
(a/theorem tombs-dormant-ta [w :- World] (=> (= (tombs-dormant 0 w) true) (= (tbl-all (ta-one (:comps w)) (:runs w)) true))
  (intro h) (exact (And.left (gtk-parts _ _ _ (tombs-dormant-gtk 0 w h)))))
(a/theorem i10-current-exempt-normalize-loop [gxz :- (List Nat), gkz :- (List Nat), fuel :- (List Nat)]
  (forall [w :- World] (=> (= (acts-alive w) true) (= (tombs-dormant 0 w) true) (= (i10-current-exempt gxz gkz w) true) (= (i10-current-exempt gxz gkz (normalize-loop fuel w)) true)))
  (induction fuel)
  (case' [cons h f ih])
  (case' [nil])
  (intros w ha hy hw) (simp only [normalize-loop]) (exact hw)
  (intros w ha hy hw)
  (cases hn (normalized w))
  (simp only [normalize-loop hn])
  (exact (ih (normalize-round w) (And.right (round-bound-round w (i10-current-exempt-well-formed gxz gkz w hw) ha)) (tombs-dormant-normalize-round 0 w (rfl) ha hy)
           (i10-current-exempt-normalize-round gxz gkz w (tombs-dormant-ta w hy) hw)))
  (simp only [normalize-loop hn]) (exact hw))
(a/theorem i10-current-exempt-normalize [gxz :- (List Nat), gkz :- (List Nat), w :- World]
  (=> (= (acts-alive w) true) (= (tombs-dormant 0 w) true) (= (i10-current-exempt gxz gkz w) true) (= (i10-current-exempt gxz gkz (normalize w)) true))
  (intros ha hy h)
  (have b := (round-bound-detach (alive-cnt w) (act-cnt w) w (round-bound-intro (alive-cnt w) (act-cnt w) w (i10-current-exempt-well-formed gxz gkz w h) ha (Nat.le_refl _) (Nat.le_refl _))))
  (exact (i10-current-exempt-normalize-loop gxz gkz (normalize-fuel (detach w)) (detach w) (And.left (And.right (round-bound-parts _ _ _ b))) (tombs-dormant-detach 0 w hy) (i10-current-exempt-detach gxz gkz w h))))

;; ===========================================================================
;; Part I. Rule R and the step; the literal I10 (one current run per computation)
;; ===========================================================================

(a/theorem i10-current-exempt-rule-r-round [gxz :- (List Nat), gkz :- (List Nat), w :- World]
  (=> (= (acts-alive w) true) (= (tombs-dormant 0 w) true) (= (i10-current-exempt gxz gkz w) true) (= (filter-safe (normalize w)) true) (= (i10-current-exempt gxz gkz (rule-r-round w)) true))
  (intros ha hy h hf)
  (simp only [rule-r-round])
  (rw [rule-r-filter-eq])
  (exact (i10-current-exempt-filter-world gxz gkz (normalize w) (keep-fn (normalize w)) (i10-current-exempt-normalize gxz gkz w ha hy h) hf)))

(a/theorem i10-current-exempt-rule-r-loop [gxz :- (List Nat), gkz :- (List Nat), fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (acts-alive w0) true) (= (tombs-dormant 0 w0) true) (= (i10-current-exempt gxz gkz w0) true) (= (rounds-safe-loop fuel w0) true)
                            (= (i10-current-exempt gxz gkz (rule-r-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 ha hy h hs) (simp only [rounds-safe-loop] at hs) (simp only [rule-r-loop]) (exact (i10-current-exempt-rule-r-round gxz gkz w0 ha hy h hs)))
  (case [cons x f ih]
    (intros w0 ha hy h hs)
    (simp only [rounds-safe-loop Bool.and_eq_true] at hs)
    (have h1 := (i10-current-exempt-rule-r-round gxz gkz w0 ha hy h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false]
      (simp only [ho] at hs) (simp only [rule-r-loop ho])
      (exact (ih (rule-r-round w0) (acts-alive-round w0 (i10-current-exempt-well-formed gxz gkz w0 h) ha) (tombs-dormant-rule-r-round w0 ha hy (And.left hs)) h1 (And.right hs))))
    (case [true] (simp only [rule-r-loop ho]) (exact h1))))

(a/theorem i10-current-exempt-rule-r [gxz :- (List Nat), gkz :- (List Nat), w :- World]
  (=> (= (acts-alive w) true) (= (tombs-dormant 0 w) true) (= (i10-current-exempt gxz gkz w) true) (= (rule-r-safe w) true) (= (i10-current-exempt gxz gkz (rule-r w)) true))
  (intros ha hy h hs)
  (simp only [rule-r-safe] at hs) (simp only [rule-r])
  (exact (i10-current-exempt-rule-r-loop gxz gkz (rule-r-fuel w) w ha hy h hs)))

(a/theorem step-i10-current [w :- World, it :- Item]
  (=> (= (chain-start w) true) (= (i10-current w) true) (= (rule-r-safe (:world (raw w it))) true) (= (i10-current (:world (world-step w it))) true))
  (intros hp h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true]
    (have e2 := (step-accepted w it ha)) (rw [e2])
    (have pb := (chain-start-parts w hp))
    (have q := (round-facts-parts w (And.right (And.right (And.right (And.right pb))))))
    (have hy := (tombs-dormant-raw 0 w it (And.left q) (And.right (And.right (And.right (And.right q))))))
    (exact (i10-current-exempt-rule-r (List.nil Nat) (List.nil Nat) (:world (raw w it)) (raw-acts-alive w it (And.left pb)) hy (i10-current-raw w it h) hs))))

(a/theorem i10-current-empty [] (= (i10-current empty-world) true) (rfl))

;; ---- the literal: every current run of C is C.run, so (unique run ids) at most one

(a/theorem count-zero10 [p :- (=> RunRow Bool), x :- Nat, rs :- (List RunRow)]
  (=> (= (nat-mem x (tbl-ids run-id rs)) false) (= (tbl-all (fn [r :- RunRow] (Bool.or (Bool.not (p r)) (Nat.beq (:id r) x))) rs) true)
      (= (tbl-count p rs) 0))
  (induction rs)
  (case [nil] (intros h1 h2) (simp only [tbl-count]))
  (case [cons hd t ih]
    (intros h1 h2)
    (cases hx (Nat.beq (run-id hd) x))
    (case [true] (simp [nat-mem tbl-ids hx] at h1))
    (case [false]
      (simp only [nat-mem tbl-ids hx] at h1)
      (simp only [tbl-all Bool.and_eq_true] at h2)
      (have hx2 (= (Nat.beq (:id hd) x) false)) (exact hx)
      (cases hp (p hd))
      (case [true] (have z := (And.left h2)) (simp only [hp hx2 Bool.not_true Bool.false_or] at z) (cases z))
      (case [false] (simp only [tbl-count hp]) (exact (ih h1 (And.right h2)))))))

(a/theorem count-le-one [p :- (=> RunRow Bool), x :- Nat, rs :- (List RunRow)]
  (=> (= (nat-nodup (tbl-ids run-id rs)) true) (= (tbl-all (fn [r :- RunRow] (Bool.or (Bool.not (p r)) (Nat.beq (:id r) x))) rs) true)
      (<= (tbl-count p rs) 1))
  (induction rs)
  (case [nil] (intros h1 h2) (simp only [tbl-count]) (omega))
  (case [cons hd t ih]
    (intros h1 h2)
    (simp only [tbl-ids nat-nodup Bool.and_eq_true] at h1)
    (simp only [tbl-all Bool.and_eq_true] at h2)
    (cases hp (p hd))
    (case [false] (simp only [tbl-count hp]) (exact (ih (And.right h1) (And.right h2))))
    (case [true]
      (have z := (And.left h2)) (simp only [hp Bool.not_true Bool.false_or] at z)
      (have e := (Nat.eq_of_beq_eq_true z))
      (have hn := (bnot-true _ (And.left h1)))
      (have hn2 (= (nat-mem x (tbl-ids run-id t)) false)) (rw [← e]) (exact hn)
      (have c0 := (count-zero10 p x t hn2 (And.right h2)))
      (simp only [tbl-count hp c0]) (omega))))

(a/theorem i10-current-current [w :- World, c :- CompRow, r :- RunRow]
  (=> (= (i10-current w) true) (List.Mem c (:comps w)) (List.Mem r (:runs w))
      (= (Bool.or (Bool.not (current-of c r)) (Nat.beq (:id r) (:run c))) true))
  (intros h mc mr)
  (cases hcur (current-of c r))
  (case [false] (simp only [Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [current-of Bool.and_eq_true] at hcur)
    (have hk0 (= (reach-mem (:id (i10-current-run-key r)) (List.nil Nat)) false)) (rfl)
    (have pc := (rc-parts _ _ (i10-current-run-key r) (i10-current-comp-key c) (i10-current-exempt-rc _ _ w r c h mr mc) hk0))
    (have ce := (cur-eq _ (i10-current-run-key r) (i10-current-comp-key c) (And.left pc) (And.left hcur) (And.right hcur)))
    (have e (= (:run c) (:id r))) (exact (And.left ce))
    (have b (= (Nat.beq (:id r) (:run c)) true)) (rw [e]) (exact (Nat.beq_refl _))
    (simp only [b Bool.or_true])))

(a/theorem i10-current-lit-i10 [w :- World] (=> (= (i10-current w) true) (= (lit-i10-current w) true))
  (intro h)
  (have hs := (i10-current-exempt-well-formed _ _ w h))
  (simp only [lit-i10-current])
  (apply (all-of-mem CompRow _ (:comps w)))
  (intros c mc)
  (simp only [one-current Nat.ble_eq])
  (exact (count-le-one (current-of c) (:run c) (:runs w) (lit-runs-nodup w hs)
           (all-of-mem RunRow _ (:runs w) (fn [r :- RunRow, mr :- (List.Mem r (:runs w))] (i10-current-current w c r h mc mr))))))

(a/theorem step-lit-i10-current [w :- World, it :- Item]
  (=> (= (chain-start w) true) (= (i10-current w) true) (= (rule-r-safe (:world (raw w it))) true) (= (lit-i10-current (:world (world-step w it))) true))
  (intros hp h hs) (exact (i10-current-lit-i10 _ (step-i10-current w it hp h hs))))

;; ---- the combined bundle: P3's chain-start and i10-current

(a/defn chain-to-i10-current [w :- World] Bool (Bool.and (chain-start w) (i10-current w)))
(a/theorem chain-to-i10-current-parts [w :- World] (=> (= (chain-to-i10-current w) true) (And (= (chain-start w) true) (= (i10-current w) true)))
  (intro h) (simp only [chain-to-i10-current Bool.and_eq_true] at h) (exact h))
(a/theorem chain-to-i10-current-empty [] (= (chain-to-i10-current empty-world) true) (rfl))
(a/theorem step-chain-to-i10-current [w :- World, it :- Item] (=> (= (chain-to-i10-current w) true) (= (chain-to-i10-current (:world (world-step w it))) true))
  (intro h)
  (have p := (chain-to-i10-current-parts w h))
  (have a1 := (step-chain-start w it (And.left p)))
  (have a2 := (step-i10-current w it (And.left p) (And.right p) (step-rule-r-safe w it (And.left p))))
  (simp only [chain-to-i10-current a1 a2 Bool.and_self]))
(a/theorem step-lit-i10-current-total [w :- World, it :- Item]
  (=> (= (chain-to-i10-current w) true) (= (lit-i10-current (:world (world-step w it))) true))
  (intro h) (exact (i10-current-lit-i10 _ (And.right (chain-to-i10-current-parts _ (step-chain-to-i10-current w it h))))))
(a/theorem chain-to-i10-current-lit-i10 [w :- World] (=> (= (chain-to-i10-current w) true) (= (lit-i10-current w) true))
  (intro h) (exact (i10-current-lit-i10 w (And.right (chain-to-i10-current-parts w h)))))
