(ns spindel.v2.retain
  "Retention (spec v1.5.1 §3): roots, retention edges, `live`, storage, the cleanup table's
  rows, §3.4 admissions and the Rule R filter (§3.3 step 3), kernel-checked (Init only).

  A node is a global row id (notes/PLAN.md). `retain-succ w x` collects the §3.2
  successors contributed by EVERY row whose id is x, in every table (with unique ids that
  is the dispatch on the one table holding x; without them nothing breaks). Each table's
  part is `tbl-gather (id-is <p>-id x) <p>-contrib rows`.

  §3.2 as modelled (one line per table; `nz n` = [n] unless n = 0):
    scope S      parent (nz); every task K with K.owner = S that runs (K.run /= 0 and the
                 run row K.run exists with act /= done); every fork marker with owner = S
    run R        only when R.act /= done: scope (nz); body entity `of` (nz); every activation
                 with run = R; R.resources; every savepoint edge whose creditor is an
                 activation of R. No extra reason for its creations (Z#2).
    comp C       only when not idle: C.run when its row exists and (it is current, i.e.
                 R.epoch = C.epoch, or C is needs-run and R.act /= done); every dep edge with
                 creditor C; basis ids; adoption-basis ids; the debtors of the adoption
                 baselines (Z#21)
    task K       K.run (nz)
    act A        the edges of A.members (Z#7: members are (edge, slot index) pairs)
    edge E       E.debtor (nz)
    pub P        P.edge (nz), unconditionally (Z#4)
    source, resource, fork marker: none
  Readings:
    1. Z#1: `C.run` is the latest run; needs-run iff done-epoch /= epoch and (C.run = none
       or C.run is not current). The current run and the re-entry predecessor are both
       C.run, so one guarded lookup of C.run's row covers both.
    2. \"the task runs it owns\": the scope retains the TASK (task -> run is its own edge),
       while the task runs. Same closure as scope -> K.run -> body entity K.
    3. Z#2: a run keeps no reason for what it created; finished children of a loop task go
       unless a handle admits them (§3.4).
    4. Savepoint edges are retained explicitly (creditor activation of R) and also as
       members of that activation.
    5. 0 is \"none\" and never a successor, except through lists (members, resources,
       basis) that hold 0 only in a malformed world.

  Roots (§3.1): root-kind scopes (Z#56: also after release-world, the root scope is never
  removed; T21 revokes the host's roots below); pins (Z#16: a multiset, a pinned id
  occurs count times); observe edges and host-wait edges (root 7, Z#27: `is-observe` is
  `host-cred`, kind wait with creditor 0 included); open explicit
  scopes; pending-activation (nz); publications with handles > 0 whose edge (/= 0) exists
  and is armed (root 6, Z#4).

  `live w` = `reach-run-l (live-fuel-list w) (retain-succ w) (roots w)`, the list-fuel
  worklist (= reach-run at the list's length, reach-run-l-eq); the fuel is 1 + |roots| + the
  sum of |retain-succ w y| over `all-ids w`, always enough (`live-converged-all`, P1; the
  oracle still asserts `converged`). `in-live w x`.

  Storage (X#7, Z#3): `storage w` = the refs of the finalizers of the runs in live(W); kept
  by the filter, not expanded, not in live. (Refs are sources by Z#3; not checked here.)

  Cleanup table (A#2): `cleanup-rows w` = for every entry: its run, its `rows` list (the
  scope subtree and owned rows are recorded there by the transitions), and from the run
  row (when present) its scope, body entity, resources and finalizer refs, closed upward under
  the scopes' CURRENT parent fields (`anc-close`: the run scope's chain of Z#38/Z#52, read at
  every Rule R pass, not stored; `scope-anc-filter`/`anc-close-filter`: the filter keeps it).

  §3.4 `admitted w y` (Z#2, Z#5): a computation with handles > 0 that is idle or fresh
  (done-epoch = none) (policy: keep while handles > 0; it must go at 0, may go earlier, we
  never drop by policy); every source with handles > 0; a completed task (result tag /=
  none) with handles > 0; a publication with handles > 0. Field trimming (an idle
  computation keeps only some fields) is not modelled.

  `keep-fn w y` = in-live | cleanup-rows | admitted | storage (I3 of v1.5.1: live ∪ storage
  ∪ cleanup ∪ admitted). `rule-r-filter w` removes
  every row (all id-keyed tables) whose id fails keep-fn; cleanup, pins and the scalar
  fields are unchanged. Only the filter: normalization (cancel/demote/detach) is step.clj.

  Theorems:
    reach-mem-nat-mem    reach-mem x xs = nat-mem x xs
    in-live-iff          converged -> (in-live w x = true <-> Reach (retain-succ w) (roots w) x)
    succ-filter-agree    for any K that contains a succ-closed L: L x ->
                         retain-succ (filter-world K w) x = retain-succ w x
    roots-filter         roots (filter-world K w) = roots w when K holds on the roots
    live-filter-reach    converged w -> Reach in the filtered world <-> Reach in w
    in-live-filter       converged w, converged w' -> in-live w' y = in-live w y
    keep-filter          converged w, converged w' -> keep-fn w' y = keep-fn w y
    rule-r-i3            converged w, converged w' -> every id of w' passes keep-fn w'
    rule-r-live          converged w, converged w' -> in-live w' y = in-live w y
    rule-r-i3            converged w, converged w' -> tbl-all (keep-fn w') (all-ids w') = true
    rule-r-idem          converged w, converged w' -> rule-r-filter w' = w'
  (w' = rule-r-filter w; converged = live-converged.) No normalization hypothesis is
  needed: the filter keeps every live row unchanged, and a live node's successors only read
  rows that are live or whose absence cannot change the answer. Every scan returns
  successors (live, so kept); the three guards that read another row (task-running reads
  K.run's row, sp-edge-of reads the creditor activation, comp-run-ok reads C.run's row) are
  true only when that row's id is itself a successor, and a filtered-out row makes the guard
  false in both worlds (guard-keep). `converged w'` is a hypothesis because fuel sufficiency
  is not proved; reach-run-frame shows the worklist runs identically at equal fuel."
  (:require [ansatz.core :as a]
            [spindel.v2.reach :refer :all]
            [spindel.v2.state :refer :all]))

;; ---------------------------------------------------------------------------
;; Generic table helpers

;; keep the rows whose id passes K
(a/defn tbl-keep [A :- Type :implicit, K :- (=> Nat Bool), idf :- (=> A Nat), xs :- (List A)] (List A)
  (match xs [nil (List.nil A)]
         [(cons h t) (if (K (idf h)) (List.cons A h (tbl-keep K idf t)) (tbl-keep K idf t))]))

;; concatenate f r over the rows r with p r
(a/defn tbl-gather [A :- Type :implicit, p :- (=> A Bool), f :- (=> A (List Nat)), xs :- (List A)] (List Nat)
  (match xs [nil (List.nil Nat)]
         [(cons h t) (if (p h) (List.append Nat (f h) (tbl-gather p f t)) (tbl-gather p f t))]))

;; ids of the rows with p r
(a/defn tbl-scan [A :- Type :implicit, idf :- (=> A Nat), p :- (=> A Bool), xs :- (List A)] (List Nat)
  (match xs [nil (List.nil Nat)]
         [(cons h t) (if (p h) (List.cons Nat (idf h) (tbl-scan idf p t)) (tbl-scan idf p t))]))

(a/defn tbl-any [A :- Type :implicit, p :- (=> A Bool), xs :- (List A)] Bool
  (match xs [nil false] [(cons h t) (Bool.or (p h) (tbl-any p t))]))

(a/defn opt-test [A :- Type :implicit, g :- (=> A Bool), o :- (Option A)] Bool
  (match o [none false] [(some r) (g r)]))

(a/defn id-is [A :- Type :implicit, idf :- (=> A Nat), x :- Nat, r :- A] Bool (Nat.beq (idf r) x))

(a/defn nz [n :- Nat] (List Nat)
  (if (Nat.beq n 0) (List.nil Nat) (List.cons Nat n (List.nil Nat))))

(a/defn created-ids [xs :- (List Created)] (List Nat)
  (match xs [nil (List.nil Nat)] [(cons h t) (List.cons Nat (:id h) (created-ids t))]))

(a/defn fin-refs [fs :- (List Finalizer)] (List Nat)
  (match fs [nil (List.nil Nat)] [(cons h t) (List.append Nat (:refs h) (fin-refs t))]))

;; ---------------------------------------------------------------------------
;; §3.2 retention edges

(a/defn run-alive [r :- RunRow] Bool (Bool.not (Nat.beq (:act r) act-done)))

;; task K runs: K.run /= 0 and its run row exists with act /= done
(a/defn task-running [w :- World, t :- TaskRow] Bool
  (Bool.and (Bool.not (Nat.beq (:run t) 0)) (opt-test run-alive (run-find w (:run t)))))
(a/defn owned-running-task [w :- World, s :- Nat, t :- TaskRow] Bool
  (Bool.and (Nat.beq (:owner t) s) (task-running w t)))
(a/defn owned-fork [s :- Nat, f :- ForkRow] Bool (Nat.beq (:owner f) s))

(a/defn scope-contrib [w :- World, s :- ScopeRow] (List Nat)
  (List.append Nat (nz (:parent s))
    (List.append Nat (tbl-scan task-id (owned-running-task w (:id s)) (:tasks w))
                     (tbl-scan fork-id (owned-fork (:id s)) (:forks w)))))

(a/defn act-of-run [x :- Nat, a :- ActRow] Bool (Nat.beq (:run a) x))
(a/defn sp-edge-of [w :- World, x :- Nat, e :- EdgeRow] Bool
  (Bool.and (Nat.beq (:kind e) ek-savepoint) (opt-test (act-of-run x) (act-find w (:creditor e)))))

(a/defn run-contrib [w :- World, r :- RunRow] (List Nat)
  (if (run-alive r)
    (List.append Nat (nz (:scope r))
    (List.append Nat (nz (:of r))
    (List.append Nat (tbl-scan act-id (act-of-run (:id r)) (:acts w))
    (List.append Nat (:resources r)
                     (tbl-scan edge-id (sp-edge-of w (:id r)) (:edges w))))))
    (List.nil Nat)))

;; the run C.run is retained: current, or C needs a run and it is not done (reading 1)
(a/defn comp-run-ok [c :- CompRow, r :- RunRow] Bool
  (Bool.or (Nat.beq (:epoch r) (:epoch c))
           (Bool.and (Bool.not (Nat.beq (:done-epoch c) (:epoch c))) (run-alive r))))
(a/defn comp-run-succ [w :- World, c :- CompRow] (List Nat)
  (if (opt-test (comp-run-ok c) (run-find w (:run c)))
    (List.cons Nat (:run c) (List.nil Nat))
    (List.nil Nat)))
(a/defn dep-of [x :- Nat, e :- EdgeRow] Bool
  (Bool.and (Nat.beq (:kind e) ek-dep) (Nat.beq (:creditor e) x)))

;; the debtors of the adoption baselines (Z#21)
(a/defn base-debtors [xs :- (List AdoptBase)] (List Nat)
  (match xs [nil (List.nil Nat)] [(cons h t) (List.cons Nat (:source h) (base-debtors t))]))

(a/defn comp-contrib [w :- World, c :- CompRow] (List Nat)
  (if (:idle c)
    (List.nil Nat)
    (List.append Nat (comp-run-succ w c)
    (List.append Nat (tbl-scan edge-id (dep-of (:id c)) (:edges w))
    (List.append Nat (created-ids (:basis c))
    (List.append Nat (created-ids (:adopt-basis c)) (base-debtors (:adopt-baselines c))))))))

(a/defn task-contrib [t :- TaskRow] (List Nat) (nz (:run t)))
(a/defn act-contrib [x :- ActRow] (List Nat) (member-edges (:members x)))
(a/defn edge-contrib [e :- EdgeRow] (List Nat) (nz (:debtor e)))
(a/defn pub-contrib [p :- PubRow] (List Nat) (nz (:edge p)))

(a/defn retain-succ [w :- World, x :- Nat] (List Nat)
  (List.append Nat (tbl-gather (id-is scope-id x) (scope-contrib w) (:scopes w))
  (List.append Nat (tbl-gather (id-is comp-id x) (comp-contrib w) (:comps w))
  (List.append Nat (tbl-gather (id-is task-id x) task-contrib (:tasks w))
  (List.append Nat (tbl-gather (id-is run-id x) (run-contrib w) (:runs w))
  (List.append Nat (tbl-gather (id-is act-id x) act-contrib (:acts w))
  (List.append Nat (tbl-gather (id-is edge-id x) edge-contrib (:edges w))
                   (tbl-gather (id-is pub-id x) pub-contrib (:pubs w)))))))))

;; ---------------------------------------------------------------------------
;; §3.1 roots, live

(a/defn is-root-scope [s :- ScopeRow] Bool (Nat.beq (:kind s) scope-root))
(a/defn is-open-explicit [s :- ScopeRow] Bool (Bool.and (Nat.beq (:kind s) scope-explicit) (:open s)))
;; observe edges and pending host-wait edges (root 7, Z#27): the edges whose creditor is the host
(a/defn is-observe [e :- EdgeRow] Bool (host-cred e))
(a/defn edge-armed [e :- EdgeRow] Bool (Nat.beq (:phase e) ph-armed))
;; root 6 (Z#4): handles > 0 and its edge (/= 0) exists and is armed
(a/defn armed-pub [w :- World, p :- PubRow] Bool
  (Bool.and (Nat.blt 0 (:handles p))
            (Bool.and (Bool.not (Nat.beq (:edge p) 0)) (opt-test edge-armed (edge-find w (:edge p))))))

(a/defn roots [w :- World] (List Nat)
  (List.append Nat (tbl-scan scope-id is-root-scope (:scopes w))
  (List.append Nat (:pins w)
  (List.append Nat (tbl-scan edge-id is-observe (:edges w))
  (List.append Nat (tbl-scan scope-id is-open-explicit (:scopes w))
  (List.append Nat (nz (:pending-act w))
                   (tbl-scan pub-id (armed-pub w) (:pubs w))))))))

(a/defn succ-all [w :- World, ys :- (List Nat)] (List Nat)
  (match ys [nil (List.nil Nat)] [(cons h t) (List.append Nat (retain-succ w h) (succ-all w t))]))

;; One list cell per unit of fuel: 1 + |roots| + the sum of |retain-succ w y| over all ids.
;; A list, not a Nat: the compiled Nat-fuel worklist is too slow (reach-closure-l).
(a/defn live-fuel-list [w :- World] (List Nat)
  (List.cons Nat 0 (List.append Nat (roots w) (succ-all w (all-ids w)))))

(a/defn live [w :- World] ReachResult
  (reach-run-l (live-fuel-list w) (retain-succ w) (roots w)))
(a/defn live-list [w :- World] (List Nat) (:visited (live w)))
(a/defn live-converged [w :- World] Bool (:converged (live w)))
(a/defn in-live [w :- World, x :- Nat] Bool (reach-mem x (live-list w)))

;; ---------------------------------------------------------------------------
;; Cleanup table rows (A#2), finalizer storage, §3.4 admissions

(a/defn run-stored [r :- RunRow] (List Nat)
  (List.cons Nat (:scope r) (List.cons Nat (:of r)
    (List.append Nat (:resources r) (fin-refs (:finalizers r))))))
;; Z#38/Z#52: cleanup[R] retains its run scope's CURRENT ancestor chain, followed through the
;; scopes' parent fields when the keep set is computed (each Rule R pass), not stored with the
;; entry, so a detach that re-parents a scope of the chain moves the retention to the new parent.
;; Worklist over the parent links with fuel 2 + #scopes (one successor per scope).
(a/defn scope-up [w :- World, x :- Nat] (List Nat)
  (match (scope-find w x) [none (List.nil Nat)] [(some s) (nz (:parent s))]))
(a/defn scope-anc-fuel [w :- World] (List Nat)
  (List.cons Nat 0 (List.cons Nat 0 (tbl-ids scope-id (:scopes w)))))
(a/defn scope-ancestors [w :- World, s :- Nat] (List Nat)
  (:visited (reach-run-l (scope-anc-fuel w) (scope-up w) (scope-up w s))))
;; the rows an entry retains are closed upward: every retained scope keeps its current chain (the
;; run scope's chain of Z#52; a scope of the stored subtree has its parent in the subtree or is the
;; run scope, so in reachable worlds this adds nothing else; ids that are not scopes add nothing)
(a/defn anc-all [w :- World, xs :- (List Nat)] (List Nat)
  (match xs [nil (List.nil Nat)] [(cons h t) (List.append Nat (scope-ancestors w h) (anc-all w t))]))
(a/defn anc-close [w :- World, xs :- (List Nat)] (List Nat) (List.append Nat xs (anc-all w xs)))
(a/defn opt-rows [o :- (Option RunRow)] (List Nat)
  (match o [none (List.nil Nat)] [(some r) (run-stored r)]))
(a/defn cleanup-base [w :- World, c :- CleanupRow] (List Nat)
  (List.cons Nat (:run c) (List.append Nat (:rows c) (opt-rows (run-find w (:run c))))))
(a/defn cleanup-contrib [w :- World, c :- CleanupRow] (List Nat) (anc-close w (cleanup-base w c)))
(a/defn cleanup-rows-in [w :- World, cs :- (List CleanupRow)] (List Nat)
  (match cs [nil (List.nil Nat)]
         [(cons h t) (List.append Nat (cleanup-contrib w h) (cleanup-rows-in w t))]))
(a/defn cleanup-rows [w :- World] (List Nat) (cleanup-rows-in w (:cleanup w)))

;; storage (X#7, Z#3): the finalizer refs of the runs in live
(a/defn stored-run [lv :- (List Nat), r :- RunRow] Bool (reach-mem (:id r) lv))
(a/defn run-refs [r :- RunRow] (List Nat) (fin-refs (:finalizers r)))
(a/defn storage-gather [w :- World, lv :- (List Nat)] (List Nat)
  (tbl-gather (stored-run lv) run-refs (:runs w)))
;; closed upward like the cleanup rows (refs are sources by Z#3 and layer 1 registers none, so
;; this adds nothing in practice; it keeps every retained scope's parent, I1)
(a/defn storage-with [w :- World, lv :- (List Nat)] (List Nat) (anc-close w (storage-gather w lv)))
(a/defn storage [w :- World] (List Nat) (storage-with w (live-list w)))

(a/defn adm-comp [y :- Nat, c :- CompRow] Bool
  (Bool.and (Nat.beq (:id c) y)
            (Bool.and (Bool.or (:idle c) (Nat.beq (:done-epoch c) 0)) (Nat.blt 0 (:handles c)))))
(a/defn adm-source [y :- Nat, x :- SourceRow] Bool
  (Bool.and (Nat.beq (:id x) y) (Nat.blt 0 (:handles x))))
(a/defn adm-task [y :- Nat, t :- TaskRow] Bool
  (Bool.and (Nat.beq (:id t) y)
            (Bool.and (Bool.not (Nat.beq (:tag (:result t)) res-none)) (Nat.blt 0 (:handles t)))))
(a/defn adm-pub [y :- Nat, p :- PubRow] Bool
  (Bool.and (Nat.beq (:id p) y) (Nat.blt 0 (:handles p))))

(a/defn admitted [w :- World, y :- Nat] Bool
  (Bool.or (tbl-any (adm-comp y) (:comps w))
  (Bool.or (tbl-any (adm-source y) (:sources w))
  (Bool.or (tbl-any (adm-task y) (:tasks w))
           (tbl-any (adm-pub y) (:pubs w))))))

;; ---------------------------------------------------------------------------
;; Rule R step 3: the filter

(a/defn keep-with [w :- World, lv :- (List Nat), cl :- (List Nat), st :- (List Nat), y :- Nat] Bool
  (Bool.or (reach-mem y lv) (Bool.or (reach-mem y cl) (Bool.or (admitted w y) (reach-mem y st)))))

(a/defn keep-fn [w :- World, y :- Nat] Bool
  (keep-with w (live-list w) (cleanup-rows w) (storage w) y))

(a/defn filter-world [K :- (=> Nat Bool), w :- World] World
  (World.mk (tbl-keep K scope-id (:scopes w)) (tbl-keep K comp-id (:comps w))
            (tbl-keep K task-id (:tasks w)) (tbl-keep K run-id (:runs w))
            (tbl-keep K source-id (:sources w)) (tbl-keep K edge-id (:edges w))
            (tbl-keep K act-id (:acts w)) (tbl-keep K resource-id (:res w))
            (:cleanup w) (tbl-keep K pub-id (:pubs w)) (:pins w) (tbl-keep K fork-id (:forks w))
            (:pending-act w) (:released w) (:next-id w)))

;; live is computed once and shared by the keep set
(a/defn rule-r-filter-lv [w :- World, lv :- (List Nat)] World
  (filter-world (keep-with w lv (cleanup-rows w) (storage-with w lv)) w))
(a/defn rule-r-filter [w :- World] World (rule-r-filter-lv w (live-list w)))

;; ---------------------------------------------------------------------------
;; Generic lemmas: one membership function, filtered tables (keep), gather/scan/any

(a/theorem reach-mem-nat-mem [x :- Nat, xs :- (List Nat)]
  (= (reach-mem x xs) (nat-mem x xs))
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (simp [reach-mem nat-mem])
  (simp only [reach-mem nat-mem (beq-comm x h) ih]))

(a/theorem keep-find-in [A :- Type, K :- (=> Nat Bool), idf :- (=> A Nat), y :- Nat, xs :- (List A)]
  (=> (= (K y) true) (= (tbl-find idf y (tbl-keep K idf xs)) (tbl-find idf y xs)))
  (intro hk)
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (simp [tbl-find tbl-keep])
  (cases hb (Nat.beq (idf h) y))
  (case [false] (cases hh (K (idf h))) (all_goals (simp [tbl-keep tbl-find hh hb ih])))
  (case [true]
    (have he (= (idf h) y)) (exact (Nat.eq_of_beq_eq_true hb))
    (have hh (= (K (idf h)) true)) (rw [he]) (exact hk)
    (simp [tbl-keep tbl-find hh hb])))

(a/theorem keep-find-out [A :- Type, K :- (=> Nat Bool), idf :- (=> A Nat), y :- Nat, xs :- (List A)]
  (=> (= (K y) false) (= (tbl-find idf y (tbl-keep K idf xs)) (Option.none A)))
  (intro hk)
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (simp [tbl-find tbl-keep])
  (cases hh (K (idf h)))
  (case [false] (simp [tbl-keep hh ih]))
  (case [true]
    (cases hb (Nat.beq (idf h) y))
    (case [false] (simp [tbl-keep tbl-find hh hb ih]))
    (case [true]
      (have he (= (idf h) y)) (exact (Nat.eq_of_beq_eq_true hb))
      (rw [he] at hh) (rw [hh] at hk) (simp at hk))))

(a/theorem guard-keep [A :- Type, K :- (=> Nat Bool), idf :- (=> A Nat), g :- (=> A Bool), y :- Nat, xs :- (List A)]
  (=> (=> (= (opt-test g (tbl-find idf y xs)) true) (= (K y) true))
      (= (opt-test g (tbl-find idf y (tbl-keep K idf xs))) (opt-test g (tbl-find idf y xs))))
  (intro h)
  (cases hk (K y))
  (case [true] (exact (congrArg (opt-test g) (keep-find-in A K idf y xs hk))))
  (case [false]
    (have he := (keep-find-out A K idf y xs hk))
    (simp only [he])
    (cases ho (opt-test g (tbl-find idf y xs)))
    (case [false] (simp [opt-test]))
    (case [true] (have hc := (h ho)) (rw [hk] at hc) (simp at hc))))

(a/theorem gather-mem [A :- Type, p :- (=> A Bool), f :- (=> A (List Nat)), r :- A, y :- Nat, xs :- (List A)]
  (=> (List.Mem r xs) (= (p r) true) (= (reach-mem y (f r)) true)
      (= (reach-mem y (tbl-gather p f xs)) true))
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (intro hm) (cases hm)
  (intros hm hp hy)
  (cases hm)
  (simp [tbl-gather hp reach-mem-append reach-mem-app hy])
  (rename_i hm2)
  (have ih2 := (ih hm2 hp hy))
  (cases hph (p h))
  (all_goals (simp [tbl-gather hph reach-mem-append reach-mem-app ih2])))

(a/theorem gather-keep [A :- Type, K :- (=> Nat Bool), idf :- (=> A Nat), p :- (=> A Bool), p2 :- (=> A Bool),
                        f :- (=> A (List Nat)), f2 :- (=> A (List Nat)), xs :- (List A)]
  (=> (forall [r :- A] (=> (List.Mem r xs) (= (p r) true) (= (K (idf r)) true)))
      (forall [r :- A] (=> (List.Mem r xs) (= (K (idf r)) true) (= (p2 r) (p r))))
      (forall [r :- A] (=> (List.Mem r xs) (= (p r) true) (= (f2 r) (f r))))
      (= (tbl-gather p2 f2 (tbl-keep K idf xs)) (tbl-gather p f xs)))
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (intros h1 h2 h3) (simp [tbl-keep tbl-gather])
  (intros h1 h2 h3)
  (have ih2 (= (tbl-gather p2 f2 (tbl-keep K idf t)) (tbl-gather p f t)))
  (apply ih)
  (intros r hr hp) (exact (h1 r (List.Mem.tail h hr) hp))
  (intros r hr hk) (exact (h2 r (List.Mem.tail h hr) hk))
  (intros r hr hp) (exact (h3 r (List.Mem.tail h hr) hp))
  (cases hp (p h))
  (case [false]
    (cases hk (K (idf h)))
    (case [false] (simp [tbl-keep tbl-gather hk hp ih2]))
    (case [true]
      (have hp2 (= (p2 h) (p h))) (exact (h2 h (List.Mem.head t) hk))
      (rw [hp] at hp2)
      (simp [tbl-keep tbl-gather hk hp hp2 ih2])))
  (case [true]
    (have hk (= (K (idf h)) true)) (exact (h1 h (List.Mem.head t) hp))
    (have hp2 (= (p2 h) (p h))) (exact (h2 h (List.Mem.head t) hk))
    (rw [hp] at hp2)
    (have hf (= (f2 h) (f h))) (exact (h3 h (List.Mem.head t) hp))
    (simp [tbl-keep tbl-gather hk hp hp2 hf ih2])))

(a/theorem scan-keep [A :- Type, K :- (=> Nat Bool), idf :- (=> A Nat), p :- (=> A Bool), p2 :- (=> A Bool), xs :- (List A)]
  (=> (forall [r :- A] (=> (List.Mem r xs) (= (p r) true) (= (K (idf r)) true)))
      (forall [r :- A] (=> (List.Mem r xs) (= (K (idf r)) true) (= (p2 r) (p r))))
      (= (tbl-scan idf p2 (tbl-keep K idf xs)) (tbl-scan idf p xs)))
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (intros h1 h2) (simp [tbl-keep tbl-scan])
  (intros h1 h2)
  (have ih2 (= (tbl-scan idf p2 (tbl-keep K idf t)) (tbl-scan idf p t)))
  (apply ih)
  (intros r hr hp) (exact (h1 r (List.Mem.tail h hr) hp))
  (intros r hr hk) (exact (h2 r (List.Mem.tail h hr) hk))
  (cases hp (p h))
  (case [false]
    (cases hk (K (idf h)))
    (case [false] (simp [tbl-keep tbl-scan hk hp ih2]))
    (case [true]
      (have hp2 (= (p2 h) (p h))) (exact (h2 h (List.Mem.head t) hk))
      (rw [hp] at hp2)
      (simp [tbl-keep tbl-scan hk hp hp2 ih2])))
  (case [true]
    (have hk (= (K (idf h)) true)) (exact (h1 h (List.Mem.head t) hp))
    (have hp2 (= (p2 h) (p h))) (exact (h2 h (List.Mem.head t) hk))
    (rw [hp] at hp2)
    (simp [tbl-keep tbl-scan hk hp hp2 ih2])))

(a/theorem scan-mem [A :- Type, idf :- (=> A Nat), p :- (=> A Bool), r :- A, xs :- (List A)]
  (=> (List.Mem r xs) (= (p r) true) (= (reach-mem (idf r) (tbl-scan idf p xs)) true))
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (intro hm) (cases hm)
  (intros hm hp)
  (cases hm)
  (simp [tbl-scan hp reach-mem-cons Nat.beq_refl])
  (rename_i hm2)
  (have ih2 := (ih hm2 hp))
  (cases hph (p h))
  (all_goals (simp [tbl-scan hph reach-mem-cons ih2])))

(a/theorem any-keep-id [A :- Type, K :- (=> Nat Bool), idf :- (=> A Nat), p :- (=> A Bool), y :- Nat, xs :- (List A)]
  (=> (forall [r :- A] (=> (= (p r) true) (= (idf r) y)))
      (= (tbl-any p (tbl-keep K idf xs)) (Bool.and (K y) (tbl-any p xs))))
  (intro hid)
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (simp [tbl-keep tbl-any])
  (cases hp (p h))
  (case [false] (cases hk (K (idf h))) (all_goals (simp [tbl-keep tbl-any hk hp ih])))
  (case [true]
    (have he (= (idf h) y)) (exact (hid h hp))
    (cases hk (K y))
    (case [true] (have hk2 (= (K (idf h)) true)) (rw [he]) (exact hk)
      (simp [tbl-keep tbl-any hk hk2 hp]))
    (case [false] (have hk2 (= (K (idf h)) false)) (rw [he]) (exact hk)
      (simp [tbl-keep tbl-any hk hk2 hp ih]))))

(a/theorem keep-keep [A :- Type, K :- (=> Nat Bool), K2 :- (=> Nat Bool), idf :- (=> A Nat), xs :- (List A)]
  (=> (forall [y :- Nat] (=> (= (K y) true) (= (K2 y) true)))
      (= (tbl-keep K2 idf (tbl-keep K idf xs)) (tbl-keep K idf xs)))
  (intro hk)
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (simp [tbl-keep])
  (cases h1 (K (idf h)))
  (case [false] (simp [tbl-keep h1 ih]))
  (case [true] (simp [tbl-keep h1 (hk (idf h) h1) ih])))

(a/theorem keep-all-ids [A :- Type, K :- (=> Nat Bool), P :- (=> Nat Bool), idf :- (=> A Nat), xs :- (List A)]
  (=> (forall [y :- Nat] (=> (= (K y) true) (= (P y) true)))
      (= (tbl-all P (tbl-ids idf (tbl-keep K idf xs))) true))
  (intro hk)
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (simp [tbl-keep tbl-ids tbl-all])
  (cases h1 (K (idf h)))
  (case [false] (simp [tbl-keep h1 ih]))
  (case [true] (simp [tbl-keep tbl-ids tbl-all h1 (hk (idf h) h1) ih])))

(a/theorem gather-id-keep [A :- Type, K :- (=> Nat Bool), idf :- (=> A Nat), x :- Nat,
                           f :- (=> A (List Nat)), f2 :- (=> A (List Nat)), xs :- (List A)]
  (=> (= (K x) true)
      (forall [r :- A] (=> (List.Mem r xs) (= (idf r) x) (= (f2 r) (f r))))
      (= (tbl-gather (id-is idf x) f2 (tbl-keep K idf xs)) (tbl-gather (id-is idf x) f xs)))
  (intro hx hf)
  (apply gather-keep)
  (intro r hr hp)
  (have he (= (idf r) x)) (exact (Nat.eq_of_beq_eq_true hp))
  (rw [he]) (exact hx)
  (intro r hr hk) (rfl)
  (intro r hr hp)
  (exact (hf r hr (Nat.eq_of_beq_eq_true hp))))


;; ---------------------------------------------------------------------------
;; The filtered world: projections; membership in a row contribution

(defmacro ^:private deffw [field idf]
  `(a/theorem ~(symbol (str "fw-" field)) [~'K :- (~'=> ~'Nat ~'Bool), ~'w :- ~'World]
     (~'= (~(keyword field) (~'filter-world ~'K ~'w)) (~'tbl-keep ~'K ~idf (~(keyword field) ~'w)))
     (~'rfl)))
(deffw scopes scope-id) (deffw comps comp-id) (deffw tasks task-id) (deffw runs run-id)
(deffw sources source-id) (deffw edges edge-id) (deffw acts act-id) (deffw res resource-id)
(deffw pubs pub-id) (deffw forks fork-id)

(defmacro ^:private deffw-same [field type]
  `(a/theorem ~(symbol (str "fw-" field)) [~'K :- (~'=> ~'Nat ~'Bool), ~'w :- ~'World]
     (~'= (~(keyword field) (~'filter-world ~'K ~'w)) (~(keyword field) ~'w))
     (~'rfl)))
(deffw-same cleanup x) (deffw-same pins x) (deffw-same pending-act x) (deffw-same released x) (deffw-same next-id x)

;; membership in a row's contribution is membership in retain-succ of its id
(defmacro ^:private defsucc-of [table row field idf contrib]
  (let [app (if (symbol? contrib) (list contrib 'r) (concat contrib ['r]))]
    `(a/theorem ~(symbol (str "succ-of-" table)) [~'w :- ~'World, ~'r :- ~row, ~'y :- ~'Nat]
       (~'=> (~'List.Mem ~'r (~(keyword field) ~'w)) (~'= (~'reach-mem ~'y ~app) ~'true)
             (~'= (~'reach-mem ~'y (~'retain-succ ~'w (~idf ~'r))) ~'true))
       (~'intro ~'hs ~'hy)
       (~'have ~'hp (~'= (~'id-is ~idf (~idf ~'r) ~'r) ~'true)) (~'exact (~'Nat.beq_refl (~idf ~'r)))
       (~'have ~'hg ~':= (~'gather-mem ~row (~'id-is ~idf (~idf ~'r)) ~contrib ~'r ~'y (~(keyword field) ~'w) ~'hs ~'hp ~'hy))
       (~'simp [~'retain-succ ~'reach-mem-append ~'reach-mem-app ~'hg]))))

(defsucc-of scope ScopeRow scopes scope-id (scope-contrib w))
(defsucc-of comp CompRow comps comp-id (comp-contrib w))
(defsucc-of task TaskRow tasks task-id task-contrib)
(defsucc-of run RunRow runs run-id (run-contrib w))
(defsucc-of act ActRow acts act-id act-contrib)
(defsucc-of edge EdgeRow edges edge-id edge-contrib)
(defsucc-of pub PubRow pubs pub-id pub-contrib)


;; ---------------------------------------------------------------------------
;; Agreement: on a node of a succ-closed L inside K, retain-succ of the filtered world
;; is retain-succ of the world. Every scan only returns successors (in L, so kept); every
;; guard that reads another row (task-running, sp-edge-of, comp-run-ok) is true only when
;; that row's id is a successor too, and a filtered-out row makes the guard false on both
;; sides (guard-keep).

(a/theorem scope-contrib-agree [w :- World, K :- (=> Nat Bool), L :- (=> Nat Prop), s :- ScopeRow]
  (=> (forall [a :- Nat] (forall [b :- Nat] (=> (L a) (= (reach-mem b (retain-succ w a)) true) (L b))))
      (forall [a :- Nat] (=> (L a) (= (K a) true)))
      (List.Mem s (:scopes w))
      (L (scope-id s))
      (= (scope-contrib (filter-world K w) s) (scope-contrib w s)))
  (intro hL hK hs hx)
  (have hf (= (tbl-scan fork-id (owned-fork (:id s)) (tbl-keep K fork-id (:forks w)))
              (tbl-scan fork-id (owned-fork (:id s)) (:forks w))))
  (apply scan-keep)
  (intro r hr hp)
  (apply hK) (apply (hL (scope-id s) (fork-id r) hx))
  (apply (succ-of-scope w s (fork-id r) hs))
  (simp [scope-contrib reach-mem-append reach-mem-app (scan-mem ForkRow fork-id (owned-fork (:id s)) r (:forks w) hr hp)])
  (intro r hr hk) (rfl)
  (have ht (= (tbl-scan task-id (owned-running-task (filter-world K w) (:id s)) (tbl-keep K task-id (:tasks w)))
              (tbl-scan task-id (owned-running-task w (:id s)) (:tasks w))))
  (apply scan-keep)
  (intro r hr hp)
  (apply hK) (apply (hL (scope-id s) (task-id r) hx))
  (apply (succ-of-scope w s (task-id r) hs))
  (simp [scope-contrib reach-mem-append reach-mem-app (scan-mem TaskRow task-id (owned-running-task w (:id s)) r (:tasks w) hr hp)])
  (intro r hr hk)
  (cases ho (Nat.beq (:owner r) (:id s)))
  (case [false] (simp [owned-running-task ho]))
  (case [true]
    (cases hz (Nat.beq (:run r) 0))
    (case [true] (simp [owned-running-task task-running ho hz]))
    (case [false]
      (have hg (= (opt-test run-alive (tbl-find run-id (:run r) (tbl-keep K run-id (:runs w))))
                  (opt-test run-alive (tbl-find run-id (:run r) (:runs w)))))
      (apply guard-keep)
      (intro hot)
      (have hp (= (owned-running-task w (:id s) r) true))
      (simp [owned-running-task task-running run-find ho hz hot])
      (have hlr (L (task-id r)))
      (apply (hL (scope-id s) (task-id r) hx))
      (apply (succ-of-scope w s (task-id r) hs))
      (simp [scope-contrib reach-mem-append reach-mem-app (scan-mem TaskRow task-id (owned-running-task w (:id s)) r (:tasks w) hr hp)])
      (have hlrun (L (:run r)))
      (apply (hL (task-id r) (:run r) hlr))
      (apply (succ-of-task w r (:run r) hr))
      (simp [task-contrib nz hz reach-mem-cons Nat.beq_refl])
      (exact (hK (:run r) hlrun))
      (simp [owned-running-task task-running run-find fw-runs ho hz hg])))
  (simp [scope-contrib fw-tasks fw-forks ht hf]))
(a/theorem tbl-find-mem [A :- Type, idf :- (=> A Nat), x :- Nat, e :- A, xs :- (List A)]
  (=> (= (tbl-find idf x xs) (Option.some A e)) (List.Mem e xs))
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (intro hf) (simp [tbl-find] at hf)
  (intro hf)
  (cases hx (Nat.beq (idf h) x))
  (case [false] (simp [tbl-find hx] at hf) (exact (List.Mem.tail h (ih hf))))
  (case [true] (simp [tbl-find hx] at hf) (rw [hf]) (exact (List.Mem.head t))))

(a/theorem run-contrib-agree [w :- World, K :- (=> Nat Bool), L :- (=> Nat Prop), q :- RunRow]
  (=> (forall [a :- Nat] (forall [b :- Nat] (=> (L a) (= (reach-mem b (retain-succ w a)) true) (L b))))
      (forall [a :- Nat] (=> (L a) (= (K a) true)))
      (List.Mem q (:runs w))
      (L (run-id q))
      (= (run-contrib (filter-world K w) q) (run-contrib w q)))
  (intro hL hK hq hx)
  (cases ha (run-alive q))
  (case [false] (simp [run-contrib ha]))
  (case [true]
    (have hin (forall [y :- Nat] (=> (= (reach-mem y (run-contrib w q)) true) (= (K y) true))))
    (intro y hy) (exact (hK y (hL (run-id q) y hx (succ-of-run w q y hq hy))))
    (have h1 (= (tbl-scan act-id (act-of-run (:id q)) (tbl-keep K act-id (:acts w)))
                (tbl-scan act-id (act-of-run (:id q)) (:acts w))))
    (apply scan-keep)
    (intro r hr hp) (apply hin)
    (simp [run-contrib ha reach-mem-append reach-mem-app (scan-mem ActRow act-id (act-of-run (:id q)) r (:acts w) hr hp)])
    (intro r hr hk) (rfl)
    (have h2 (= (tbl-scan edge-id (sp-edge-of (filter-world K w) (:id q)) (tbl-keep K edge-id (:edges w)))
                (tbl-scan edge-id (sp-edge-of w (:id q)) (:edges w))))
    (apply scan-keep)
    (intro r hr hp) (apply hin)
    (simp [run-contrib ha reach-mem-append reach-mem-app (scan-mem EdgeRow edge-id (sp-edge-of w (:id q)) r (:edges w) hr hp)])
    (intro r hr hk)
    (cases hkd (Nat.beq (:kind r) ek-savepoint))
    (case [false] (simp [sp-edge-of hkd]))
    (case [true]
      (have hg (= (opt-test (act-of-run (:id q)) (tbl-find act-id (:creditor r) (tbl-keep K act-id (:acts w))))
                  (opt-test (act-of-run (:id q)) (tbl-find act-id (:creditor r) (:acts w)))))
      (apply guard-keep)
      (intro hot)
      (cases hf (tbl-find act-id (:creditor r) (:acts w)))
      (case [none] (simp [hf opt-test] at hot))
      (case [some e]
        (have hot2 (= (act-of-run (:id q) e) true)) (rw [hf] at hot) (exact hot)
        (have hai := (tbl-find-id ActRow act-id (:creditor r) e (:acts w) hf))
        (have ham := (tbl-find-mem ActRow act-id (:creditor r) e (:acts w) hf))
        (rw [← hai])
        (apply hin)
        (simp [run-contrib ha reach-mem-append reach-mem-app (scan-mem ActRow act-id (act-of-run (:id q)) e (:acts w) ham hot2)]))
      (simp [sp-edge-of act-find fw-acts hkd hg]))
    (simp [run-contrib ha fw-acts fw-edges h1 h2])))

(a/theorem comp-contrib-agree [w :- World, K :- (=> Nat Bool), L :- (=> Nat Prop), c :- CompRow]
  (=> (forall [a :- Nat] (forall [b :- Nat] (=> (L a) (= (reach-mem b (retain-succ w a)) true) (L b))))
      (forall [a :- Nat] (=> (L a) (= (K a) true)))
      (List.Mem c (:comps w))
      (L (comp-id c))
      (= (comp-contrib (filter-world K w) c) (comp-contrib w c)))
  (intro hL hK hc hx)
  (cases hi (:idle c))
  (case [true] (simp [comp-contrib hi]))
  (case [false]
    (have hin (forall [y :- Nat] (=> (= (reach-mem y (comp-contrib w c)) true) (= (K y) true))))
    (intro y hy) (exact (hK y (hL (comp-id c) y hx (succ-of-comp w c y hc hy))))
    (have h1 (= (tbl-scan edge-id (dep-of (:id c)) (tbl-keep K edge-id (:edges w)))
                (tbl-scan edge-id (dep-of (:id c)) (:edges w))))
    (apply scan-keep)
    (intro r hr hp) (apply hin)
    (simp [comp-contrib hi reach-mem-append reach-mem-app (scan-mem EdgeRow edge-id (dep-of (:id c)) r (:edges w) hr hp)])
    (intro r hr hk) (rfl)
    (have hg (= (opt-test (comp-run-ok c) (tbl-find run-id (:run c) (tbl-keep K run-id (:runs w))))
                (opt-test (comp-run-ok c) (tbl-find run-id (:run c) (:runs w)))))
    (apply guard-keep)
    (intro hot) (apply hin)
    (have hs (= (comp-run-succ w c) (List.cons Nat (:run c) (List.nil Nat))))
    (simp [comp-run-succ run-find hot])
    (simp [comp-contrib hi hs reach-mem-append reach-mem-app reach-mem-cons Nat.beq_refl])
    (have h2 (= (comp-run-succ (filter-world K w) c) (comp-run-succ w c)))
    (simp [comp-run-succ run-find fw-runs hg])
    (simp [comp-contrib hi fw-edges h1 h2])))

(a/theorem succ-filter-agree [w :- World, K :- (=> Nat Bool), L :- (=> Nat Prop), x :- Nat]
  (=> (forall [a :- Nat] (forall [b :- Nat] (=> (L a) (= (reach-mem b (retain-succ w a)) true) (L b))))
      (forall [a :- Nat] (=> (L a) (= (K a) true)))
      (L x)
      (= (retain-succ (filter-world K w) x) (retain-succ w x)))
  (intro hL hK hx)
  (have hkx (= (K x) true)) (exact (hK x hx))
  (have g1 (= (tbl-gather (id-is scope-id x) (scope-contrib (filter-world K w)) (tbl-keep K scope-id (:scopes w)))
              (tbl-gather (id-is scope-id x) (scope-contrib w) (:scopes w))))
  (apply (gather-id-keep ScopeRow K scope-id x (scope-contrib w) (scope-contrib (filter-world K w)) (:scopes w) hkx))
  (intro r hr he) (apply (scope-contrib-agree w K L r hL hK hr)) (rw [he]) (exact hx)
  (have g2 (= (tbl-gather (id-is comp-id x) (comp-contrib (filter-world K w)) (tbl-keep K comp-id (:comps w)))
              (tbl-gather (id-is comp-id x) (comp-contrib w) (:comps w))))
  (apply (gather-id-keep CompRow K comp-id x (comp-contrib w) (comp-contrib (filter-world K w)) (:comps w) hkx))
  (intro r hr he) (apply (comp-contrib-agree w K L r hL hK hr)) (rw [he]) (exact hx)
  (have g4 (= (tbl-gather (id-is run-id x) (run-contrib (filter-world K w)) (tbl-keep K run-id (:runs w)))
              (tbl-gather (id-is run-id x) (run-contrib w) (:runs w))))
  (apply (gather-id-keep RunRow K run-id x (run-contrib w) (run-contrib (filter-world K w)) (:runs w) hkx))
  (intro r hr he) (apply (run-contrib-agree w K L r hL hK hr)) (rw [he]) (exact hx)
  (have g3 (= (tbl-gather (id-is task-id x) task-contrib (tbl-keep K task-id (:tasks w)))
              (tbl-gather (id-is task-id x) task-contrib (:tasks w))))
  (apply (gather-id-keep TaskRow K task-id x task-contrib task-contrib (:tasks w) hkx)) (intro r hr he) (rfl)
  (have g5 (= (tbl-gather (id-is act-id x) act-contrib (tbl-keep K act-id (:acts w)))
              (tbl-gather (id-is act-id x) act-contrib (:acts w))))
  (apply (gather-id-keep ActRow K act-id x act-contrib act-contrib (:acts w) hkx)) (intro r hr he) (rfl)
  (have g6 (= (tbl-gather (id-is edge-id x) edge-contrib (tbl-keep K edge-id (:edges w)))
              (tbl-gather (id-is edge-id x) edge-contrib (:edges w))))
  (apply (gather-id-keep EdgeRow K edge-id x edge-contrib edge-contrib (:edges w) hkx)) (intro r hr he) (rfl)
  (have g7 (= (tbl-gather (id-is pub-id x) pub-contrib (tbl-keep K pub-id (:pubs w)))
              (tbl-gather (id-is pub-id x) pub-contrib (:pubs w))))
  (apply (gather-id-keep PubRow K pub-id x pub-contrib pub-contrib (:pubs w) hkx)) (intro r hr he) (rfl)
  (simp [retain-succ fw-scopes fw-comps fw-tasks fw-runs fw-acts fw-edges fw-pubs g1 g2 g3 g4 g5 g6 g7]))

(a/theorem roots-filter [w :- World, K :- (=> Nat Bool)]
  (=> (forall [y :- Nat] (=> (= (reach-mem y (roots w)) true) (= (K y) true)))
      (forall [y :- Nat] (=> (= (reach-mem y (roots w)) true)
        (forall [z :- Nat] (=> (= (reach-mem z (retain-succ w y)) true) (= (K z) true)))))
      (= (roots (filter-world K w)) (roots w)))
  (intro hr hs)
  (have h2 (= (tbl-scan edge-id is-observe (tbl-keep K edge-id (:edges w))) (tbl-scan edge-id is-observe (:edges w))))
  (apply scan-keep)
  (intro r hm hp) (apply hr)
  (simp [roots reach-mem-append reach-mem-app (scan-mem EdgeRow edge-id is-observe r (:edges w) hm hp)])
  (intro r hm hk) (rfl)
  (have h3 (= (tbl-scan scope-id is-open-explicit (tbl-keep K scope-id (:scopes w))) (tbl-scan scope-id is-open-explicit (:scopes w))))
  (apply scan-keep)
  (intro r hm hp) (apply hr)
  (simp [roots reach-mem-append reach-mem-app (scan-mem ScopeRow scope-id is-open-explicit r (:scopes w) hm hp)])
  (intro r hm hk) (rfl)
  (have h4 (= (tbl-scan pub-id (armed-pub (filter-world K w)) (tbl-keep K pub-id (:pubs w))) (tbl-scan pub-id (armed-pub w) (:pubs w))))
  (apply scan-keep)
  (intro r hm hp) (apply hr)
  (simp [roots reach-mem-append reach-mem-app (scan-mem PubRow pub-id (armed-pub w) r (:pubs w) hm hp)])
  (intro r hm hk)
  (cases hh (Nat.blt 0 (:handles r)))
  (case [false] (simp [armed-pub hh]))
  (case [true]
    (cases hz (Nat.beq (:edge r) 0))
    (case [true] (simp [armed-pub hh hz]))
    (case [false]
      (have hg (= (opt-test edge-armed (tbl-find edge-id (:edge r) (tbl-keep K edge-id (:edges w))))
                  (opt-test edge-armed (tbl-find edge-id (:edge r) (:edges w)))))
      (apply guard-keep)
      (intro hot)
      (have hp (= (armed-pub w r) true))
      (simp [armed-pub edge-find hh hz hot])
      (have hroot (= (reach-mem (pub-id r) (roots w)) true))
      (simp [roots reach-mem-append reach-mem-app (scan-mem PubRow pub-id (armed-pub w) r (:pubs w) hm hp)])
      (have he (= (reach-mem (:edge r) (pub-contrib r)) true))
      (simp [pub-contrib nz hz reach-mem-cons Nat.beq_refl])
      (exact (hs (pub-id r) hroot (:edge r) (succ-of-pub w r (:edge r) hm he)))
      (simp [armed-pub edge-find fw-edges hh hz hg])))
  (have h1 (= (tbl-scan scope-id is-root-scope (tbl-keep K scope-id (:scopes w))) (tbl-scan scope-id is-root-scope (:scopes w))))
  (apply scan-keep)
  (intro r hm hp) (apply hr)
  (simp [roots reach-mem-append reach-mem-app (scan-mem ScopeRow scope-id is-root-scope r (:scopes w) hm hp)])
  (intro r hm hk) (rfl)
  (simp [roots fw-pins fw-edges fw-scopes fw-pubs fw-pending-act h1 h2 h3 h4]))

;; ---------------------------------------------------------------------------
;; live

(a/theorem in-live-iff [w :- World, x :- Nat]
  (=> (= (live-converged w) true) (Iff (= (in-live w x) true) (Reach (retain-succ w) (roots w) x)))
  (intro hc)
  (have e := (reach-run-l-eq (live-fuel-list w) (retain-succ w) (roots w)))
  (have hc2 (= (ReachResult.converged (reach-run (List.length (live-fuel-list w)) (retain-succ w) (roots w))) true))
  (rw [← e]) (exact hc)
  (have h := (reach-run-iff (List.length (live-fuel-list w)) (retain-succ w) (roots w) x hc2))
  (rw [← e] at h)
  (exact h))

(a/theorem live-filter-reach [w :- World, K :- (=> Nat Bool), y :- Nat]
  (=> (= (live-converged w) true)
      (forall [a :- Nat] (=> (= (in-live w a) true) (= (K a) true)))
      (Iff (Reach (retain-succ (filter-world K w)) (roots (filter-world K w)) y) (Reach (retain-succ w) (roots w) y)))
  (intro hc hk)
  (have hK (forall [a :- Nat] (=> (Reach (retain-succ w) (roots w) a) (= (K a) true))))
  (intro a ha) (exact (hk a (Iff.mpr (in-live-iff w a hc) ha)))
  (have hL (forall [a :- Nat] (forall [b :- Nat] (=> (Reach (retain-succ w) (roots w) a) (= (reach-mem b (retain-succ w a)) true) (Reach (retain-succ w) (roots w) b)))))
  (intro a b ha hb) (exact (Reach.step a b ha (Iff.mp (reach-mem-iff b (retain-succ w a)) hb)))
  (have hroots (= (roots (filter-world K w)) (roots w)))
  (apply roots-filter)
  (intro z hz) (exact (hK z (Reach.root z (Iff.mp (reach-mem-iff z (roots w)) hz))))
  (intro z hz v hv)
  (exact (hK v (hL z v (Reach.root z (Iff.mp (reach-mem-iff z (roots w)) hz)) hv)))
  (apply (reach-frame-roots (retain-succ w) (retain-succ (filter-world K w)) (roots w) (roots (filter-world K w)) y hroots))
  (intro z hz)
  (exact (succ-filter-agree w K (Reach (retain-succ w) (roots w)) z hL hK hz)))

(a/theorem in-live-filter [w :- World, K :- (=> Nat Bool), y :- Nat]
  (=> (= (live-converged w) true) (= (live-converged (filter-world K w)) true)
      (forall [a :- Nat] (=> (= (in-live w a) true) (= (K a) true)))
      (= (in-live (filter-world K w) y) (in-live w y)))
  (intro hc hc2 hk)
  (have e := (live-filter-reach w K y hc hk))
  (have i1 := (in-live-iff (filter-world K w) y hc2))
  (have i2 := (in-live-iff w y hc))
  (cases h1 (in-live (filter-world K w) y))
  (case [true]
    (have r2 := (Iff.mp e (Iff.mp i1 h1)))
    (exact (Eq.symm (Iff.mpr i2 r2))))
  (case [false]
    (cases h2 (in-live w y))
    (case [false] (rfl))
    (case [true]
      (have c := (Iff.mpr i1 (Iff.mpr e (Iff.mp i2 h2))))
      (rw [h1] at c) (simp at c))))


;; ---------------------------------------------------------------------------
;; The keep set is stable under its own filter; I3; idempotence

;; Z#52: the ancestor chain is recomputed in the filtered world; it converges in every world
;; (one parent per scope, fuel 2 + #scopes), and the filter keeps the scope and its chain, so
;; the chain is the same (frame + fuel independence of a converged worklist).
(a/theorem nz-len [p :- Nat] (<= (List.length (nz p)) 1)
  (cases hz (Nat.beq p 0)) (all_goals (simp [nz hz])))
(a/theorem scope-up-len [w :- World, x :- Nat] (<= (List.length (scope-up w x)) 1)
  (cases hf (scope-find w x))
  (case [none] (simp [scope-up hf]))
  (case [some s] (simp only [scope-up hf]) (exact (nz-len (:parent s)))))
(a/theorem scope-up-absent [w :- World, x :- Nat]
  (=> (= (reach-mem x (tbl-ids scope-id (:scopes w))) false) (= (scope-up w x) (List.nil Nat)))
  (intro h)
  (cases hf (scope-find w x))
  (case [none] (simp only [scope-up hf]))
  (case [some s]
    (have a := (tbl-find-has ScopeRow scope-id x s (:scopes w) hf))
    (rw [reach-mem-nat-mem nat-mem-ids a] at h) (cases h)))
(a/theorem scope-anc-conv [w :- World, s :- Nat]
  (= (:converged (reach-run-l (scope-anc-fuel w) (scope-up w) (scope-up w s))) true)
  (apply (reach-run-l-conv (scope-anc-fuel w) (scope-up w) (scope-up w s) (tbl-ids scope-id (:scopes w)) (scope-up-absent w)))
  (have a := (scope-up-len w s))
  (have b := (unseen-cost-le1 (scope-up w) (List.nil Nat) (tbl-ids scope-id (:scopes w)) (scope-up-len w)))
  (simp only [scope-anc-fuel List.length])
  (omega))
(a/theorem scope-up-filter [w :- World, K :- (=> Nat Bool), z :- Nat]
  (=> (= (K z) true) (= (scope-up (filter-world K w) z) (scope-up w z)))
  (intro hz)
  (have e := (keep-find-in ScopeRow K scope-id z (:scopes w) hz))
  (simp only [scope-up scope-find fw-scopes e]))
(a/theorem scope-anc-filter [w :- World, K :- (=> Nat Bool), s :- Nat]
  (=> (= (K s) true) (forall [a :- Nat] (=> (= (reach-mem a (scope-ancestors w s)) true) (= (K a) true)))
      (= (scope-ancestors (filter-world K w) s) (scope-ancestors w s)))
  (intros hs hk)
  (have c1 := (scope-anc-conv (filter-world K w) s))
  (have c2 := (scope-anc-conv w s))
  (rw [reach-run-l-eq] at c1)
  (rw [reach-run-l-eq] at c2)
  (have er := (scope-up-filter w K s hs))
  (rw [er] at c1)
  (have fr (= (reach-run (List.length (scope-anc-fuel (filter-world K w))) (scope-up (filter-world K w)) (scope-up w s))
              (reach-run (List.length (scope-anc-fuel (filter-world K w))) (scope-up w) (scope-up w s))))
  (apply reach-run-frame)
  (intros z hz)
  (apply (scope-up-filter w K z))
  (apply hk)
  (simp only [scope-ancestors])
  (rw [reach-run-l-eq])
  (exact (reach-run-complete _ _ _ z c2 hz))
  (rw [fr] at c1)
  (have eq := (reach-run-conv-eq _ _ (scope-up w) (scope-up w s) c1 c2))
  (simp only [scope-ancestors])
  (rw [reach-run-l-eq reach-run-l-eq er fr eq]))

(a/theorem anc-all-filter [w :- World, K :- (=> Nat Bool), xs :- (List Nat)]
  (=> (forall [a :- Nat] (=> (= (reach-mem a xs) true) (= (K a) true)))
      (forall [a :- Nat] (=> (= (reach-mem a (anc-all w xs)) true) (= (K a) true)))
      (= (anc-all (filter-world K w) xs) (anc-all w xs)))
  (induction xs)
  (case [nil] (intros h1 h2) (simp only [anc-all]))
  (case [cons x t ih]
    (intros h1 h2)
    (have kx (= (K x) true)) (apply h1) (simp [reach-mem-cons Nat.beq_refl])
    (have ka (forall [a :- Nat] (=> (= (reach-mem a (scope-ancestors w x)) true) (= (K a) true))))
    (intros a ha) (apply h2) (simp [anc-all reach-mem-append reach-mem-app ha])
    (have e1 := (scope-anc-filter w K x kx ka))
    (have e2 (= (anc-all (filter-world K w) t) (anc-all w t)))
    (apply ih)
    (intros a ha) (apply h1) (simp [reach-mem-cons ha])
    (intros a ha) (apply h2) (simp [anc-all reach-mem-append reach-mem-app ha])
    (simp only [anc-all e1 e2])))

(a/theorem anc-close-filter [w :- World, K :- (=> Nat Bool), xs :- (List Nat)]
  (=> (forall [a :- Nat] (=> (= (reach-mem a (anc-close w xs)) true) (= (K a) true)))
      (= (anc-close (filter-world K w) xs) (anc-close w xs)))
  (intro h)
  (have h1 (forall [a :- Nat] (=> (= (reach-mem a xs) true) (= (K a) true))))
  (intros a ha) (apply h) (simp [anc-close reach-mem-append reach-mem-app ha])
  (have h2 (forall [a :- Nat] (=> (= (reach-mem a (anc-all w xs)) true) (= (K a) true))))
  (intros a ha) (apply h) (simp [anc-close reach-mem-append reach-mem-app ha])
  (have e := (anc-all-filter w K xs h1 h2))
  (simp only [anc-close e]))

(a/theorem anc-all-of [w :- World, xs :- (List Nat), x :- Nat, y :- Nat]
  (=> (= (reach-mem x xs) true) (= (reach-mem y (scope-ancestors w x)) true) (= (reach-mem y (anc-all w xs)) true))
  (induction xs)
  (case [nil] (intros hx hy) (simp [reach-mem] at hx))
  (case [cons h t ih]
    (intros hx hy)
    (cases he (Nat.beq x h))
    (case [true]
      (have e (= x h)) (exact (Nat.eq_of_beq_eq_true he))
      (rw [e] at hy)
      (simp [anc-all reach-mem-append reach-mem-app hy]))
    (case [false]
      (have ht (= (reach-mem x t) true)) (simp only [reach-mem-cons he Bool.false_or] at hx) (exact hx)
      (simp [anc-all reach-mem-append reach-mem-app (ih ht hy)]))))

(a/theorem anc-all-sub [w :- World, xs :- (List Nat), ys :- (List Nat), y :- Nat]
  (=> (forall [z :- Nat] (=> (= (reach-mem z xs) true) (= (reach-mem z ys) true)))
      (= (reach-mem y (anc-all w xs)) true) (= (reach-mem y (anc-all w ys)) true))
  (induction xs)
  (case [nil] (intros hs hy) (simp [anc-all reach-mem] at hy))
  (case [cons h t ih]
    (intros hs hy)
    (simp only [anc-all reach-mem-append reach-mem-app Bool.or_eq_true] at hy)
    (have hs2 (forall [z :- Nat] (=> (= (reach-mem z t) true) (= (reach-mem z ys) true))))
    (intros z hz) (apply hs) (simp [reach-mem-cons hz])
    (have hh (= (reach-mem h (List.cons Nat h t)) true)) (simp [reach-mem-cons Nat.beq_refl])
    (cases hy)
    (case [inl a] (exact (anc-all-of w ys h y (hs h hh) a)))
    (case [inr b] (exact (ih hs2 b)))))

(a/theorem anc-close-mono [w :- World, xs :- (List Nat), ys :- (List Nat), y :- Nat]
  (=> (forall [z :- Nat] (=> (= (reach-mem z xs) true) (= (reach-mem z ys) true)))
      (= (reach-mem y (anc-close w xs)) true) (= (reach-mem y (anc-close w ys)) true))
  (intros hs hy)
  (simp only [anc-close reach-mem-append reach-mem-app Bool.or_eq_true] at hy)
  (cases hy)
  (case [inl a] (simp [anc-close reach-mem-append reach-mem-app (hs y a)]))
  (case [inr b] (simp [anc-close reach-mem-append reach-mem-app (anc-all-sub w xs ys y hs b)])))

(a/theorem cleanup-in-filter [w :- World, K :- (=> Nat Bool), cs :- (List CleanupRow)]
  (=> (forall [a :- Nat] (=> (= (reach-mem a (cleanup-rows-in w cs)) true) (= (K a) true)))
      (= (cleanup-rows-in (filter-world K w) cs) (cleanup-rows-in w cs)))
  (induction cs)
  (case' [cons h t ih])
  (case' [nil])
  (intro hk) (simp [cleanup-rows-in])
  (intro hk)
  (have ih2 (= (cleanup-rows-in (filter-world K w) t) (cleanup-rows-in w t)))
  (apply ih) (intro a ha) (apply hk) (simp [cleanup-rows-in reach-mem-append reach-mem-app ha])
  (have hc (forall [a :- Nat] (=> (= (reach-mem a (cleanup-contrib w h)) true) (= (K a) true))))
  (intros a ha) (apply hk) (simp [cleanup-rows-in reach-mem-append reach-mem-app ha])
  (have hkr (= (K (:run h)) true))
  (apply hc) (simp [cleanup-contrib anc-close cleanup-base reach-mem-append reach-mem-app reach-mem-cons Nat.beq_refl])
  (have hf := (keep-find-in RunRow K run-id (:run h) (:runs w) hkr))
  (have hf2 (= (run-find (filter-world K w) (:run h)) (run-find w (:run h)))) (simp only [run-find fw-runs hf])
  (have hb (= (cleanup-base (filter-world K w) h) (cleanup-base w h))) (simp only [cleanup-base hf2])
  (have ho (= (cleanup-contrib (filter-world K w) h) (cleanup-contrib w h)))
  (simp only [cleanup-contrib hb])
  (exact (anc-close-filter w K (cleanup-base w h) hc))
  (simp only [cleanup-rows-in ho ih2]))

(a/theorem cleanup-filter [w :- World, K :- (=> Nat Bool)]
  (=> (forall [a :- Nat] (=> (= (reach-mem a (cleanup-rows w)) true) (= (K a) true)))
      (= (cleanup-rows (filter-world K w)) (cleanup-rows w)))
  (intro hk)
  (simp only [cleanup-rows fw-cleanup])
  (exact (cleanup-in-filter w K (:cleanup w) hk)))

(a/theorem storage-filter [w :- World, K :- (=> Nat Bool), lv :- (List Nat), lv2 :- (List Nat)]
  (=> (forall [a :- Nat] (= (reach-mem a lv2) (reach-mem a lv)))
      (forall [a :- Nat] (=> (= (reach-mem a lv) true) (= (K a) true)))
      (forall [a :- Nat] (=> (= (reach-mem a (storage-with w lv)) true) (= (K a) true)))
      (= (storage-with (filter-world K w) lv2) (storage-with w lv)))
  (intro he hk hk2)
  (have eg (= (storage-gather (filter-world K w) lv2) (storage-gather w lv)))
  (simp only [storage-gather fw-runs])
  (apply gather-keep)
  (intro r hr hp) (apply hk)
  (exact hp)
  (intro r hr hk3) (simp [stored-run he])
  (intro r hr hp) (rfl)
  (simp only [storage-with eg])
  (exact (anc-close-filter w K (storage-gather w lv) hk2)))

(a/theorem adm-id [y :- Nat, b :- Nat, c :- Bool]
  (=> (= (Bool.and (Nat.beq b y) c) true) (= b y))
  (intro h)
  (cases hb (Nat.beq b y))
  (case [true] (exact (Nat.eq_of_beq_eq_true hb)))
  (case [false] (rw [hb] at h) (simp at h)))

(a/theorem admitted-filter [w :- World, K :- (=> Nat Bool), y :- Nat]
  (= (admitted (filter-world K w) y) (Bool.and (K y) (admitted w y)))
  (have a1 := (any-keep-id CompRow K comp-id (adm-comp y) y (:comps w)
                (fn [r :- CompRow, h :- (= (adm-comp y r) true)] (adm-id y (:id r) (Bool.and (Bool.or (:idle r) (Nat.beq (:done-epoch r) 0)) (Nat.blt 0 (:handles r))) h))))
  (have a2 := (any-keep-id SourceRow K source-id (adm-source y) y (:sources w)
                (fn [r :- SourceRow, h :- (= (adm-source y r) true)] (adm-id y (:id r) (Nat.blt 0 (:handles r)) h))))
  (have a3 := (any-keep-id TaskRow K task-id (adm-task y) y (:tasks w)
                (fn [r :- TaskRow, h :- (= (adm-task y r) true)]
                  (adm-id y (:id r) (Bool.and (Bool.not (Nat.beq (:tag (:result r)) res-none)) (Nat.blt 0 (:handles r))) h))))
  (have a4 := (any-keep-id PubRow K pub-id (adm-pub y) y (:pubs w)
                (fn [r :- PubRow, h :- (= (adm-pub y r) true)] (adm-id y (:id r) (Nat.blt 0 (:handles r)) h))))
  (simp only [admitted fw-comps fw-sources fw-tasks fw-pubs a1 a2 a3 a4])
  (cases hk (K y))
  (all_goals (simp)))

(a/theorem rule-r-filter-eq [w :- World] (= (rule-r-filter w) (filter-world (keep-fn w) w)) (rfl))

(a/theorem keep-of-live [w :- World, a :- Nat] (=> (= (in-live w a) true) (= (keep-fn w a) true))
  (intro h)
  (have h2 (= (reach-mem a (live-list w)) true)) (exact h)
  (simp [keep-fn keep-with h2]))

(a/theorem bool-absorb [a :- Bool, b :- Bool, c :- Bool, d :- Bool]
  (= (Bool.or a (Bool.or b (Bool.or (Bool.and (Bool.or a (Bool.or b (Bool.or c d))) c) d)))
     (Bool.or a (Bool.or b (Bool.or c d))))
  (cases a) (all_goals (cases b)) (all_goals (cases c)) (all_goals (cases d)) (all_goals (rfl)))

(a/theorem keep-filter [w :- World, y :- Nat]
  (=> (= (live-converged w) true) (= (live-converged (rule-r-filter w)) true)
      (= (keep-fn (rule-r-filter w) y) (keep-fn w y)))
  (intro hc hc2)
  (rw [rule-r-filter-eq] at hc2)
  (rw [rule-r-filter-eq])
  (have hk (forall [a :- Nat] (=> (= (in-live w a) true) (= (keep-fn w a) true))))
  (intro a ha) (exact (keep-of-live w a ha))
  (have e1 (forall [a :- Nat] (= (in-live (filter-world (keep-fn w) w) a) (in-live w a))))
  (intro a) (exact (in-live-filter w (keep-fn w) a hc hc2 hk))
  (have e2 (= (cleanup-rows (filter-world (keep-fn w) w)) (cleanup-rows w)))
  (apply cleanup-filter) (intro a ha) (simp [keep-fn keep-with ha])
  (have e3 (= (storage (filter-world (keep-fn w) w)) (storage w)))
  (simp only [storage]) (apply storage-filter) (intro a) (exact (e1 a)) (intro a ha) (exact (hk a ha)) (intro a ha) (simp [keep-fn keep-with storage ha])
  (have e4 := (admitted-filter w (keep-fn w) y))
  (have u1 (= (keep-fn (filter-world (keep-fn w) w) y)
              (Bool.or (in-live (filter-world (keep-fn w) w) y)
                (Bool.or (reach-mem y (cleanup-rows (filter-world (keep-fn w) w)))
                  (Bool.or (admitted (filter-world (keep-fn w) w) y) (reach-mem y (storage (filter-world (keep-fn w) w))))))))
  (rfl)
  (have u2 (= (keep-fn w y)
              (Bool.or (in-live w y) (Bool.or (reach-mem y (cleanup-rows w)) (Bool.or (admitted w y) (reach-mem y (storage w)))))))
  (rfl)
  (rw [u1]) (rw [(e1 y)]) (rw [e2]) (rw [e3]) (rw [e4]) (rw [u2])
  (exact (bool-absorb (in-live w y) (reach-mem y (cleanup-rows w)) (admitted w y) (reach-mem y (storage w)))))

(a/theorem all-ids-filter [w :- World, K :- (=> Nat Bool), P :- (=> Nat Bool)]
  (=> (forall [y :- Nat] (=> (= (K y) true) (= (P y) true)))
      (= (tbl-all P (all-ids (filter-world K w))) true))
  (intro hk)
  (simp only [all-ids fw-scopes fw-comps fw-tasks fw-runs fw-sources fw-edges fw-acts fw-res fw-pubs fw-forks
              tbl-all-nat-app
              (keep-all-ids ScopeRow K P scope-id (:scopes w) hk) (keep-all-ids CompRow K P comp-id (:comps w) hk)
              (keep-all-ids TaskRow K P task-id (:tasks w) hk) (keep-all-ids RunRow K P run-id (:runs w) hk)
              (keep-all-ids SourceRow K P source-id (:sources w) hk) (keep-all-ids EdgeRow K P edge-id (:edges w) hk)
              (keep-all-ids ActRow K P act-id (:acts w) hk) (keep-all-ids ResRow K P resource-id (:res w) hk)
              (keep-all-ids PubRow K P pub-id (:pubs w) hk) (keep-all-ids ForkRow K P fork-id (:forks w) hk)
              Bool.and_self]))

(a/theorem filter-filter [w :- World, K :- (=> Nat Bool), K2 :- (=> Nat Bool)]
  (=> (forall [y :- Nat] (=> (= (K y) true) (= (K2 y) true)))
      (= (filter-world K2 (filter-world K w)) (filter-world K w)))
  (intro hk)
  (simp [filter-world (keep-keep ScopeRow K K2 scope-id (:scopes w) hk) (keep-keep CompRow K K2 comp-id (:comps w) hk)
              (keep-keep TaskRow K K2 task-id (:tasks w) hk) (keep-keep RunRow K K2 run-id (:runs w) hk)
              (keep-keep SourceRow K K2 source-id (:sources w) hk) (keep-keep EdgeRow K K2 edge-id (:edges w) hk)
              (keep-keep ActRow K K2 act-id (:acts w) hk) (keep-keep ResRow K K2 resource-id (:res w) hk)
              (keep-keep PubRow K K2 pub-id (:pubs w) hk) (keep-keep ForkRow K K2 fork-id (:forks w) hk)]))

;; I3 after the filter: every id of the filtered world is live there, in a cleanup entry,
;; admitted by §3.4, or a finalizer ref of a running live run.
(a/theorem rule-r-i3 [w :- World]
  (=> (= (live-converged w) true) (= (live-converged (rule-r-filter w)) true)
      (= (tbl-all (keep-fn (rule-r-filter w)) (all-ids (rule-r-filter w))) true))
  (intro hc hc2)
  (have hk (forall [y :- Nat] (=> (= (keep-fn w y) true) (= (keep-fn (rule-r-filter w) y) true))))
  (intro y hy) (have e := (keep-filter w y hc hc2)) (rw [e]) (exact hy)
  (rw [rule-r-filter-eq])
  (exact (all-ids-filter w (keep-fn w) (keep-fn (rule-r-filter w)) hk)))

(a/theorem rule-r-idem [w :- World]
  (=> (= (live-converged w) true) (= (live-converged (rule-r-filter w)) true)
      (= (rule-r-filter (rule-r-filter w)) (rule-r-filter w)))
  (intro hc hc2)
  (have hk (forall [y :- Nat] (=> (= (keep-fn w y) true) (= (keep-fn (rule-r-filter w) y) true))))
  (intro y hy) (have e := (keep-filter w y hc hc2)) (rw [e]) (exact hy)
  (have h1 (= (rule-r-filter (rule-r-filter w)) (filter-world (keep-fn (rule-r-filter w)) (rule-r-filter w))))
  (exact (rule-r-filter-eq (rule-r-filter w)))
  (rw [h1])
  (have h2 (= (rule-r-filter w) (filter-world (keep-fn w) w))) (exact (rule-r-filter-eq w))
  (have h3 := (filter-filter w (keep-fn w) (keep-fn (rule-r-filter w)) hk))
  (rw [← h2] at h3)
  (exact h3))

;; live is stable under the filter
(a/theorem rule-r-live [w :- World, y :- Nat]
  (=> (= (live-converged w) true) (= (live-converged (rule-r-filter w)) true)
      (= (in-live (rule-r-filter w) y) (in-live w y)))
  (intro hc hc2)
  (rw [rule-r-filter-eq] at hc2)
  (rw [rule-r-filter-eq])
  (have hk (forall [a :- Nat] (=> (= (in-live w a) true) (= (keep-fn w a) true))))
  (intro a ha) (exact (keep-of-live w a ha))
  (exact (in-live-filter w (keep-fn w) y hc hc2 hk)))

;; ---------------------------------------------------------------------------
;; P1: the live worklist always converges (fuel sufficiency, spindel.v2.reach's
;; reach-run-l-conv with universe all-ids). No uniqueness of ids is needed: a node outside
;; all-ids is no row's id, so it has no successors, and the fuel counts every id's
;; successors with its multiplicity in all-ids.

(a/theorem or-false-parts [a :- Bool, b :- Bool]
  (=> (= (Bool.or a b) false) (And (= a false) (= b false)))
  (intro h) (cases a) (cases b) (all_goals (simp at h)) (exact (And.intro (rfl) (rfl))))

(a/theorem reach-mem-nat-app [x :- Nat, xs :- (List Nat), ys :- (List Nat)]
  (= (reach-mem x (nat-app xs ys)) (Bool.or (reach-mem x xs) (reach-mem x ys)))
  (induction xs)
  (case [nil] (simp [nat-app reach-mem]))
  (case [cons h t ih] (simp only [nat-app reach-mem-cons ih Bool.or_assoc])))

(a/theorem gather-absent [A :- Type, idf :- (=> A Nat), f :- (=> A (List Nat)), x :- Nat, xs :- (List A)]
  (=> (= (reach-mem x (tbl-ids idf xs)) false) (= (tbl-gather (id-is idf x) f xs) (List.nil Nat)))
  (induction xs)
  (case [nil] (intro h) (simp [tbl-gather]))
  (case [cons h t ih]
    (intro hm)
    (simp only [tbl-ids reach-mem-cons] at hm)
    (have hp := (or-false-parts _ _ hm))
    (have hi (= (id-is idf x h) false))
    (simp only [id-is]) (exact (beq-symm-false x (idf h) (And.left hp)))
    (simp only [tbl-gather hi])
    (exact (ih (And.right hp)))))

(a/theorem retain-succ-absent [w :- World, x :- Nat]
  (=> (= (reach-mem x (all-ids w)) false) (= (retain-succ w x) (List.nil Nat)))
  (intro h)
  (simp only [all-ids reach-mem-nat-app] at h)
  (have p1 := (or-false-parts _ _ h))
  (have p2 := (or-false-parts _ _ (And.right p1)))
  (have p3 := (or-false-parts _ _ (And.right p2)))
  (have p4 := (or-false-parts _ _ (And.right p3)))
  (have p5 := (or-false-parts _ _ (And.right p4)))
  (have p6 := (or-false-parts _ _ (And.right p5)))
  (have p7 := (or-false-parts _ _ (And.right p6)))
  (have p8 := (or-false-parts _ _ (And.right p7)))
  (have p9 := (or-false-parts _ _ (And.right p8)))
  (simp only [retain-succ
              (gather-absent ScopeRow scope-id (scope-contrib w) x (:scopes w) (And.left p1))
              (gather-absent CompRow comp-id (comp-contrib w) x (:comps w) (And.left p2))
              (gather-absent TaskRow task-id task-contrib x (:tasks w) (And.left p3))
              (gather-absent RunRow run-id (run-contrib w) x (:runs w) (And.left p4))
              (gather-absent EdgeRow edge-id edge-contrib x (:edges w) (And.left p6))
              (gather-absent ActRow act-id act-contrib x (:acts w) (And.left p7))
              (gather-absent PubRow pub-id pub-contrib x (:pubs w) (And.left p9))]))

(a/theorem succ-all-length [w :- World, us :- (List Nat)]
  (= (List.length (succ-all w us)) (unseen-cost (retain-succ w) (List.nil Nat) us))
  (induction us)
  (case [nil] (simp [succ-all unseen-cost]))
  (case [cons h t ih]
    (simp only [succ-all unseen-cost list-length-append ih])))

;; Theorem (P1): live always converges with its computed fuel
(a/theorem live-converged-all [w :- World] (= (live-converged w) true)
  (simp only [live-converged live])
  (apply (reach-run-l-conv (live-fuel-list w) (retain-succ w) (roots w) (all-ids w) (retain-succ-absent w)))
  (simp only [live-fuel-list List.length list-length-append succ-all-length])
  (omega))
