(ns spindel.v2.sys
  "Layer 2, semantic: a system of worlds (notes/LAYER2.md §3-§5), kernel-checked.

  A cell holds one layer-1 `World`. A fork is a value copy of the parent's world; the child's
  inherited armed resources are recorded as dormant and settled by `wake`, which is a sequence of
  layer-1 items (a timer stays armed; any other resource fires `err ::forked` and is acknowledged).
  So every world of every reachable system satisfies the layer-1 bundle `p3l` (F5), by `step-p3l`.

  The marker of a fork (spec §8.1: `{child, owner}` in the parent, retained by its owner scope) is
  the child cell's `parent` and `owner` fields here: a marker retains nothing in the parent, so
  keeping it outside the parent's tables changes no layer-1 retention.

  A savepoint is a resource of kind `rk-savepoint` (= offload; S1 publish = T17 arm; S2 resume = T18 fire +
  T15 acknowledge; S7 abandon = T14 cancel of its run), so layer 1 needs no new transition. A
  publication records the savepoint's resource and a frozen basis (the world at the publishing
  commit). `instantiate` makes an unborn cell from the basis; `activate` fires its pending
  savepoint and settles the other inherited resources.

  Theorems:
    F5      sinv-put (generic), sinv-step, sinv-fork, sinv-wake, sinv-drop, sinv-resume,
            sinv-instantiate, sinv-activate, sinv-init; pinv-publish, pinv-abandon
    frames  step-frame, fork-frame, fork-effect-frame, instantiate-frame
    copies  fork-copy (the child of a born cell starts from the parent's world), instantiate-copy and
            instantiate-indep (every instance of a publication starts from its basis)
    guard   fork-refused, fork-effect-refused (a fork of an unborn cell changes nothing)
    S4      activate-born, activate-once (a second activation changes nothing)
    merge   sinv-merge, merge-frame, merge-refused (a refused merge changes nothing), merge-unchanged
            (a child that wrote no inherited source merges to the same parent)
    release sinv-idle-release, drop-step-comm (dropping a world commutes with every step elsewhere)
    C1      sinv-accept, sinv-complete, sinv-release-unborn (p3l-release-unborn: p3l reads no
            `released`), complete-latch. Completion soundness `cinv` (a live complete cell is
            ready: released and: unborn, or no run and every accepted child complete or
            collected): cinv-none, and kept by accept, complete, release-unborn, activate, drop,
            idle-release unconditionally; by fork, fork-effect, instantiate for an id no cell has
            accepted; by step, wake, resume, merge, publish, abandon under the premise `hq` (a
            layer-1 step keeps a released world released and a quiet world quiet; false of an
            arbitrary p3l world, kept as stated). Without hq (`cinv-step-q`, `cinv-wake-q`,
            `cinv-resume-q`, `cinv-merge-q`, `cinv-publish-q`, `cinv-abandon-q`): under `qsinv` (every
            live cell is an E4-released unborn instance or holds spindel.v2.qworld's `qinv`) and
            `qpinv` (every live publication's basis is released or holds qinv), both kept by every
            operation (`qsinv-*`, `qpinv-*`). A fork or fork effect of an unborn cell (E4-released
            or not) is refused (`fork-refused`, `fork-effect-refused`): question 9, engine 54e3df1.

  C1c stage A (Z#70): `Cell.joins`, the host joins (`Join`: id, target, state pending / delivered / withdrawn);
  `sys-join` (admission), `sys-deliver` (delivery of the pending joins on complete targets), `sys-withdraw` (the
  host's withdraw fn, question 12), `complete-cell` delivers the rest (abandonment); a fork, fork effect or
  instance starts with none. System operations, not Items.

  C1c stage B (Z#71, spindel.v2.owned): owned forks. `sys-own` (the count at the `(fork)` effect: a fork marker in the
  parent's world), `sys-owned-done` (`[:owned-done s child]`), `Cell.norm` (the inherited markers, W-NORMALIZE) and
  `sys-drain` (`[:normalize]`); both end with `sys-complete`, and `complete-ready` requires no marker (questions 15,
  16). Their invariants are the proof stage's.

  Not here: following mode (not in the engine either), sealing, sources created in the child (not merged)."
  (:require [ansatz.core :as a]
            [spindel.v2.state :refer :all]
            [spindel.v2.step :refer :all]
            [spindel.v2.engine :refer :all]
            [spindel.v2.hmk2 :refer [p3l]]
            [spindel.v2.progress :refer [quiescent]]
            [spindel.v2.cow :refer [fupd]]
            [spindel.v2.quiet]
            [spindel.v2.qworld]
            [spindel.v2.ledger :refer [task-complete]]
            [spindel.v2.owned :refer :all]))

(a/defn err-forked [] Nat 1)
;; layer 1 arms timers and offloads only (`arm-kind-ok`): a savepoint is an offload-kind resource,
;; told apart by its publication (`Pub.res`). Any other kind would be refused by T17, and every
;; statement below about a published savepoint would hold of nothing.
(a/defn rk-savepoint [] Nat rk-offload)

;; a world of the system: `parent`/`owner` are its fork marker (0 = the root world), `dormant` the
;; inherited resources not yet settled; an instance is `unborn` until its `pending` savepoint is fired.
;; C1 (T21 completion, Z#67): `kids` are the child cells this world accepted (its completion
;; obligations, never inherited), `complete` its completion (released, no run left, every accepted
;; child complete or collected; an unborn instance released before activation at once).
;; C1c stage A (Z#70): `joins` the pending host joins (`on-joined` / `await-joined`), one target task id per
;; subscription; never inherited (a fork, fork effect or instance starts with none)
;; C1c (question 12): a host join is one `on-joined` subscription: its id (the number of joins the cell admitted
;; before it), its target task id and its state, pending, delivered or withdrawn. Delivery and withdrawal race
;; (a CAS in the engine) and the winner is final: both act on a pending join only, so a join is delivered at
;; most once and a withdrawn one never. Entries are never removed (the engine prunes withdrawn ones lazily).
(a/structure Join [] (id Nat) (target Nat) (st Nat))
(a/defn js-pending [] Nat 0)
(a/defn js-delivered [] Nat 1)
(a/defn js-withdrawn [] Nat 2)
(a/defn join-id [j :- Join] Nat (:id j))
(a/defn jpend [j :- Join] Bool (Nat.beq (:st j) js-pending))
(a/defn hj-done [j :- Join] Join (if (jpend j) (Join.mk (:id j) (:target j) js-delivered) j))
(a/defn hj-drop [j :- Join] Join (if (jpend j) (Join.mk (:id j) (:target j) js-withdrawn) j))
(a/defn joins-map [f :- (=> Join Join), js :- (List Join)] (List Join)
  (match js [nil (List.nil Join)] [(cons h t) (List.cons Join (f h) (joins-map f t))]))
;; the live (pending) joins: the sidecar's `:pending-joins`
(a/defn pending-joins [js :- (List Join)] Nat (tbl-count jpend js))

(a/structure Cell [] (world World) (live Bool) (parent Nat) (owner Nat) (dormant (List Nat))
  (unborn Bool) (pending Nat) (kids (List Nat)) (complete Bool) (joins (List Join)) (norm (List Nat)))

;; a publication: the cell and run that published, the savepoint's resource, the frozen basis
(a/structure Pub [] (cell Nat) (res Nat) (run Nat) (basis World) (live Bool))

;; every live world satisfies the layer-1 bundle; so does every live publication's basis
(a/defn sinv [cells :- (=> Nat Cell)] Prop
  (forall [k :- Nat] (=> (= (:live (cells k)) true) (= (p3l (:world (cells k))) true))))

(a/defn pinv [pubs :- (=> Nat Pub)] Prop
  (forall [p :- Nat] (=> (= (:live (pubs p)) true) (= (p3l (:basis (pubs p))) true))))

(a/theorem sinv-put [cells :- (=> Nat Cell), k :- Nat, c2 :- Cell]
  (=> (sinv cells) (=> (= (:live c2) true) (= (p3l (:world c2)) true)) (sinv (fupd cells k c2)))
  (intros hs hc)
  (simp only [sinv] at hs)
  (simp only [sinv])
  (intros j hl)
  (cases hjk (Nat.beq j k))
  (case [false]
    (simp only [fupd hjk] at hl)
    (simp only [fupd hjk])
    (exact (hs j hl)))
  (case [true]
    (have e (= j k)) (exact (Nat.eq_of_beq_eq_true hjk))
    (rw [e] at hl)
    (rw [e])
    (simp only [fupd-same] at hl)
    (simp only [fupd-same])
    (exact (hc hl))))

(a/theorem sinv-live [cells :- (=> Nat Cell), k :- Nat]
  (=> (sinv cells) (= (:live (cells k)) true) (= (p3l (:world (cells k))) true))
  (intros hs hl) (simp only [sinv] at hs) (exact (hs k hl)))

;; ---------------------------------------------------------------------------
;; L1: a layer-1 item in world k

(a/defn cell-step [c :- Cell, it :- Item] Cell
  (Cell.mk (:world (world-step (:world c) it)) (:live c) (:parent c) (:owner c) (:dormant c)
           (:unborn c) (:pending c) (:kids c) (:complete c) (:joins c) (:norm c)))

(a/defn sys-step [cells :- (=> Nat Cell), k :- Nat, it :- Item] (=> Nat Cell)
  (fupd cells k (cell-step (cells k) it)))

(a/theorem step-frame [cells :- (=> Nat Cell), k :- Nat, it :- Item, j :- Nat]
  (=> (Not (= j k)) (= (sys-step cells k it j) (cells j)))
  (intro hne)
  (simp only [sys-step fupd (nbeq-ne j k hne)]))

(a/theorem sinv-step [cells :- (=> Nat Cell), k :- Nat, it :- Item]
  (=> (sinv cells) (sinv (sys-step cells k it)))
  (intro hs)
  (have hc (=> (= (:live (cell-step (cells k) it)) true) (= (p3l (:world (cell-step (cells k) it))) true)))
  (intro hl)
  (simp only [cell-step] at hl)
  (simp only [cell-step])
  (exact (step-p3l (:world (cells k)) it (sinv-live cells k hs hl)))
  (simp only [sys-step])
  (exact (sinv-put cells k (cell-step (cells k) it) hs hc)))

;; ---------------------------------------------------------------------------
;; L2/L3: fork of world k into the fresh cell m (a value copy)
;;
;; Guard (question 9, engine-v2 54e3df1): the source cell is born. Host `fork!` throws "fork! of an
;; unactivated instance" while the instance is unborn, and an E4 release keeps it unborn (`born?`
;; requires not released); the `(fork)` effect needs a run inside a slice, and an unborn instance
;; drains no slice (E4: its inherited work waits). So a fork of an unborn cell is refused: no
;; item, the system unchanged (`fork-refused`, `fork-effect-refused`).

(a/defn armed-ids [rs :- (List ResRow)] (List Nat)
  (match rs [nil (List.nil Nat)]
         [(cons r t) (if (Nat.beq (:phase r) rp-armed) (List.cons Nat (:id r) (armed-ids t)) (armed-ids t))]))

;; C1 R1: every outstanding resource is inherited (armed ones are dormant; cancelling or fired but
;; unacknowledged ones are discharged at the first turn, `wake-one`)
(a/defn res-ids [rs :- (List ResRow)] (List Nat)
  (match rs [nil (List.nil Nat)] [(cons r t) (List.cons Nat (:id r) (res-ids t))]))

(a/defn fork-cell [c :- Cell, k :- Nat, owner :- Nat] Cell
  (Cell.mk (:world c) true k owner (nat-app (res-ids (:res (:world c))) (:dormant c)) false 0 (List.nil Nat) false (List.nil Join) (marker-ids (:world c))))

(a/defn sys-fork [cells :- (=> Nat Cell), k :- Nat, m :- Nat, owner :- Nat] (=> Nat Cell)
  (if (:unborn (cells k)) cells (fupd cells m (fork-cell (cells k) k owner))))

;; a fork of an unborn cell (E4-released or not) is refused
(a/theorem fork-refused [cells :- (=> Nat Cell), k :- Nat, m :- Nat, owner :- Nat]
  (=> (= (:unborn (cells k)) true) (= (sys-fork cells k m owner) cells))
  (intro hu) (simp only [sys-fork hu]))

(a/theorem fork-frame [cells :- (=> Nat Cell), k :- Nat, m :- Nat, owner :- Nat, j :- Nat]
  (=> (Not (= j m)) (= (sys-fork cells k m owner j) (cells j)))
  (intro hne)
  (cases hu (:unborn (cells k)))
  (case [true] (simp only [sys-fork hu]))
  (case [false] (simp only [sys-fork hu fupd (nbeq-ne j m hne)])))

(a/theorem fork-copy [cells :- (=> Nat Cell), k :- Nat, m :- Nat, owner :- Nat]
  (=> (= (:unborn (cells k)) false) (= (:world (sys-fork cells k m owner m)) (:world (cells k))))
  (intro hu)
  (simp only [sys-fork hu fupd-same fork-cell]))

(a/theorem sinv-fork [cells :- (=> Nat Cell), k :- Nat, m :- Nat, owner :- Nat]
  (=> (sinv cells) (= (:live (cells k)) true) (sinv (sys-fork cells k m owner)))
  (intros hs hlk)
  (cases hu (:unborn (cells k)))
  (case [true] (simp only [sys-fork hu]) (exact hs))
  (case [false]
    (have hc (=> (= (:live (fork-cell (cells k) k owner)) true) (= (p3l (:world (fork-cell (cells k) k owner))) true)))
    (intro hl)
    (simp only [fork-cell])
    (exact (sinv-live cells k hs hlk))
    (simp only [sys-fork hu])
    (exact (sinv-put cells m (fork-cell (cells k) k owner) hs hc))))

;; ---------------------------------------------------------------------------
;; L4: the fix-up of a fork's inherited resources, as layer-1 items

(a/defn fire-ack [w :- World, z :- Nat, tag :- Nat, v :- Nat] World
  (:world (world-step (:world (world-step w (Item.resource-fire z tag v))) (Item.resource-ack z))))

(a/theorem p3l-fire-ack [w :- World, z :- Nat, tag :- Nat, v :- Nat]
  (=> (= (p3l w) true) (= (p3l (fire-ack w z tag v)) true))
  (intro h)
  (simp only [fire-ack])
  (exact (step-p3l _ (Item.resource-ack z) (step-p3l w (Item.resource-fire z tag v) h))))

;; C1 R1: an inherited timer stays armed (it is rescheduled); any other inherited resource is settled
;; at the first turn: armed, it fails with ::forked and is acknowledged; cancelling or fired but
;; unacknowledged, it has no counterpart here and is acknowledged (its fire is refused: not armed)
(a/defn timer-kept [r :- ResRow] Bool (Bool.and (Nat.beq (:kind r) rk-timer) (Nat.beq (:phase r) rp-armed)))
(a/defn wake-one [w :- World, z :- Nat] World
  (match (resource-find w z)
    [none w]
    [(some r) (if (timer-kept r) w (fire-ack w z res-err err-forked))]))

(a/defn wake-all [w :- World, zs :- (List Nat)] World
  (match zs [nil w] [(cons z t) (wake-all (wake-one w z) t)]))

(a/theorem p3l-wake-one [w :- World, z :- Nat]
  (=> (= (p3l w) true) (= (p3l (wake-one w z)) true))
  (intro h)
  (cases hf (resource-find w z))
  (case [none] (simp only [wake-one hf]) (exact h))
  (case [some r]
    (cases hk (timer-kept r))
    (case [true] (simp only [wake-one hf hk]) (exact h))
    (case [false]
      (simp only [wake-one hf hk])
      (exact (p3l-fire-ack w z res-err err-forked h)))))

(a/theorem p3l-wake-all [zs :- (List Nat)]
  (forall [w :- World] (=> (= (p3l w) true) (= (p3l (wake-all w zs)) true)))
  (induction zs)
  (case [nil] (intros w h) (simp only [wake-all]) (exact h))
  (case [cons z t ih] (intros w h) (simp only [wake-all]) (exact (ih (wake-one w z) (p3l-wake-one w z h)))))

(a/defn wake-cell [c :- Cell] Cell
  (Cell.mk (wake-all (:world c) (:dormant c)) (:live c) (:parent c) (:owner c) (List.nil Nat)
           (:unborn c) (:pending c) (:kids c) (:complete c) (:joins c) (:norm c)))

;; an unborn instance is not woken: its inherited work waits for `activate` (S3)
(a/defn sys-wake [cells :- (=> Nat Cell), k :- Nat] (=> Nat Cell)
  (if (:unborn (cells k)) cells (fupd cells k (wake-cell (cells k)))))

(a/theorem sinv-wake [cells :- (=> Nat Cell), k :- Nat]
  (=> (sinv cells) (sinv (sys-wake cells k)))
  (intro hs)
  (cases hu (:unborn (cells k)))
  (case [true] (simp only [sys-wake hu]) (exact hs))
  (case [false]
    (have hc (=> (= (:live (wake-cell (cells k))) true) (= (p3l (:world (wake-cell (cells k)))) true)))
    (intro hl)
    (simp only [wake-cell] at hl)
    (simp only [wake-cell])
    (exact (p3l-wake-all (:dormant (cells k)) (:world (cells k)) (sinv-live cells k hs hl)))
    (simp only [sys-wake hu])
    (exact (sinv-put cells k (wake-cell (cells k)) hs hc))))

;; ---------------------------------------------------------------------------
;; C1 world completion (T21, Z#67; engine `accept-child!`, `maybe-complete!`, E4). Internal: the
;; engine logs no item for it (its host-observation sidecars show it, oracle `check-observations`).

;; R2: owner k accepts child m (own-child! at the fork effect, host fork!, activate!): one obligation
;; until m completes or is collected; a complete owner takes none
(a/defn accept-cell [c :- Cell, m :- Nat] Cell
  (Cell.mk (:world c) (:live c) (:parent c) (:owner c) (:dormant c) (:unborn c) (:pending c)
           (List.cons Nat m (:kids c)) (:complete c) (:joins c) (:norm c)))
(a/defn sys-accept [cells :- (=> Nat Cell), k :- Nat, m :- Nat] (=> Nat Cell)
  (if (:complete (cells k)) cells (fupd cells k (accept-cell (cells k) m))))

;; W1: complete once released with no unretired run and every accepted child complete or collected
;; (a dropped cell); an unborn instance released before its activation at once (nothing in it runs).
;; C1c stage B (questions 15, 16): and no fork marker, i.e. W-OWNED-N all zero and W-NORMALIZE empty
(a/defn kid-done [cells :- (=> Nat Cell), m :- Nat] Bool (Bool.or (Bool.not (:live (cells m))) (:complete (cells m))))
(a/defn complete-ready [cells :- (=> Nat Cell), k :- Nat] Bool
  (Bool.and (:released (:world (cells k)))
            (Bool.or (:unborn (cells k))
                     (Bool.and (Nat.beq (world-runs (:world (cells k))) 0)
                               (Bool.and (tbl-all (kid-done cells) (:kids (cells k))) (no-markers (:world (cells k))))))))
(a/defn complete-cell [c :- Cell] Cell
  (Cell.mk (:world c) (:live c) (:parent c) (:owner c) (:dormant c) (:unborn c) (:pending c) (:kids c) true
           (joins-map hj-done (:joins c)) (:norm c)))
(a/defn sys-complete [cells :- (=> Nat Cell), k :- Nat] (=> Nat Cell)
  (if (complete-ready cells k) (fupd cells k (complete-cell (cells k))) cells))

;; E4: an unborn instance released before its activation only sets the flag (engine.clj
;; `release-unborn`); `sys-complete` then completes it. Its invariant: `sinv-release-unborn`.
(a/defn release-unborn-cell [c :- Cell] Cell
  (Cell.mk (release-unborn (:world c)) (:live c) (:parent c) (:owner c) (:dormant c) (:unborn c) (:pending c)
           (:kids c) (:complete c) (:joins c) (:norm c)))
(a/defn sys-release-unborn [cells :- (=> Nat Cell), k :- Nat] (=> Nat Cell)
  (if (Bool.and (:unborn (cells k)) (Bool.not (:released (:world (cells k)))))
      (fupd cells k (release-unborn-cell (cells k))) cells))

;; ---------------------------------------------------------------------------
;; C1c stage A (spec Z#70): host joins. `on-joined(K, cb)` / `await-joined` in world k: no row, edge,
;; handle, id or item (not a layer-1 transition), admitted after release (no released guard), never
;; inherited. Delivered once the target task is complete (spindel.v2.ledger `task-complete`), or once the
;; world is (abandonment: an unborn instance's copied tasks never run, so they never complete).
;;   sys-join      admission. The target is a task id the host holds a handle to, so an allocated id
;;                 (`0 < t < next-id`; an id no handle can name is refused: the system unchanged). Recorded with
;;                 the next join id, delivered at once when the target or the cell is complete, else pending.
;;   sys-deliver   delivers every pending join whose target is complete (the engine runs it inside the
;;                 commit that completes the target, `task-complete!`).
;;   sys-withdraw  the withdraw fn `on-joined` returns (question 12): a pending join becomes withdrawn, delivery
;;                 skips it; a delivered one stays delivered.
;;   complete-cell delivers every pending join with the world's completion (`complete-world!`).
;; All of them are system operations, not Items.
;; admission: the join's id is the number admitted so far; delivered at once when the target or the cell is complete
(a/defn join-new [c :- Cell, t :- Nat] Join
  (Join.mk (List.length (:joins c)) t
           (if (Bool.or (:complete c) (task-complete (:world c) t)) js-delivered js-pending)))
(a/defn join-cell [c :- Cell, t :- Nat] Cell
  (Cell.mk (:world c) (:live c) (:parent c) (:owner c) (:dormant c) (:unborn c) (:pending c) (:kids c)
           (:complete c) (List.cons Join (join-new c t) (:joins c)) (:norm c)))
;; the target is a task id the host holds a handle to: allocated (`t < next-id`) and not 0 (none)
(a/defn join-ok [c :- Cell, t :- Nat] Bool
  (Bool.and (:live c) (Bool.and (Nat.blt 0 t) (Nat.blt t (:next-id (:world c))))))
(a/defn sys-join [cells :- (=> Nat Cell), k :- Nat, t :- Nat] (=> Nat Cell)
  (if (join-ok (cells k) t) (fupd cells k (join-cell (cells k) t)) cells))
;; delivery: every pending join on a complete target (every pending join, once the cell is complete)
(a/defn hj-due [w :- World, j :- Join] Join (if (task-complete w (:target j)) (hj-done j) j))
(a/defn deliver-cell [c :- Cell] Cell
  (Cell.mk (:world c) (:live c) (:parent c) (:owner c) (:dormant c) (:unborn c) (:pending c) (:kids c)
           (:complete c) (if (:complete c) (joins-map hj-done (:joins c)) (joins-map (hj-due (:world c)) (:joins c))) (:norm c)))
(a/defn sys-deliver [cells :- (=> Nat Cell), k :- Nat] (=> Nat Cell)
  (fupd cells k (deliver-cell (cells k))))
;; withdrawal (question 12): the withdraw fn `on-joined` returns, a host-side mark on join j (no gate, no item);
;; it acts on a pending join only (a delivered join stays delivered)
(a/defn withdraw-cell [c :- Cell, j :- Nat] Cell
  (Cell.mk (:world c) (:live c) (:parent c) (:owner c) (:dormant c) (:unborn c) (:pending c) (:kids c)
           (:complete c) (tbl-upd join-id j hj-drop (:joins c)) (:norm c)))
(a/defn sys-withdraw [cells :- (=> Nat Cell), k :- Nat, j :- Nat] (=> Nat Cell)
  (fupd cells k (withdraw-cell (cells k) j)))

(a/theorem sinv-accept [cells :- (=> Nat Cell), k :- Nat, m :- Nat]
  (=> (sinv cells) (sinv (sys-accept cells k m)))
  (intro hs)
  (cases hc (:complete (cells k)))
  (case [true] (simp only [sys-accept hc]) (exact hs))
  (case [false]
    (have h1 (=> (= (:live (accept-cell (cells k) m)) true) (= (p3l (:world (accept-cell (cells k) m))) true)))
    (intro hl) (simp only [accept-cell] at hl) (simp only [accept-cell]) (exact (sinv-live cells k hs hl))
    (simp only [sys-accept hc])
    (exact (sinv-put cells k (accept-cell (cells k) m) hs h1))))

(a/theorem sinv-complete [cells :- (=> Nat Cell), k :- Nat]
  (=> (sinv cells) (sinv (sys-complete cells k)))
  (intro hs)
  (cases hc (complete-ready cells k))
  (case [false] (simp only [sys-complete hc]) (exact hs))
  (case [true]
    (have h1 (=> (= (:live (complete-cell (cells k))) true) (= (p3l (:world (complete-cell (cells k)))) true)))
    (intro hl) (simp only [complete-cell] at hl) (simp only [complete-cell]) (exact (sinv-live cells k hs hl))
    (simp only [sys-complete hc])
    (exact (sinv-put cells k (complete-cell (cells k)) hs h1))))

;; a complete cell stays complete through its own steps and every system operation that keeps its
;; flag (the latch); completion soundness (complete -> released, no run, no open accepted child) and
;; its stability under the layer-1 steps of a released, quiet world are Stage B obligations
(a/theorem complete-latch [cells :- (=> Nat Cell), k :- Nat]
  (=> (= (:complete (cells k)) true) (= (:complete (sys-complete cells k k)) true))
  (intro h)
  (cases hc (complete-ready cells k))
  (case [false] (simp only [sys-complete hc]) (exact h))
  (case [true] (simp only [sys-complete hc fupd-same complete-cell])))

;; ---------------------------------------------------------------------------
;; C1c stage B (Z#71, spindel.v2.owned): owned forks. `norm` is the cell's inherited markers (W-NORMALIZE): a
;; fork, fork effect or instance starts with every marker its copied world holds; `[:normalize]` drains them.
;;   sys-own         own-child!'s count at the `(fork)` effect of cell k for the child cell m, owned by the forking
;;                   run's current scope s (`cur-scope`): a marker in k's world, in the counting branch only. With
;;                   sys-fork-effect (taken before it: the child does not inherit its own marker) and sys-accept.
;;   sys-owned-done  `[:owned-done s child]` in the owner k: the marker `child` goes, then maybe-complete!.
;;   sys-drain       `[:normalize]` in a born cell k (first turn or activation): its inherited markers go, then
;;                   maybe-complete!. An unborn cell does not drain (an E4-released one completes abandoned).
;; System operations; the engine logs the last two as items of the cell's world.
(a/defn world-cell [c :- Cell, w :- World] Cell
  (Cell.mk w (:live c) (:parent c) (:owner c) (:dormant c) (:unborn c) (:pending c) (:kids c) (:complete c) (:joins c)
           (:norm c)))
(a/defn sys-own [cells :- (=> Nat Cell), k :- Nat, s :- Nat, m :- Nat] (=> Nat Cell)
  (fupd cells k (world-cell (cells k) (own-world (:world (cells k)) s m))))
(a/defn sys-owned-done [cells :- (=> Nat Cell), k :- Nat, s :- Nat, c :- Nat] (=> Nat Cell)
  (sys-complete (fupd cells k (world-cell (cells k) (owned-done-world (:world (cells k)) s c))) k))
(a/defn drain-cell [c :- Cell] Cell
  (Cell.mk (drain-world (:world c) (:norm c)) (:live c) (:parent c) (:owner c) (:dormant c) (:unborn c) (:pending c)
           (:kids c) (:complete c) (:joins c) (List.nil Nat)))
(a/defn sys-drain [cells :- (=> Nat Cell), k :- Nat] (=> Nat Cell)
  (if (:unborn (cells k)) cells (sys-complete (fupd cells k (drain-cell (cells k))) k)))

;; ---------------------------------------------------------------------------
;; L10/L11: a world leaves the system

(a/defn drop-cell [c :- Cell] Cell
  (Cell.mk (:world c) false (:parent c) (:owner c) (:dormant c) (:unborn c) (:pending c) (:kids c) (:complete c) (:joins c) (:norm c)))

(a/defn sys-drop [cells :- (=> Nat Cell), k :- Nat] (=> Nat Cell)
  (fupd cells k (drop-cell (cells k))))

(a/theorem sinv-drop [cells :- (=> Nat Cell), k :- Nat]
  (=> (sinv cells) (sinv (sys-drop cells k)))
  (intro hs)
  (have hc (=> (= (:live (drop-cell (cells k))) true) (= (p3l (:world (drop-cell (cells k)))) true)))
  (intro hl)
  (simp only [drop-cell] at hl)
  (simp at hl)
  (simp only [sys-drop])
  (exact (sinv-put cells k (drop-cell (cells k)) hs hc)))

;; ---------------------------------------------------------------------------
;; L3: the `(fork)` effect of the run with stamp `st`. The parent's world is unchanged (its run
;; keeps the slice and continues with [:parent child]). In the child the run's copy is parked at
;; the effect and resumed with `v` = [:child nil]: a resource it arms, fired and acknowledged at
;; once, so the run is active outside its slice and the child's first item for it is `schedule`.
;; The fork resource is not dormant; the parent's armed resources are.

(a/defn fork-effect-world [w :- World, st :- Nat, kont :- Nat, v :- Nat] World
  (fire-ack (:world (world-step w (Item.arm st rk-offload kont (:next-id w)))) (:next-id w) res-ok v))

(a/theorem p3l-fork-effect-world [w :- World, st :- Nat, kont :- Nat, v :- Nat]
  (=> (= (p3l w) true) (= (p3l (fork-effect-world w st kont v)) true))
  (intro h)
  (simp only [fork-effect-world])
  (exact (p3l-fire-ack _ (:next-id w) res-ok v (step-p3l w (Item.arm st rk-offload kont (:next-id w)) h))))

(a/defn fork-effect-cell [c :- Cell, k :- Nat, owner :- Nat, st :- Nat, kont :- Nat, v :- Nat] Cell
  (Cell.mk (fork-effect-world (:world c) st kont v) true k owner
           (nat-app (res-ids (:res (:world c))) (:dormant c)) false 0 (List.nil Nat) false (List.nil Join) (marker-ids (:world c))))

(a/defn sys-fork-effect [cells :- (=> Nat Cell), k :- Nat, m :- Nat, owner :- Nat, st :- Nat, kont :- Nat, v :- Nat]
  (=> Nat Cell)
  (if (:unborn (cells k)) cells (fupd cells m (fork-effect-cell (cells k) k owner st kont v))))

;; the fork effect in an unborn cell (E4-released or not) is refused
(a/theorem fork-effect-refused [cells :- (=> Nat Cell), k :- Nat, m :- Nat, owner :- Nat, st :- Nat, kont :- Nat, v :- Nat]
  (=> (= (:unborn (cells k)) true) (= (sys-fork-effect cells k m owner st kont v) cells))
  (intro hu) (simp only [sys-fork-effect hu]))

(a/theorem fork-effect-frame [cells :- (=> Nat Cell), k :- Nat, m :- Nat, owner :- Nat, st :- Nat, kont :- Nat, v :- Nat,
                              j :- Nat]
  (=> (Not (= j m)) (= (sys-fork-effect cells k m owner st kont v j) (cells j)))
  (intro hne)
  (cases hu (:unborn (cells k)))
  (case [true] (simp only [sys-fork-effect hu]))
  (case [false] (simp only [sys-fork-effect hu fupd (nbeq-ne j m hne)])))

(a/theorem sinv-fork-effect [cells :- (=> Nat Cell), k :- Nat, m :- Nat, owner :- Nat, st :- Nat, kont :- Nat, v :- Nat]
  (=> (sinv cells) (= (:live (cells k)) true) (sinv (sys-fork-effect cells k m owner st kont v)))
  (intros hs hlk)
  (cases hu (:unborn (cells k)))
  (case [true] (simp only [sys-fork-effect hu]) (exact hs))
  (case [false]
    (have hc (=> (= (:live (fork-effect-cell (cells k) k owner st kont v)) true)
                 (= (p3l (:world (fork-effect-cell (cells k) k owner st kont v))) true)))
    (intro hl)
    (simp only [fork-effect-cell])
    (exact (p3l-fork-effect-world (:world (cells k)) st kont v (sinv-live cells k hs hlk)))
    (simp only [sys-fork-effect hu])
    (exact (sinv-put cells m (fork-effect-cell (cells k) k owner st kont v) hs hc))))

;; ---------------------------------------------------------------------------
;; L5 (S1): publish. The run with stamp `st` in world k arms a savepoint resource `fresh`;
;; the publication p records it with the world at this commit as its basis.

(a/defn publish-item [st :- Nat, kont :- Nat, fresh :- Nat] Item (Item.arm st rk-savepoint kont fresh))

(a/defn sys-publish [cells :- (=> Nat Cell), k :- Nat, st :- Nat, kont :- Nat, fresh :- Nat] (=> Nat Cell)
  (sys-step cells k (publish-item st kont fresh)))

(a/defn pubs-publish [cells :- (=> Nat Cell), pubs :- (=> Nat Pub), k :- Nat, p :- Nat, st :- Nat, kont :- Nat,
                      fresh :- Nat] (=> Nat Pub)
  (fupd pubs p (Pub.mk k fresh st (:world (world-step (:world (cells k)) (publish-item st kont fresh))) true)))

(a/theorem pinv-publish [cells :- (=> Nat Cell), pubs :- (=> Nat Pub), k :- Nat, p :- Nat, st :- Nat, kont :- Nat,
                         fresh :- Nat]
  (=> (sinv cells) (= (:live (cells k)) true) (pinv pubs) (pinv (pubs-publish cells pubs k p st kont fresh)))
  (intros hs hlk hp)
  (simp only [pinv] at hp)
  (simp only [pinv])
  (intros q hl)
  (cases hqp (Nat.beq q p))
  (case [false]
    (simp only [pubs-publish fupd hqp] at hl)
    (simp only [pubs-publish fupd hqp])
    (exact (hp q hl)))
  (case [true]
    (have e (= q p)) (exact (Nat.eq_of_beq_eq_true hqp))
    (rw [e])
    (simp only [pubs-publish fupd-same])
    (exact (step-p3l (:world (cells k)) (publish-item st kont fresh) (sinv-live cells k hs hlk)))))

;; ---------------------------------------------------------------------------
;; L6 (S2): resume in place: the savepoint fires with `ok v` in the publishing world and is acknowledged

(a/defn resume-cell [c :- Cell, z :- Nat, v :- Nat] Cell
  (Cell.mk (fire-ack (:world c) z res-ok v) (:live c) (:parent c) (:owner c) (:dormant c) (:unborn c) (:pending c)
           (:kids c) (:complete c) (:joins c) (:norm c)))

(a/defn sys-resume [cells :- (=> Nat Cell), pubs :- (=> Nat Pub), p :- Nat, v :- Nat] (=> Nat Cell)
  (fupd cells (:cell (pubs p)) (resume-cell (cells (:cell (pubs p))) (:res (pubs p)) v)))

(a/theorem sinv-resume [cells :- (=> Nat Cell), pubs :- (=> Nat Pub), p :- Nat, v :- Nat]
  (=> (sinv cells) (sinv (sys-resume cells pubs p v)))
  (intro hs)
  (have hc (=> (= (:live (resume-cell (cells (:cell (pubs p))) (:res (pubs p)) v)) true)
               (= (p3l (:world (resume-cell (cells (:cell (pubs p))) (:res (pubs p)) v))) true)))
  (intro hl)
  (simp only [resume-cell] at hl)
  (simp only [resume-cell])
  (exact (p3l-fire-ack (:world (cells (:cell (pubs p)))) (:res (pubs p)) res-ok v (sinv-live cells (:cell (pubs p)) hs hl)))
  (simp only [sys-resume])
  (exact (sinv-put cells (:cell (pubs p)) (resume-cell (cells (:cell (pubs p))) (:res (pubs p)) v) hs hc)))

;; ---------------------------------------------------------------------------
;; L7 (S3): instantiate. A new unborn cell m from the publication's basis; its pending
;; activation is the savepoint's resource.

(a/defn inst-cell [b :- Pub, owner :- Nat] Cell
  (Cell.mk (:basis b) true (:cell b) owner (res-ids (:res (:basis b))) true (:res b) (List.nil Nat) false (List.nil Join) (marker-ids (:basis b))))

(a/defn sys-instantiate [cells :- (=> Nat Cell), pubs :- (=> Nat Pub), p :- Nat, m :- Nat, owner :- Nat] (=> Nat Cell)
  (fupd cells m (inst-cell (pubs p) owner)))

(a/theorem instantiate-frame [cells :- (=> Nat Cell), pubs :- (=> Nat Pub), p :- Nat, m :- Nat, owner :- Nat, j :- Nat]
  (=> (Not (= j m)) (= (sys-instantiate cells pubs p m owner j) (cells j)))
  (intro hne)
  (simp only [sys-instantiate fupd (nbeq-ne j m hne)]))

(a/theorem instantiate-copy [cells :- (=> Nat Cell), pubs :- (=> Nat Pub), p :- Nat, m :- Nat, owner :- Nat]
  (= (:world (sys-instantiate cells pubs p m owner m)) (:basis (pubs p)))
  (simp only [sys-instantiate fupd-same inst-cell]))

;; two instances of one publication, made in any two systems, start from the same world
(a/theorem instantiate-indep [cells :- (=> Nat Cell), cells2 :- (=> Nat Cell), pubs :- (=> Nat Pub), p :- Nat,
                              m :- Nat, m2 :- Nat, owner :- Nat, owner2 :- Nat]
  (= (:world (sys-instantiate cells pubs p m owner m)) (:world (sys-instantiate cells2 pubs p m2 owner2 m2)))
  (simp only [instantiate-copy]))

(a/theorem sinv-instantiate [cells :- (=> Nat Cell), pubs :- (=> Nat Pub), p :- Nat, m :- Nat, owner :- Nat]
  (=> (sinv cells) (pinv pubs) (= (:live (pubs p)) true) (sinv (sys-instantiate cells pubs p m owner)))
  (intros hs hp hlp)
  (simp only [pinv] at hp)
  (have hc (=> (= (:live (inst-cell (pubs p) owner)) true) (= (p3l (:world (inst-cell (pubs p) owner))) true)))
  (intro hl)
  (simp only [inst-cell])
  (exact (hp p hlp))
  (simp only [sys-instantiate])
  (exact (sinv-put cells m (inst-cell (pubs p) owner) hs hc)))

;; ---------------------------------------------------------------------------
;; L8 (S4): activate. The pending savepoint fires with `ok v`; the other inherited resources are settled.

(a/defn act-ok [c :- Cell] Bool
  (Bool.and (:unborn c) (Bool.and (Bool.not (Nat.beq (:pending c) 0)) (Bool.not (:released (:world c))))))

(a/defn act-cell [c :- Cell, v :- Nat] Cell
  (Cell.mk (wake-all (fire-ack (:world c) (:pending c) res-ok v) (:dormant c)) (:live c) (:parent c) (:owner c)
           (List.nil Nat) false 0 (:kids c) (:complete c) (:joins c) (:norm c)))

(a/defn sys-activate [cells :- (=> Nat Cell), m :- Nat, v :- Nat] (=> Nat Cell)
  (if (act-ok (cells m)) (fupd cells m (act-cell (cells m) v)) cells))

(a/theorem sinv-activate [cells :- (=> Nat Cell), m :- Nat, v :- Nat]
  (=> (sinv cells) (sinv (sys-activate cells m v)))
  (intro hs)
  (cases hg (act-ok (cells m)))
  (case [false] (simp only [sys-activate hg]) (exact hs))
  (case [true]
    (have hc (=> (= (:live (act-cell (cells m) v)) true) (= (p3l (:world (act-cell (cells m) v))) true)))
    (intro hl)
    (simp only [act-cell] at hl)
    (simp only [act-cell])
    (exact (p3l-wake-all (:dormant (cells m)) _
              (p3l-fire-ack (:world (cells m)) (:pending (cells m)) res-ok v (sinv-live cells m hs hl))))
    (simp only [sys-activate hg])
    (exact (sinv-put cells m (act-cell (cells m) v) hs hc))))

;; an activated instance is born, and cannot be activated again
(a/theorem activate-born [cells :- (=> Nat Cell), m :- Nat, v :- Nat]
  (= (act-ok (sys-activate cells m v m)) false)
  (cases hg (act-ok (cells m)))
  (case [false] (simp only [sys-activate hg]))
  (case [true] (simp only [sys-activate hg fupd-same act-cell act-ok Bool.false_and])))

(a/theorem activate-once [cells :- (=> Nat Cell), m :- Nat, v :- Nat, v2 :- Nat]
  (= (sys-activate (sys-activate cells m v) m v2) (sys-activate cells m v))
  (have hb := (activate-born cells m v))
  (simp only [sys-activate hb]))

;; ---------------------------------------------------------------------------
;; L9 (S7): abandon. The publishing run is cancelled (T14) and the publication ends.

(a/defn sys-abandon [cells :- (=> Nat Cell), pubs :- (=> Nat Pub), p :- Nat] (=> Nat Cell)
  (sys-step cells (:cell (pubs p)) (Item.cancel (:run (pubs p)))))

(a/defn pubs-abandon [pubs :- (=> Nat Pub), p :- Nat] (=> Nat Pub)
  (fupd pubs p (Pub.mk (:cell (pubs p)) (:res (pubs p)) (:run (pubs p)) (:basis (pubs p)) false)))

(a/theorem pinv-abandon [pubs :- (=> Nat Pub), p :- Nat]
  (=> (pinv pubs) (pinv (pubs-abandon pubs p)))
  (intro hp)
  (simp only [pinv] at hp)
  (simp only [pinv])
  (intros q hl)
  (cases hqp (Nat.beq q p))
  (case [false]
    (simp only [pubs-abandon fupd hqp] at hl)
    (simp only [pubs-abandon fupd hqp])
    (exact (hp q hl)))
  (case [true]
    (have e (= q p)) (exact (Nat.eq_of_beq_eq_true hqp))
    (rw [e] at hl)
    (simp only [pubs-abandon fupd-same] at hl)
    (simp at hl)))

;; ---------------------------------------------------------------------------
;; L12: merge of child world c into parent world p, relative to the child's fork-time basis b.
;; The diff is the inherited sources whose version changed in the child; each is a host write (T2)
;; in the parent. The merge is refused, with no change, unless the child is quiescent, the parent
;; has not written any of those sources since the fork, and every write is accepted.

(a/defn version-of [w :- World, x :- Nat] Nat
  (match (source-find w x) [none 0] [(some s) (:version s)]))

(a/defn state-of [w :- World, x :- Nat] Nat
  (match (source-find w x) [none 0] [(some s) (:state s)]))

(a/defn diff-ids [c :- World, b :- World, xs :- (List Nat)] (List Nat)
  (match xs [nil (List.nil Nat)]
         [(cons x t) (if (Nat.beq (version-of c x) (version-of b x)) (diff-ids c b t)
                         (List.cons Nat x (diff-ids c b t)))]))

;; C0 (spec §4.3 Links and forks): links are not part of a mergeable fork's basis (each world
;; realizes its own elements); a stream the fork appended to is (its version changed: the write is
;; refused, so the merge is: stream merge is C2)
(a/defn not-link [s :- SourceRow] Bool (Bool.not (Nat.beq (:kind s) sk-link)))
(a/defn diff [c :- World, b :- World] (List Nat) (diff-ids c b (tbl-ids source-id (tbl-filter not-link (:sources b)))))

(a/defn no-conflict [p :- World, b :- World, ds :- (List Nat)] Bool
  (match ds [nil true]
         [(cons x t) (Bool.and (Nat.beq (version-of p x) (version-of b x)) (no-conflict p b t))]))

(a/defn apply-diff [p :- World, c :- World, ds :- (List Nat)] Outcome
  (match ds [nil (Outcome.mk p true)]
         [(cons x t) (if (:accepted (world-step p (Item.write x (state-of c x))))
                         (apply-diff (:world (world-step p (Item.write x (state-of c x)))) c t)
                         (Outcome.mk p false))]))

(a/defn merge-ok [p :- World, c :- World, b :- World] Bool
  (Bool.and (quiescent c)
            (Bool.and (no-conflict p b (diff c b)) (:accepted (apply-diff p c (diff c b))))))

(a/defn merge-world [p :- World, c :- World, b :- World] World
  (if (merge-ok p c b) (:world (apply-diff p c (diff c b))) p))

(a/theorem p3l-apply-diff [c :- World, ds :- (List Nat)]
  (forall [p :- World] (=> (= (p3l p) true) (= (p3l (:world (apply-diff p c ds))) true)))
  (induction ds)
  (case [nil] (intros p h) (simp only [apply-diff]) (exact h))
  (case [cons x t ih]
    (intros p h)
    (cases ha (:accepted (world-step p (Item.write x (state-of c x)))))
    (case [false] (simp only [apply-diff ha]) (exact h))
    (case [true]
      (simp only [apply-diff ha])
      (exact (ih _ (step-p3l p (Item.write x (state-of c x)) h))))))

(a/theorem p3l-merge-world [p :- World, c :- World, b :- World]
  (=> (= (p3l p) true) (= (p3l (merge-world p c b)) true))
  (intro h)
  (cases hm (merge-ok p c b))
  (case [false] (simp only [merge-world hm]) (exact h))
  (case [true] (simp only [merge-world hm]) (exact (p3l-apply-diff c (diff c b) p h))))

;; a refused merge changes nothing
(a/theorem merge-refused [p :- World, c :- World, b :- World]
  (=> (= (merge-ok p c b) false) (= (merge-world p c b) p))
  (intro hm) (simp only [merge-world hm]))

;; a child that wrote no inherited source has an empty diff, so its merge changes nothing
(a/theorem diff-ids-self [w :- World, xs :- (List Nat)]
  (= (diff-ids w w xs) (List.nil Nat))
  (induction xs)
  (case [nil] (simp only [diff-ids]))
  (case [cons x t ih] (simp only [diff-ids Nat.beq_refl ih])))

(a/theorem merge-unchanged [p :- World, b :- World]
  (= (merge-world p b b) p)
  (cases hm (merge-ok p b b))
  (case [false] (simp only [merge-world hm]))
  (case [true] (simp only [merge-world hm diff diff-ids-self apply-diff])))

(a/defn merge-cell [c :- Cell, w :- World] Cell
  (Cell.mk w (:live c) (:parent c) (:owner c) (:dormant c) (:unborn c) (:pending c) (:kids c) (:complete c) (:joins c) (:norm c)))

(a/defn sys-merge [cells :- (=> Nat Cell), k :- Nat, m :- Nat, b :- World] (=> Nat Cell)
  (fupd cells k (merge-cell (cells k) (merge-world (:world (cells k)) (:world (cells m)) b))))

(a/theorem merge-frame [cells :- (=> Nat Cell), k :- Nat, m :- Nat, b :- World, j :- Nat]
  (=> (Not (= j k)) (= (sys-merge cells k m b j) (cells j)))
  (intro hne)
  (simp only [sys-merge fupd (nbeq-ne j k hne)]))

(a/theorem sinv-merge [cells :- (=> Nat Cell), k :- Nat, m :- Nat, b :- World]
  (=> (sinv cells) (sinv (sys-merge cells k m b)))
  (intro hs)
  (have hc (=> (= (:live (merge-cell (cells k) (merge-world (:world (cells k)) (:world (cells m)) b))) true)
               (= (p3l (:world (merge-cell (cells k) (merge-world (:world (cells k)) (:world (cells m)) b)))) true)))
  (intro hl)
  (simp only [merge-cell] at hl)
  (simp only [merge-cell])
  (exact (p3l-merge-world (:world (cells k)) (:world (cells m)) b (sinv-live cells k hs hl)))
  (simp only [sys-merge])
  (exact (sinv-put cells k (merge-cell (cells k) (merge-world (:world (cells k)) (:world (cells m)) b)) hs hc)))

;; ---------------------------------------------------------------------------
;; L11: idle release. A world with nothing that can act in it or observe it may leave at any time:
;; dropping it commutes with every step of every other world.

(a/defn no-handle-c [c :- CompRow] Bool (Nat.beq (:handles c) 0))
(a/defn no-handle-k [k :- TaskRow] Bool (Nat.beq (:handles k) 0))
(a/defn no-handle-x [x :- SourceRow] Bool (Nat.beq (:handles x) 0))
(a/defn not-host-edge [e :- EdgeRow] Bool (Bool.not (host-cred e)))
(a/defn not-explicit-open [s :- ScopeRow] Bool (Bool.not (Bool.and (Nat.beq (:kind s) scope-explicit) (:open s))))

(a/defn idle-world [w :- World] Bool
  (Bool.and (nats-empty (tbl-ids run-id (:runs w)))
    (Bool.and (nats-empty (:pins w))
      (Bool.and (tbl-all not-host-edge (:edges w))
        (Bool.and (tbl-all not-explicit-open (:scopes w))
          (Bool.and (tbl-all no-handle-c (:comps w))
            (Bool.and (tbl-all no-handle-k (:tasks w)) (tbl-all no-handle-x (:sources w)))))))))

(a/defn idle-cell [c :- Cell] Bool
  (Bool.and (idle-world (:world c)) (Bool.and (Bool.not (:unborn c)) (Nat.beq (:pending c) 0))))

(a/defn sys-idle-release [cells :- (=> Nat Cell), m :- Nat] (=> Nat Cell)
  (if (idle-cell (cells m)) (sys-drop cells m) cells))

(a/theorem sinv-idle-release [cells :- (=> Nat Cell), m :- Nat]
  (=> (sinv cells) (sinv (sys-idle-release cells m)))
  (intro hs)
  (cases hi (idle-cell (cells m)))
  (case [false] (simp only [sys-idle-release hi]) (exact hs))
  (case [true] (simp only [sys-idle-release hi]) (exact (sinv-drop cells m hs))))

(a/theorem drop-step-comm [cells :- (=> Nat Cell), k :- Nat, m :- Nat, it :- Item, j :- Nat]
  (=> (Not (= k m)) (= (sys-drop (sys-step cells k it) m j) (sys-step (sys-drop cells m) k it j)))
  (intro hne)
  (have hkm := (nbeq-ne k m hne))
  (have hmk (= (Nat.beq m k) false)) (apply nbeq-ne) (intro e) (exact (hne (Eq.symm e)))
  (cases hjm (Nat.beq j m))
  (case [false]
    (cases hjk (Nat.beq j k))
    (case [false] (simp only [sys-drop sys-step fupd hjm hjk]))
    (case [true] (simp only [sys-drop sys-step fupd hjm hjk hkm])))
  (case [true]
    (have e (= j m)) (exact (Nat.eq_of_beq_eq_true hjm))
    (rw [e])
    (simp only [sys-drop sys-step fupd hmk Nat.beq_refl])))

;; the start: every live cell holds the empty world
(a/theorem sinv-init [cells :- (=> Nat Cell)]
  (=> (forall [k :- Nat] (=> (= (:live (cells k)) true) (= (:world (cells k)) empty-world)))
      (sinv cells))
  (intro h0)
  (simp only [sinv])
  (intros k hl)
  (rw [(h0 k hl)]))

;; ---------------------------------------------------------------------------
;; C1 completion soundness (W1): a live complete cell is ready (released and: unborn, or no run left
;; and every accepted child complete or collected), through every system operation. The layer-1
;; part a step needs is `wq`: a step keeps a released world released and a quiet world quiet
;; (`HQ`, the premise named in notes/PLAN.md C1).

(a/defn wq [w :- World, w2 :- World] Prop
  (And (=> (= (:released w) true) (= (:released w2) true))
       (=> (= (world-quiet w) true) (= (world-quiet w2) true))))

(a/theorem wq-refl [w :- World] (wq w w)
  (simp only [wq]) (apply And.intro) (intro h) (exact h) (intro h) (exact h))
(a/theorem wq-trans [w :- World, w2 :- World, w3 :- World] (=> (wq w w2) (wq w2 w3) (wq w w3))
  (intros h1 h2)
  (simp only [wq] at h1) (simp only [wq] at h2) (simp only [wq])
  (apply And.intro)
  (intro h) (exact ((And.left h2) ((And.left h1) h)))
  (intro h) (exact ((And.right h2) ((And.right h1) h))))

(a/theorem wq-fire-ack [hq :- (forall [w :- World, it :- Item] (=> (= (p3l w) true) (wq w (:world (world-step w it))))),
                        w :- World, z :- Nat, tag :- Nat, v :- Nat]
  (=> (= (p3l w) true) (wq w (fire-ack w z tag v)))
  (intro h)
  (simp only [fire-ack])
  (exact (wq-trans _ _ _ (hq w (Item.resource-fire z tag v) h)
           (hq _ (Item.resource-ack z) (step-p3l w (Item.resource-fire z tag v) h)))))

(a/theorem wq-wake-one [hq :- (forall [w :- World, it :- Item] (=> (= (p3l w) true) (wq w (:world (world-step w it))))),
                        w :- World, z :- Nat]
  (=> (= (p3l w) true) (wq w (wake-one w z)))
  (intro h)
  (cases hf (resource-find w z))
  (case [none] (simp only [wake-one hf]) (exact (wq-refl w)))
  (case [some r]
    (cases hk (timer-kept r))
    (case [true] (simp only [wake-one hf hk]) (exact (wq-refl w)))
    (case [false] (simp only [wake-one hf hk]) (exact (wq-fire-ack hq w z res-err err-forked h)))))

(a/theorem wq-wake-all [hq :- (forall [w :- World, it :- Item] (=> (= (p3l w) true) (wq w (:world (world-step w it))))),
                        zs :- (List Nat)]
  (forall [w :- World] (=> (= (p3l w) true) (wq w (wake-all w zs))))
  (induction zs)
  (case [nil] (intros w h) (simp only [wake-all]) (exact (wq-refl w)))
  (case [cons z t ih]
    (intros w h) (simp only [wake-all])
    (exact (wq-trans _ _ _ (wq-wake-one hq w z h) (ih (wake-one w z) (p3l-wake-one w z h))))))

(a/theorem wq-apply-diff [hq :- (forall [w :- World, it :- Item] (=> (= (p3l w) true) (wq w (:world (world-step w it))))),
                          c :- World, ds :- (List Nat)]
  (forall [p :- World] (=> (= (p3l p) true) (wq p (:world (apply-diff p c ds)))))
  (induction ds)
  (case [nil] (intros p h) (simp only [apply-diff]) (exact (wq-refl p)))
  (case [cons x t ih]
    (intros p h)
    (cases ha (:accepted (world-step p (Item.write x (state-of c x)))))
    (case [false] (simp only [apply-diff ha]) (exact (wq-refl p)))
    (case [true]
      (simp only [apply-diff ha])
      (exact (wq-trans _ _ _ (hq p (Item.write x (state-of c x)) h)
               (ih _ (step-p3l p (Item.write x (state-of c x)) h)))))))

(a/theorem wq-merge-world [hq :- (forall [w :- World, it :- Item] (=> (= (p3l w) true) (wq w (:world (world-step w it))))),
                           p :- World, c :- World, b :- World]
  (=> (= (p3l p) true) (wq p (merge-world p c b)))
  (intro h)
  (cases hm (merge-ok p c b))
  (case [false] (simp only [merge-world hm]) (exact (wq-refl p)))
  (case [true] (simp only [merge-world hm]) (exact (wq-apply-diff hq c (diff c b) p h))))

;; C1c stage B: a layer-1 world has no fork marker (gw, spindel.v2.qworld `p3l-forks-nil`)
(a/theorem p3l-no-markers [w :- World] (=> (= (p3l w) true) (= (no-markers w) true))
  (intro h) (simp only [no-markers (p3l-forks-nil w h)]))

;; ---- the invariant
(a/defn cinv [cells :- (=> Nat Cell)] Prop
  (forall [k :- Nat] (=> (= (:live (cells k)) true) (= (:complete (cells k)) true) (= (complete-ready cells k) true))))
(a/defn kid-done-c [c :- Cell] Bool (Bool.or (Bool.not (:live c)) (:complete c)))
(a/defn nat-ne [m :- Nat, x :- Nat] Bool (Bool.not (Nat.beq x m)))

(a/theorem kids-mono [cells :- (=> Nat Cell), cells2 :- (=> Nat Cell),
                      hm :- (forall [x :- Nat] (=> (= (kid-done cells x) true) (= (kid-done cells2 x) true))), xs :- (List Nat)]
  (=> (= (tbl-all (kid-done cells) xs) true) (= (tbl-all (kid-done cells2) xs) true))
  (induction xs)
  (case [nil] (intro h) (simp only [tbl-all]))
  (case [cons x t ih]
    (intro h) (simp only [tbl-all Bool.and_eq_true] at h)
    (simp only [tbl-all (hm x (And.left h)) (ih (And.right h)) Bool.and_self])))

;; one cell k is replaced by c2: kid-done can only become true (it does not undo a child's
;; completion or collection), and a live complete c2 is ready in the new system
(a/theorem cinv-put [cells :- (=> Nat Cell), k :- Nat, c2 :- Cell]
  (=> (cinv cells)
      (=> (= (kid-done-c (cells k)) true) (= (kid-done-c c2) true))
      (=> (= (:live c2) true) (= (:complete c2) true) (= (complete-ready (fupd cells k c2) k) true))
      (cinv (fupd cells k c2)))
  (intros hc hd hr)
  (have hm (forall [x :- Nat] (=> (= (kid-done cells x) true) (= (kid-done (fupd cells k c2) x) true))))
  (intros x hx)
  (cases hxk (Nat.beq x k))
  (case [false] (simp only [kid-done fupd hxk]) (simp only [kid-done] at hx) (exact hx))
  (case [true]
    (have e (= x k)) (exact (Nat.eq_of_beq_eq_true hxk))
    (rw [e] at hx) (rw [e])
    (simp only [kid-done fupd-same]) (simp only [kid-done] at hx)
    (exact (hd hx)))
  (simp only [cinv] at hc) (simp only [cinv])
  (intros j hl hj)
  (cases hjk (Nat.beq j k))
  (case [true]
    (have e (= j k)) (exact (Nat.eq_of_beq_eq_true hjk))
    (rw [e] at hl hj) (rw [e])
    (simp only [fupd-same] at hl hj)
    (exact (hr hl hj)))
  (case [false]
    (simp only [fupd hjk] at hl hj)
    (have r0 := (hc j hl hj))
    (simp only [complete-ready fupd hjk])
    (simp only [complete-ready Bool.and_eq_true Bool.or_eq_true] at r0)
    (have r1 := (And.right r0))
    (cases r1)
    (case [inl u] (simp only [(And.left r0) u Bool.true_or Bool.and_self]))
    (case [inr q]
      (have k2 := (kids-mono cells (fupd cells k c2) hm (:kids (cells j)) (And.left (And.right q))))
      (simp only [(And.left r0) (And.left q) k2 (And.right (And.right q)) Bool.and_self Bool.or_true]))))

(a/theorem kd-put-mono [cells :- (=> Nat Cell), k :- Nat, c2 :- Cell]
  (=> (=> (= (kid-done-c (cells k)) true) (= (kid-done-c c2) true))
      (forall [x :- Nat] (=> (= (kid-done cells x) true) (= (kid-done (fupd cells k c2) x) true))))
  (intros hd x hx)
  (cases hxk (Nat.beq x k))
  (case [false] (simp only [kid-done fupd hxk]) (simp only [kid-done] at hx) (exact hx))
  (case [true]
    (have e (= x k)) (exact (Nat.eq_of_beq_eq_true hxk))
    (rw [e] at hx) (rw [e])
    (simp only [kid-done fupd-same]) (simp only [kid-done] at hx)
    (exact (hd hx))))

;; a ready cell stays ready when it is replaced by c2 with the same unborn flag and kids, a world
;; that `wq` relates to its own, and a kid-done that does not regress
(a/theorem ready-put [cells :- (=> Nat Cell), k :- Nat, c2 :- Cell]
  (=> (= (complete-ready cells k) true) (wq (:world (cells k)) (:world c2))
      (= (:unborn c2) (:unborn (cells k))) (= (:kids c2) (:kids (cells k)))
      (=> (= (kid-done-c (cells k)) true) (= (kid-done-c c2) true))
      (=> (= (no-markers (:world (cells k))) true) (= (no-markers (:world c2)) true))
      (= (complete-ready (fupd cells k c2) k) true))
  (intros r0 hw hu hk hd hn)
  (simp only [wq] at hw)
  (simp only [complete-ready Bool.and_eq_true Bool.or_eq_true] at r0)
  (have rel := ((And.left hw) (And.left r0)))
  (simp only [complete-ready fupd-same hu hk rel Bool.true_and])
  (have r1 := (And.right r0))
  (cases r1)
  (case [inl u] (simp only [u Bool.true_or]))
  (case [inr q]
    (have hq0 (= (world-quiet (:world (cells k))) true)) (simp only [world-quiet (And.left r0) (And.left q) Bool.and_self])
    (have hq2 := ((And.right hw) hq0))
    (simp only [world-quiet Bool.and_eq_true] at hq2)
    (have k2 := (kids-mono cells (fupd cells k c2) (kd-put-mono cells k c2 hd) (:kids (cells k)) (And.left (And.right q))))
    (simp only [(And.right hq2) k2 (hn (And.right (And.right q))) Bool.and_self Bool.or_true])))

;; a world change of a cell that keeps its other fields
(a/theorem cinv-world [cells :- (=> Nat Cell), k :- Nat, c2 :- Cell]
  (=> (cinv cells) (= (:live c2) (:live (cells k))) (= (:complete c2) (:complete (cells k)))
      (= (:unborn c2) (:unborn (cells k))) (= (:kids c2) (:kids (cells k)))
      (=> (= (:live (cells k)) true) (wq (:world (cells k)) (:world c2)))
      (=> (= (:live (cells k)) true) (= (no-markers (:world (cells k))) true) (= (no-markers (:world c2)) true))
      (cinv (fupd cells k c2)))
  (intros hc hl hcp hu hk hw hn)
  (have hd (=> (= (kid-done-c (cells k)) true) (= (kid-done-c c2) true)))
  (intro h) (simp only [kid-done-c hl hcp]) (simp only [kid-done-c] at h) (exact h)
  (apply (cinv-put cells k c2 hc hd))
  (intros l2 c2t)
  (have l1 (= (:live (cells k)) true)) (rw [← hl]) (exact l2)
  (have c1 (= (:complete (cells k)) true)) (rw [← hcp]) (exact c2t)
  (have hc2 := hc) (simp only [cinv] at hc2)
  (exact (ready-put cells k c2 (hc2 k l1 c1) (hw l1) hu hk hd (hn l1))))

(a/theorem kids-fresh [cells :- (=> Nat Cell), m :- Nat, c2 :- Cell, xs :- (List Nat)]
  (=> (= (tbl-all (nat-ne m) xs) true) (= (tbl-all (kid-done cells) xs) true) (= (tbl-all (kid-done (fupd cells m c2)) xs) true))
  (induction xs)
  (case [nil] (intros h1 h2) (simp only [tbl-all]))
  (case [cons x t ih]
    (intros h1 h2)
    (simp only [tbl-all Bool.and_eq_true] at h1 h2)
    (have ne (= (Nat.beq x m) false)) (have z := (And.left h1)) (simp only [nat-ne] at z) (exact (bnot-true _ z))
    (simp only [tbl-all kid-done fupd ne])
    (have z2 := (And.left h2)) (simp only [kid-done] at z2)
    (simp only [z2 (ih (And.right h1) (And.right h2)) Bool.and_self])))

;; a new cell at an id no cell has accepted, not complete
(a/theorem cinv-fresh [cells :- (=> Nat Cell), m :- Nat, c2 :- Cell]
  (=> (cinv cells) (forall [j :- Nat] (= (tbl-all (nat-ne m) (:kids (cells j))) true)) (= (:complete c2) false)
      (cinv (fupd cells m c2)))
  (intros hc hf hn)
  (simp only [cinv] at hc) (simp only [cinv])
  (intros j hl hj)
  (cases hjm (Nat.beq j m))
  (case [true]
    (have e (= j m)) (exact (Nat.eq_of_beq_eq_true hjm))
    (rw [e] at hj) (simp only [fupd-same hn] at hj) (cases hj))
  (case [false]
    (simp only [fupd hjm] at hl hj)
    (have r0 := (hc j hl hj))
    (simp only [complete-ready fupd hjm])
    (simp only [complete-ready Bool.and_eq_true Bool.or_eq_true] at r0)
    (have r1 := (And.right r0))
    (cases r1)
    (case [inl u] (simp only [(And.left r0) u Bool.true_or Bool.and_self]))
    (case [inr q]
      (have k2 := (kids-fresh cells m c2 (:kids (cells j)) (hf j) (And.left (And.right q))))
      (simp only [(And.left r0) (And.left q) k2 (And.right (And.right q)) Bool.and_self Bool.or_true]))))

;; ---- every system operation keeps cinv (HQ: a layer-1 step keeps a released world released and a
;; quiet one quiet; fork, fork effect and instance take an id no cell has accepted)
(a/theorem cinv-step [hq :- (forall [w :- World, it :- Item] (=> (= (p3l w) true) (wq w (:world (world-step w it))))), cells :- (=> Nat Cell), k :- Nat, it :- Item]
  (=> (sinv cells) (cinv cells) (cinv (sys-step cells k it)))
  (intros hs hc)
  (simp only [sys-step])
  (exact (cinv-world cells k (cell-step (cells k) it) hc (rfl) (rfl) (rfl) (rfl)
           (fn [hl :- (= (:live (cells k)) true)] (hq (:world (cells k)) it (sinv-live cells k hs hl)))
           (fn [hl :- (= (:live (cells k)) true), hn0 :- (= (no-markers (:world (cells k))) true)] (p3l-no-markers _ (step-p3l (:world (cells k)) it (sinv-live cells k hs hl)))))))

(a/theorem cinv-wake [hq :- (forall [w :- World, it :- Item] (=> (= (p3l w) true) (wq w (:world (world-step w it))))), cells :- (=> Nat Cell), k :- Nat]
  (=> (sinv cells) (cinv cells) (cinv (sys-wake cells k)))
  (intros hs hc)
  (cases hu (:unborn (cells k)))
  (case [true] (simp only [sys-wake hu]) (exact hc))
  (case [false]
    (simp only [sys-wake hu])
    (exact (cinv-world cells k (wake-cell (cells k)) hc (rfl) (rfl) (rfl) (rfl)
             (fn [hl :- (= (:live (cells k)) true)] (wq-wake-all hq (:dormant (cells k)) (:world (cells k)) (sinv-live cells k hs hl)))
             (fn [hl :- (= (:live (cells k)) true), hn0 :- (= (no-markers (:world (cells k))) true)] (p3l-no-markers _ (p3l-wake-all (:dormant (cells k)) (:world (cells k)) (sinv-live cells k hs hl))))))))

(a/theorem cinv-resume [hq :- (forall [w :- World, it :- Item] (=> (= (p3l w) true) (wq w (:world (world-step w it))))), cells :- (=> Nat Cell), pubs :- (=> Nat Pub), p :- Nat, v :- Nat]
  (=> (sinv cells) (cinv cells) (cinv (sys-resume cells pubs p v)))
  (intros hs hc)
  (simp only [sys-resume])
  (exact (cinv-world cells (:cell (pubs p)) (resume-cell (cells (:cell (pubs p))) (:res (pubs p)) v) hc (rfl) (rfl) (rfl) (rfl)
           (fn [hl :- (= (:live (cells (:cell (pubs p)))) true)]
             (wq-fire-ack hq (:world (cells (:cell (pubs p)))) (:res (pubs p)) res-ok v (sinv-live cells (:cell (pubs p)) hs hl)))
           (fn [hl :- (= (:live (cells (:cell (pubs p)))) true), hn0 :- (= (no-markers (:world (cells (:cell (pubs p))))) true)] (p3l-no-markers _ (p3l-fire-ack (:world (cells (:cell (pubs p)))) (:res (pubs p)) res-ok v (sinv-live cells (:cell (pubs p)) hs hl)))))))

(a/theorem cinv-merge [hq :- (forall [w :- World, it :- Item] (=> (= (p3l w) true) (wq w (:world (world-step w it))))), cells :- (=> Nat Cell), k :- Nat, m :- Nat, b :- World]
  (=> (sinv cells) (cinv cells) (cinv (sys-merge cells k m b)))
  (intros hs hc)
  (simp only [sys-merge])
  (exact (cinv-world cells k (merge-cell (cells k) (merge-world (:world (cells k)) (:world (cells m)) b)) hc (rfl) (rfl) (rfl) (rfl)
           (fn [hl :- (= (:live (cells k)) true)] (wq-merge-world hq (:world (cells k)) (:world (cells m)) b (sinv-live cells k hs hl)))
           (fn [hl :- (= (:live (cells k)) true), hn0 :- (= (no-markers (:world (cells k))) true)] (p3l-no-markers _ (p3l-merge-world (:world (cells k)) (:world (cells m)) b (sinv-live cells k hs hl)))))))

(a/theorem cinv-publish [hq :- (forall [w :- World, it :- Item] (=> (= (p3l w) true) (wq w (:world (world-step w it))))), cells :- (=> Nat Cell), k :- Nat, st :- Nat, kont :- Nat, fresh :- Nat]
  (=> (sinv cells) (cinv cells) (cinv (sys-publish cells k st kont fresh)))
  (intros hs hc) (simp only [sys-publish]) (exact (cinv-step hq cells k _ hs hc)))

(a/theorem cinv-abandon [hq :- (forall [w :- World, it :- Item] (=> (= (p3l w) true) (wq w (:world (world-step w it))))), cells :- (=> Nat Cell), pubs :- (=> Nat Pub), p :- Nat]
  (=> (sinv cells) (cinv cells) (cinv (sys-abandon cells pubs p)))
  (intros hs hc) (simp only [sys-abandon]) (exact (cinv-step hq cells _ _ hs hc)))

(a/theorem cinv-drop [cells :- (=> Nat Cell), k :- Nat]
  (=> (cinv cells) (cinv (sys-drop cells k)))
  (intro hc)
  (simp only [sys-drop])
  (apply (cinv-put cells k (drop-cell (cells k)) hc))
  (intro h) (simp only [kid-done-c drop-cell Bool.not_false Bool.true_or])
  (intros hl hj) (simp only [drop-cell] at hl) (cases hl))

(a/theorem cinv-idle-release [cells :- (=> Nat Cell), m :- Nat]
  (=> (cinv cells) (cinv (sys-idle-release cells m)))
  (intro hc)
  (cases hi (idle-cell (cells m)))
  (case [false] (simp only [sys-idle-release hi]) (exact hc))
  (case [true] (simp only [sys-idle-release hi]) (exact (cinv-drop cells m hc))))

(a/theorem cinv-accept [cells :- (=> Nat Cell), k :- Nat, m :- Nat]
  (=> (cinv cells) (cinv (sys-accept cells k m)))
  (intro hc)
  (cases hk (:complete (cells k)))
  (case [true] (simp only [sys-accept hk]) (exact hc))
  (case [false]
    (simp only [sys-accept hk])
    (apply (cinv-put cells k (accept-cell (cells k) m) hc))
    (intro h) (simp only [kid-done-c accept-cell]) (simp only [kid-done-c] at h) (exact h)
    (intros hl hj) (simp only [accept-cell hk] at hj) (cases hj)))

(a/theorem cinv-complete [cells :- (=> Nat Cell), k :- Nat]
  (=> (cinv cells) (cinv (sys-complete cells k)))
  (intro hc)
  (cases hr (complete-ready cells k))
  (case [false] (simp only [sys-complete hr]) (exact hc))
  (case [true]
    (simp only [sys-complete hr])
    (have hd (=> (= (kid-done-c (cells k)) true) (= (kid-done-c (complete-cell (cells k))) true)))
    (intro h) (simp only [kid-done-c complete-cell Bool.or_true])
    (apply (cinv-put cells k (complete-cell (cells k)) hc hd))
    (intros hl hj)
    (exact (ready-put cells k (complete-cell (cells k)) hr (wq-refl (:world (cells k))) (rfl) (rfl) hd (self-imp _)))))

;; a complete cell is released (cinv), so the E4 release and an activation never touch one
(a/theorem complete-released [cells :- (=> Nat Cell), k :- Nat]
  (=> (cinv cells) (= (:live (cells k)) true) (= (:complete (cells k)) true) (= (:released (:world (cells k))) true))
  (intros hc hl hk)
  (simp only [cinv] at hc)
  (have r := (hc k hl hk))
  (simp only [complete-ready Bool.and_eq_true] at r)
  (exact (And.left r)))

(a/theorem cinv-release-unborn [cells :- (=> Nat Cell), k :- Nat]
  (=> (cinv cells) (cinv (sys-release-unborn cells k)))
  (intro hc)
  (cases hg (Bool.and (:unborn (cells k)) (Bool.not (:released (:world (cells k))))))
  (case [false] (simp only [sys-release-unborn hg]) (exact hc))
  (case [true]
    (simp only [sys-release-unborn hg])
    (simp only [Bool.and_eq_true] at hg)
    (have nr := (bnot-true _ (And.right hg)))
    (apply (cinv-put cells k (release-unborn-cell (cells k)) hc))
    (intro h) (simp only [kid-done-c release-unborn-cell]) (simp only [kid-done-c] at h) (exact h)
    (intros hl hj)
    (simp only [release-unborn-cell] at hl hj)
    (have z := (complete-released cells k hc hl hj))
    (rw [nr] at z) (cases z)))

(a/theorem cinv-activate [cells :- (=> Nat Cell), m :- Nat, v :- Nat]
  (=> (cinv cells) (cinv (sys-activate cells m v)))
  (intro hc)
  (cases hg (act-ok (cells m)))
  (case [false] (simp only [sys-activate hg]) (exact hc))
  (case [true]
    (simp only [sys-activate hg])
    (simp only [act-ok Bool.and_eq_true] at hg)
    (have nr := (bnot-true _ (And.right (And.right hg))))
    (apply (cinv-put cells m (act-cell (cells m) v) hc))
    (intro h) (simp only [kid-done-c act-cell]) (simp only [kid-done-c] at h) (exact h)
    (intros hl hj)
    (simp only [act-cell] at hl hj)
    (have z := (complete-released cells m hc hl hj))
    (rw [nr] at z) (cases z)))

(a/theorem cinv-fork [cells :- (=> Nat Cell), k :- Nat, m :- Nat, owner :- Nat]
  (=> (cinv cells) (forall [j :- Nat] (= (tbl-all (nat-ne m) (:kids (cells j))) true)) (cinv (sys-fork cells k m owner)))
  (intros hc hf)
  (cases hu (:unborn (cells k)))
  (case [true] (simp only [sys-fork hu]) (exact hc))
  (case [false] (simp only [sys-fork hu]) (exact (cinv-fresh cells m (fork-cell (cells k) k owner) hc hf (rfl)))))

(a/theorem cinv-fork-effect [cells :- (=> Nat Cell), k :- Nat, m :- Nat, owner :- Nat, st :- Nat, kont :- Nat, v :- Nat]
  (=> (cinv cells) (forall [j :- Nat] (= (tbl-all (nat-ne m) (:kids (cells j))) true))
      (cinv (sys-fork-effect cells k m owner st kont v)))
  (intros hc hf)
  (cases hu (:unborn (cells k)))
  (case [true] (simp only [sys-fork-effect hu]) (exact hc))
  (case [false]
    (simp only [sys-fork-effect hu])
    (exact (cinv-fresh cells m (fork-effect-cell (cells k) k owner st kont v) hc hf (rfl)))))

(a/theorem cinv-instantiate [cells :- (=> Nat Cell), pubs :- (=> Nat Pub), p :- Nat, m :- Nat, owner :- Nat]
  (=> (cinv cells) (forall [j :- Nat] (= (tbl-all (nat-ne m) (:kids (cells j))) true))
      (cinv (sys-instantiate cells pubs p m owner)))
  (intros hc hf) (simp only [sys-instantiate]) (exact (cinv-fresh cells m (inst-cell (pubs p) owner) hc hf (rfl))))

;; a system whose cells are all not complete satisfies cinv (e.g. a fresh system)
(a/theorem cinv-none [cells :- (=> Nat Cell)]
  (=> (forall [k :- Nat] (= (:complete (cells k)) false)) (cinv cells))
  (intro h) (simp only [cinv]) (intros k hl hk) (rw [(h k)] at hk) (cases hk))

;; ---- E4: the release of an unborn instance keeps the system invariant. `p3l` reads no `released`
;; flag (it is checked definitionally: every bundle of p3l is a function of the other tables).
(a/theorem p3l-release-unborn [w :- World] (= (p3l (release-unborn w)) (p3l w)) (rfl))

(a/theorem sinv-release-unborn [cells :- (=> Nat Cell), k :- Nat]
  (=> (sinv cells) (sinv (sys-release-unborn cells k)))
  (intro hs)
  (cases hg (Bool.and (:unborn (cells k)) (Bool.not (:released (:world (cells k))))))
  (case [false] (simp only [sys-release-unborn hg]) (exact hs))
  (case [true]
    (simp only [sys-release-unborn hg])
    (have hc (=> (= (:live (release-unborn-cell (cells k))) true) (= (p3l (:world (release-unborn-cell (cells k)))) true)))
    (intro hl)
    (simp only [release-unborn-cell] at hl)
    (simp only [release-unborn-cell p3l-release-unborn])
    (exact (sinv-live cells k hs hl))
    (exact (sinv-put cells k (release-unborn-cell (cells k)) hs hc))))

;; ---------------------------------------------------------------------------
;; C1 completion stability without `hq` (spindel.v2.quiet, spindel.v2.qworld): every live cell is an
;; E4-released unborn instance or holds `qinv` (K, gc, I3 besides p3l), and every live publication's
;; basis is released or holds qinv. A layer-1 step (and every composite of steps) keeps a released
;; world released (`step-released`) and leaves a quiet qinv world as it is (`quiet-step`); an unborn
;; cell is ready by its flag, so it needs only the released half (`wqc`).

(a/defn cq [c :- Cell] Bool (Bool.or (Bool.and (:unborn c) (:released (:world c))) (qinv (:world c))))
(a/defn qsinv [cells :- (=> Nat Cell)] Prop
  (forall [k :- Nat] (=> (= (:live (cells k)) true) (= (cq (cells k)) true))))
(a/defn qpinv [pubs :- (=> Nat Pub)] Prop
  (forall [p :- Nat] (=> (= (:live (pubs p)) true) (= (Bool.or (:released (:basis (pubs p))) (qinv (:basis (pubs p)))) true))))

(a/theorem qsinv-live [cells :- (=> Nat Cell), k :- Nat]
  (=> (qsinv cells) (= (:live (cells k)) true) (= (cq (cells k)) true))
  (intros hs hl) (simp only [qsinv] at hs) (exact (hs k hl)))
(a/theorem qsinv-put [cells :- (=> Nat Cell), k :- Nat, c2 :- Cell]
  (=> (qsinv cells) (=> (= (:live c2) true) (= (cq c2) true)) (qsinv (fupd cells k c2)))
  (intros hs hc)
  (simp only [qsinv] at hs) (simp only [qsinv])
  (intros j hl)
  (cases hjk (Nat.beq j k))
  (case [false] (simp only [fupd hjk] at hl) (simp only [fupd hjk]) (exact (hs j hl)))
  (case [true]
    (have e (= j k)) (exact (Nat.eq_of_beq_eq_true hjk))
    (rw [e] at hl) (rw [e]) (simp only [fupd-same] at hl) (simp only [fupd-same]) (exact (hc hl))))
(a/theorem cq-born [c :- Cell] (=> (= (cq c) true) (= (:unborn c) false) (= (qinv (:world c)) true))
  (intros h hu) (simp only [cq hu Bool.false_and Bool.false_or] at h) (exact h))
(a/theorem cq-trans [c :- Cell, c2 :- Cell]
  (=> (= (:unborn c2) (:unborn c)) (=> (= (:released (:world c)) true) (= (:released (:world c2)) true))
      (=> (= (qinv (:world c)) true) (= (qinv (:world c2)) true)) (= (cq c) true) (= (cq c2) true))
  (intros hu hr hq h)
  (simp only [cq Bool.or_eq_true Bool.and_eq_true] at h)
  (cases h)
  (case [inl a] (simp only [cq hu (And.left a) (hr (And.right a)) Bool.and_self Bool.true_or]))
  (case [inr b] (simp only [cq (hq b) Bool.or_true])))
(a/theorem qacc [w :- World, it :- Item] (=> (= (qh w) true) (= (:accepted (world-step w it)) false))
  (intro h) (rw [(step-refuse w it (quiet-refused w it h))]))

;; ---- released stays through the composites
(a/theorem rel-step [w :- World, it :- Item]
  (=> (= (p3l w) true) (= (:released w) true) (= (:released (:world (world-step w it))) true))
  (intros h hr) (exact (step-released w it (p3l-p3b w h) hr)))
(a/theorem rel-fire-ack [w :- World, z :- Nat, tag :- Nat, v :- Nat]
  (=> (= (p3l w) true) (= (:released w) true) (= (:released (fire-ack w z tag v)) true))
  (intros h hr) (simp only [fire-ack])
  (exact (rel-step _ (Item.resource-ack z) (step-p3l w (Item.resource-fire z tag v) h) (rel-step w (Item.resource-fire z tag v) h hr))))
(a/theorem rel-wake-one [w :- World, z :- Nat]
  (=> (= (p3l w) true) (= (:released w) true) (= (:released (wake-one w z)) true))
  (intros h hr)
  (cases hf (resource-find w z))
  (case [none] (simp only [wake-one hf]) (exact hr))
  (case [some r]
    (cases hk (timer-kept r))
    (case [true] (simp only [wake-one hf hk]) (exact hr))
    (case [false] (simp only [wake-one hf hk]) (exact (rel-fire-ack w z res-err err-forked h hr)))))
(a/theorem rel-wake-all [zs :- (List Nat)]
  (forall [w :- World] (=> (= (p3l w) true) (= (:released w) true) (= (:released (wake-all w zs)) true)))
  (induction zs)
  (case [nil] (intros w h hr) (simp only [wake-all]) (exact hr))
  (case [cons z t ih] (intros w h hr) (simp only [wake-all]) (exact (ih (wake-one w z) (p3l-wake-one w z h) (rel-wake-one w z h hr)))))
(a/theorem rel-apply-diff [c :- World, ds :- (List Nat)]
  (forall [p :- World] (=> (= (p3l p) true) (= (:released p) true) (= (:released (:world (apply-diff p c ds))) true)))
  (induction ds)
  (case [nil] (intros p h hr) (simp only [apply-diff]) (exact hr))
  (case [cons x t ih]
    (intros p h hr)
    (cases ha (:accepted (world-step p (Item.write x (state-of c x)))))
    (case [false] (simp only [apply-diff ha]) (exact hr))
    (case [true]
      (simp only [apply-diff ha])
      (exact (ih _ (step-p3l p (Item.write x (state-of c x)) h) (rel-step p (Item.write x (state-of c x)) h hr))))))
(a/theorem rel-merge-world [p :- World, c :- World, b :- World]
  (=> (= (p3l p) true) (= (:released p) true) (= (:released (merge-world p c b)) true))
  (intros h hr)
  (cases hm (merge-ok p c b))
  (case [false] (simp only [merge-world hm]) (exact hr))
  (case [true] (simp only [merge-world hm]) (exact (rel-apply-diff c (diff c b) p h hr))))

;; ---- a quiet qinv world: every composite is the identity
(a/theorem qid-fire-ack [w :- World, z :- Nat, tag :- Nat, v :- Nat] (=> (= (qh w) true) (= (fire-ack w z tag v) w))
  (intro h) (simp only [fire-ack])
  (rw [(quiet-step w (Item.resource-fire z tag v) h)]) (exact (quiet-step w (Item.resource-ack z) h)))
(a/theorem qid-wake-one [w :- World, z :- Nat] (=> (= (qh w) true) (= (wake-one w z) w))
  (intro h)
  (cases hf (resource-find w z))
  (case [none] (simp only [wake-one hf]))
  (case [some r]
    (cases hk (timer-kept r))
    (case [true] (simp only [wake-one hf hk]))
    (case [false] (simp only [wake-one hf hk]) (exact (qid-fire-ack w z res-err err-forked h)))))
(a/theorem qid-wake-all [zs :- (List Nat)] (forall [w :- World] (=> (= (qh w) true) (= (wake-all w zs) w)))
  (induction zs)
  (case [nil] (intros w h) (simp only [wake-all]))
  (case [cons z t ih] (intros w h) (simp only [wake-all]) (rw [(qid-wake-one w z h)]) (exact (ih w h))))
(a/theorem qid-apply-diff [p :- World, c :- World, ds :- (List Nat)] (=> (= (qh p) true) (= (:world (apply-diff p c ds)) p))
  (intro h)
  (cases ds)
  (case [nil] (simp only [apply-diff]))
  (case [cons x t] (simp only [apply-diff (qacc p (Item.write x (state-of c x)) h)])))
(a/theorem qid-merge-world [p :- World, c :- World, b :- World] (=> (= (qh p) true) (= (merge-world p c b) p))
  (intro h)
  (cases hm (merge-ok p c b))
  (case [false] (simp only [merge-world hm]))
  (case [true] (simp only [merge-world hm]) (exact (qid-apply-diff p c (diff c b) h))))

;; ---- qinv through the composites
(a/theorem qinv-fire-ack [w :- World, z :- Nat, tag :- Nat, v :- Nat] (=> (= (qinv w) true) (= (qinv (fire-ack w z tag v)) true))
  (intro h) (simp only [fire-ack]) (exact (step-qinv _ (Item.resource-ack z) (step-qinv w (Item.resource-fire z tag v) h))))
(a/theorem qinv-wake-one [w :- World, z :- Nat] (=> (= (qinv w) true) (= (qinv (wake-one w z)) true))
  (intro h)
  (cases hf (resource-find w z))
  (case [none] (simp only [wake-one hf]) (exact h))
  (case [some r]
    (cases hk (timer-kept r))
    (case [true] (simp only [wake-one hf hk]) (exact h))
    (case [false] (simp only [wake-one hf hk]) (exact (qinv-fire-ack w z res-err err-forked h)))))
(a/theorem qinv-wake-all [zs :- (List Nat)] (forall [w :- World] (=> (= (qinv w) true) (= (qinv (wake-all w zs)) true)))
  (induction zs)
  (case [nil] (intros w h) (simp only [wake-all]) (exact h))
  (case [cons z t ih] (intros w h) (simp only [wake-all]) (exact (ih (wake-one w z) (qinv-wake-one w z h)))))
(a/theorem qinv-apply-diff [c :- World, ds :- (List Nat)]
  (forall [p :- World] (=> (= (qinv p) true) (= (qinv (:world (apply-diff p c ds))) true)))
  (induction ds)
  (case [nil] (intros p h) (simp only [apply-diff]) (exact h))
  (case [cons x t ih]
    (intros p h)
    (cases ha (:accepted (world-step p (Item.write x (state-of c x)))))
    (case [false] (simp only [apply-diff ha]) (exact h))
    (case [true] (simp only [apply-diff ha]) (exact (ih _ (step-qinv p (Item.write x (state-of c x)) h))))))
(a/theorem qinv-merge-world [p :- World, c :- World, b :- World] (=> (= (qinv p) true) (= (qinv (merge-world p c b)) true))
  (intro h)
  (cases hm (merge-ok p c b))
  (case [false] (simp only [merge-world hm]) (exact h))
  (case [true] (simp only [merge-world hm]) (exact (qinv-apply-diff c (diff c b) p h))))
(a/theorem qinv-fork-effect-world [w :- World, st :- Nat, kont :- Nat, v :- Nat]
  (=> (= (qinv w) true) (= (qinv (fork-effect-world w st kont v)) true))
  (intro h) (simp only [fork-effect-world])
  (exact (qinv-fire-ack _ (:next-id w) res-ok v (step-qinv w (Item.arm st rk-offload kont (:next-id w)) h))))

;; ---- the cell-level relation: released stays; a born cell's quiet world stays quiet
(a/defn wqc [c :- Cell, w2 :- World] Prop
  (And (=> (= (:released (:world c)) true) (= (:released w2) true))
       (=> (= (:unborn c) false) (= (world-quiet (:world c)) true) (= (world-quiet w2) true))))
(a/theorem wqc-of [c :- Cell, w2 :- World]
  (=> (= (cq c) true) (=> (= (:released (:world c)) true) (= (:released w2) true))
      (=> (= (qh (:world c)) true) (= w2 (:world c))) (wqc c w2))
  (intros hc hr hid)
  (simp only [wqc])
  (apply And.intro)
  (exact hr)
  (intros hu hq)
  (have e := (hid (qh-of _ (cq-born c hc hu) hq)))
  (rw [e]) (exact hq))

(a/theorem ready-put-q [cells :- (=> Nat Cell), k :- Nat, c2 :- Cell]
  (=> (= (complete-ready cells k) true) (wqc (cells k) (:world c2))
      (= (:unborn c2) (:unborn (cells k))) (= (:kids c2) (:kids (cells k)))
      (=> (= (kid-done-c (cells k)) true) (= (kid-done-c c2) true))
      (=> (= (no-markers (:world (cells k))) true) (= (no-markers (:world c2)) true))
      (= (complete-ready (fupd cells k c2) k) true))
  (intros r0 hw hu hk hd hn)
  (simp only [wqc] at hw)
  (simp only [complete-ready Bool.and_eq_true Bool.or_eq_true] at r0)
  (have rel := ((And.left hw) (And.left r0)))
  (simp only [complete-ready fupd-same hu hk rel Bool.true_and])
  (cases hub (:unborn (cells k)))
  (case [true] (simp only [Bool.true_or]))
  (case [false]
    (have r1 := (And.right r0))
    (cases r1)
    (case [inl u] (rw [hub] at u) (cases u))
    (case [inr q]
      (have hq0 (= (world-quiet (:world (cells k))) true)) (simp only [world-quiet (And.left r0) (And.left q) Bool.and_self])
      (have hq2 := ((And.right hw) hub hq0))
      (simp only [world-quiet Bool.and_eq_true] at hq2)
      (have k2 := (kids-mono cells (fupd cells k c2) (kd-put-mono cells k c2 hd) (:kids (cells k)) (And.left (And.right q))))
      (simp only [(And.right hq2) k2 (hn (And.right (And.right q))) Bool.and_self Bool.or_true]))))

(a/theorem cinv-world-q [cells :- (=> Nat Cell), k :- Nat, c2 :- Cell]
  (=> (cinv cells) (= (:live c2) (:live (cells k))) (= (:complete c2) (:complete (cells k)))
      (= (:unborn c2) (:unborn (cells k))) (= (:kids c2) (:kids (cells k)))
      (=> (= (:live (cells k)) true) (wqc (cells k) (:world c2)))
      (=> (= (:live (cells k)) true) (= (no-markers (:world (cells k))) true) (= (no-markers (:world c2)) true))
      (cinv (fupd cells k c2)))
  (intros hc hl hcp hu hk hw hn)
  (have hd (=> (= (kid-done-c (cells k)) true) (= (kid-done-c c2) true)))
  (intro h) (simp only [kid-done-c hl hcp]) (simp only [kid-done-c] at h) (exact h)
  (apply (cinv-put cells k c2 hc hd))
  (intros l2 c2t)
  (have l1 (= (:live (cells k)) true)) (rw [← hl]) (exact l2)
  (have c1 (= (:complete (cells k)) true)) (rw [← hcp]) (exact c2t)
  (have hc2 := hc) (simp only [cinv] at hc2)
  (exact (ready-put-q cells k c2 (hc2 k l1 c1) (hw l1) hu hk hd (hn l1))))

;; ---- completion stability with no premise beyond the system invariants sinv and qsinv
(a/theorem cinv-step-q [cells :- (=> Nat Cell), k :- Nat, it :- Item]
  (=> (sinv cells) (qsinv cells) (cinv cells) (cinv (sys-step cells k it)))
  (intros hs hq hc)
  (simp only [sys-step])
  (exact (cinv-world-q cells k (cell-step (cells k) it) hc (rfl) (rfl) (rfl) (rfl)
           (fn [hl :- (= (:live (cells k)) true)]
             (wqc-of (cells k) _ (qsinv-live cells k hq hl) (rel-step (:world (cells k)) it (sinv-live cells k hs hl))
               (fn [h :- (= (qh (:world (cells k))) true)] (quiet-step (:world (cells k)) it h))))
           (fn [hl :- (= (:live (cells k)) true), hn0 :- (= (no-markers (:world (cells k))) true)] (p3l-no-markers _ (step-p3l (:world (cells k)) it (sinv-live cells k hs hl)))))))

(a/theorem cinv-wake-q [cells :- (=> Nat Cell), k :- Nat]
  (=> (sinv cells) (qsinv cells) (cinv cells) (cinv (sys-wake cells k)))
  (intros hs hq hc)
  (cases hu (:unborn (cells k)))
  (case [true] (simp only [sys-wake hu]) (exact hc))
  (case [false]
    (simp only [sys-wake hu])
    (exact (cinv-world-q cells k (wake-cell (cells k)) hc (rfl) (rfl) (rfl) (rfl)
             (fn [hl :- (= (:live (cells k)) true)]
               (wqc-of (cells k) _ (qsinv-live cells k hq hl) (rel-wake-all (:dormant (cells k)) (:world (cells k)) (sinv-live cells k hs hl))
                 (fn [h :- (= (qh (:world (cells k))) true)] (qid-wake-all (:dormant (cells k)) (:world (cells k)) h))))
             (fn [hl :- (= (:live (cells k)) true), hn0 :- (= (no-markers (:world (cells k))) true)] (p3l-no-markers _ (p3l-wake-all (:dormant (cells k)) (:world (cells k)) (sinv-live cells k hs hl))))))))

(a/theorem cinv-resume-q [cells :- (=> Nat Cell), pubs :- (=> Nat Pub), p :- Nat, v :- Nat]
  (=> (sinv cells) (qsinv cells) (cinv cells) (cinv (sys-resume cells pubs p v)))
  (intros hs hq hc)
  (simp only [sys-resume])
  (exact (cinv-world-q cells (:cell (pubs p)) (resume-cell (cells (:cell (pubs p))) (:res (pubs p)) v) hc (rfl) (rfl) (rfl) (rfl)
           (fn [hl :- (= (:live (cells (:cell (pubs p)))) true)]
             (wqc-of (cells (:cell (pubs p))) _ (qsinv-live cells (:cell (pubs p)) hq hl)
               (rel-fire-ack (:world (cells (:cell (pubs p)))) (:res (pubs p)) res-ok v (sinv-live cells (:cell (pubs p)) hs hl))
               (fn [h :- (= (qh (:world (cells (:cell (pubs p))))) true)] (qid-fire-ack (:world (cells (:cell (pubs p)))) (:res (pubs p)) res-ok v h))))
           (fn [hl :- (= (:live (cells (:cell (pubs p)))) true), hn0 :- (= (no-markers (:world (cells (:cell (pubs p))))) true)] (p3l-no-markers _ (p3l-fire-ack (:world (cells (:cell (pubs p)))) (:res (pubs p)) res-ok v (sinv-live cells (:cell (pubs p)) hs hl)))))))

(a/theorem cinv-merge-q [cells :- (=> Nat Cell), k :- Nat, m :- Nat, b :- World]
  (=> (sinv cells) (qsinv cells) (cinv cells) (cinv (sys-merge cells k m b)))
  (intros hs hq hc)
  (simp only [sys-merge])
  (exact (cinv-world-q cells k (merge-cell (cells k) (merge-world (:world (cells k)) (:world (cells m)) b)) hc (rfl) (rfl) (rfl) (rfl)
           (fn [hl :- (= (:live (cells k)) true)]
             (wqc-of (cells k) _ (qsinv-live cells k hq hl) (rel-merge-world (:world (cells k)) (:world (cells m)) b (sinv-live cells k hs hl))
               (fn [h :- (= (qh (:world (cells k))) true)] (qid-merge-world (:world (cells k)) (:world (cells m)) b h))))
           (fn [hl :- (= (:live (cells k)) true), hn0 :- (= (no-markers (:world (cells k))) true)] (p3l-no-markers _ (p3l-merge-world (:world (cells k)) (:world (cells m)) b (sinv-live cells k hs hl)))))))

(a/theorem cinv-publish-q [cells :- (=> Nat Cell), k :- Nat, st :- Nat, kont :- Nat, fresh :- Nat]
  (=> (sinv cells) (qsinv cells) (cinv cells) (cinv (sys-publish cells k st kont fresh)))
  (intros hs hq hc) (simp only [sys-publish]) (exact (cinv-step-q cells k _ hs hq hc)))

(a/theorem cinv-abandon-q [cells :- (=> Nat Cell), pubs :- (=> Nat Pub), p :- Nat]
  (=> (sinv cells) (qsinv cells) (cinv cells) (cinv (sys-abandon cells pubs p)))
  (intros hs hq hc) (simp only [sys-abandon]) (exact (cinv-step-q cells _ _ hs hq hc)))

;; ---- qsinv and qpinv are system invariants
(a/theorem qsinv-init [cells :- (=> Nat Cell)]
  (=> (forall [k :- Nat] (=> (= (:live (cells k)) true) (= (:world (cells k)) empty-world))) (qsinv cells))
  (intro h0) (simp only [qsinv]) (intros k hl) (simp only [cq (h0 k hl) qinv-empty Bool.or_true]))
(a/theorem qpinv-none [pubs :- (=> Nat Pub)] (=> (forall [p :- Nat] (= (:live (pubs p)) false)) (qpinv pubs))
  (intro h) (simp only [qpinv]) (intros p hl) (rw [(h p)] at hl) (cases hl))

(a/theorem qsinv-step [cells :- (=> Nat Cell), k :- Nat, it :- Item]
  (=> (sinv cells) (qsinv cells) (qsinv (sys-step cells k it)))
  (intros hs hq)
  (simp only [sys-step])
  (apply (qsinv-put cells k (cell-step (cells k) it) hq))
  (intro hl) (simp only [cell-step] at hl)
  (exact (cq-trans (cells k) (cell-step (cells k) it) (rfl)
           (fn [r :- (= (:released (:world (cells k))) true)] (rel-step (:world (cells k)) it (sinv-live cells k hs hl) r))
           (fn [q :- (= (qinv (:world (cells k))) true)] (step-qinv (:world (cells k)) it q)) (qsinv-live cells k hq hl))))

(a/theorem qsinv-wake [cells :- (=> Nat Cell), k :- Nat]
  (=> (sinv cells) (qsinv cells) (qsinv (sys-wake cells k)))
  (intros hs hq)
  (cases hu (:unborn (cells k)))
  (case [true] (simp only [sys-wake hu]) (exact hq))
  (case [false]
    (simp only [sys-wake hu])
    (apply (qsinv-put cells k (wake-cell (cells k)) hq))
    (intro hl) (simp only [wake-cell] at hl)
    (exact (cq-trans (cells k) (wake-cell (cells k)) (rfl)
             (fn [r :- (= (:released (:world (cells k))) true)] (rel-wake-all (:dormant (cells k)) (:world (cells k)) (sinv-live cells k hs hl) r))
             (fn [q :- (= (qinv (:world (cells k))) true)] (qinv-wake-all (:dormant (cells k)) (:world (cells k)) q)) (qsinv-live cells k hq hl)))))

(a/theorem qsinv-resume [cells :- (=> Nat Cell), pubs :- (=> Nat Pub), p :- Nat, v :- Nat]
  (=> (sinv cells) (qsinv cells) (qsinv (sys-resume cells pubs p v)))
  (intros hs hq)
  (simp only [sys-resume])
  (apply (qsinv-put cells (:cell (pubs p)) (resume-cell (cells (:cell (pubs p))) (:res (pubs p)) v) hq))
  (intro hl) (simp only [resume-cell] at hl)
  (exact (cq-trans (cells (:cell (pubs p))) (resume-cell (cells (:cell (pubs p))) (:res (pubs p)) v) (rfl)
           (fn [r :- (= (:released (:world (cells (:cell (pubs p))))) true)]
             (rel-fire-ack (:world (cells (:cell (pubs p)))) (:res (pubs p)) res-ok v (sinv-live cells (:cell (pubs p)) hs hl) r))
           (fn [q :- (= (qinv (:world (cells (:cell (pubs p))))) true)] (qinv-fire-ack (:world (cells (:cell (pubs p)))) (:res (pubs p)) res-ok v q))
           (qsinv-live cells (:cell (pubs p)) hq hl))))

(a/theorem qsinv-merge [cells :- (=> Nat Cell), k :- Nat, m :- Nat, b :- World]
  (=> (sinv cells) (qsinv cells) (qsinv (sys-merge cells k m b)))
  (intros hs hq)
  (simp only [sys-merge])
  (apply (qsinv-put cells k (merge-cell (cells k) (merge-world (:world (cells k)) (:world (cells m)) b)) hq))
  (intro hl) (simp only [merge-cell] at hl)
  (exact (cq-trans (cells k) (merge-cell (cells k) (merge-world (:world (cells k)) (:world (cells m)) b)) (rfl)
           (fn [r :- (= (:released (:world (cells k))) true)] (rel-merge-world (:world (cells k)) (:world (cells m)) b (sinv-live cells k hs hl) r))
           (fn [q :- (= (qinv (:world (cells k))) true)] (qinv-merge-world (:world (cells k)) (:world (cells m)) b q)) (qsinv-live cells k hq hl))))

(a/theorem qsinv-publish [cells :- (=> Nat Cell), k :- Nat, st :- Nat, kont :- Nat, fresh :- Nat]
  (=> (sinv cells) (qsinv cells) (qsinv (sys-publish cells k st kont fresh)))
  (intros hs hq) (simp only [sys-publish]) (exact (qsinv-step cells k _ hs hq)))
(a/theorem qsinv-abandon [cells :- (=> Nat Cell), pubs :- (=> Nat Pub), p :- Nat]
  (=> (sinv cells) (qsinv cells) (qsinv (sys-abandon cells pubs p)))
  (intros hs hq) (simp only [sys-abandon]) (exact (qsinv-step cells _ _ hs hq)))

(a/theorem qsinv-accept [cells :- (=> Nat Cell), k :- Nat, m :- Nat]
  (=> (qsinv cells) (qsinv (sys-accept cells k m)))
  (intro hq)
  (cases hc (:complete (cells k)))
  (case [true] (simp only [sys-accept hc]) (exact hq))
  (case [false]
    (simp only [sys-accept hc])
    (apply (qsinv-put cells k (accept-cell (cells k) m) hq))
    (intro hl) (simp only [accept-cell] at hl) (simp only [cq accept-cell]) (exact (qsinv-live cells k hq hl))))
(a/theorem qsinv-complete [cells :- (=> Nat Cell), k :- Nat]
  (=> (qsinv cells) (qsinv (sys-complete cells k)))
  (intro hq)
  (cases hr (complete-ready cells k))
  (case [false] (simp only [sys-complete hr]) (exact hq))
  (case [true]
    (simp only [sys-complete hr])
    (apply (qsinv-put cells k (complete-cell (cells k)) hq))
    (intro hl) (simp only [complete-cell] at hl) (simp only [cq complete-cell]) (exact (qsinv-live cells k hq hl))))
(a/theorem qsinv-drop [cells :- (=> Nat Cell), k :- Nat]
  (=> (qsinv cells) (qsinv (sys-drop cells k)))
  (intro hq) (simp only [sys-drop])
  (apply (qsinv-put cells k (drop-cell (cells k)) hq))
  (intro hl) (simp only [drop-cell] at hl) (cases hl))
(a/theorem qsinv-idle-release [cells :- (=> Nat Cell), m :- Nat]
  (=> (qsinv cells) (qsinv (sys-idle-release cells m)))
  (intro hq)
  (cases hi (idle-cell (cells m)))
  (case [false] (simp only [sys-idle-release hi]) (exact hq))
  (case [true] (simp only [sys-idle-release hi]) (exact (qsinv-drop cells m hq))))
;; E4: the released unborn instance is the first disjunct of cq
(a/theorem qsinv-release-unborn [cells :- (=> Nat Cell), k :- Nat]
  (=> (qsinv cells) (qsinv (sys-release-unborn cells k)))
  (intro hq)
  (cases hg (Bool.and (:unborn (cells k)) (Bool.not (:released (:world (cells k))))))
  (case [false] (simp only [sys-release-unborn hg]) (exact hq))
  (case [true]
    (simp only [sys-release-unborn hg])
    (simp only [Bool.and_eq_true] at hg)
    (apply (qsinv-put cells k (release-unborn-cell (cells k)) hq))
    (intro hl)
    (have e (= (:released (release-unborn (:world (cells k)))) true)) (simp only [release-unborn set-released])
    (simp only [cq release-unborn-cell (And.left hg) e Bool.and_self Bool.true_or])))
;; activation: the instance is not released (act-ok), so it holds qinv; it is born after
(a/theorem qsinv-activate [cells :- (=> Nat Cell), m :- Nat, v :- Nat]
  (=> (qsinv cells) (qsinv (sys-activate cells m v)))
  (intro hq)
  (cases hg (act-ok (cells m)))
  (case [false] (simp only [sys-activate hg]) (exact hq))
  (case [true]
    (simp only [sys-activate hg])
    (simp only [act-ok Bool.and_eq_true] at hg)
    (have nr := (bnot-true _ (And.right (And.right hg))))
    (apply (qsinv-put cells m (act-cell (cells m) v) hq))
    (intro hl) (simp only [act-cell] at hl)
    (have c := (qsinv-live cells m hq hl))
    (simp only [cq nr Bool.and_false Bool.false_or] at c)
    (simp only [cq act-cell Bool.false_and Bool.false_or])
    (exact (qinv-wake-all (:dormant (cells m)) _ (qinv-fire-ack (:world (cells m)) (:pending (cells m)) res-ok v c)))))
;; a fork (value copy) or a fork effect: refused from an unborn cell (the guard), so the source is
;; born and its cq is qinv (`cq-born`)
(a/theorem qsinv-fork [cells :- (=> Nat Cell), k :- Nat, m :- Nat, owner :- Nat]
  (=> (qsinv cells) (= (:live (cells k)) true) (qsinv (sys-fork cells k m owner)))
  (intros hq hlk)
  (cases hu (:unborn (cells k)))
  (case [true] (simp only [sys-fork hu]) (exact hq))
  (case [false]
    (simp only [sys-fork hu])
    (apply (qsinv-put cells m (fork-cell (cells k) k owner) hq))
    (intro hl)
    (have c := (cq-born (cells k) (qsinv-live cells k hq hlk) hu))
    (simp only [cq fork-cell c Bool.false_and Bool.false_or])))
(a/theorem qsinv-fork-effect [cells :- (=> Nat Cell), k :- Nat, m :- Nat, owner :- Nat, st :- Nat, kont :- Nat, v :- Nat]
  (=> (qsinv cells) (= (:live (cells k)) true) (qsinv (sys-fork-effect cells k m owner st kont v)))
  (intros hq hlk)
  (cases hu (:unborn (cells k)))
  (case [true] (simp only [sys-fork-effect hu]) (exact hq))
  (case [false]
    (simp only [sys-fork-effect hu])
    (apply (qsinv-put cells m (fork-effect-cell (cells k) k owner st kont v) hq))
    (intro hl)
    (have c := (cq-born (cells k) (qsinv-live cells k hq hlk) hu))
    (simp only [cq fork-effect-cell Bool.false_and Bool.false_or])
    (exact (qinv-fork-effect-world (:world (cells k)) st kont v c))))
(a/theorem qsinv-instantiate [cells :- (=> Nat Cell), pubs :- (=> Nat Pub), p :- Nat, m :- Nat, owner :- Nat]
  (=> (qsinv cells) (qpinv pubs) (= (:live (pubs p)) true) (qsinv (sys-instantiate cells pubs p m owner)))
  (intros hq hp hlp)
  (simp only [qpinv] at hp)
  (simp only [sys-instantiate])
  (apply (qsinv-put cells m (inst-cell (pubs p) owner) hq))
  (intro hl)
  (simp only [cq inst-cell Bool.true_and]) (exact (hp p hlp)))
(a/theorem qpinv-publish [cells :- (=> Nat Cell), pubs :- (=> Nat Pub), k :- Nat, p :- Nat, st :- Nat, kont :- Nat, fresh :- Nat]
  (=> (sinv cells) (qsinv cells) (= (:live (cells k)) true) (qpinv pubs) (qpinv (pubs-publish cells pubs k p st kont fresh)))
  (intros hs hq hlk hp)
  (simp only [qpinv] at hp) (simp only [qpinv])
  (intros q hl)
  (cases hqp (Nat.beq q p))
  (case [false]
    (simp only [pubs-publish fupd hqp] at hl) (simp only [pubs-publish fupd hqp]) (exact (hp q hl)))
  (case [true]
    (have e (= q p)) (exact (Nat.eq_of_beq_eq_true hqp))
    (rw [e]) (simp only [pubs-publish fupd-same])
    (have c := (qsinv-live cells k hq hlk))
    (simp only [cq Bool.or_eq_true Bool.and_eq_true] at c)
    (cases c)
    (case [inl a]
      (simp only [(rel-step (:world (cells k)) (publish-item st kont fresh) (sinv-live cells k hs hlk) (And.right a)) Bool.true_or]))
    (case [inr b]
      (simp only [(step-qinv (:world (cells k)) (publish-item st kont fresh) b) Bool.or_true]))))
(a/theorem qpinv-abandon [pubs :- (=> Nat Pub), p :- Nat]
  (=> (qpinv pubs) (qpinv (pubs-abandon pubs p)))
  (intro hp)
  (simp only [qpinv] at hp) (simp only [qpinv])
  (intros q hl)
  (cases hqp (Nat.beq q p))
  (case [false] (simp only [pubs-abandon fupd hqp] at hl) (simp only [pubs-abandon fupd hqp]) (exact (hp q hl)))
  (case [true]
    (have e (= q p)) (exact (Nat.eq_of_beq_eq_true hqp))
    (rw [e] at hl) (simp only [pubs-abandon fupd-same] at hl) (simp at hl)))


;; ===========================================================================
;; C1c stage A, the proof stage: host joins (Z#70, questions 10, 12, 14)
;; ===========================================================================
;;   jinv       every live cell: complete -> no pending join; join ids distinct and below the number admitted;
;;              targets are not 0. Kept by every system operation (`jinv-*`), from `jinv-init`.
;;   delivery   after sys-deliver every pending join's target is incomplete (`deliver-pending`).
;;   frames     sys-join / sys-deliver / sys-withdraw keep sinv, cinv, qsinv (the world is untouched; qpinv reads
;;              only publications, which they do not touch).
;;   once       a join that is not pending stays in the list as it is through sys-deliver, sys-withdraw,
;;              sys-complete and sys-join (`once-*`), and join ids are distinct (jinv), so it is delivered at
;;              most once and a withdrawn join never (`final-stays`).
;;   Q10/Q14    a complete born cell has every task (id /= 0) and every non-root scope complete
;;              (`complete-born-ledger`); at a born cell's completion every join is delivered already by
;;              sys-deliver, so abandonment (`complete-cell`) changes no join (`born-complete-delivered`,
;;              `born-abandon-none`): abandonment is only ever needed for an unborn instance.

(a/theorem sx-not-intro [b :- Bool] (=> (= b false) (= (Bool.not b) true)) (intro h) (rw [h]))
(a/theorem sx-not-of [b :- Bool] (=> (= (Bool.not b) true) (= b false)) (intro h) (cases b) (rfl) (simp at h))
(a/defn jnp [j :- Join] Bool (Bool.not (jpend j)))
(a/defn jids [js :- (List Join)] (List Nat) (tbl-ids join-id js))
(a/defn jl-one [n :- Nat, j :- Join] Bool (Bool.and (Nat.blt (:id j) n) (Nat.blt 0 (:target j))))
(a/defn jl-ok [js :- (List Join)] Bool (Bool.and (nat-nodup (jids js)) (tbl-all (jl-one (List.length js)) js)))
(a/defn jok [c :- Cell] Bool (Bool.and (Bool.or (Bool.not (:complete c)) (tbl-all jnp (:joins c))) (jl-ok (:joins c))))
(a/defn jinv [cells :- (=> Nat Cell)] Prop (forall [k :- Nat] (=> (= (:live (cells k)) true) (= (jok (cells k)) true))))

(a/theorem jinv-live [cells :- (=> Nat Cell), k :- Nat] (=> (jinv cells) (= (:live (cells k)) true) (= (jok (cells k)) true))
  (intros h hl) (simp only [jinv] at h) (exact (h k hl)))
(a/theorem jinv-put [cells :- (=> Nat Cell), k :- Nat, c2 :- Cell]
  (=> (jinv cells) (=> (= (:live c2) true) (= (jok c2) true)) (jinv (fupd cells k c2)))
  (intros hs hc)
  (simp only [jinv] at hs) (simp only [jinv])
  (intros j hl)
  (cases hjk (Nat.beq j k))
  (case [false] (simp only [fupd hjk] at hl) (simp only [fupd hjk]) (exact (hs j hl)))
  (case [true]
    (have e (= j k)) (exact (Nat.eq_of_beq_eq_true hjk))
    (rw [e] at hl) (rw [e]) (simp only [fupd-same] at hl) (simp only [fupd-same]) (exact (hc hl))))
(a/theorem jinv-same [cells :- (=> Nat Cell), k :- Nat, c2 :- Cell]
  (=> (jinv cells) (= (:live c2) (:live (cells k))) (= (:complete c2) (:complete (cells k))) (= (:joins c2) (:joins (cells k)))
      (jinv (fupd cells k c2)))
  (intros h hl hc hj)
  (apply (jinv-put cells k c2 h))
  (intro l2) (rw [hl] at l2)
  (have o := (jinv-live cells k h l2))
  (simp only [jok hc hj]) (simp only [jok] at o) (exact o))
(a/theorem jok-nil [c :- Cell] (=> (= (:joins c) (List.nil Join)) (= (jok c) true))
  (intro h) (simp only [jok jl-ok jids h tbl-ids tbl-all nat-nodup Bool.or_true Bool.and_self]))
(a/theorem jinv-init [cells :- (=> Nat Cell)]
  (=> (forall [k :- Nat] (=> (= (:live (cells k)) true) (= (:joins (cells k)) (List.nil Join)))) (jinv cells))
  (intro h0) (simp only [jinv]) (intros k hl) (exact (jok-nil (cells k) (h0 k hl))))

;; ---- the join list transformers
(a/theorem jmap-len [f :- (=> Join Join), js :- (List Join)] (= (List.length (joins-map f js)) (List.length js))
  (induction js) (case [nil] (simp only [joins-map List.length])) (case [cons h t ih] (simp only [joins-map List.length ih])))
(a/theorem jmap-ids [f :- (=> Join Join), hf :- (forall [j :- Join] (= (:id (f j)) (:id j))), js :- (List Join)]
  (= (jids (joins-map f js)) (jids js))
  (induction js)
  (case [nil] (simp only [joins-map jids tbl-ids]))
  (case [cons h t ih] (simp only [jids] at ih) (simp only [joins-map jids tbl-ids join-id (hf h) ih])))
(a/theorem jmap-all [f :- (=> Join Join), P :- (=> Join Bool), Q :- (=> Join Bool),
                     hpq :- (forall [j :- Join] (=> (= (P j) true) (= (Q (f j)) true))), js :- (List Join)]
  (=> (= (tbl-all P js) true) (= (tbl-all Q (joins-map f js)) true))
  (induction js)
  (case [nil] (intro h) (simp only [joins-map tbl-all]))
  (case [cons h t ih]
    (intro hp) (simp only [tbl-all Bool.and_eq_true] at hp)
    (simp only [joins-map tbl-all (hpq h (And.left hp)) (ih (And.right hp)) Bool.and_self])))
(a/theorem jl-ok-map [f :- (=> Join Join), hid :- (forall [j :- Join] (= (:id (f j)) (:id j))),
                      htg :- (forall [j :- Join] (= (:target (f j)) (:target j))), js :- (List Join)]
  (=> (= (jl-ok js) true) (= (jl-ok (joins-map f js)) true))
  (intro h)
  (simp only [jl-ok Bool.and_eq_true] at h)
  (simp only [jl-ok (jmap-ids f hid js) (jmap-len f js) (And.left h) Bool.true_and])
  (apply (jmap-all f (jl-one (List.length js)) (jl-one (List.length js)) _ js (And.right h)))
  (intros j q) (simp only [jl-one (hid j) (htg j)]) (simp only [jl-one] at q) (exact q))

(a/theorem hj-done-id [j :- Join] (= (:id (hj-done j)) (:id j)) (cases hp (jpend j)) (all_goals (simp only [hj-done hp])))
(a/theorem hj-done-tg [j :- Join] (= (:target (hj-done j)) (:target j)) (cases hp (jpend j)) (all_goals (simp only [hj-done hp])))
(a/theorem hj-drop-id [j :- Join] (= (join-id (hj-drop j)) (join-id j)) (cases hp (jpend j)) (all_goals (simp only [hj-drop join-id hp])))
(a/theorem hj-drop-tg [j :- Join] (= (:target (hj-drop j)) (:target j)) (cases hp (jpend j)) (all_goals (simp only [hj-drop hp])))
(a/theorem hj-due-id [w :- World, j :- Join] (= (:id (hj-due w j)) (:id j))
  (cases ht (task-complete w (:target j))) (all_goals (simp only [hj-due ht hj-done-id])))
(a/theorem hj-due-tg [w :- World, j :- Join] (= (:target (hj-due w j)) (:target j))
  (cases ht (task-complete w (:target j))) (all_goals (simp only [hj-due ht hj-done-tg])))
(a/theorem done-np [j :- Join] (= (jnp (hj-done j)) true)
  (cases hp (jpend j))
  (case [true] (simp only [jnp hj-done hp jpend js-delivered js-pending]))
  (case [false] (simp only [jnp hj-done hp Bool.not_false])))
(a/theorem done-fix [j :- Join] (=> (= (jpend j) false) (= (hj-done j) j)) (intro hp) (simp only [hj-done hp]))
(a/theorem drop-fix [j :- Join] (=> (= (jpend j) false) (= (hj-drop j) j)) (intro hp) (simp only [hj-drop hp]))
(a/theorem due-fix [w :- World, j :- Join] (=> (= (jpend j) false) (= (hj-due w j) j))
  (intro hp) (cases ht (task-complete w (:target j))) (all_goals (simp only [hj-due ht (done-fix j hp)])))
(a/theorem np-of [j :- Join] (=> (= (jnp j) true) (= (jpend j) false))
  (intro h) (cases hp (jpend j)) (rfl) (simp only [jnp hp Bool.not_true] at h) (cases h))
(a/theorem jall-done [js :- (List Join)] (= (tbl-all jnp (joins-map hj-done js)) true)
  (induction js) (case [nil] (simp only [joins-map tbl-all])) (case [cons h t ih] (simp only [joins-map tbl-all done-np ih Bool.and_self])))
(a/theorem upd-len [A :- Type, idf :- (=> A Nat), x :- Nat, f :- (=> A A), xs :- (List A)] (= (List.length (tbl-upd idf x f xs)) (List.length xs))
  (induction xs)
  (case [nil] (simp only [tbl-upd List.length]))
  (case [cons h t ih] (cases hx (Nat.beq (idf h) x)) (all_goals (simp only [tbl-upd hx List.length ih]))))
(a/theorem lt-mem [n :- Nat, js :- (List Join)] (=> (= (tbl-all (jl-one n) js) true) (= (nat-mem n (jids js)) false))
  (induction js)
  (case [nil] (intro h) (simp only [jids tbl-ids nat-mem]))
  (case [cons h t ih]
    (intro hp) (simp only [tbl-all jl-one Bool.and_eq_true Nat.blt_eq] at hp)
    (have hb (= (Nat.beq (:id h) n) false))
    (cases e (Nat.beq (:id h) n)) (rfl) (have e2 := (Nat.eq_of_beq_eq_true e)) (have l := (And.left (And.left hp))) (omega)
    (have i := (ih (tbl-all-mono Join _ _ (fn [j :- Join, q :- (= (jl-one n j) true)] q) t (And.right hp))))
    (simp only [jids] at i)
    (simp only [jids tbl-ids nat-mem join-id hb i])))
(a/theorem jl-one-up [n :- Nat, j :- Join] (=> (= (jl-one n j) true) (= (jl-one (+ n 1) j) true))
  (intro h) (simp only [jl-one Bool.and_eq_true Nat.blt_eq] at h) (simp only [jl-one Bool.and_eq_true Nat.blt_eq])
  (have l := (And.left h)) (have l2 (< (:id j) (+ n 1))) (omega) (exact (And.intro l2 (And.right h))))

;; ---- jinv through every system operation
(a/theorem jinv-join [cells :- (=> Nat Cell), k :- Nat, t :- Nat] (=> (jinv cells) (jinv (sys-join cells k t)))
  (intro h)
  (cases hj (join-ok (cells k) t))
  (case [false] (simp only [sys-join hj]) (exact h))
  (case [true]
    (simp only [sys-join hj])
    (apply (jinv-put cells k _ h))
    (intro hl)
    (have hl0 (= (:live (cells k)) true)) (exact hl)
    (have o := (jinv-live cells k h hl0))
    (simp only [jok jl-ok Bool.and_eq_true] at o)
    (have ht (= (Nat.blt 0 t) true)) (simp only [join-ok Bool.and_eq_true] at hj) (exact (And.left (And.right hj)))
    (have nm := (lt-mem (List.length (:joins (cells k))) (:joins (cells k)) (And.right (And.right o))))
    (have a1 (= (jl-ok (List.cons Join (join-new (cells k) t) (:joins (cells k)))) true))
    (simp only [jl-ok jids tbl-ids nat-nodup tbl-all List.length join-id join-new Bool.and_eq_true])
    (simp only [jids] at nm)
    (apply And.intro)
    (exact (And.intro (sx-not-intro _ nm) (And.left (And.right o))))
    (apply And.intro)
    (simp only [jl-one ht Nat.blt_eq Bool.and_true]) (try (omega))
    (exact (tbl-all-mono Join _ _ (jl-one-up (List.length (:joins (cells k)))) _ (And.right (And.right o))))
    (have a0 (= (Bool.or (Bool.not (:complete (cells k))) (tbl-all jnp (List.cons Join (join-new (cells k) t) (:joins (cells k))))) true))
    (cases hc (:complete (cells k)))
    (case [false] (simp only [Bool.not_false Bool.true_or]))
    (case [true]
      (have a2 := (And.left o)) (simp only [hc Bool.not_true Bool.false_or] at a2)
      (simp only [tbl-all jnp join-new hc Bool.true_or jpend js-delivered js-pending a2 Bool.not_true Bool.false_or Bool.and_true])
      (try (rfl)))
    (simp only [jok join-cell a0 a1 Bool.and_self])))
(a/theorem jinv-deliver [cells :- (=> Nat Cell), k :- Nat] (=> (jinv cells) (jinv (sys-deliver cells k)))
  (intro h)
  (simp only [sys-deliver])
  (apply (jinv-put cells k _ h))
  (intro hl)
  (have hl0 (= (:live (cells k)) true)) (exact hl)
  (have o := (jinv-live cells k h hl0))
  (simp only [jok Bool.and_eq_true] at o)
  (cases hc (:complete (cells k)))
  (case [true]
    (simp only [jok deliver-cell hc jall-done Bool.not_true Bool.false_or Bool.true_and])
    (exact (jl-ok-map hj-done hj-done-id hj-done-tg _ (And.right o))))
  (case [false]
    (simp only [jok deliver-cell hc Bool.not_false Bool.true_or Bool.true_and])
    (exact (jl-ok-map (hj-due (:world (cells k))) (hj-due-id (:world (cells k))) (hj-due-tg (:world (cells k))) _ (And.right o)))))
(a/theorem jinv-withdraw [cells :- (=> Nat Cell), k :- Nat, x :- Nat] (=> (jinv cells) (jinv (sys-withdraw cells k x)))
  (intro h)
  (simp only [sys-withdraw])
  (apply (jinv-put cells k _ h))
  (intro hl)
  (have hl0 (= (:live (cells k)) true)) (exact hl)
  (have o := (jinv-live cells k h hl0))
  (simp only [jok jl-ok Bool.and_eq_true] at o)
  (have a0 (= (Bool.or (Bool.not (:complete (cells k))) (tbl-all jnp (tbl-upd join-id x hj-drop (:joins (cells k))))) true))
  (cases hc (:complete (cells k)))
  (case [false] (simp only [Bool.not_false Bool.true_or]))
  (case [true]
    (have a2 := (And.left o)) (simp only [hc Bool.not_true Bool.false_or] at a2)
    (simp only [Bool.not_true Bool.false_or])
    (apply (tbl-all-upd Join join-id x hj-drop jnp jnp _ _ _ a2))
    (intros j q e) (rw [(drop-fix j (np-of j q))]) (exact q)
    (intros j q e) (exact q))
  (have nd := (And.left (And.right o))) (simp only [jids] at nd)
  (have a1 (= (jl-ok (tbl-upd join-id x hj-drop (:joins (cells k)))) true))
  (simp only [jl-ok jids (tbl-ids-upd Join join-id x hj-drop hj-drop-id (:joins (cells k))) (upd-len Join join-id x hj-drop (:joins (cells k)))
              nd Bool.true_and])
  (apply (tbl-all-upd Join join-id x hj-drop (jl-one (List.length (:joins (cells k)))) (jl-one (List.length (:joins (cells k)))) _ _ _ (And.right (And.right o))))
  (intros j q e) (simp only [jl-one hj-drop-tg]) (have i := (hj-drop-id j)) (simp only [join-id] at i) (rw [i]) (simp only [jl-one] at q) (exact q)
  (intros j q e) (exact q)
  (simp only [jok withdraw-cell a0 a1 Bool.and_self]))
(a/theorem jinv-complete [cells :- (=> Nat Cell), k :- Nat] (=> (jinv cells) (jinv (sys-complete cells k)))
  (intro h)
  (cases hr (complete-ready cells k))
  (case [false] (simp only [sys-complete hr]) (exact h))
  (case [true]
    (simp only [sys-complete hr])
    (apply (jinv-put cells k _ h))
    (intro hl)
    (have hl0 (= (:live (cells k)) true)) (exact hl)
    (have o := (jinv-live cells k h hl0))
    (simp only [jok Bool.and_eq_true] at o)
    (simp only [jok complete-cell jall-done Bool.not_true Bool.false_or Bool.true_and])
    (exact (jl-ok-map hj-done hj-done-id hj-done-tg _ (And.right o)))))
(a/theorem jinv-step [cells :- (=> Nat Cell), k :- Nat, it :- Item] (=> (jinv cells) (jinv (sys-step cells k it)))
  (intro h) (simp only [sys-step]) (exact (jinv-same cells k (cell-step (cells k) it) h (rfl) (rfl) (rfl))))
(a/theorem jinv-publish [cells :- (=> Nat Cell), k :- Nat, st :- Nat, kont :- Nat, fresh :- Nat]
  (=> (jinv cells) (jinv (sys-publish cells k st kont fresh)))
  (intro h) (simp only [sys-publish]) (exact (jinv-step cells k _ h)))
(a/theorem jinv-abandon [cells :- (=> Nat Cell), pubs :- (=> Nat Pub), p :- Nat] (=> (jinv cells) (jinv (sys-abandon cells pubs p)))
  (intro h) (simp only [sys-abandon]) (exact (jinv-step cells _ _ h)))
(a/theorem jinv-wake [cells :- (=> Nat Cell), k :- Nat] (=> (jinv cells) (jinv (sys-wake cells k)))
  (intro h)
  (cases hu (:unborn (cells k)))
  (case [true] (simp only [sys-wake hu]) (exact h))
  (case [false] (simp only [sys-wake hu]) (exact (jinv-same cells k (wake-cell (cells k)) h (rfl) (rfl) (rfl)))))
(a/theorem jinv-accept [cells :- (=> Nat Cell), k :- Nat, m :- Nat] (=> (jinv cells) (jinv (sys-accept cells k m)))
  (intro h)
  (cases hc (:complete (cells k)))
  (case [true] (simp only [sys-accept hc]) (exact h))
  (case [false] (simp only [sys-accept hc]) (exact (jinv-same cells k (accept-cell (cells k) m) h (rfl) (rfl) (rfl)))))
(a/theorem jinv-release-unborn [cells :- (=> Nat Cell), k :- Nat] (=> (jinv cells) (jinv (sys-release-unborn cells k)))
  (intro h)
  (cases hr (Bool.and (:unborn (cells k)) (Bool.not (:released (:world (cells k))))))
  (case [false] (simp only [sys-release-unborn hr]) (exact h))
  (case [true] (simp only [sys-release-unborn hr]) (exact (jinv-same cells k (release-unborn-cell (cells k)) h (rfl) (rfl) (rfl)))))
(a/theorem jinv-drop [cells :- (=> Nat Cell), k :- Nat] (=> (jinv cells) (jinv (sys-drop cells k)))
  (intro h) (simp only [sys-drop]) (apply (jinv-put cells k _ h)) (intro hl) (simp only [drop-cell] at hl) (cases hl))
(a/theorem jinv-idle-release [cells :- (=> Nat Cell), m :- Nat] (=> (jinv cells) (jinv (sys-idle-release cells m)))
  (intro h)
  (cases hi (idle-cell (cells m)))
  (case [false] (simp only [sys-idle-release hi]) (exact h))
  (case [true] (simp only [sys-idle-release hi]) (exact (jinv-drop cells m h))))
(a/theorem jinv-resume [cells :- (=> Nat Cell), pubs :- (=> Nat Pub), p :- Nat, v :- Nat] (=> (jinv cells) (jinv (sys-resume cells pubs p v)))
  (intro h) (simp only [sys-resume]) (exact (jinv-same cells (:cell (pubs p)) (resume-cell (cells (:cell (pubs p))) (:res (pubs p)) v) h (rfl) (rfl) (rfl))))
(a/theorem jinv-activate [cells :- (=> Nat Cell), m :- Nat, v :- Nat] (=> (jinv cells) (jinv (sys-activate cells m v)))
  (intro h)
  (cases ha (act-ok (cells m)))
  (case [false] (simp only [sys-activate ha]) (exact h))
  (case [true] (simp only [sys-activate ha]) (exact (jinv-same cells m (act-cell (cells m) v) h (rfl) (rfl) (rfl)))))
(a/theorem jinv-merge [cells :- (=> Nat Cell), k :- Nat, m :- Nat, b :- World] (=> (jinv cells) (jinv (sys-merge cells k m b)))
  (intro h) (simp only [sys-merge]) (exact (jinv-same cells k (merge-cell (cells k) (merge-world (:world (cells k)) (:world (cells m)) b)) h (rfl) (rfl) (rfl))))
(a/theorem jinv-fork [cells :- (=> Nat Cell), k :- Nat, m :- Nat, owner :- Nat] (=> (jinv cells) (jinv (sys-fork cells k m owner)))
  (intro h)
  (cases hu (:unborn (cells k)))
  (case [true] (simp only [sys-fork hu]) (exact h))
  (case [false] (simp only [sys-fork hu]) (apply (jinv-put cells m _ h)) (intro hl) (exact (jok-nil (fork-cell (cells k) k owner) (rfl)))))
(a/theorem jinv-fork-effect [cells :- (=> Nat Cell), k :- Nat, m :- Nat, owner :- Nat, st :- Nat, kont :- Nat, v :- Nat]
  (=> (jinv cells) (jinv (sys-fork-effect cells k m owner st kont v)))
  (intro h)
  (cases hu (:unborn (cells k)))
  (case [true] (simp only [sys-fork-effect hu]) (exact h))
  (case [false] (simp only [sys-fork-effect hu]) (apply (jinv-put cells m _ h)) (intro hl) (exact (jok-nil (fork-effect-cell (cells k) k owner st kont v) (rfl)))))
(a/theorem jinv-instantiate [cells :- (=> Nat Cell), pubs :- (=> Nat Pub), p :- Nat, m :- Nat, owner :- Nat]
  (=> (jinv cells) (jinv (sys-instantiate cells pubs p m owner)))
  (intro h) (simp only [sys-instantiate]) (apply (jinv-put cells m _ h)) (intro hl) (exact (jok-nil (inst-cell (pubs p) owner) (rfl))))

;; ---- delivery: after sys-deliver every pending join waits on an incomplete target
(a/defn jdp [w :- World, j :- Join] Bool (Bool.or (jnp j) (Bool.not (task-complete w (:target j)))))
(a/theorem due-jdp [w :- World, j :- Join] (= (jdp w (hj-due w j)) true)
  (cases ht (task-complete w (:target j)))
  (case [true] (simp only [jdp hj-due ht done-np Bool.true_or]))
  (case [false] (simp only [jdp hj-due ht Bool.not_false Bool.or_true])))
(a/theorem jall-of [f :- (=> Join Join), Q :- (=> Join Bool), hq :- (forall [j :- Join] (= (Q (f j)) true)), js :- (List Join)]
  (= (tbl-all Q (joins-map f js)) true)
  (induction js) (case [nil] (simp only [joins-map tbl-all])) (case [cons h t ih] (simp only [joins-map tbl-all (hq h) ih Bool.and_self])))
(a/theorem deliver-pending [cells :- (=> Nat Cell), k :- Nat, j :- Join]
  (=> (List.Mem j (:joins ((sys-deliver cells k) k))) (= (jpend j) true)
      (= (task-complete (:world (cells k)) (:target j)) false))
  (intros m hp)
  (simp only [sys-deliver fupd-same deliver-cell] at m)
  (cases hc (:complete (cells k)))
  (case [true]
    (simp only [hc] at m)
    (have a := (tbl-all-mem Join jnp j _ (jall-done (:joins (cells k))) m))
    (simp only [jnp hp Bool.not_true] at a) (cases a))
  (case [false]
    (simp only [hc] at m)
    (have a := (tbl-all-mem Join (jdp (:world (cells k))) j _ (jall-of (hj-due (:world (cells k))) _ (due-jdp (:world (cells k))) (:joins (cells k))) m))
    (simp only [jdp jnp hp Bool.not_true Bool.false_or] at a)
    (exact (sx-not-of _ a))))

;; ---- frames: the world and every flag but the joins are untouched
(a/theorem sinv-join [cells :- (=> Nat Cell), k :- Nat, t :- Nat] (=> (sinv cells) (sinv (sys-join cells k t)))
  (intro h)
  (cases hj (join-ok (cells k) t))
  (case [false] (simp only [sys-join hj]) (exact h))
  (case [true] (simp only [sys-join hj]) (exact (sinv-put cells k _ h (fn [hl :- (= (:live (join-cell (cells k) t)) true)] (sinv-live cells k h hl))))))
(a/theorem sinv-deliver [cells :- (=> Nat Cell), k :- Nat] (=> (sinv cells) (sinv (sys-deliver cells k)))
  (intro h) (simp only [sys-deliver]) (exact (sinv-put cells k _ h (fn [hl :- (= (:live (deliver-cell (cells k))) true)] (sinv-live cells k h hl)))))
(a/theorem sinv-withdraw [cells :- (=> Nat Cell), k :- Nat, x :- Nat] (=> (sinv cells) (sinv (sys-withdraw cells k x)))
  (intro h) (simp only [sys-withdraw]) (exact (sinv-put cells k _ h (fn [hl :- (= (:live (withdraw-cell (cells k) x)) true)] (sinv-live cells k h hl)))))
(a/theorem qsinv-join [cells :- (=> Nat Cell), k :- Nat, t :- Nat] (=> (qsinv cells) (qsinv (sys-join cells k t)))
  (intro h)
  (cases hj (join-ok (cells k) t))
  (case [false] (simp only [sys-join hj]) (exact h))
  (case [true] (simp only [sys-join hj]) (exact (qsinv-put cells k _ h (fn [hl :- (= (:live (join-cell (cells k) t)) true)] (qsinv-live cells k h hl))))))
(a/theorem qsinv-deliver [cells :- (=> Nat Cell), k :- Nat] (=> (qsinv cells) (qsinv (sys-deliver cells k)))
  (intro h) (simp only [sys-deliver]) (exact (qsinv-put cells k _ h (fn [hl :- (= (:live (deliver-cell (cells k))) true)] (qsinv-live cells k h hl)))))
(a/theorem qsinv-withdraw [cells :- (=> Nat Cell), k :- Nat, x :- Nat] (=> (qsinv cells) (qsinv (sys-withdraw cells k x)))
  (intro h) (simp only [sys-withdraw]) (exact (qsinv-put cells k _ h (fn [hl :- (= (:live (withdraw-cell (cells k) x)) true)] (qsinv-live cells k h hl)))))
(a/theorem cinv-join [cells :- (=> Nat Cell), k :- Nat, t :- Nat] (=> (cinv cells) (cinv (sys-join cells k t)))
  (intro h)
  (cases hj (join-ok (cells k) t))
  (case [false] (simp only [sys-join hj]) (exact h))
  (case [true] (simp only [sys-join hj])
    (exact (cinv-world cells k (join-cell (cells k) t) h (rfl) (rfl) (rfl) (rfl) (fn [hl :- (= (:live (cells k)) true)] (wq-refl (:world (cells k))))
             (fn [hl :- (= (:live (cells k)) true)] (self-imp _))))))
(a/theorem cinv-deliver [cells :- (=> Nat Cell), k :- Nat] (=> (cinv cells) (cinv (sys-deliver cells k)))
  (intro h) (simp only [sys-deliver])
  (exact (cinv-world cells k (deliver-cell (cells k)) h (rfl) (rfl) (rfl) (rfl) (fn [hl :- (= (:live (cells k)) true)] (wq-refl (:world (cells k))))
             (fn [hl :- (= (:live (cells k)) true)] (self-imp _)))))
(a/theorem cinv-withdraw [cells :- (=> Nat Cell), k :- Nat, x :- Nat] (=> (cinv cells) (cinv (sys-withdraw cells k x)))
  (intro h) (simp only [sys-withdraw])
  (exact (cinv-world cells k (withdraw-cell (cells k) x) h (rfl) (rfl) (rfl) (rfl) (fn [hl :- (= (:live (cells k)) true)] (wq-refl (:world (cells k))))
             (fn [hl :- (= (:live (cells k)) true)] (self-imp _)))))

;; ---- delivery at most once: a join that is not pending stays as it is, and join ids are distinct
(a/defn jkeep [js :- (List Join), js2 :- (List Join)] Prop
  (forall [j :- Join] (=> (List.Mem j js) (= (jpend j) false) (List.Mem j js2))))
(a/theorem jmem-cases [a :- Join, b :- Join, l :- (List Join), P :- Prop]
  (=> (List.Mem a (List.cons Join b l)) (=> (= a b) P) (=> (List.Mem a l) P) P)
  (intros m h1 h2)
  (cases m)
  (case [head] (exact (h1 (rfl))))
  (case [tail m2] (exact (h2 m2))))
(a/theorem map-keep [f :- (=> Join Join), hf :- (forall [j :- Join] (=> (= (jpend j) false) (= (f j) j))), js :- (List Join)]
  (jkeep js (joins-map f js))
  (simp only [jkeep])
  (induction js)
  (case [nil] (intros j m p) (cases m))
  (case [cons h t ih]
    (intros j m p)
    (apply (jmem-cases j h t _ m))
    (intro e) (rw [e] at p) (rw [e]) (simp only [joins-map (hf h p)]) (exact (List.Mem.head _))
    (intro m2) (simp only [joins-map]) (exact (List.Mem.tail _ (ih j m2 p)))))
(a/theorem upd-keep-head [x :- Nat, f :- (=> Join Join), hf :- (forall [j :- Join] (=> (= (jpend j) false) (= (f j) j))),
                          h :- Join, t :- (List Join)]
  (=> (= (jpend h) false) (List.Mem h (tbl-upd join-id x f (List.cons Join h t))))
  (intro p)
  (cases hx (Nat.beq (join-id h) x))
  (all_goals (simp only [tbl-upd hx (hf h p)]))
  (all_goals (exact (List.Mem.head _))))
(a/theorem upd-keep [x :- Nat, f :- (=> Join Join), hf :- (forall [j :- Join] (=> (= (jpend j) false) (= (f j) j))), js :- (List Join)]
  (jkeep js (tbl-upd join-id x f js))
  (simp only [jkeep])
  (induction js)
  (case [nil] (intros j m p) (cases m))
  (case [cons h t ih]
    (intros j m p)
    (apply (jmem-cases j h t _ m))
    (intro e) (rw [e] at p) (rw [e]) (exact (upd-keep-head x f hf h t p))
    (intro m2) (cases hx (Nat.beq (join-id h) x)) (all_goals (simp only [tbl-upd hx])) (all_goals (exact (List.Mem.tail _ (ih j m2 p))))))
(a/theorem once-deliver [cells :- (=> Nat Cell), k :- Nat] (jkeep (:joins (cells k)) (:joins ((sys-deliver cells k) k)))
  (simp only [sys-deliver fupd-same deliver-cell])
  (cases hc (:complete (cells k)))
  (case [true] (simp only [hc]) (exact (map-keep hj-done done-fix _)))
  (case [false] (simp only [hc]) (exact (map-keep (hj-due (:world (cells k))) (due-fix (:world (cells k))) _))))
(a/theorem once-withdraw [cells :- (=> Nat Cell), k :- Nat, x :- Nat] (jkeep (:joins (cells k)) (:joins ((sys-withdraw cells k x) k)))
  (simp only [sys-withdraw fupd-same withdraw-cell]) (exact (upd-keep x hj-drop drop-fix _)))
(a/theorem once-complete [cells :- (=> Nat Cell), k :- Nat] (jkeep (:joins (cells k)) (:joins ((sys-complete cells k) k)))
  (cases hr (complete-ready cells k))
  (case [false] (simp only [sys-complete hr jkeep]) (intros j m p) (exact m))
  (case [true] (simp only [sys-complete hr fupd-same complete-cell]) (exact (map-keep hj-done done-fix _))))
(a/theorem once-join [cells :- (=> Nat Cell), k :- Nat, t :- Nat] (jkeep (:joins (cells k)) (:joins ((sys-join cells k t) k)))
  (cases hj (join-ok (cells k) t))
  (case [false] (simp only [sys-join hj jkeep]) (intros j m p) (exact m))
  (case [true] (simp only [sys-join hj fupd-same join-cell jkeep]) (intros j m p) (exact (List.Mem.tail _ m))))
(a/theorem jmem-uniq [js :- (List Join), j :- Join, j2 :- Join]
  (=> (= (nat-nodup (jids js)) true) (List.Mem j js) (List.Mem j2 js) (= (:id j2) (:id j)) (= j2 j))
  (intros hn m m2 e)
  (cases hf (tbl-find join-id (:id j) js))
  (case [none]
    (have z := (tbl-find-none-has Join join-id (:id j) js hf))
    (have hh := (mem-ids-has Join join-id j js m))
    (rw [(nat-mem-ids Join join-id (:id j) js)] at hh)
    (have hh2 (= (tbl-has join-id (:id j) js) true)) (exact hh)
    (rw [z] at hh2) (cases hh2))
  (case [some r]
    (have a := (find-uniq Join join-id js j r hn m hf))
    (have hf2 (= (tbl-find join-id (join-id j2) js) (Option.some Join r))) (simp only [join-id e]) (exact hf)
    (have b := (find-uniq Join join-id js j2 r hn m2 hf2))
    (rw [a b])))
;; Theorem: a join that is not pending (delivered or withdrawn) is the only join with its id after any of the
;; operations that change joins (the race's winner is final; no second delivery)
(a/theorem final-stays [js :- (List Join), js2 :- (List Join), j :- Join, j2 :- Join]
  (=> (jkeep js js2) (= (nat-nodup (jids js2)) true) (List.Mem j js) (= (jpend j) false)
      (List.Mem j2 js2) (= (:id j2) (:id j)) (= j2 j))
  (intros hk hn m p m2 e)
  (simp only [jkeep] at hk)
  (exact (jmem-uniq js2 j j2 hn (hk j m p) m2 e)))

;; ---- questions 10 and 14: a complete born cell
(a/theorem ready-born-quiet [cells :- (=> Nat Cell), k :- Nat]
  (=> (qsinv cells) (= (:live (cells k)) true) (= (:unborn (cells k)) false) (= (complete-ready cells k) true)
      (= (qh (:world (cells k))) true))
  (intros hq hl hu hr)
  (have qi := (cq-born (cells k) (qsinv-live cells k hq hl) hu))
  (simp only [complete-ready hu Bool.false_or Bool.and_eq_true] at hr)
  (apply (qh-of _ qi))
  (simp only [world-quiet (And.left hr) (And.left (And.right hr)) Bool.and_self]))
;; Theorem (question 10): a complete born world has every task (id /= 0) and every non-root scope complete
(a/theorem complete-born-ledger [cells :- (=> Nat Cell), k :- Nat]
  (=> (qsinv cells) (cinv cells) (= (:live (cells k)) true) (= (:complete (cells k)) true) (= (:unborn (cells k)) false)
      (And (forall [t :- Nat] (=> (= (Nat.beq t 0) false) (= (task-complete (:world (cells k)) t) true)))
           (forall [s :- Nat] (=> (= (Nat.beq s root-scope-id) false) (= (scope-complete (:world (cells k)) s) true)))))
  (intros hq hc hl hk hu)
  (simp only [cinv] at hc)
  (have qh0 := (ready-born-quiet cells k hq hl hu (hc k hl hk)))
  (exact (And.intro (fn [t :- Nat, ht :- (= (Nat.beq t 0) false)] (quiet-task-complete _ t qh0 ht))
                    (fn [s :- Nat, hs :- (= (Nat.beq s root-scope-id) false)] (quiet-scope-complete _ s qh0 hs)))))
(a/theorem due-all-done [w :- World, js :- (List Join)]
  (=> (= (tbl-all (fn [j :- Join] (task-complete w (:target j))) js) true) (= (tbl-all jnp (joins-map (hj-due w) js)) true))
  (induction js)
  (case [nil] (intro h) (simp only [joins-map tbl-all]))
  (case [cons h t ih]
    (intro hp) (simp only [tbl-all Bool.and_eq_true] at hp)
    (simp only [joins-map tbl-all hj-due (And.left hp) done-np (ih (And.right hp)) Bool.and_self])))
;; Theorem (question 14): at a born cell's completion (complete-ready) every join target is complete, so after
;; sys-deliver nothing is pending
(a/theorem born-complete-delivered [cells :- (=> Nat Cell), k :- Nat]
  (=> (qsinv cells) (jinv cells) (= (:live (cells k)) true) (= (:unborn (cells k)) false) (= (complete-ready cells k) true)
      (= (tbl-all jnp (:joins ((sys-deliver cells k) k))) true))
  (intros hq hj hl hu hr)
  (have qh0 := (ready-born-quiet cells k hq hl hu hr))
  (have o := (jinv-live cells k hj hl))
  (simp only [jok jl-ok Bool.and_eq_true] at o)
  (have tc (= (tbl-all (fn [j :- Join] (task-complete (:world (cells k)) (:target j))) (:joins (cells k))) true))
  (apply (tbl-all-mono Join (jl-one (List.length (:joins (cells k)))) _ _ (:joins (cells k)) (And.right (And.right o))))
  (intros j q)
  (simp only [jl-one Bool.and_eq_true Nat.blt_eq] at q)
  (have t0 (= (Nat.beq (:target j) 0) false)) (cases e (Nat.beq (:target j) 0)) (rfl) (have e2 := (Nat.eq_of_beq_eq_true e)) (have l := (And.right q)) (omega)
  (exact (quiet-task-complete _ (:target j) qh0 t0))
  (simp only [sys-deliver fupd-same deliver-cell])
  (cases hc (:complete (cells k)))
  (case [true] (simp only [hc jall-done]))
  (case [false] (simp only [hc]) (exact (due-all-done _ _ tc))))
;; ... so the abandonment delivery of complete-cell changes no join of a born cell
(a/theorem all-np-fix [js :- (List Join)] (=> (= (tbl-all jnp js) true) (= (joins-map hj-done js) js))
  (induction js)
  (case [nil] (intro h) (simp only [joins-map]))
  (case [cons h t ih]
    (intro hp) (simp only [tbl-all Bool.and_eq_true] at hp)
    (simp only [joins-map (done-fix h (np-of h (And.left hp))) (ih (And.right hp))])))
(a/theorem born-abandon-none [cells :- (=> Nat Cell), k :- Nat]
  (=> (qsinv cells) (jinv cells) (= (:live (cells k)) true) (= (:unborn (cells k)) false) (= (complete-ready cells k) true)
      (= (:joins (complete-cell ((sys-deliver cells k) k))) (:joins ((sys-deliver cells k) k))))
  (intros hq hj hl hu hr)
  (simp only [complete-cell])
  (exact (all-np-fix _ (born-complete-delivered cells k hq hj hl hu hr))))
