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

  Not here: following mode (not in the engine either), sealing, sources created in the child (not merged)."
  (:require [ansatz.core :as a]
            [spindel.v2.state :refer :all]
            [spindel.v2.step :refer :all]
            [spindel.v2.engine :refer :all]
            [spindel.v2.hmk2 :refer [p3l]]
            [spindel.v2.progress :refer [quiescent]]
            [spindel.v2.cow :refer [fupd]]
            [spindel.v2.quiet]
            [spindel.v2.qworld]))

(a/defn err-forked [] Nat 1)
;; layer 1 arms timers and offloads only (`arm-kind-ok`): a savepoint is an offload-kind resource,
;; told apart by its publication (`Pub.res`). Any other kind would be refused by T17, and every
;; statement below about a published savepoint would hold of nothing.
(a/defn rk-savepoint [] Nat rk-offload)

;; a world of the system: `parent`/`owner` are its fork marker (0 = the root world), `dormant` the
;; inherited resources not yet settled; an instance is `unborn` until its `pending` savepoint is fired.
;; C1 (T21 completion, Z#67): `kids` are the child cells this world accepted (its completion
;; obligations, never inherited), `complete` its completion (released, no run left, every accepted
;; child complete or collected; an unborn instance released before activation at once)
(a/structure Cell [] (world World) (live Bool) (parent Nat) (owner Nat) (dormant (List Nat))
  (unborn Bool) (pending Nat) (kids (List Nat)) (complete Bool))

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
           (:unborn c) (:pending c) (:kids c) (:complete c)))

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
  (Cell.mk (:world c) true k owner (nat-app (res-ids (:res (:world c))) (:dormant c)) false 0 (List.nil Nat) false))

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
           (:unborn c) (:pending c) (:kids c) (:complete c)))

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
           (List.cons Nat m (:kids c)) (:complete c)))
(a/defn sys-accept [cells :- (=> Nat Cell), k :- Nat, m :- Nat] (=> Nat Cell)
  (if (:complete (cells k)) cells (fupd cells k (accept-cell (cells k) m))))

;; W1: complete once released with no unretired run and every accepted child complete or collected
;; (a dropped cell); an unborn instance released before its activation at once (nothing in it runs)
(a/defn kid-done [cells :- (=> Nat Cell), m :- Nat] Bool (Bool.or (Bool.not (:live (cells m))) (:complete (cells m))))
(a/defn complete-ready [cells :- (=> Nat Cell), k :- Nat] Bool
  (Bool.and (:released (:world (cells k)))
            (Bool.or (:unborn (cells k))
                     (Bool.and (Nat.beq (world-runs (:world (cells k))) 0) (tbl-all (kid-done cells) (:kids (cells k)))))))
(a/defn complete-cell [c :- Cell] Cell
  (Cell.mk (:world c) (:live c) (:parent c) (:owner c) (:dormant c) (:unborn c) (:pending c) (:kids c) true))
(a/defn sys-complete [cells :- (=> Nat Cell), k :- Nat] (=> Nat Cell)
  (if (complete-ready cells k) (fupd cells k (complete-cell (cells k))) cells))

;; E4: an unborn instance released before its activation only sets the flag (engine.clj
;; `release-unborn`); `sys-complete` then completes it. Its invariant: `sinv-release-unborn`.
(a/defn release-unborn-cell [c :- Cell] Cell
  (Cell.mk (release-unborn (:world c)) (:live c) (:parent c) (:owner c) (:dormant c) (:unborn c) (:pending c)
           (:kids c) (:complete c)))
(a/defn sys-release-unborn [cells :- (=> Nat Cell), k :- Nat] (=> Nat Cell)
  (if (Bool.and (:unborn (cells k)) (Bool.not (:released (:world (cells k)))))
      (fupd cells k (release-unborn-cell (cells k))) cells))

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
;; L10/L11: a world leaves the system

(a/defn drop-cell [c :- Cell] Cell
  (Cell.mk (:world c) false (:parent c) (:owner c) (:dormant c) (:unborn c) (:pending c) (:kids c) (:complete c)))

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
           (nat-app (res-ids (:res (:world c))) (:dormant c)) false 0 (List.nil Nat) false))

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
           (:kids c) (:complete c)))

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
  (Cell.mk (:basis b) true (:cell b) owner (res-ids (:res (:basis b))) true (:res b) (List.nil Nat) false))

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
           (List.nil Nat) false 0 (:kids c) (:complete c)))

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
  (Cell.mk w (:live c) (:parent c) (:owner c) (:dormant c) (:unborn c) (:pending c) (:kids c) (:complete c)))

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
      (have k2 := (kids-mono cells (fupd cells k c2) hm (:kids (cells j)) (And.right q)))
      (simp only [(And.left r0) (And.left q) k2 Bool.and_self Bool.or_true]))))

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
      (= (complete-ready (fupd cells k c2) k) true))
  (intros r0 hw hu hk hd)
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
    (have k2 := (kids-mono cells (fupd cells k c2) (kd-put-mono cells k c2 hd) (:kids (cells k)) (And.right q)))
    (simp only [(And.right hq2) k2 Bool.and_self Bool.or_true])))

;; a world change of a cell that keeps its other fields
(a/theorem cinv-world [cells :- (=> Nat Cell), k :- Nat, c2 :- Cell]
  (=> (cinv cells) (= (:live c2) (:live (cells k))) (= (:complete c2) (:complete (cells k)))
      (= (:unborn c2) (:unborn (cells k))) (= (:kids c2) (:kids (cells k)))
      (=> (= (:live (cells k)) true) (wq (:world (cells k)) (:world c2)))
      (cinv (fupd cells k c2)))
  (intros hc hl hcp hu hk hw)
  (have hd (=> (= (kid-done-c (cells k)) true) (= (kid-done-c c2) true)))
  (intro h) (simp only [kid-done-c hl hcp]) (simp only [kid-done-c] at h) (exact h)
  (apply (cinv-put cells k c2 hc hd))
  (intros l2 c2t)
  (have l1 (= (:live (cells k)) true)) (rw [← hl]) (exact l2)
  (have c1 (= (:complete (cells k)) true)) (rw [← hcp]) (exact c2t)
  (have hc2 := hc) (simp only [cinv] at hc2)
  (exact (ready-put cells k c2 (hc2 k l1 c1) (hw l1) hu hk hd)))

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
      (have k2 := (kids-fresh cells m c2 (:kids (cells j)) (hf j) (And.right q)))
      (simp only [(And.left r0) (And.left q) k2 Bool.and_self Bool.or_true]))))

;; ---- every system operation keeps cinv (HQ: a layer-1 step keeps a released world released and a
;; quiet one quiet; fork, fork effect and instance take an id no cell has accepted)
(a/theorem cinv-step [hq :- (forall [w :- World, it :- Item] (=> (= (p3l w) true) (wq w (:world (world-step w it))))), cells :- (=> Nat Cell), k :- Nat, it :- Item]
  (=> (sinv cells) (cinv cells) (cinv (sys-step cells k it)))
  (intros hs hc)
  (simp only [sys-step])
  (exact (cinv-world cells k (cell-step (cells k) it) hc (rfl) (rfl) (rfl) (rfl)
           (fn [hl :- (= (:live (cells k)) true)] (hq (:world (cells k)) it (sinv-live cells k hs hl))))))

(a/theorem cinv-wake [hq :- (forall [w :- World, it :- Item] (=> (= (p3l w) true) (wq w (:world (world-step w it))))), cells :- (=> Nat Cell), k :- Nat]
  (=> (sinv cells) (cinv cells) (cinv (sys-wake cells k)))
  (intros hs hc)
  (cases hu (:unborn (cells k)))
  (case [true] (simp only [sys-wake hu]) (exact hc))
  (case [false]
    (simp only [sys-wake hu])
    (exact (cinv-world cells k (wake-cell (cells k)) hc (rfl) (rfl) (rfl) (rfl)
             (fn [hl :- (= (:live (cells k)) true)] (wq-wake-all hq (:dormant (cells k)) (:world (cells k)) (sinv-live cells k hs hl)))))))

(a/theorem cinv-resume [hq :- (forall [w :- World, it :- Item] (=> (= (p3l w) true) (wq w (:world (world-step w it))))), cells :- (=> Nat Cell), pubs :- (=> Nat Pub), p :- Nat, v :- Nat]
  (=> (sinv cells) (cinv cells) (cinv (sys-resume cells pubs p v)))
  (intros hs hc)
  (simp only [sys-resume])
  (exact (cinv-world cells (:cell (pubs p)) (resume-cell (cells (:cell (pubs p))) (:res (pubs p)) v) hc (rfl) (rfl) (rfl) (rfl)
           (fn [hl :- (= (:live (cells (:cell (pubs p)))) true)]
             (wq-fire-ack hq (:world (cells (:cell (pubs p)))) (:res (pubs p)) res-ok v (sinv-live cells (:cell (pubs p)) hs hl))))))

(a/theorem cinv-merge [hq :- (forall [w :- World, it :- Item] (=> (= (p3l w) true) (wq w (:world (world-step w it))))), cells :- (=> Nat Cell), k :- Nat, m :- Nat, b :- World]
  (=> (sinv cells) (cinv cells) (cinv (sys-merge cells k m b)))
  (intros hs hc)
  (simp only [sys-merge])
  (exact (cinv-world cells k (merge-cell (cells k) (merge-world (:world (cells k)) (:world (cells m)) b)) hc (rfl) (rfl) (rfl) (rfl)
           (fn [hl :- (= (:live (cells k)) true)] (wq-merge-world hq (:world (cells k)) (:world (cells m)) b (sinv-live cells k hs hl))))))

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
    (exact (ready-put cells k (complete-cell (cells k)) hr (wq-refl (:world (cells k))) (rfl) (rfl) hd))))

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
      (= (complete-ready (fupd cells k c2) k) true))
  (intros r0 hw hu hk hd)
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
      (have k2 := (kids-mono cells (fupd cells k c2) (kd-put-mono cells k c2 hd) (:kids (cells k)) (And.right q)))
      (simp only [(And.right hq2) k2 Bool.and_self Bool.or_true]))))

(a/theorem cinv-world-q [cells :- (=> Nat Cell), k :- Nat, c2 :- Cell]
  (=> (cinv cells) (= (:live c2) (:live (cells k))) (= (:complete c2) (:complete (cells k)))
      (= (:unborn c2) (:unborn (cells k))) (= (:kids c2) (:kids (cells k)))
      (=> (= (:live (cells k)) true) (wqc (cells k) (:world c2)))
      (cinv (fupd cells k c2)))
  (intros hc hl hcp hu hk hw)
  (have hd (=> (= (kid-done-c (cells k)) true) (= (kid-done-c c2) true)))
  (intro h) (simp only [kid-done-c hl hcp]) (simp only [kid-done-c] at h) (exact h)
  (apply (cinv-put cells k c2 hc hd))
  (intros l2 c2t)
  (have l1 (= (:live (cells k)) true)) (rw [← hl]) (exact l2)
  (have c1 (= (:complete (cells k)) true)) (rw [← hcp]) (exact c2t)
  (have hc2 := hc) (simp only [cinv] at hc2)
  (exact (ready-put-q cells k c2 (hc2 k l1 c1) (hw l1) hu hk hd)))

;; ---- completion stability with no premise beyond the system invariants sinv and qsinv
(a/theorem cinv-step-q [cells :- (=> Nat Cell), k :- Nat, it :- Item]
  (=> (sinv cells) (qsinv cells) (cinv cells) (cinv (sys-step cells k it)))
  (intros hs hq hc)
  (simp only [sys-step])
  (exact (cinv-world-q cells k (cell-step (cells k) it) hc (rfl) (rfl) (rfl) (rfl)
           (fn [hl :- (= (:live (cells k)) true)]
             (wqc-of (cells k) _ (qsinv-live cells k hq hl) (rel-step (:world (cells k)) it (sinv-live cells k hs hl))
               (fn [h :- (= (qh (:world (cells k))) true)] (quiet-step (:world (cells k)) it h)))))))

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
                 (fn [h :- (= (qh (:world (cells k))) true)] (qid-wake-all (:dormant (cells k)) (:world (cells k)) h))))))))

(a/theorem cinv-resume-q [cells :- (=> Nat Cell), pubs :- (=> Nat Pub), p :- Nat, v :- Nat]
  (=> (sinv cells) (qsinv cells) (cinv cells) (cinv (sys-resume cells pubs p v)))
  (intros hs hq hc)
  (simp only [sys-resume])
  (exact (cinv-world-q cells (:cell (pubs p)) (resume-cell (cells (:cell (pubs p))) (:res (pubs p)) v) hc (rfl) (rfl) (rfl) (rfl)
           (fn [hl :- (= (:live (cells (:cell (pubs p)))) true)]
             (wqc-of (cells (:cell (pubs p))) _ (qsinv-live cells (:cell (pubs p)) hq hl)
               (rel-fire-ack (:world (cells (:cell (pubs p)))) (:res (pubs p)) res-ok v (sinv-live cells (:cell (pubs p)) hs hl))
               (fn [h :- (= (qh (:world (cells (:cell (pubs p))))) true)] (qid-fire-ack (:world (cells (:cell (pubs p)))) (:res (pubs p)) res-ok v h)))))))

(a/theorem cinv-merge-q [cells :- (=> Nat Cell), k :- Nat, m :- Nat, b :- World]
  (=> (sinv cells) (qsinv cells) (cinv cells) (cinv (sys-merge cells k m b)))
  (intros hs hq hc)
  (simp only [sys-merge])
  (exact (cinv-world-q cells k (merge-cell (cells k) (merge-world (:world (cells k)) (:world (cells m)) b)) hc (rfl) (rfl) (rfl) (rfl)
           (fn [hl :- (= (:live (cells k)) true)]
             (wqc-of (cells k) _ (qsinv-live cells k hq hl) (rel-merge-world (:world (cells k)) (:world (cells m)) b (sinv-live cells k hs hl))
               (fn [h :- (= (qh (:world (cells k))) true)] (qid-merge-world (:world (cells k)) (:world (cells m)) b h)))))))

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

