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
    copies  fork-copy (the child starts from the parent's world), instantiate-copy and
            instantiate-indep (every instance of a publication starts from its basis)
    S4      activate-born, activate-once (a second activation changes nothing)
    merge   sinv-merge, merge-frame, merge-refused (a refused merge changes nothing), merge-unchanged
            (a child that wrote no inherited source merges to the same parent)
    release sinv-idle-release, drop-step-comm (dropping a world commutes with every step elsewhere)

  Not here: following mode (not in the engine either), sealing, sources created in the child (not merged)."
  (:require [ansatz.core :as a]
            [spindel.v2.state :refer :all]
            [spindel.v2.step :refer :all]
            [spindel.v2.engine :refer :all]
            [spindel.v2.hmk2 :refer [p3l]]
            [spindel.v2.progress :refer [quiescent]]
            [spindel.v2.cow :refer [fupd]]))

(a/defn err-forked [] Nat 1)
;; layer 1 arms timers and offloads only (`arm-kind-ok`): a savepoint is an offload-kind resource,
;; told apart by its publication (`Pub.res`). Any other kind would be refused by T17, and every
;; statement below about a published savepoint would hold of nothing.
(a/defn rk-savepoint [] Nat rk-offload)

;; a world of the system: `parent`/`owner` are its fork marker (0 = the root world), `dormant` the
;; inherited resources not yet settled; an instance is `unborn` until its `pending` savepoint is fired
(a/structure Cell [] (world World) (live Bool) (parent Nat) (owner Nat) (dormant (List Nat))
  (unborn Bool) (pending Nat))

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
           (:unborn c) (:pending c)))

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

(a/defn armed-ids [rs :- (List ResRow)] (List Nat)
  (match rs [nil (List.nil Nat)]
         [(cons r t) (if (Nat.beq (:phase r) rp-armed) (List.cons Nat (:id r) (armed-ids t)) (armed-ids t))]))

(a/defn fork-cell [c :- Cell, k :- Nat, owner :- Nat] Cell
  (Cell.mk (:world c) true k owner (nat-app (armed-ids (:res (:world c))) (:dormant c)) false 0))

(a/defn sys-fork [cells :- (=> Nat Cell), k :- Nat, m :- Nat, owner :- Nat] (=> Nat Cell)
  (fupd cells m (fork-cell (cells k) k owner)))

(a/theorem fork-frame [cells :- (=> Nat Cell), k :- Nat, m :- Nat, owner :- Nat, j :- Nat]
  (=> (Not (= j m)) (= (sys-fork cells k m owner j) (cells j)))
  (intro hne)
  (simp only [sys-fork fupd (nbeq-ne j m hne)]))

(a/theorem fork-copy [cells :- (=> Nat Cell), k :- Nat, m :- Nat, owner :- Nat]
  (= (:world (sys-fork cells k m owner m)) (:world (cells k)))
  (simp only [sys-fork fupd-same fork-cell]))

(a/theorem sinv-fork [cells :- (=> Nat Cell), k :- Nat, m :- Nat, owner :- Nat]
  (=> (sinv cells) (= (:live (cells k)) true) (sinv (sys-fork cells k m owner)))
  (intros hs hlk)
  (have hc (=> (= (:live (fork-cell (cells k) k owner)) true) (= (p3l (:world (fork-cell (cells k) k owner))) true)))
  (intro hl)
  (simp only [fork-cell])
  (exact (sinv-live cells k hs hlk))
  (simp only [sys-fork])
  (exact (sinv-put cells m (fork-cell (cells k) k owner) hs hc)))

;; ---------------------------------------------------------------------------
;; L4: the fix-up of a fork's inherited resources, as layer-1 items

(a/defn fire-ack [w :- World, z :- Nat, tag :- Nat, v :- Nat] World
  (:world (world-step (:world (world-step w (Item.resource-fire z tag v))) (Item.resource-ack z))))

(a/theorem p3l-fire-ack [w :- World, z :- Nat, tag :- Nat, v :- Nat]
  (=> (= (p3l w) true) (= (p3l (fire-ack w z tag v)) true))
  (intro h)
  (simp only [fire-ack])
  (exact (step-p3l _ (Item.resource-ack z) (step-p3l w (Item.resource-fire z tag v) h))))

(a/defn wake-one [w :- World, z :- Nat] World
  (match (resource-find w z)
    [none w]
    [(some r) (if (Nat.beq (:kind r) rk-timer) w (fire-ack w z res-err err-forked))]))

(a/defn wake-all [w :- World, zs :- (List Nat)] World
  (match zs [nil w] [(cons z t) (wake-all (wake-one w z) t)]))

(a/theorem p3l-wake-one [w :- World, z :- Nat]
  (=> (= (p3l w) true) (= (p3l (wake-one w z)) true))
  (intro h)
  (cases hf (resource-find w z))
  (case [none] (simp only [wake-one hf]) (exact h))
  (case [some r]
    (cases hk (Nat.beq (:kind r) rk-timer))
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
           (:unborn c) (:pending c)))

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
;; L10/L11: a world leaves the system

(a/defn drop-cell [c :- Cell] Cell
  (Cell.mk (:world c) false (:parent c) (:owner c) (:dormant c) (:unborn c) (:pending c)))

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
           (nat-app (armed-ids (:res (:world c))) (:dormant c)) false 0))

(a/defn sys-fork-effect [cells :- (=> Nat Cell), k :- Nat, m :- Nat, owner :- Nat, st :- Nat, kont :- Nat, v :- Nat]
  (=> Nat Cell)
  (fupd cells m (fork-effect-cell (cells k) k owner st kont v)))

(a/theorem fork-effect-frame [cells :- (=> Nat Cell), k :- Nat, m :- Nat, owner :- Nat, st :- Nat, kont :- Nat, v :- Nat,
                              j :- Nat]
  (=> (Not (= j m)) (= (sys-fork-effect cells k m owner st kont v j) (cells j)))
  (intro hne)
  (simp only [sys-fork-effect fupd (nbeq-ne j m hne)]))

(a/theorem sinv-fork-effect [cells :- (=> Nat Cell), k :- Nat, m :- Nat, owner :- Nat, st :- Nat, kont :- Nat, v :- Nat]
  (=> (sinv cells) (= (:live (cells k)) true) (sinv (sys-fork-effect cells k m owner st kont v)))
  (intros hs hlk)
  (have hc (=> (= (:live (fork-effect-cell (cells k) k owner st kont v)) true)
               (= (p3l (:world (fork-effect-cell (cells k) k owner st kont v))) true)))
  (intro hl)
  (simp only [fork-effect-cell])
  (exact (p3l-fork-effect-world (:world (cells k)) st kont v (sinv-live cells k hs hlk)))
  (simp only [sys-fork-effect])
  (exact (sinv-put cells m (fork-effect-cell (cells k) k owner st kont v) hs hc)))

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
  (Cell.mk (fire-ack (:world c) z res-ok v) (:live c) (:parent c) (:owner c) (:dormant c) (:unborn c) (:pending c)))

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
  (Cell.mk (:basis b) true (:cell b) owner (armed-ids (:res (:basis b))) true (:res b)))

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

(a/defn act-ok [c :- Cell] Bool (Bool.and (:unborn c) (Bool.not (Nat.beq (:pending c) 0))))

(a/defn act-cell [c :- Cell, v :- Nat] Cell
  (Cell.mk (wake-all (fire-ack (:world c) (:pending c) res-ok v) (:dormant c)) (:live c) (:parent c) (:owner c)
           (List.nil Nat) false 0))

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

(a/defn diff [c :- World, b :- World] (List Nat) (diff-ids c b (tbl-ids source-id (:sources b))))

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
  (Cell.mk w (:live c) (:parent c) (:owner c) (:dormant c) (:unborn c) (:pending c)))

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
