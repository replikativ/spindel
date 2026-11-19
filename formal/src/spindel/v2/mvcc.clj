(ns spindel.v2.mvcc
  "Layer 2, physical, MVCC representation (spec §8.1 \"Representation (MVCC, 2026-11-15)\",
  `v2-fork-memory-design` §2, §7; engine `core.cljc` `preserve!`, `version-of`, `view`, `resolve-row`,
  `peek-row`, `own-copy!`, `fork-world*`, `instance-world*`, `register-token!`, `prune-cell!`,
  `finish-token!`/`maybe-finish-token!`), kernel-checked (Init only). It replaced the model of the
  engine's earlier forward-map representation (`spindel.v2.cow`, retired: in git history); the
  semantic layer (`spindel.v2.sys`: a fork is a value copy) is unchanged. See notes/LAYER2.md §9.

  State (`MSt`): a heap `h : address -> MRow` (id, owner world `ow`, stamp ordinal `so`, value,
  versions `[k m img]`), the next free address `n`, `home : id -> address` (the row its creator made),
  per world an `MW` (ordinal, copy map `fwd : id -> address`, lineage `[own f tok mp]` nearest first,
  the owner's token cells `[o tok]`), token states `ts` (0 live, 1 shared, 2 dead), the active worlds,
  the savepoint bases, and as ghost state the semantic tables `dom`/`tab` (the value-copy model).
  Values are opaque Nats; references abstract to ids, so path compression is invisible;
  the lineage cut is the domain (`inherited?` is not modelled here).

  Reading (`mv-res`): an owned row, else the world's own copy, else the lineage nearest first: an
  ancestor's copy as it was at the fork, or the ancestor's own row, at the fork's ordinal (`mv-vat`:
  the live row if its stamp is not newer, else the version whose range holds the ordinal).

  Operations: `mv-write` (the `rv` barrier `mv-pres` then the change), `mv-copy` (own-copy!),
  `mv-create`, `mv-fork` (ordinal advances, token registered, the parent's own token shared),
  `mv-inst` (S3: the basis's lineage, its token shared), `mv-prune`, `mv-finish` (the world's own token
  ends unless shared), `mv-drop` (a world is collected), `mv-collect` (an unreachable token ends)."
  (:require [ansatz.core :as a]))

(a/load-init!)

;; ---------------------------------------------------------------------------
;; Rows, versions, worlds

;; a saved version: the state forks with ordinal in [k, m] read
(a/structure MVer [] (k Nat) (m Nat) (img Nat))
;; a row object: logical id, owner world, stamp ordinal, current value, saved versions
(a/structure MRow [] (id Nat) (ow Nat) (so Nat) (val Nat) (vers (List MVer)))
;; an owner's token cell: the fork's ordinal and its token
(a/structure MCell [] (o Nat) (tok Nat))
;; a lineage entry: ancestor, ordinal of the fork, token, the ancestor's copy map at the fork
(a/structure MEnt [] (own Nat) (f Nat) (tok Nat) (mp (=> Nat Nat)))
;; a world: ordinal, copy map (0 = none), lineage (nearest first), token cells of its forks
(a/structure MW [] (ord Nat) (fwd (=> Nat Nat)) (lin (List MEnt)) (cells (List MCell)))

(a/defn mv-upd [A :- Type :implicit, f :- (=> Nat A), k :- Nat, v :- A] (=> Nat A)
  (fn [x :- Nat] (if (Nat.beq x k) v (f x))))

;; ---------------------------------------------------------------------------
;; Reading

;; the first version whose range holds ordinal f
(a/defn mv-look [vs :- (List MVer), f :- Nat] (Option Nat)
  (match vs
    [nil (Option.none Nat)]
    [(cons v t) (if (Bool.and (Nat.ble (:k v) f) (Nat.ble f (:m v)))
                  (Option.some Nat (:img v))
                  (mv-look t f))]))

;; `version-of`: row x as forks at ordinal f see it
(a/defn mv-vat [x :- MRow, f :- Nat] (Option Nat)
  (if (Nat.ble (:so x) f) (Option.some Nat (:val x)) (mv-look (:vers x) f)))

;; `view`: the lineage, nearest first, for id i whose reference is the row at address r
(a/defn mv-scan [h :- (=> Nat MRow), r :- Nat, i :- Nat, l :- (List MEnt)] (Option Nat)
  (match l
    [nil (Option.none Nat)]
    [(cons e t) (if (Nat.beq (MEnt.mp e i) 0)
                  (if (Nat.beq (:ow (h r)) (:own e)) (mv-vat (h r) (:f e)) (mv-scan h r i t))
                  (mv-vat (h (MEnt.mp e i)) (:f e)))]))

;; `peek-row`/`resolve-row` read side: world w (state W) reads id i
(a/defn mv-res [h :- (=> Nat MRow), home :- (=> Nat Nat), w :- Nat, W :- MW, i :- Nat] (Option Nat)
  (if (Nat.beq (:ow (h (home i))) w)
    (Option.some Nat (:val (h (home i))))
    (if (Nat.beq (MW.fwd W i) 0)
      (mv-scan h (home i) i (:lin W))
      (Option.some Nat (:val (h (MW.fwd W i)))))))

;; ---------------------------------------------------------------------------
;; Owner side: the barrier (`preserve!`) and pruning

;; a fork with ordinal in [k, m] whose token has not ended (`live-token-in?`)
(a/defn mv-live-in [cs :- (List MCell), ts :- (=> Nat Nat), k :- Nat, m :- Nat] Bool
  (match cs
    [nil false]
    [(cons c t) (Bool.or (Bool.and (Nat.ble k (:o c))
                                   (Bool.and (Nat.ble (:o c) m) (Bool.not (Nat.beq (ts (:tok c)) 2))))
                         (mv-live-in t ts k m))]))

;; `prune-versions`: the versions some live fork can still read
(a/defn mv-prune-vs [cs :- (List MCell), ts :- (=> Nat Nat), vs :- (List MVer)] (List MVer)
  (match vs
    [nil (List.nil MVer)]
    [(cons v t) (if (mv-live-in cs ts (:k v) (:m v))
                  (List.cons MVer v (mv-prune-vs cs ts t))
                  (mv-prune-vs cs ts t))]))

;; `preserve!` on a row stamped before the owner's ordinal o: save its state for the forks
;; [so, o-1] if one of them is live, prune, restamp
(a/defn mv-pres [cs :- (List MCell), ts :- (=> Nat Nat), o :- Nat, x :- MRow] MRow
  (if (Nat.blt (:so x) o)
    (MRow.mk (:id x) (:ow x) o (:val x)
             (if (mv-live-in cs ts (:so x) (- o 1))
               (List.append (mv-prune-vs cs ts (:vers x))
                            (List.cons MVer (MVer.mk (:so x) (- o 1) (:val x)) (List.nil MVer)))
               (mv-prune-vs cs ts (:vers x))))
    x))

;; a change of the (restamped) row's value
(a/defn mv-setv [x :- MRow, y :- Nat] MRow
  (MRow.mk (:id x) (:ow x) (:so x) y (:vers x)))

;; ---------------------------------------------------------------------------
;; The family state and its operations

(a/structure MSt []
  (h (=> Nat MRow)) (n Nat) (home (=> Nat Nat)) (fam (=> Nat MW))
  (act (=> Nat Bool)) (bas (=> Nat Bool)) (ts (=> Nat Nat))
  (dom (=> Nat (=> Nat Bool))) (tab (=> Nat (=> Nat Nat))))

;; the address world w writes for id i: its own row, else its copy (`resolve-row` after own-copy!)
(a/defn mv-tgt [s :- MSt, w :- Nat, i :- Nat] Nat
  (if (Nat.beq (:ow ((:h s) ((:home s) i))) w) ((:home s) i) (MW.fwd ((:fam s) w) i)))

;; `own-copy!`: world w copies the version v it reads of the inherited id i to the fresh address n
(a/defn mv-copy [s :- MSt, w :- Nat, i :- Nat, v :- Nat] MSt
  (MSt.mk (mv-upd (:h s) (:n s) (MRow.mk i w (:ord ((:fam s) w)) v (List.nil MVer)))
          (+ (:n s) 1) (:home s)
          (mv-upd (:fam s) w (MW.mk (:ord ((:fam s) w)) (mv-upd (MW.fwd ((:fam s) w)) i (:n s))
                                    (:lin ((:fam s) w)) (:cells ((:fam s) w))))
          (:act s) (:bas s) (:ts s) (:dom s) (:tab s)))

;; a write of y to id i by world w: the barrier, then the change; the table changes at (w, i)
(a/defn mv-write [s :- MSt, w :- Nat, i :- Nat, y :- Nat] MSt
  (MSt.mk (mv-upd (:h s) (mv-tgt s w i)
                  (mv-setv (mv-pres (:cells ((:fam s) w)) (:ts s) (:ord ((:fam s) w)) ((:h s) (mv-tgt s w i))) y))
          (:n s) (:home s) (:fam s) (:act s) (:bas s) (:ts s) (:dom s)
          (mv-upd (:tab s) w (mv-upd ((:tab s) w) i y))))

;; a new row i created by world w with value y
(a/defn mv-create [s :- MSt, w :- Nat, i :- Nat, y :- Nat] MSt
  (MSt.mk (mv-upd (:h s) (:n s) (MRow.mk i w (:ord ((:fam s) w)) y (List.nil MVer)))
          (+ (:n s) 1) (mv-upd (:home s) i (:n s)) (:fam s) (:act s) (:bas s) (:ts s)
          (mv-upd (:dom s) w (mv-upd ((:dom s) w) i true))
          (mv-upd (:tab s) w (mv-upd ((:tab s) w) i y))))

;; a token state after `token-share!`: an ended token stays ended, otherwise it is shared (sticky)
(a/defn mv-shr [v :- Nat] Nat (if (Nat.beq v 2) 2 1))

;; `share-token!`: the token a world got at its fork (the head of its lineage) is shared (sticky)
(a/defn mv-share [ts :- (=> Nat Nat), l :- (List MEnt)] (=> Nat Nat)
  (match l
    [nil ts]
    [(cons e t) (mv-upd ts (:tok e) (mv-shr (ts (:tok e))))]))

;; `finish-token!`: it ends unless shared
(a/defn mv-fin [ts :- (=> Nat Nat), l :- (List MEnt)] (=> Nat Nat)
  (match l
    [nil ts]
    [(cons e t) (mv-upd ts (:tok e) (if (Nat.beq (ts (:tok e)) 0) 2 (ts (:tok e))))]))

;; `fork-world*` of w: child c (a savepoint basis when b), token t at w's ordinal o; w advances
(a/defn mv-fork [s :- MSt, w :- Nat, c :- Nat, t :- Nat, b :- Bool] MSt
  (MSt.mk (:h s) (:n s) (:home s)
          (mv-upd (mv-upd (:fam s) w
                          (MW.mk (+ (:ord ((:fam s) w)) 1) (MW.fwd ((:fam s) w)) (:lin ((:fam s) w))
                                 (List.append (:cells ((:fam s) w))
                                              (List.cons MCell (MCell.mk (:ord ((:fam s) w)) t) (List.nil MCell)))))
                  c (MW.mk 0 (fn [x :- Nat] 0)
                           (List.cons MEnt (MEnt.mk w (:ord ((:fam s) w)) t (MW.fwd ((:fam s) w))) (:lin ((:fam s) w)))
                           (List.nil MCell)))
          (mv-upd (:act s) c true) (mv-upd (:bas s) c b)
          (mv-upd (mv-share (:ts s) (:lin ((:fam s) w))) t 0)
          (mv-upd (:dom s) c ((:dom s) w)) (mv-upd (:tab s) c ((:tab s) w))))

;; `instance-world*` (S3): an instance c of the basis b takes b's lineage; b's token is shared
(a/defn mv-inst [s :- MSt, b :- Nat, c :- Nat] MSt
  (MSt.mk (:h s) (:n s) (:home s)
          (mv-upd (:fam s) c (MW.mk 0 (fn [x :- Nat] 0) (:lin ((:fam s) b)) (List.nil MCell)))
          (mv-upd (:act s) c true) (mv-upd (:bas s) c false)
          (mv-share (:ts s) (:lin ((:fam s) b)))
          (mv-upd (:dom s) c ((:dom s) b)) (mv-upd (:tab s) c ((:tab s) b))))

;; `prune-cell!` / the sweep: the row at address a keeps the versions a live fork of its owner reads
(a/defn mv-prune [s :- MSt, a :- Nat] MSt
  (MSt.mk (mv-upd (:h s) a
                  (MRow.mk (:id ((:h s) a)) (:ow ((:h s) a)) (:so ((:h s) a)) (:val ((:h s) a))
                           (mv-prune-vs (:cells ((:fam s) (:ow ((:h s) a)))) (:ts s) (:vers ((:h s) a)))))
          (:n s) (:home s) (:fam s) (:act s) (:bas s) (:ts s) (:dom s) (:tab s)))

;; `maybe-finish-token!`: world w finished (released, no work, cleanup or armed resource)
(a/defn mv-finish [s :- MSt, w :- Nat] MSt
  (MSt.mk (:h s) (:n s) (:home s) (:fam s) (mv-upd (:act s) w false) (:bas s)
          (mv-fin (:ts s) (:lin ((:fam s) w))) (:dom s) (:tab s)))

;; world w is collected (or a publication disposed): it reads nothing any more
(a/defn mv-drop [s :- MSt, w :- Nat] MSt
  (MSt.mk (:h s) (:n s) (:home s) (:fam s) (mv-upd (:act s) w false) (:bas s) (:ts s) (:dom s) (:tab s)))

;; an unreachable token ends (the Cleaner)
(a/defn mv-collect [s :- MSt, t :- Nat] MSt
  (MSt.mk (:h s) (:n s) (:home s) (:fam s) (:act s) (:bas s) (mv-upd (:ts s) t 2) (:dom s) (:tab s)))

;; ---------------------------------------------------------------------------
;; Basic lemmas

(a/theorem mv-nbeq-ne [a :- Nat, b :- Nat] (=> (Not (= a b)) (= (Nat.beq a b) false))
  (intro hne)
  (cases hab (Nat.beq a b))
  (rfl)
  (exact (absurd (Nat.eq_of_beq_eq_true hab) hne)))

(a/theorem mv-upd-same [A :- Type :implicit, f :- (=> Nat A), k :- Nat, v :- A]
  (= (mv-upd f k v k) v)
  (simp only [mv-upd Nat.beq_refl]))

(a/theorem mv-upd-other [A :- Type :implicit, f :- (=> Nat A), k :- Nat, v :- A, x :- Nat]
  (=> (Not (= x k)) (= (mv-upd f k v x) (f x)))
  (intro h) (simp only [mv-upd (mv-nbeq-ne x k h)]))

;; ---------------------------------------------------------------------------
;; Versions: lookup, pruning, the barrier

;; every saved range ends before s (versions are older than the stamp)
(a/defn mv-vlt [s :- Nat, vs :- (List MVer)] Bool
  (match vs [nil true] [(cons v t) (Bool.and (Nat.blt (:m v) s) (mv-vlt s t))]))

;; a token cell at ordinal o with token t
(a/defn mv-has-cell [cs :- (List MCell), o :- Nat, t :- Nat] Bool
  (match cs [nil false] [(cons c r) (Bool.or (Bool.and (Nat.beq (:o c) o) (Nat.beq (:tok c) t)) (mv-has-cell r o t))]))

(a/theorem mv-look-app-some [l1 :- (List MVer), l2 :- (List MVer), f :- Nat, y :- Nat]
  (=> (= (mv-look l1 f) (Option.some Nat y)) (= (mv-look (List.append l1 l2) f) (Option.some Nat y)))
  (induction l1)
  (case [nil] (intro hl) (simp only [mv-look] at hl) (cases hl))
  (case [cons v t ih]
    (intro hl)
    (cases hc (Bool.and (Nat.ble (:k v) f) (Nat.ble f (:m v))))
    (case [false] (simp only [mv-look hc] at hl) (simp only [List.append mv-look hc]) (exact (ih hl)))
    (case [true] (simp only [mv-look hc] at hl) (simp only [List.append mv-look hc]) (exact hl))))

(a/theorem mv-look-app-none [l1 :- (List MVer), l2 :- (List MVer), f :- Nat]
  (=> (= (mv-look l1 f) (Option.none Nat)) (= (mv-look (List.append l1 l2) f) (mv-look l2 f)))
  (induction l1)
  (case [nil] (intro hl) (simp only [List.append]))
  (case [cons v t ih]
    (intro hl)
    (cases hc (Bool.and (Nat.ble (:k v) f) (Nat.ble f (:m v))))
    (case [false] (simp only [mv-look hc] at hl) (simp only [List.append mv-look hc]) (exact (ih hl)))
    (case [true] (simp only [mv-look hc] at hl) (cases hl))))

(a/theorem mv-live-mono [cs :- (List MCell), ts :- (=> Nat Nat), f :- Nat, k :- Nat, m :- Nat]
  (=> (= (mv-live-in cs ts f f) true) (<= k f) (<= f m) (= (mv-live-in cs ts k m) true))
  (intros hl hk hm)
  (induction cs)
  (case [nil] (simp only [mv-live-in] at hl) (cases hl))
  (case [cons c r ih]
    (simp only [mv-live-in Bool.or_eq_true Bool.and_eq_true Nat.ble_eq] at hl)
    (simp only [mv-live-in Bool.or_eq_true Bool.and_eq_true Nat.ble_eq])
    (cases hl)
    (case [inl h1] (left) (have q1 (<= k (:o c))) (omega) (have q2 (<= (:o c) m)) (omega)
      (exact (And.intro q1 (And.intro q2 (And.right (And.right h1))))))
    (case [inr h2] (right) (exact (ih h2)))))

(a/theorem mv-cell-live [cs :- (List MCell), ts :- (=> Nat Nat), f :- Nat, t :- Nat]
  (=> (= (mv-has-cell cs f t) true) (Not (= (ts t) 2)) (= (mv-live-in cs ts f f) true))
  (intros hc hd)
  (induction cs)
  (case [nil] (simp only [mv-has-cell] at hc) (cases hc))
  (case [cons c r ih]
    (simp only [mv-has-cell Bool.or_eq_true Bool.and_eq_true Nat.beq_eq] at hc)
    (simp only [mv-live-in Bool.or_eq_true Bool.and_eq_true Nat.ble_eq])
    (cases hc)
    (case [inl h1]
      (left)
      (have e1 := (And.left h1)) (have e2 := (And.right h1))
      (have q1 (<= f (:o c))) (omega) (have q2 (<= (:o c) f)) (omega)
      (have q3 (= (Bool.not (Nat.beq (ts (:tok c)) 2)) true))
      (rw [e2]) (rw [(mv-nbeq-ne (ts t) 2 hd)])
      (exact (And.intro q1 (And.intro q2 q3))))
    (case [inr h2] (right) (exact (ih h2)))))

;; pruning keeps what a live fork at f reads (the first version holding f survives)
(a/theorem mv-look-prune [cs :- (List MCell), ts :- (=> Nat Nat), f :- Nat, vs :- (List MVer)]
  (=> (= (mv-live-in cs ts f f) true) (= (mv-look (mv-prune-vs cs ts vs) f) (mv-look vs f)))
  (intro hl)
  (induction vs)
  (case [nil] (simp only [mv-prune-vs mv-look]))
  (case [cons v t ih]
    (cases hc (Bool.and (Nat.ble (:k v) f) (Nat.ble f (:m v))))
    (case [false]
      (cases hk (mv-live-in cs ts (:k v) (:m v)))
      (case [false] (simp only [mv-prune-vs hk mv-look hc]) (exact ih))
      (case [true] (simp only [mv-prune-vs hk mv-look hc]) (exact ih)))
    (case [true]
      (have hc2 := hc)
      (simp only [Bool.and_eq_true Nat.ble_eq] at hc2)
      (have hk := (mv-live-mono cs ts f (:k v) (:m v) hl (And.left hc2) (And.right hc2)))
      (simp only [mv-prune-vs hk mv-look hc]))))

(a/theorem mv-look-vlt-none [s :- Nat, f :- Nat, vs :- (List MVer)]
  (=> (= (mv-vlt s vs) true) (<= s f) (= (mv-look vs f) (Option.none Nat)))
  (intros hv hsf)
  (induction vs)
  (case [nil] (simp only [mv-look]))
  (case [cons v t ih]
    (simp only [mv-vlt Bool.and_eq_true Nat.blt_eq] at hv)
    (cases hc (Bool.and (Nat.ble (:k v) f) (Nat.ble f (:m v))))
    (case [false] (simp only [mv-look hc]) (exact (ih (And.right hv))))
    (case [true]
      (have hc2 := hc)
      (simp only [Bool.and_eq_true Nat.ble_eq] at hc2)
      (have q := (And.left hv)) (have q2 := (And.right hc2))
      (exfalso) (omega))))

(a/theorem mv-vlt-prune [cs :- (List MCell), ts :- (=> Nat Nat), s :- Nat, vs :- (List MVer)]
  (=> (= (mv-vlt s vs) true) (= (mv-vlt s (mv-prune-vs cs ts vs)) true))
  (intro hv)
  (induction vs)
  (case [nil] (simp only [mv-prune-vs mv-vlt]))
  (case [cons v t ih]
    (simp only [mv-vlt Bool.and_eq_true] at hv)
    (cases hk (mv-live-in cs ts (:k v) (:m v)))
    (case [false] (simp only [mv-prune-vs hk]) (exact (ih (And.right hv))))
    (case [true] (simp only [mv-prune-vs hk mv-vlt Bool.and_eq_true])
      (exact (And.intro (And.left hv) (ih (And.right hv)))))))

(a/theorem mv-vlt-mono [s :- Nat, s2 :- Nat, vs :- (List MVer)]
  (=> (= (mv-vlt s vs) true) (<= s s2) (= (mv-vlt s2 vs) true))
  (intros hv hs)
  (induction vs)
  (case [nil] (simp only [mv-vlt]))
  (case [cons v t ih]
    (simp only [mv-vlt Bool.and_eq_true Nat.blt_eq] at hv)
    (simp only [mv-vlt Bool.and_eq_true Nat.blt_eq])
    (have q := (And.left hv)) (have q2 (< (:m v) s2)) (omega)
    (exact (And.intro q2 (ih (And.right hv))))))

(a/theorem mv-vlt-app [s :- Nat, l1 :- (List MVer), l2 :- (List MVer)]
  (=> (= (mv-vlt s l1) true) (= (mv-vlt s l2) true) (= (mv-vlt s (List.append l1 l2)) true))
  (intros h1 h2)
  (induction l1)
  (case [nil] (simp only [List.append]) (exact h2))
  (case [cons v t ih]
    (simp only [mv-vlt Bool.and_eq_true] at h1)
    (simp only [List.append mv-vlt Bool.and_eq_true])
    (exact (And.intro (And.left h1) (ih (And.right h1))))))

(a/theorem mv-blt-f [a :- Nat, b :- Nat] (=> (= (Nat.blt a b) false) (<= b a))
  (intro h)
  (have hn (Not (< a b)))
  (intro hc) (have q (= (Nat.blt a b) true)) (simp only [Nat.blt_eq]) (exact hc) (rw [q] at h) (cases h)
  (omega))

(a/theorem mv-ble-f [a :- Nat, b :- Nat] (=> (= (Nat.ble a b) false) (< b a))
  (intro h)
  (have hn (Not (<= a b)))
  (intro hc) (have q (= (Nat.ble a b) true)) (simp only [Nat.ble_eq]) (exact hc) (rw [q] at h) (cases h)
  (omega))

(a/theorem mv-ble-of-lt [a :- Nat, b :- Nat] (=> (< b a) (= (Nat.ble a b) false))
  (intro h)
  (cases q (Nat.ble a b)) (rfl) (simp only [Nat.ble_eq] at q) (exfalso) (omega))

;; THE BARRIER. A fork at ordinal f < o whose token is live reads the same state of row x after
;; the owner preserves it (`preserve!` at ordinal o) and changes it.
(a/theorem mv-vat-pres [cs :- (List MCell), ts :- (=> Nat Nat), o :- Nat, x :- MRow, y :- Nat, f :- Nat]
  (=> (< f o) (<= (:so x) o) (= (mv-vlt (:so x) (:vers x)) true) (= (mv-live-in cs ts f f) true)
      (= (mv-vat (mv-setv (mv-pres cs ts o x) y) f) (mv-vat x f)))
  (intros hfo hso hv hl)
  (cases hb (Nat.blt (:so x) o))
  (case [false]
    ;; stamped at the current ordinal: nothing to save; forks read the versions
    (have hb2 := (mv-blt-f (:so x) o hb))
    (have hq (< f (:so x))) (omega)
    (have hsf := (mv-ble-of-lt (:so x) f hq))
    (simp only [mv-pres hb mv-setv mv-vat hsf]))
  (case [true]
    (have hb2 := hb)
    (simp only [Nat.blt_eq] at hb2)
    (have hof := (mv-ble-of-lt o f hfo))
    (cases hsf (Nat.ble (:so x) f))
    (case [true]
      ;; unchanged since the fork: the saved version is the live state
      (have hsf2 := hsf)
      (simp only [Nat.ble_eq] at hsf2)
      (have hq2 (<= f (- o 1))) (omega)
      (have hk := (mv-live-mono cs ts f (:so x) (- o 1) hl hsf2 hq2))
      (have hn := (mv-look-vlt-none (:so x) f (:vers x) hv hsf2))
      (have hpn (= (mv-look (mv-prune-vs cs ts (:vers x)) f) (Option.none Nat)))
      (rw [(mv-look-prune cs ts f (:vers x) hl)]) (exact hn)
      (have hin (= (Bool.and (Nat.ble (:so x) f) (Nat.ble f (- o 1))) true))
      (simp only [Bool.and_eq_true Nat.ble_eq]) (exact (And.intro hsf2 hq2))
      (simp only [mv-pres hb mv-setv mv-vat hof hsf hk])
      (rw [(mv-look-app-none _ _ f hpn)])
      (simp only [mv-look hin]))
    (case [false]
      ;; changed since the fork: the version it reads is kept, the new one starts after it
      (have hsf2 := (mv-ble-f (:so x) f hsf))
      (have hout (= (Bool.and (Nat.ble (:so x) f) (Nat.ble f (- o 1))) false))
      (simp only [hsf Bool.false_and])
      (cases hk (mv-live-in cs ts (:so x) (- o 1)))
      (case [false]
        (simp only [mv-pres hb mv-setv mv-vat hof hsf hk])
        (exact (mv-look-prune cs ts f (:vers x) hl)))
      (case [true]
        (simp only [mv-pres hb mv-setv mv-vat hof hsf hk])
        (cases hL (mv-look (mv-prune-vs cs ts (:vers x)) f))
        (case [none]
          (rw [(mv-look-app-none _ _ f hL)])
          (rw [(Eq.symm (mv-look-prune cs ts f (:vers x) hl))])
          (rw [hL])
          (simp only [mv-look hout]))
        (case [some z]
          (rw [(mv-look-app-some _ _ f z hL)])
          (rw [(Eq.symm (mv-look-prune cs ts f (:vers x) hl))])
          (rw [hL]))))))

;; ---------------------------------------------------------------------------
;; Reading is local: frame lemmas

;; every lineage entry satisfies P
(a/defn mv-allE [P :- (=> MEnt Prop), l :- (List MEnt)] Prop
  (match l [nil True] [(cons e t) (And (P e) (mv-allE P t))]))

(a/theorem mv-allE-mono [P :- (=> MEnt Prop), Q :- (=> MEnt Prop), l :- (List MEnt)]
  (=> (forall [e :- MEnt] (=> (P e) (Q e))) (mv-allE P l) (mv-allE Q l))
  (intros hpq hp)
  (induction l)
  (case [nil] (simp only [mv-allE]))
  (case [cons e t ih]
    (simp only [mv-allE] at hp)
    (simp only [mv-allE])
    (exact (And.intro (hpq e (And.left hp)) (ih (And.right hp))))))

;; what entry e makes a reader of id i (reference r) read is the same under h and h2
(a/defn mv-same-at [h :- (=> Nat MRow), h2 :- (=> Nat MRow), r :- Nat, i :- Nat, e :- MEnt] Prop
  (And (=> (Not (= (MEnt.mp e i) 0)) (= (mv-vat (h2 (MEnt.mp e i)) (:f e)) (mv-vat (h (MEnt.mp e i)) (:f e))))
       (=> (= (:ow (h r)) (:own e)) (= (mv-vat (h2 r) (:f e)) (mv-vat (h r) (:f e))))))

(a/theorem mv-scan-frame [h :- (=> Nat MRow), h2 :- (=> Nat MRow), r :- Nat, i :- Nat, l :- (List MEnt)]
  (=> (= (:ow (h2 r)) (:ow (h r))) (mv-allE (mv-same-at h h2 r i) l)
      (= (mv-scan h2 r i l) (mv-scan h r i l)))
  (intros how hs)
  (induction l)
  (case [nil] (simp only [mv-scan]))
  (case [cons e t ih]
    (simp only [mv-allE mv-same-at] at hs)
    (have he := (And.left hs))
    (cases hm (Nat.beq (MEnt.mp e i) 0))
    (case [false]
      (have hne := (Nat.ne_of_beq_eq_false hm))
      (simp only [mv-scan hm])
      (exact ((And.left he) hne)))
    (case [true]
      (cases ho (Nat.beq (:ow (h r)) (:own e)))
      (case [false]
        (simp only [mv-scan hm how ho])
        (exact (ih (And.right hs))))
      (case [true]
        (have heq := (Nat.eq_of_beq_eq_true ho))
        (simp only [mv-scan hm how ho])
        (exact ((And.right he) heq))))))

(a/theorem mv-res-frame [h :- (=> Nat MRow), h2 :- (=> Nat MRow), home :- (=> Nat Nat), w :- Nat, W :- MW, i :- Nat]
  (=> (= (:ow (h2 (home i))) (:ow (h (home i))))
      (=> (= (:ow (h (home i))) w) (= (:val (h2 (home i))) (:val (h (home i)))))
      (=> (Not (= (MW.fwd W i) 0)) (= (:val (h2 (MW.fwd W i))) (:val (h (MW.fwd W i)))))
      (mv-allE (mv-same-at h h2 (home i) i) (:lin W))
      (= (mv-res h2 home w W i) (mv-res h home w W i)))
  (intros how hown hfwd hs)
  (cases ho (Nat.beq (:ow (h (home i))) w))
  (case [true]
    (simp only [mv-res how ho (hown (Nat.eq_of_beq_eq_true ho))]))
  (case [false]
    (cases hf (Nat.beq (MW.fwd W i) 0))
    (case [true] (simp only [mv-res how ho hf]) (exact (mv-scan-frame h h2 (home i) i (:lin W) how hs)))
    (case [false] (simp only [mv-res how ho hf (hfwd (Nat.ne_of_beq_eq_false hf))]))))

;; ---------------------------------------------------------------------------
;; The invariant

;; rows: a stamp is never ahead of its owner's ordinal; saved ranges end before the stamp
(a/defn mv-k-row [s :- MSt] Prop
  (forall [a :- Nat] (=> (< a (:n s))
    (And (<= (:so ((:h s) a)) (:ord ((:fam s) (:ow ((:h s) a)))))
         (= (mv-vlt (:so ((:h s) a)) (:vers ((:h s) a))) true)))))

;; copy maps: a copy is a row of that id, owned by the world
(a/defn mv-k-fwd [s :- MSt] Prop
  (forall [u :- Nat, i :- Nat] (=> (Not (= (MW.fwd ((:fam s) u) i) 0))
    (And (< (MW.fwd ((:fam s) u) i) (:n s))
         (And (= (:id ((:h s) (MW.fwd ((:fam s) u) i))) i)
              (= (:ow ((:h s) (MW.fwd ((:fam s) u) i))) u))))))

;; a lineage entry: the fork is older than its owner's ordinal, its token has not ended and is
;; registered with the owner, and the copy map it carries names the owner's rows of each id
(a/defn mv-ent-ok [s :- MSt, e :- MEnt] Prop
  (And (< (:f e) (:ord ((:fam s) (:own e))))
       (And (Not (= ((:ts s) (:tok e)) 2))
            (And (= (mv-has-cell (:cells ((:fam s) (:own e))) (:f e) (:tok e)) true)
                 (forall [i :- Nat] (=> (Not (= (MEnt.mp e i) 0))
                   (And (< (MEnt.mp e i) (:n s))
                        (And (= (:id ((:h s) (MEnt.mp e i))) i)
                             (= (:ow ((:h s) (MEnt.mp e i))) (:own e))))))))))

(a/defn mv-k-lin [s :- MSt] Prop
  (forall [u :- Nat] (=> (= ((:act s) u) true) (mv-allE (mv-ent-ok s) (:lin ((:fam s) u))))))

;; the creator's row of every id an active world has
(a/defn mv-k-home [s :- MSt] Prop
  (forall [u :- Nat, i :- Nat] (=> (= ((:act s) u) true) (= (((:dom s) u) i) true)
    (And (< ((:home s) i) (:n s)) (= (:id ((:h s) ((:home s) i))) i)))))

(a/defn mv-tl [l :- (List MEnt)] (List MEnt) (match l [nil (List.nil MEnt)] [(cons e t) t]))
(a/defn mv-ht [l :- (List MEnt)] (Option Nat) (match l [nil (Option.none Nat)] [(cons e t) (Option.some Nat (:tok e))]))

;; sharing: a token below the head of a lineage is shared (something was derived from its fork);
;; two active worlds with the same head token (instances of one basis) share it
(a/defn mv-shared-tok [ts :- (=> Nat Nat), e :- MEnt] Prop (= (ts (:tok e)) 1))
(a/defn mv-k-share [s :- MSt] Prop
  (And (forall [u :- Nat] (=> (= ((:act s) u) true) (mv-allE (mv-shared-tok (:ts s)) (mv-tl (:lin ((:fam s) u))))))
       (forall [u :- Nat, v :- Nat, t :- Nat]
         (=> (= ((:act s) u) true) (= ((:act s) v) true) (Not (= u v))
             (= (mv-ht (:lin ((:fam s) u))) (Option.some Nat t)) (= (mv-ht (:lin ((:fam s) v))) (Option.some Nat t))
             (= ((:ts s) t) 1)))))

;; a savepoint basis never runs: it owns no row and has no copy
(a/defn mv-k-bas [s :- MSt] Prop
  (forall [u :- Nat] (=> (= ((:act s) u) true) (= ((:bas s) u) true)
    (And (forall [i :- Nat] (= (MW.fwd ((:fam s) u) i) 0))
         (forall [a :- Nat] (=> (< a (:n s)) (Not (= (:ow ((:h s) a)) u))))))))

;; REFINEMENT: every active world reads exactly its table (the value-copy model)
(a/defn mv-ref [s :- MSt] Prop
  (forall [u :- Nat, i :- Nat] (=> (= ((:act s) u) true) (= (((:dom s) u) i) true)
    (= (mv-res (:h s) (:home s) u ((:fam s) u) i) (Option.some Nat (((:tab s) u) i))))))

(a/defn mv-inv [s :- MSt] Prop
  (And (mv-k-row s) (And (mv-k-fwd s) (And (mv-k-lin s) (And (mv-k-home s)
    (And (mv-k-share s) (And (mv-k-bas s) (mv-ref s))))))))

;; ---------------------------------------------------------------------------
;; The barrier keeps a row's identity

(a/theorem mv-pres-id [cs :- (List MCell), ts :- (=> Nat Nat), o :- Nat, x :- MRow, y :- Nat]
  (And (= (:id (mv-setv (mv-pres cs ts o x) y)) (:id x)) (= (:ow (mv-setv (mv-pres cs ts o x) y)) (:ow x)))
  (cases hb (Nat.blt (:so x) o))
  (case [false] (simp only [mv-pres hb mv-setv and_self]))
  (case [true] (simp only [mv-pres hb mv-setv and_self])))

;; after the barrier the stamp is the owner's ordinal (or was already), and versions stay older
(a/theorem mv-pres-row [cs :- (List MCell), ts :- (=> Nat Nat), o :- Nat, x :- MRow, y :- Nat]
  (=> (<= (:so x) o) (= (mv-vlt (:so x) (:vers x)) true)
      (And (<= (:so (mv-setv (mv-pres cs ts o x) y)) o)
           (= (mv-vlt (:so (mv-setv (mv-pres cs ts o x) y)) (:vers (mv-setv (mv-pres cs ts o x) y))) true)))
  (intros hso hv)
  (cases hb (Nat.blt (:so x) o))
  (case [false] (simp only [mv-pres hb mv-setv]) (exact (And.intro hso hv)))
  (case [true]
    (have hb2 := hb) (simp only [Nat.blt_eq] at hb2)
    (have hpv := (mv-vlt-mono (:so x) o _ (mv-vlt-prune cs ts (:so x) (:vers x) hv) hso))
    (cases hk (mv-live-in cs ts (:so x) (- o 1)))
    (case [false] (simp only [mv-pres hb mv-setv hk]) (exact (And.intro (Nat.le_refl o) hpv)))
    (case [true]
      (have hnew (= (mv-vlt o (List.cons MVer (MVer.mk (:so x) (- o 1) (:val x)) (List.nil MVer))) true))
      (simp only [mv-vlt Bool.and_eq_true Nat.blt_eq Bool.and_true]) (omega)
      (simp only [mv-pres hb mv-setv hk])
      (exact (And.intro (Nat.le_refl o) (mv-vlt-app o _ _ hpv hnew))))))

;; ---------------------------------------------------------------------------
;; A write keeps the invariant

(a/theorem mv-write-h-other [s :- MSt, w :- Nat, i :- Nat, y :- Nat, b :- Nat]
  (=> (Not (= b (mv-tgt s w i))) (= ((:h (mv-write s w i y)) b) ((:h s) b)))
  (intro hne)
  (simp only [mv-write (mv-upd-other (:h s) (mv-tgt s w i) _ b hne)]))

(a/theorem mv-write-h-at [s :- MSt, w :- Nat, i :- Nat, y :- Nat]
  (= ((:h (mv-write s w i y)) (mv-tgt s w i))
     (mv-setv (mv-pres (:cells ((:fam s) w)) (:ts s) (:ord ((:fam s) w)) ((:h s) (mv-tgt s w i))) y))
  (simp only [mv-write mv-upd-same]))

(a/theorem mv-write-idow [s :- MSt, w :- Nat, i :- Nat, y :- Nat, b :- Nat]
  (And (= (:id ((:h (mv-write s w i y)) b)) (:id ((:h s) b)))
       (= (:ow ((:h (mv-write s w i y)) b)) (:ow ((:h s) b))))
  (cases hb (Nat.beq b (mv-tgt s w i)))
  (case [false]
    (rw [(mv-write-h-other s w i y b (Nat.ne_of_beq_eq_false hb))])
    (exact (And.intro (Eq.refl _) (Eq.refl _))))
  (case [true]
    (have e := (Nat.eq_of_beq_eq_true hb))
    (rw [e (mv-write-h-at s w i y)])
    (exact (mv-pres-id (:cells ((:fam s) w)) (:ts s) (:ord ((:fam s) w)) ((:h s) (mv-tgt s w i)) y))))

;; the written address: the creator's row of i (owned by w) or w's copy of i
(a/theorem mv-tgt-ok [s :- MSt, w :- Nat, i :- Nat]
  (=> (mv-k-fwd s) (mv-k-home s) (= ((:act s) w) true) (= (((:dom s) w) i) true)
      (Or (= (:ow ((:h s) ((:home s) i))) w) (Not (= (MW.fwd ((:fam s) w) i) 0)))
      (And (< (mv-tgt s w i) (:n s))
           (And (= (:id ((:h s) (mv-tgt s w i))) i) (= (:ow ((:h s) (mv-tgt s w i))) w))))
  (intros hf hh ha hd hpre)
  (simp only [mv-k-fwd] at hf)
  (simp only [mv-k-home] at hh)
  (have qh := (hh w i ha hd))
  (cases ho (Nat.beq (:ow ((:h s) ((:home s) i))) w))
  (case [true]
    (simp only [mv-tgt ho])
    (exact (And.intro (And.left qh) (And.intro (And.right qh) (Nat.eq_of_beq_eq_true ho)))))
  (case [false]
    (have hno := (Nat.ne_of_beq_eq_false ho))
    (have hfw (Not (= (MW.fwd ((:fam s) w) i) 0)))
    (cases hpre) (case [inl h1] (exact (absurd h1 hno))) (case [inr h2] (exact h2))
    (simp only [mv-tgt ho])
    (exact (hf w i hfw))))

;; a fork reading the written row through one of its lineage entries sees what it saw (barrier)
(a/theorem mv-write-vat [s :- MSt, w :- Nat, i :- Nat, y :- Nat, e :- MEnt, b :- Nat]
  (=> (mv-k-row s) (mv-ent-ok s e) (< (mv-tgt s w i) (:n s)) (= (:ow ((:h s) (mv-tgt s w i))) w)
      (= (:ow ((:h s) b)) (:own e))
      (= (mv-vat ((:h (mv-write s w i y)) b) (:f e)) (mv-vat ((:h s) b) (:f e))))
  (intros hr he hn hw hb)
  (cases hba (Nat.beq b (mv-tgt s w i)))
  (case [false] (rw [(mv-write-h-other s w i y b (Nat.ne_of_beq_eq_false hba))]))
  (case [true]
    (have eb := (Nat.eq_of_beq_eq_true hba))
    (rw [eb] at hb)
    (have eo (= (:own e) w)) (rw [(Eq.symm hb)]) (exact hw)
    (simp only [mv-ent-ok] at he)
    (rw [eo] at he)
    (simp only [mv-k-row] at hr)
    (have qr := (hr (mv-tgt s w i) hn))
    (rw [hw] at qr)
    (have hl := (mv-cell-live (:cells ((:fam s) w)) (:ts s) (:f e) (:tok e)
                              (And.left (And.right (And.right he))) (And.left (And.right he))))
    (rw [eb (mv-write-h-at s w i y)])
    (exact (mv-vat-pres (:cells ((:fam s) w)) (:ts s) (:ord ((:fam s) w)) ((:h s) (mv-tgt s w i)) y (:f e)
                        (And.left he) (And.left qr) (And.right qr) hl))))

(a/theorem mv-write-home [s :- MSt, w :- Nat, i :- Nat, y :- Nat] (= (:home (mv-write s w i y)) (:home s)) (rfl))
(a/theorem mv-write-fam [s :- MSt, w :- Nat, i :- Nat, y :- Nat] (= (:fam (mv-write s w i y)) (:fam s)) (rfl))
(a/theorem mv-write-act [s :- MSt, w :- Nat, i :- Nat, y :- Nat] (= (:act (mv-write s w i y)) (:act s)) (rfl))
(a/theorem mv-write-dom [s :- MSt, w :- Nat, i :- Nat, y :- Nat] (= (:dom (mv-write s w i y)) (:dom s)) (rfl))
(a/theorem mv-write-n [s :- MSt, w :- Nat, i :- Nat, y :- Nat] (= (:n (mv-write s w i y)) (:n s)) (rfl))
(a/theorem mv-write-ts [s :- MSt, w :- Nat, i :- Nat, y :- Nat] (= (:ts (mv-write s w i y)) (:ts s)) (rfl))
(a/theorem mv-write-bas [s :- MSt, w :- Nat, i :- Nat, y :- Nat] (= (:bas (mv-write s w i y)) (:bas s)) (rfl))
(a/theorem mv-write-tab [s :- MSt, w :- Nat, i :- Nat, y :- Nat]
  (= (:tab (mv-write s w i y)) (mv-upd (:tab s) w (mv-upd ((:tab s) w) i y))) (rfl))

(a/theorem mv-res-own [h :- (=> Nat MRow), home :- (=> Nat Nat), w :- Nat, W :- MW, i :- Nat]
  (=> (= (:ow (h (home i))) w) (= (mv-res h home w W i) (Option.some Nat (:val (h (home i))))))
  (intro ho) (simp only [mv-res ho Nat.beq_refl]))

(a/theorem mv-res-fwd [h :- (=> Nat MRow), home :- (=> Nat Nat), w :- Nat, W :- MW, i :- Nat]
  (=> (Not (= (:ow (h (home i))) w)) (Not (= (MW.fwd W i) 0))
      (= (mv-res h home w W i) (Option.some Nat (:val (h (MW.fwd W i))))))
  (intros ho hf) (simp only [mv-res (mv-nbeq-ne _ _ ho) (mv-nbeq-ne _ _ hf)]))

;; every read other than (w, i) is unchanged by w's write of i
(a/theorem mv-write-res-frame [s :- MSt, w :- Nat, i :- Nat, y :- Nat, u :- Nat, j :- Nat]
  (=> (mv-inv s) (= ((:act s) w) true) (= (((:dom s) w) i) true)
      (Or (= (:ow ((:h s) ((:home s) i))) w) (Not (= (MW.fwd ((:fam s) w) i) 0)))
      (= ((:act s) u) true) (= (((:dom s) u) j) true) (Not (And (= u w) (= j i)))
      (= (mv-res (:h (mv-write s w i y)) (:home s) u ((:fam s) u) j)
         (mv-res (:h s) (:home s) u ((:fam s) u) j)))
  (intros hinv ha hd hpre hu hdj hne)
  (have hrow := (And.left hinv))
  (have hfwd := (And.left (And.right hinv)))
  (have hlin := (And.left (And.right (And.right hinv))))
  (have hhome := (And.left (And.right (And.right (And.right hinv)))))
  (have ht := (mv-tgt-ok s w i hfwd hhome ha hd hpre))
  (have tn := (And.left ht)) (have tid := (And.left (And.right ht))) (have tow := (And.right (And.right ht)))
  (simp only [mv-k-home] at hhome)
  (have qh := (hhome u j hu hdj))
  (apply mv-res-frame)
  ;; the creator's row: its owner and id are kept
  (exact (And.right (mv-write-idow s w i y ((:home s) j))))
  ;; own read of j
  (intro hou)
  (cases hba (Nat.beq ((:home s) j) (mv-tgt s w i)))
  (case [false] (rw [(mv-write-h-other s w i y _ (Nat.ne_of_beq_eq_false hba))]))
  (case [true]
    (have eb := (Nat.eq_of_beq_eq_true hba))
    (exfalso) (apply hne)
    (have q1 := (And.right qh)) (rw [eb tid] at q1)
    (rw [eb tow] at hou)
    (exact (And.intro (Eq.symm hou) (Eq.symm q1))))
  ;; read through the copy map
  (intro hf0)
  (simp only [mv-k-fwd] at hfwd)
  (have qf := (hfwd u j hf0))
  (cases hba (Nat.beq (MW.fwd ((:fam s) u) j) (mv-tgt s w i)))
  (case [false] (rw [(mv-write-h-other s w i y _ (Nat.ne_of_beq_eq_false hba))]))
  (case [true]
    (have eb := (Nat.eq_of_beq_eq_true hba))
    (exfalso) (apply hne)
    (have q1 := (And.left (And.right qf))) (have q2 := (And.right (And.right qf)))
    (rw [eb tid] at q1) (rw [eb tow] at q2)
    (exact (And.intro (Eq.symm q2) (Eq.symm q1))))
  ;; read through the lineage: the barrier
  (simp only [mv-k-lin] at hlin)
  (apply (mv-allE-mono (mv-ent-ok s) _ _ _ (hlin u hu)))
  (intros e he)
  (simp only [mv-same-at])
  (apply And.intro)
  (intro hm)
  (have qe := he) (simp only [mv-ent-ok] at qe)
  (have qm := ((And.right (And.right (And.right qe))) j hm))
  (exact (mv-write-vat s w i y e (MEnt.mp e j) hrow he tn tow (And.right (And.right qm))))
  (intro hoe)
  (exact (mv-write-vat s w i y e ((:home s) j) hrow he tn tow hoe)))

(a/theorem mv-write-ref [s :- MSt, w :- Nat, i :- Nat, y :- Nat]
  (=> (mv-inv s) (= ((:act s) w) true) (= (((:dom s) w) i) true)
      (Or (= (:ow ((:h s) ((:home s) i))) w) (Not (= (MW.fwd ((:fam s) w) i) 0)))
      (mv-ref (mv-write s w i y)))
  (intros hinv ha hd hpre)
  (have href := (And.right (And.right (And.right (And.right (And.right (And.right hinv)))))))
  (simp only [mv-ref] at href)
  (intros u j hu hdj)
  (rw [mv-write-act] at hu) (rw [mv-write-dom] at hdj)
  (rw [mv-write-home mv-write-fam mv-write-tab])
  (cases huw (Nat.beq u w))
  (case [false]
    (have hne := (Nat.ne_of_beq_eq_false huw))
    (have hn2 (Not (And (= u w) (= j i)))) (intro c) (exact (hne (And.left c)))
    (rw [(mv-write-res-frame s w i y u j hinv ha hd hpre hu hdj hn2) (mv-upd-other (:tab s) w _ u hne)])
    (exact (href u j hu hdj)))
  (case [true]
    (have eu := (Nat.eq_of_beq_eq_true huw))
    (rw [eu] at hu hdj) (rw [eu mv-upd-same])
    (cases hji (Nat.beq j i))
    (case [false]
      (have hne := (Nat.ne_of_beq_eq_false hji))
      (have hn2 (Not (And (= w w) (= j i)))) (intro c) (exact (hne (And.right c)))
      (rw [(mv-write-res-frame s w i y w j hinv ha hd hpre hu hdj hn2) (mv-upd-other ((:tab s) w) i _ j hne)])
      (exact (href w j hu hdj)))
    (case [true]
      ;; the writer reads its new value
      (have ej := (Nat.eq_of_beq_eq_true hji))
      (rw [ej mv-upd-same])
      (have hval (= (:val ((:h (mv-write s w i y)) (mv-tgt s w i))) y))
      (rw [(mv-write-h-at s w i y)])
      (have how := (And.right (mv-write-idow s w i y ((:home s) i))))
      (cases ho (Nat.beq (:ow ((:h s) ((:home s) i))) w))
      (case [true]
        (have eo := (Nat.eq_of_beq_eq_true ho))
        (have et (= (mv-tgt s w i) ((:home s) i))) (simp only [mv-tgt ho])
        (rw [et] at hval)
        (rw [(mv-res-own (:h (mv-write s w i y)) (:home s) w ((:fam s) w) i (Eq.trans how eo)) hval]))
      (case [false]
        (have hno := (Nat.ne_of_beq_eq_false ho))
        (have hfw (Not (= (MW.fwd ((:fam s) w) i) 0)))
        (cases hpre) (case [inl h1] (exact (absurd h1 hno))) (case [inr h2] (exact h2))
        (have et (= (mv-tgt s w i) (MW.fwd ((:fam s) w) i))) (simp only [mv-tgt ho])
        (rw [et] at hval)
        (have hno2 (Not (= (:ow ((:h (mv-write s w i y)) ((:home s) i))) w))) (rw [how]) (exact hno)
        (rw [(mv-res-fwd (:h (mv-write s w i y)) (:home s) w ((:fam s) w) i hno2 hfw) hval])))))

;; ---------------------------------------------------------------------------
;; Heap variants: a state whose heap keeps every row's id and owner keeps the structural parts

(a/defn mv-same-idow [h :- (=> Nat MRow), h2 :- (=> Nat MRow)] Prop
  (forall [b :- Nat] (And (= (:id (h2 b)) (:id (h b))) (= (:ow (h2 b)) (:ow (h b))))))

(a/theorem mv-k-fwd-heap [s :- MSt, s2 :- MSt]
  (=> (= (:n s2) (:n s)) (= (:fam s2) (:fam s)) (mv-same-idow (:h s) (:h s2)) (mv-k-fwd s) (mv-k-fwd s2))
  (intros hn hf hh hk)
  (simp only [mv-k-fwd] at hk)
  (simp only [mv-same-idow] at hh)
  (intros u i hne)
  (rw [hf] at hne)
  (have q := (hk u i hne))
  (rw [hn hf (And.left (hh (MW.fwd ((:fam s) u) i))) (And.right (hh (MW.fwd ((:fam s) u) i)))])
  (exact q))

(a/theorem mv-ent-ok-heap [s :- MSt, s2 :- MSt, e :- MEnt]
  (=> (= (:n s2) (:n s)) (= (:fam s2) (:fam s)) (= (:ts s2) (:ts s)) (mv-same-idow (:h s) (:h s2))
      (mv-ent-ok s e) (mv-ent-ok s2 e))
  (intros hn hf ht hh he)
  (simp only [mv-ent-ok] at he)
  (simp only [mv-same-idow] at hh)
  (simp only [mv-ent-ok])
  (rw [hf ht hn])
  (apply And.intro) (exact (And.left he))
  (apply And.intro) (exact (And.left (And.right he)))
  (apply And.intro) (exact (And.left (And.right (And.right he))))
  (intros i hm)
  (have q := ((And.right (And.right (And.right he))) i hm))
  (rw [(And.left (hh (MEnt.mp e i))) (And.right (hh (MEnt.mp e i)))])
  (exact q))

(a/theorem mv-k-lin-heap [s :- MSt, s2 :- MSt]
  (=> (= (:n s2) (:n s)) (= (:fam s2) (:fam s)) (= (:ts s2) (:ts s)) (= (:act s2) (:act s))
      (mv-same-idow (:h s) (:h s2)) (mv-k-lin s) (mv-k-lin s2))
  (intros hn hf ht ha hh hk)
  (simp only [mv-k-lin] at hk)
  (intros u hu)
  (rw [ha] at hu)
  (rw [hf])
  (exact (mv-allE-mono (mv-ent-ok s) (mv-ent-ok s2) _ (fn [e :- MEnt] (mv-ent-ok-heap s s2 e hn hf ht hh)) (hk u hu))))

(a/theorem mv-k-home-heap [s :- MSt, s2 :- MSt]
  (=> (= (:n s2) (:n s)) (= (:home s2) (:home s)) (= (:act s2) (:act s)) (= (:dom s2) (:dom s))
      (mv-same-idow (:h s) (:h s2)) (mv-k-home s) (mv-k-home s2))
  (intros hn hm ha hd hh hk)
  (simp only [mv-k-home] at hk)
  (simp only [mv-same-idow] at hh)
  (intros u i hu hdi)
  (rw [ha] at hu) (rw [hd] at hdi)
  (rw [hn hm (And.left (hh ((:home s) i)))])
  (exact (hk u i hu hdi)))

(a/theorem mv-k-share-same [s :- MSt, s2 :- MSt]
  (=> (= (:fam s2) (:fam s)) (= (:ts s2) (:ts s)) (= (:act s2) (:act s)) (mv-k-share s) (mv-k-share s2))
  (intros hf ht ha hk)
  (simp only [mv-k-share] at hk)
  (simp only [mv-k-share])
  (rw [hf ht ha])
  (exact hk))

(a/theorem mv-k-bas-heap [s :- MSt, s2 :- MSt]
  (=> (= (:n s2) (:n s)) (= (:fam s2) (:fam s)) (= (:act s2) (:act s)) (= (:bas s2) (:bas s))
      (mv-same-idow (:h s) (:h s2)) (mv-k-bas s) (mv-k-bas s2))
  (intros hn hf ha hb hh hk)
  (simp only [mv-k-bas] at hk)
  (simp only [mv-same-idow] at hh)
  (intros u hu hbu)
  (rw [ha] at hu) (rw [hb] at hbu)
  (have q := (hk u hu hbu))
  (apply And.intro)
  (rw [hf]) (exact (And.left q))
  (intros a hl)
  (rw [hn] at hl)
  (rw [(And.right (hh a))])
  (exact ((And.right q) a hl)))

(a/theorem mv-write-same [s :- MSt, w :- Nat, i :- Nat, y :- Nat]
  (mv-same-idow (:h s) (:h (mv-write s w i y)))
  (simp only [mv-same-idow])
  (intro b)
  (exact (mv-write-idow s w i y b)))

(a/theorem mv-write-k-row [s :- MSt, w :- Nat, i :- Nat, y :- Nat]
  (=> (mv-k-row s) (< (mv-tgt s w i) (:n s)) (= (:ow ((:h s) (mv-tgt s w i))) w) (mv-k-row (mv-write s w i y)))
  (intros hr hn hw)
  (simp only [mv-k-row] at hr)
  (intros a ha)
  (rw [mv-write-n] at ha)
  (rw [mv-write-fam (And.right (mv-write-idow s w i y a))])
  (cases hba (Nat.beq a (mv-tgt s w i)))
  (case [false]
    (rw [(mv-write-h-other s w i y a (Nat.ne_of_beq_eq_false hba))])
    (exact (hr a ha)))
  (case [true]
    (have eb := (Nat.eq_of_beq_eq_true hba))
    (have qr := (hr (mv-tgt s w i) hn))
    (rw [hw] at qr)
    (rw [eb hw (mv-write-h-at s w i y)])
    (exact (mv-pres-row (:cells ((:fam s) w)) (:ts s) (:ord ((:fam s) w)) ((:h s) (mv-tgt s w i)) y
                        (And.left qr) (And.right qr)))))

;; A WRITE (the `rv` barrier, then the change) keeps the invariant
(a/theorem mv-write-inv [s :- MSt, w :- Nat, i :- Nat, y :- Nat]
  (=> (mv-inv s) (= ((:act s) w) true) (= (((:dom s) w) i) true)
      (Or (= (:ow ((:h s) ((:home s) i))) w) (Not (= (MW.fwd ((:fam s) w) i) 0)))
      (mv-inv (mv-write s w i y)))
  (intros hinv ha hd hpre)
  (have ht := (mv-tgt-ok s w i (And.left (And.right hinv)) (And.left (And.right (And.right (And.right hinv)))) ha hd hpre))
  (have hs := (mv-write-same s w i y))
  (apply And.intro)
  (exact (mv-write-k-row s w i y (And.left hinv) (And.left ht) (And.right (And.right ht))))
  (apply And.intro)
  (exact (mv-k-fwd-heap s _ (mv-write-n s w i y) (mv-write-fam s w i y) hs (And.left (And.right hinv))))
  (apply And.intro)
  (exact (mv-k-lin-heap s _ (mv-write-n s w i y) (mv-write-fam s w i y) (mv-write-ts s w i y) (mv-write-act s w i y)
                        hs (And.left (And.right (And.right hinv)))))
  (apply And.intro)
  (exact (mv-k-home-heap s _ (mv-write-n s w i y) (mv-write-home s w i y) (mv-write-act s w i y) (mv-write-dom s w i y)
                         hs (And.left (And.right (And.right (And.right hinv))))))
  (apply And.intro)
  (exact (mv-k-share-same s _ (mv-write-fam s w i y) (mv-write-ts s w i y) (mv-write-act s w i y)
                          (And.left (And.right (And.right (And.right (And.right hinv)))))))
  (apply And.intro)
  (exact (mv-k-bas-heap s _ (mv-write-n s w i y) (mv-write-fam s w i y) (mv-write-act s w i y) (mv-write-bas s w i y)
                        hs (And.left (And.right (And.right (And.right (And.right (And.right hinv))))))))
  (exact (mv-write-ref s w i y hinv ha hd hpre)))

;; ---------------------------------------------------------------------------
;; Pruning keeps the invariant (reclamation is safe)

;; RECLAMATION, safety form: after pruning, every version left on a row is covered by a live
;; fork of the row's owner
(a/defn mv-covered [cs :- (List MCell), ts :- (=> Nat Nat), vs :- (List MVer)] Bool
  (match vs [nil true] [(cons v t) (Bool.and (mv-live-in cs ts (:k v) (:m v)) (mv-covered cs ts t))]))

(a/theorem mv-prune-covered [cs :- (List MCell), ts :- (=> Nat Nat), vs :- (List MVer)]
  (= (mv-covered cs ts (mv-prune-vs cs ts vs)) true)
  (induction vs)
  (case [nil] (simp only [mv-prune-vs mv-covered]))
  (case [cons v t ih]
    (cases hk (mv-live-in cs ts (:k v) (:m v)))
    (case [false] (simp only [mv-prune-vs hk]) (exact ih))
    (case [true] (simp only [mv-prune-vs hk mv-covered Bool.true_and]) (exact ih))))

(a/defn mv-pruned [s :- MSt, a :- Nat] MRow
  (MRow.mk (:id ((:h s) a)) (:ow ((:h s) a)) (:so ((:h s) a)) (:val ((:h s) a))
           (mv-prune-vs (:cells ((:fam s) (:ow ((:h s) a)))) (:ts s) (:vers ((:h s) a)))))

(a/theorem mv-prune-h [s :- MSt, a :- Nat, b :- Nat]
  (= ((:h (mv-prune s a)) b) (if (Nat.beq b a) (mv-pruned s a) ((:h s) b)))
  (rfl))

(a/theorem mv-prune-fields [s :- MSt, a :- Nat, b :- Nat]
  (And (= (:id ((:h (mv-prune s a)) b)) (:id ((:h s) b)))
       (And (= (:ow ((:h (mv-prune s a)) b)) (:ow ((:h s) b)))
            (And (= (:so ((:h (mv-prune s a)) b)) (:so ((:h s) b)))
                 (= (:val ((:h (mv-prune s a)) b)) (:val ((:h s) b))))))
  (rw [mv-prune-h])
  (cases hb (Nat.beq b a))
  (case [false] (simp only [and_self]))
  (case [true]
    (have e := (Nat.eq_of_beq_eq_true hb)) (rw [e])
    (simp only [mv-pruned and_self])))

;; a live fork of the owner reads the same version after pruning
(a/theorem mv-prune-vat [s :- MSt, a :- Nat, e :- MEnt, b :- Nat]
  (=> (mv-ent-ok s e) (= (:ow ((:h s) b)) (:own e))
      (= (mv-vat ((:h (mv-prune s a)) b) (:f e)) (mv-vat ((:h s) b) (:f e))))
  (intros he hb)
  (rw [mv-prune-h])
  (cases hba (Nat.beq b a))
  (case [false] (rfl))
  (case [true]
    (have eb := (Nat.eq_of_beq_eq_true hba))
    (rw [eb] at hb) (rw [eb])
    (simp only [mv-ent-ok] at he)
    (rw [(Eq.symm hb)] at he)
    (have hl := (mv-cell-live _ (:ts s) (:f e) (:tok e) (And.left (And.right (And.right he))) (And.left (And.right he))))
    (cases hsf (Nat.ble (:so ((:h s) a)) (:f e)))
    (case [true] (simp only [mv-pruned mv-vat hsf]))
    (case [false]
      (simp only [mv-pruned mv-vat hsf])
      (exact (mv-look-prune _ (:ts s) (:f e) _ hl)))))

(a/theorem mv-prune-proj [s :- MSt, a :- Nat]
  (And (= (:n (mv-prune s a)) (:n s))
       (And (= (:home (mv-prune s a)) (:home s))
            (And (= (:fam (mv-prune s a)) (:fam s))
                 (And (= (:act (mv-prune s a)) (:act s))
                      (And (= (:bas (mv-prune s a)) (:bas s))
                           (And (= (:ts (mv-prune s a)) (:ts s))
                                (And (= (:dom (mv-prune s a)) (:dom s)) (= (:tab (mv-prune s a)) (:tab s)))))))))
  (simp only [mv-prune and_self]))

(a/theorem mv-prune-ref [s :- MSt, a :- Nat]
  (=> (mv-inv s) (mv-ref (mv-prune s a)))
  (intro hinv)
  (have hlin := (And.left (And.right (And.right hinv))))
  (have href := (And.right (And.right (And.right (And.right (And.right (And.right hinv)))))))
  (have pp := (mv-prune-proj s a))
  (simp only [mv-ref] at href)
  (simp only [mv-k-lin] at hlin)
  (intros u j hu hdj)
  (rw [(And.left (And.right (And.right (And.right pp))))] at hu)
  (rw [(And.left (And.right (And.right (And.right (And.right (And.right (And.right pp)))))))] at hdj)
  (rw [(And.left (And.right pp)) (And.left (And.right (And.right pp)))
       (And.right (And.right (And.right (And.right (And.right (And.right (And.right pp)))))))])
  (rw [(Eq.symm (href u j hu hdj))])
  (apply mv-res-frame)
  (exact (And.left (And.right (mv-prune-fields s a ((:home s) j)))))
  (intro hx) (exact (And.right (And.right (And.right (mv-prune-fields s a ((:home s) j))))))
  (intro hx) (exact (And.right (And.right (And.right (mv-prune-fields s a (MW.fwd ((:fam s) u) j))))))
  (apply (mv-allE-mono (mv-ent-ok s) _ _ _ (hlin u hu)))
  (intros e he)
  (simp only [mv-same-at])
  (apply And.intro)
  (intro hm)
  (have qe := he) (simp only [mv-ent-ok] at qe)
  (exact (mv-prune-vat s a e (MEnt.mp e j) he (And.right (And.right ((And.right (And.right (And.right qe))) j hm)))))
  (intro hoe)
  (exact (mv-prune-vat s a e ((:home s) j) he hoe)))

(a/theorem mv-prune-same [s :- MSt, a :- Nat] (mv-same-idow (:h s) (:h (mv-prune s a)))
  (simp only [mv-same-idow])
  (intro b)
  (exact (And.intro (And.left (mv-prune-fields s a b)) (And.left (And.right (mv-prune-fields s a b))))))

(a/theorem mv-prune-k-row [s :- MSt, a :- Nat]
  (=> (mv-k-row s) (mv-k-row (mv-prune s a)))
  (intro hr)
  (simp only [mv-k-row] at hr)
  (have pp := (mv-prune-proj s a))
  (intros b hb)
  (rw [(And.left pp)] at hb)
  (have pf := (mv-prune-fields s a b))
  (rw [(And.left (And.right (And.right pp))) (And.left (And.right pf)) (And.left (And.right (And.right pf)))])
  (have q := (hr b hb))
  (apply And.intro) (exact (And.left q))
  (rw [mv-prune-h])
  (cases hba (Nat.beq b a))
  (case [false] (exact (And.right q)))
  (case [true]
    (have eb := (Nat.eq_of_beq_eq_true hba))
    (rw [eb] at q) (rw [eb])
    (simp only [mv-pruned])
    (exact (mv-vlt-prune _ (:ts s) _ _ (And.right q)))))

;; PRUNING (`prune-cell!`, the sweep, the prune inside `preserve!`) keeps the invariant
(a/theorem mv-prune-inv [s :- MSt, a :- Nat]
  (=> (mv-inv s) (mv-inv (mv-prune s a)))
  (intro hinv)
  (have pp := (mv-prune-proj s a))
  (have hs := (mv-prune-same s a))
  (have pn := (And.left pp))
  (have pm := (And.left (And.right pp)))
  (have pf := (And.left (And.right (And.right pp))))
  (have pa := (And.left (And.right (And.right (And.right pp)))))
  (have pb := (And.left (And.right (And.right (And.right (And.right pp))))))
  (have pt := (And.left (And.right (And.right (And.right (And.right (And.right pp)))))))
  (have pd := (And.left (And.right (And.right (And.right (And.right (And.right (And.right pp))))))))
  (apply And.intro) (exact (mv-prune-k-row s a (And.left hinv)))
  (apply And.intro) (exact (mv-k-fwd-heap s _ pn pf hs (And.left (And.right hinv))))
  (apply And.intro) (exact (mv-k-lin-heap s _ pn pf pt pa hs (And.left (And.right (And.right hinv)))))
  (apply And.intro) (exact (mv-k-home-heap s _ pn pm pa pd hs (And.left (And.right (And.right (And.right hinv))))))
  (apply And.intro) (exact (mv-k-share-same s _ pf pt pa (And.left (And.right (And.right (And.right (And.right hinv)))))))
  (apply And.intro) (exact (mv-k-bas-heap s _ pn pf pa pb hs (And.left (And.right (And.right (And.right (And.right (And.right hinv))))))))
  (exact (mv-prune-ref s a hinv)))

;; ---------------------------------------------------------------------------
;; Transport across growth (new rows above n, ordinals and token cells growing)

(a/theorem mv-ent-ok-ext [s :- MSt, s2 :- MSt, e :- MEnt]
  (=> (<= (:n s) (:n s2)) (forall [b :- Nat] (=> (< b (:n s)) (= ((:h s2) b) ((:h s) b))))
      (<= (:ord ((:fam s) (:own e))) (:ord ((:fam s2) (:own e))))
      (=> (= (mv-has-cell (:cells ((:fam s) (:own e))) (:f e) (:tok e)) true)
          (= (mv-has-cell (:cells ((:fam s2) (:own e))) (:f e) (:tok e)) true))
      (Not (= ((:ts s2) (:tok e)) 2))
      (mv-ent-ok s e) (mv-ent-ok s2 e))
  (intros hn hh ho hc ht he)
  (simp only [mv-ent-ok] at he)
  (simp only [mv-ent-ok])
  (apply And.intro) (have q := (And.left he)) (omega)
  (apply And.intro) (exact ht)
  (apply And.intro) (exact (hc (And.left (And.right (And.right he)))))
  (intros i hm)
  (have q := ((And.right (And.right (And.right he))) i hm))
  (have ql := (And.left q))
  (rw [(hh (MEnt.mp e i) ql)])
  (apply And.intro) (omega)
  (exact (And.right q)))

(a/theorem mv-has-cell-app [cs :- (List MCell), c :- MCell, o :- Nat, t :- Nat]
  (=> (= (mv-has-cell cs o t) true)
      (= (mv-has-cell (List.append cs (List.cons MCell c (List.nil MCell))) o t) true))
  (intro hc)
  (induction cs)
  (case [nil] (simp only [mv-has-cell] at hc) (cases hc))
  (case [cons d r ih]
    (simp only [mv-has-cell Bool.or_eq_true] at hc)
    (simp only [List.append mv-has-cell Bool.or_eq_true])
    (cases hc)
    (case [inl h1] (left) (exact h1))
    (case [inr h2] (right) (exact (ih h2)))))

;; resolution reads only rows below n (they are unchanged) and id i's entries of the copy map
;; and lineage (unchanged)
(a/theorem mv-res-ext [s :- MSt, h2 :- (=> Nat MRow), home2 :- (=> Nat Nat), u :- Nat, W2 :- MW, j :- Nat]
  (=> (mv-k-fwd s) (mv-allE (mv-ent-ok s) (:lin ((:fam s) u)))
      (< ((:home s) j) (:n s))
      (forall [b :- Nat] (=> (< b (:n s)) (= (h2 b) ((:h s) b))))
      (= (home2 j) ((:home s) j)) (= (MW.fwd W2 j) (MW.fwd ((:fam s) u) j)) (= (:lin W2) (:lin ((:fam s) u)))
      (= (mv-res h2 home2 u W2 j) (mv-res (:h s) (:home s) u ((:fam s) u) j)))
  (intros hf hl hhm hh hm hfw hln)
  (have e1 (= (mv-res h2 home2 u W2 j) (mv-res h2 (:home s) u ((:fam s) u) j)))
  (simp only [mv-res hm hfw hln])
  (rw [e1])
  (apply mv-res-frame)
  (rw [(hh _ hhm)])
  (intro hx) (rw [(hh _ hhm)])
  (intro hx)
  (simp only [mv-k-fwd] at hf)
  (rw [(hh _ (And.left (hf u j hx)))])
  (apply (mv-allE-mono (mv-ent-ok s) _ _ _ hl))
  (intros e he)
  (simp only [mv-same-at])
  (apply And.intro)
  (intro hmp)
  (simp only [mv-ent-ok] at he)
  (rw [(hh _ (And.left ((And.right (And.right (And.right he))) j hmp)))])
  (intro hoe)
  (rw [(hh _ hhm)]))

;; ---------------------------------------------------------------------------
;; Copy on access (`own-copy!`) keeps the invariant

(a/theorem mv-copy-h-old [s :- MSt, w :- Nat, i :- Nat, v :- Nat, b :- Nat]
  (=> (< b (:n s)) (= ((:h (mv-copy s w i v)) b) ((:h s) b)))
  (intro hb)
  (have hne (Not (= b (:n s)))) (omega)
  (simp only [mv-copy (mv-upd-other (:h s) (:n s) _ b hne)]))

(a/theorem mv-copy-h-new [s :- MSt, w :- Nat, i :- Nat, v :- Nat]
  (= ((:h (mv-copy s w i v)) (:n s)) (MRow.mk i w (:ord ((:fam s) w)) v (List.nil MVer)))
  (simp only [mv-copy mv-upd-same]))

(a/theorem mv-copy-fam [s :- MSt, w :- Nat, i :- Nat, v :- Nat, x :- Nat]
  (And (= (:ord ((:fam (mv-copy s w i v)) x)) (:ord ((:fam s) x)))
       (And (= (:lin ((:fam (mv-copy s w i v)) x)) (:lin ((:fam s) x)))
            (= (:cells ((:fam (mv-copy s w i v)) x)) (:cells ((:fam s) x)))))
  (cases hx (Nat.beq x w))
  (case [false] (simp only [mv-copy (mv-upd-other (:fam s) w _ x (Nat.ne_of_beq_eq_false hx)) and_self]))
  (case [true]
    (have e := (Nat.eq_of_beq_eq_true hx)) (rw [e])
    (simp only [mv-copy mv-upd-same and_self])))

(a/theorem mv-copy-fwd [s :- MSt, w :- Nat, i :- Nat, v :- Nat, x :- Nat, j :- Nat]
  (=> (Not (And (= x w) (= j i))) (= (MW.fwd ((:fam (mv-copy s w i v)) x) j) (MW.fwd ((:fam s) x) j)))
  (intro hne)
  (cases hx (Nat.beq x w))
  (case [false] (simp only [mv-copy (mv-upd-other (:fam s) w _ x (Nat.ne_of_beq_eq_false hx))]))
  (case [true]
    (have e := (Nat.eq_of_beq_eq_true hx))
    (have hj (Not (= j i))) (intro ej) (exact (hne (And.intro e ej)))
    (rw [e])
    (simp only [mv-copy mv-upd-same (mv-upd-other (MW.fwd ((:fam s) w)) i _ j hj)])))

(a/theorem mv-copy-fwd-at [s :- MSt, w :- Nat, i :- Nat, v :- Nat]
  (= (MW.fwd ((:fam (mv-copy s w i v)) w) i) (:n s))
  (simp only [mv-copy mv-upd-same]))

(a/theorem mv-copy-proj [s :- MSt, w :- Nat, i :- Nat, v :- Nat]
  (And (= (:n (mv-copy s w i v)) (+ (:n s) 1))
       (And (= (:home (mv-copy s w i v)) (:home s))
            (And (= (:act (mv-copy s w i v)) (:act s))
                 (And (= (:bas (mv-copy s w i v)) (:bas s))
                      (And (= (:ts (mv-copy s w i v)) (:ts s))
                           (And (= (:dom (mv-copy s w i v)) (:dom s)) (= (:tab (mv-copy s w i v)) (:tab s))))))))
  (simp only [mv-copy and_self]))

;; sharing depends on lineages, token states and the active set only
(a/theorem mv-k-share-lin [s :- MSt, s2 :- MSt]
  (=> (forall [x :- Nat] (= (:lin ((:fam s2) x)) (:lin ((:fam s) x)))) (= (:ts s2) (:ts s)) (= (:act s2) (:act s))
      (mv-k-share s) (mv-k-share s2))
  (intros hl ht ha hk)
  (simp only [mv-k-share] at hk)
  (simp only [mv-k-share])
  (rw [ht ha])
  (apply And.intro)
  (intros u hu) (rw [(hl u)]) (exact ((And.left hk) u hu))
  (intros u x t hu hx hne h1 h2)
  (rw [(hl u)] at h1) (rw [(hl x)] at h2)
  (exact ((And.right hk) u x t hu hx hne h1 h2)))

;; COPY ON ACCESS: w copies the version v it reads of an inherited id i
(a/theorem mv-copy-inv [s :- MSt, w :- Nat, i :- Nat, v :- Nat]
  (=> (mv-inv s) (< 0 (:n s)) (= ((:act s) w) true) (= (((:dom s) w) i) true) (= ((:bas s) w) false)
      (Not (= (:ow ((:h s) ((:home s) i))) w)) (= (MW.fwd ((:fam s) w) i) 0)
      (= (mv-res (:h s) (:home s) w ((:fam s) w) i) (Option.some Nat v))
      (mv-inv (mv-copy s w i v)))
  (intros hinv hpos ha hd hb hno hf0 hv)
  (have hrow := (And.left hinv))
  (have hfwd := (And.left (And.right hinv)))
  (have hlin := (And.left (And.right (And.right hinv))))
  (have hhome := (And.left (And.right (And.right (And.right hinv)))))
  (have hshare := (And.left (And.right (And.right (And.right (And.right hinv))))))
  (have hbas := (And.left (And.right (And.right (And.right (And.right (And.right hinv)))))))
  (have href := (And.right (And.right (And.right (And.right (And.right (And.right hinv)))))))
  (have pp := (mv-copy-proj s w i v))
  (have pn := (And.left pp))
  (have pm := (And.left (And.right pp)))
  (have pa := (And.left (And.right (And.right pp))))
  (have pb := (And.left (And.right (And.right (And.right pp)))))
  (have pt := (And.left (And.right (And.right (And.right (And.right pp))))))
  (have pd := (And.left (And.right (And.right (And.right (And.right (And.right pp)))))))
  (have pta := (And.right (And.right (And.right (And.right (And.right (And.right pp)))))))
  (have hold := (fn [b :- Nat] (mv-copy-h-old s w i v b)))
  (simp only [mv-k-home] at hhome)
  (have qhi := (hhome w i ha hd))
  (apply And.intro)
  ;; rows
  (simp only [mv-k-row] at hrow)
  (intros b hbn)
  (rw [pn] at hbn)
  (cases hbb (Nat.blt b (:n s)))
  (case [true]
    (have hl := hbb) (simp only [Nat.blt_eq] at hl)
    (rw [(hold b hl) (And.left (mv-copy-fam s w i v (:ow ((:h s) b))))])
    (exact (hrow b hl)))
  (case [false]
    (have hl := (mv-blt-f b (:n s) hbb))
    (have eb (= b (:n s))) (omega)
    (rw [eb (mv-copy-h-new s w i v)])
    (apply And.intro)
    (show (<= (:ord ((:fam s) w)) (:ord ((:fam (mv-copy s w i v)) w))))
    (rw [(And.left (mv-copy-fam s w i v w))]) (exact (Nat.le_refl _))
    (simp only [mv-vlt]))
  (apply And.intro)
  ;; copy maps
  (simp only [mv-k-fwd] at hfwd)
  (intros u j hne)
  (rw [pn])
  (cases huj (Bool.and (Nat.beq u w) (Nat.beq j i)))
  (case [true]
    (have q := huj) (simp only [Bool.and_eq_true Nat.beq_eq] at q)
    (rw [(And.left q) (And.right q) (mv-copy-fwd-at s w i v) (mv-copy-h-new s w i v)])
    (apply And.intro) (omega)
    (exact (And.intro (Eq.refl _) (Eq.refl _))))
  (case [false]
    (have hn2 (Not (And (= u w) (= j i))))
    (intro c) (rw [(And.left c) (And.right c) Nat.beq_refl Nat.beq_refl] at huj) (cases huj)
    (rw [(mv-copy-fwd s w i v u j hn2)] at hne)
    (rw [(mv-copy-fwd s w i v u j hn2)])
    (have q := (hfwd u j hne))
    (rw [(hold _ (And.left q))])
    (apply And.intro) (have q1 := (And.left q)) (omega)
    (exact (And.right q)))
  (apply And.intro)
  ;; lineages
  (simp only [mv-k-lin] at hlin)
  (intros u hu)
  (rw [pa] at hu)
  (rw [(And.left (And.right (mv-copy-fam s w i v u)))])
  (apply (mv-allE-mono (mv-ent-ok s) _ _ _ (hlin u hu)))
  (intros e he)
  (have hn1 (<= (:n s) (:n (mv-copy s w i v)))) (rw [pn]) (omega)
  (apply (mv-ent-ok-ext s _ e hn1 hold))
  (rw [(And.left (mv-copy-fam s w i v (:own e)))]) (exact (Nat.le_refl _))
  (intro hc) (rw [(And.right (And.right (mv-copy-fam s w i v (:own e))))]) (exact hc)
  (rw [pt]) (simp only [mv-ent-ok] at he) (exact (And.left (And.right he)))
  (exact he)
  (apply And.intro)
  ;; creators' rows
  (intros u j hu hdj)
  (rw [pa] at hu) (rw [pd] at hdj)
  (have q := (hhome u j hu hdj))
  (rw [pn pm (hold _ (And.left q))])
  (apply And.intro) (have q1 := (And.left q)) (omega)
  (exact (And.right q))
  (apply And.intro)
  ;; sharing
  (exact (mv-k-share-lin s _ (fn [x :- Nat] (And.left (And.right (mv-copy-fam s w i v x)))) pt pa hshare))
  (apply And.intro)
  ;; bases
  (simp only [mv-k-bas] at hbas)
  (intros u hu hbu)
  (rw [pa] at hu) (rw [pb] at hbu)
  (have q := (hbas u hu hbu))
  (have huw (Not (= u w))) (intro e) (rw [e hb] at hbu) (cases hbu)
  (apply And.intro)
  (intro j) (rw [(mv-copy-fwd s w i v u j (fn [c :- (And (= u w) (= j i))] (huw (And.left c))))]) (exact ((And.left q) j))
  (intros b hbn)
  (rw [pn] at hbn)
  (cases hbb (Nat.blt b (:n s)))
  (case [true]
    (have hl := hbb) (simp only [Nat.blt_eq] at hl)
    (rw [(hold b hl)]) (exact ((And.right q) b hl)))
  (case [false]
    (have hl := (mv-blt-f b (:n s) hbb))
    (have eb (= b (:n s))) (omega)
    (rw [eb (mv-copy-h-new s w i v)])
    (intro e) (exact (huw (Eq.symm e))))
  ;; refinement
  (simp only [mv-ref] at href)
  (intros u j hu hdj)
  (rw [pa] at hu) (rw [pd] at hdj)
  (rw [pta pm])
  (cases huj (Bool.and (Nat.beq u w) (Nat.beq j i)))
  (case [true]
    (have q := huj) (simp only [Bool.and_eq_true Nat.beq_eq] at q)
    (rw [(And.left q) (And.right q)])
    (have hno2 (Not (= (:ow ((:h (mv-copy s w i v)) ((:home s) i))) w)))
    (rw [(hold _ (And.left qhi))]) (exact hno)
    (have hf2 (Not (= (MW.fwd ((:fam (mv-copy s w i v)) w) i) 0)))
    (rw [(mv-copy-fwd-at s w i v)]) (omega)
    (rw [(mv-res-fwd _ _ w _ i hno2 hf2) (mv-copy-fwd-at s w i v) (mv-copy-h-new s w i v)])
    (have hr := (href w i ha hd))
    (rw [hv] at hr)
    (rw [hr]))
  (case [false]
    (have hn2 (Not (And (= u w) (= j i))))
    (intro c) (rw [(And.left c) (And.right c) Nat.beq_refl Nat.beq_refl] at huj) (cases huj)
    (rw [(mv-res-ext s _ _ u _ j hfwd (hlin u hu) (And.left (hhome u j hu hdj)) hold (Eq.refl _)
                     (mv-copy-fwd s w i v u j hn2) (And.left (And.right (mv-copy-fam s w i v u))))])
    (exact (href u j hu hdj))))

;; ---------------------------------------------------------------------------
;; Creation keeps the invariant

(a/theorem mv-create-h-old [s :- MSt, w :- Nat, i :- Nat, y :- Nat, b :- Nat]
  (=> (< b (:n s)) (= ((:h (mv-create s w i y)) b) ((:h s) b)))
  (intro hb)
  (have hne (Not (= b (:n s)))) (omega)
  (simp only [mv-create (mv-upd-other (:h s) (:n s) _ b hne)]))

(a/theorem mv-create-h-new [s :- MSt, w :- Nat, i :- Nat, y :- Nat]
  (= ((:h (mv-create s w i y)) (:n s)) (MRow.mk i w (:ord ((:fam s) w)) y (List.nil MVer)))
  (simp only [mv-create mv-upd-same]))

(a/theorem mv-create-proj [s :- MSt, w :- Nat, i :- Nat, y :- Nat]
  (And (= (:n (mv-create s w i y)) (+ (:n s) 1))
       (And (= (:fam (mv-create s w i y)) (:fam s))
            (And (= (:act (mv-create s w i y)) (:act s))
                 (And (= (:bas (mv-create s w i y)) (:bas s)) (= (:ts (mv-create s w i y)) (:ts s))))))
  (simp only [mv-create and_self]))

;; an id other than the new one keeps its creator's row, domain and table entry
(a/theorem mv-create-other [s :- MSt, w :- Nat, i :- Nat, y :- Nat, u :- Nat, j :- Nat]
  (=> (Not (= j i))
      (And (= ((:home (mv-create s w i y)) j) ((:home s) j))
           (And (= (((:dom (mv-create s w i y)) u) j) (((:dom s) u) j))
                (= (((:tab (mv-create s w i y)) u) j) (((:tab s) u) j)))))
  (intro hj)
  (cases hu (Nat.beq u w))
  (case [false]
    (have hne := (Nat.ne_of_beq_eq_false hu))
    (simp only [mv-create (mv-upd-other (:home s) i _ j hj) (mv-upd-other (:dom s) w _ u hne)
                (mv-upd-other (:tab s) w _ u hne) and_self]))
  (case [true]
    (have e := (Nat.eq_of_beq_eq_true hu)) (rw [e])
    (simp only [mv-create (mv-upd-other (:home s) i _ j hj) mv-upd-same
                (mv-upd-other ((:dom s) w) i _ j hj) (mv-upd-other ((:tab s) w) i _ j hj) and_self])))

;; a read in the new state of (u, j) is one of the old domain unless it is the new row
(a/theorem mv-create-dom [s :- MSt, w :- Nat, i :- Nat, y :- Nat, u :- Nat, j :- Nat]
  (=> (forall [x :- Nat] (=> (= ((:act s) x) true) (= (((:dom s) x) i) false)))
      (= ((:act s) u) true) (= (((:dom (mv-create s w i y)) u) j) true)
      (Or (And (= u w) (= j i)) (And (Not (= j i)) (= (((:dom s) u) j) true))))
  (intros hfr hu hd)
  (cases hj (Nat.beq j i))
  (case [false]
    (have hne := (Nat.ne_of_beq_eq_false hj))
    (right)
    (rw [(And.left (And.right (mv-create-other s w i y u j hne)))] at hd)
    (exact (And.intro hne hd)))
  (case [true]
    (have ej := (Nat.eq_of_beq_eq_true hj))
    (left)
    (apply And.intro)
    (cases hu2 (Nat.beq u w))
    (case [true] (exact (Nat.eq_of_beq_eq_true hu2)))
    (case [false]
      (have hne := (Nat.ne_of_beq_eq_false hu2))
      (rw [ej] at hd)
      (simp only [mv-create (mv-upd-other (:dom s) w _ u hne)] at hd)
      (rw [(hfr u hu)] at hd) (cases hd))
    (exact ej)))

;; CREATION: w creates the row of a fresh id i (no active world has i yet)
(a/theorem mv-create-inv [s :- MSt, w :- Nat, i :- Nat, y :- Nat]
  (=> (mv-inv s) (= ((:act s) w) true) (= ((:bas s) w) false)
      (forall [x :- Nat] (=> (= ((:act s) x) true) (= (((:dom s) x) i) false)))
      (mv-inv (mv-create s w i y)))
  (intros hinv ha hb hfr)
  (have hrow := (And.left hinv))
  (have hfwd := (And.left (And.right hinv)))
  (have hlin := (And.left (And.right (And.right hinv))))
  (have hhome := (And.left (And.right (And.right (And.right hinv)))))
  (have hshare := (And.left (And.right (And.right (And.right (And.right hinv))))))
  (have hbas := (And.left (And.right (And.right (And.right (And.right (And.right hinv)))))))
  (have href := (And.right (And.right (And.right (And.right (And.right (And.right hinv)))))))
  (have pp := (mv-create-proj s w i y))
  (have pn := (And.left pp))
  (have pf := (And.left (And.right pp)))
  (have pa := (And.left (And.right (And.right pp))))
  (have pb := (And.left (And.right (And.right (And.right pp)))))
  (have pt := (And.right (And.right (And.right (And.right pp)))))
  (have hold := (fn [b :- Nat] (mv-create-h-old s w i y b)))
  (simp only [mv-k-home] at hhome)
  (apply And.intro)
  ;; rows
  (simp only [mv-k-row] at hrow)
  (intros b hbn)
  (rw [pn] at hbn) (rw [pf])
  (cases hbb (Nat.blt b (:n s)))
  (case [true]
    (have hl := hbb) (simp only [Nat.blt_eq] at hl)
    (rw [(hold b hl)]) (exact (hrow b hl)))
  (case [false]
    (have hl := (mv-blt-f b (:n s) hbb))
    (have eb (= b (:n s))) (omega)
    (rw [eb (mv-create-h-new s w i y)])
    (apply And.intro)
    (show (<= (:ord ((:fam s) w)) (:ord ((:fam s) w)))) (exact (Nat.le_refl _))
    (simp only [mv-vlt]))
  (apply And.intro)
  ;; copy maps
  (simp only [mv-k-fwd] at hfwd)
  (intros u j hne)
  (rw [pf] at hne) (rw [pf pn])
  (have q := (hfwd u j hne))
  (rw [(hold _ (And.left q))])
  (apply And.intro) (have q1 := (And.left q)) (omega)
  (exact (And.right q))
  (apply And.intro)
  ;; lineages
  (simp only [mv-k-lin] at hlin)
  (intros u hu)
  (rw [pa] at hu) (rw [pf])
  (apply (mv-allE-mono (mv-ent-ok s) _ _ _ (hlin u hu)))
  (intros e he)
  (have hn1 (<= (:n s) (:n (mv-create s w i y)))) (rw [pn]) (omega)
  (apply (mv-ent-ok-ext s _ e hn1 hold))
  (rw [pf]) (exact (Nat.le_refl _))
  (intro hc) (rw [pf]) (exact hc)
  (rw [pt]) (simp only [mv-ent-ok] at he) (exact (And.left (And.right he)))
  (exact he)
  (apply And.intro)
  ;; creators' rows
  (intros u j hu hdj)
  (rw [pa] at hu)
  (rw [pn])
  (have cdm := (mv-create-dom s w i y u j hfr hu hdj)) (cases cdm)
  (case [inl c]
    (rw [(And.right c)])
    (have hm (= ((:home (mv-create s w i y)) i) (:n s))) (simp only [mv-create mv-upd-same])
    (rw [hm (mv-create-h-new s w i y)])
    (apply And.intro) (omega) (rfl))
  (case [inr c]
    (have q := (hhome u j hu (And.right c)))
    (rw [(And.left (mv-create-other s w i y u j (And.left c))) (hold _ (And.left q))])
    (apply And.intro) (have q1 := (And.left q)) (omega)
    (exact (And.right q)))
  (apply And.intro)
  ;; sharing
  (exact (mv-k-share-same s _ pf pt pa hshare))
  (apply And.intro)
  ;; bases
  (simp only [mv-k-bas] at hbas)
  (intros u hu hbu)
  (rw [pa] at hu) (rw [pb] at hbu) (rw [pf pn])
  (have q := (hbas u hu hbu))
  (apply And.intro) (exact (And.left q))
  (intros b hbn)
  (cases hbb (Nat.blt b (:n s)))
  (case [true]
    (have hl := hbb) (simp only [Nat.blt_eq] at hl)
    (rw [(hold b hl)]) (exact ((And.right q) b hl)))
  (case [false]
    (have hl := (mv-blt-f b (:n s) hbb))
    (have eb (= b (:n s))) (omega)
    (rw [eb (mv-create-h-new s w i y)])
    (intro e) (rw [(Eq.symm e) hb] at hbu) (cases hbu))
  ;; refinement
  (simp only [mv-ref] at href)
  (intros u j hu hdj)
  (rw [pa] at hu)
  (have cdm := (mv-create-dom s w i y u j hfr hu hdj)) (cases cdm)
  (case [inl c]
    (rw [(And.left c) (And.right c) pf])
    (have hm (= ((:home (mv-create s w i y)) i) (:n s))) (simp only [mv-create mv-upd-same])
    (have ho (= (:ow ((:h (mv-create s w i y)) ((:home (mv-create s w i y)) i))) w))
    (rw [hm (mv-create-h-new s w i y)])
    (rw [(mv-res-own _ _ w _ i ho) hm (mv-create-h-new s w i y)])
    (simp only [mv-create mv-upd-same]))
  (case [inr c]
    (have co := (mv-create-other s w i y u j (And.left c)))
    (rw [(And.right (And.right co)) pf])
    (rw [(mv-res-ext s _ _ u _ j hfwd (hlin u hu) (And.left (hhome u j hu (And.right c))) hold
                     (And.left co) (Eq.refl _) (Eq.refl _))])
    (exact (href u j hu (And.right c)))))

;; ---------------------------------------------------------------------------
;; A world copies only rows it does not own (a fork reads a parent's copy map before its rows)

(a/defn mv-k-ownfwd [s :- MSt] Prop
  (forall [u :- Nat, j :- Nat] (=> (= ((:act s) u) true) (= (((:dom s) u) j) true) (Not (= (MW.fwd ((:fam s) u) j) 0))
    (Not (= (:ow ((:h s) ((:home s) j))) u)))))

(a/theorem mv-ownfwd-write [s :- MSt, w :- Nat, i :- Nat, y :- Nat]
  (=> (mv-k-ownfwd s) (mv-k-ownfwd (mv-write s w i y)))
  (intro hk)
  (simp only [mv-k-ownfwd] at hk)
  (intros u j hu hd hf)
  (rw [mv-write-act] at hu) (rw [mv-write-dom] at hd) (rw [mv-write-fam] at hf)
  (rw [mv-write-home (And.right (mv-write-idow s w i y ((:home s) j)))])
  (exact (hk u j hu hd hf)))

(a/theorem mv-ownfwd-prune [s :- MSt, a :- Nat]
  (=> (mv-k-ownfwd s) (mv-k-ownfwd (mv-prune s a)))
  (intro hk)
  (simp only [mv-k-ownfwd] at hk)
  (have pp := (mv-prune-proj s a))
  (intros u j hu hd hf)
  (rw [(And.left (And.right (And.right (And.right pp))))] at hu)
  (rw [(And.left (And.right (And.right (And.right (And.right (And.right (And.right pp)))))))] at hd)
  (rw [(And.left (And.right (And.right pp)))] at hf)
  (rw [(And.left (And.right pp)) (And.left (And.right (mv-prune-fields s a ((:home s) j))))])
  (exact (hk u j hu hd hf)))

(a/theorem mv-ownfwd-copy [s :- MSt, w :- Nat, i :- Nat, v :- Nat]
  (=> (mv-k-ownfwd s) (mv-k-home s) (= ((:act s) w) true) (= (((:dom s) w) i) true)
      (Not (= (:ow ((:h s) ((:home s) i))) w))
      (mv-k-ownfwd (mv-copy s w i v)))
  (intros hk hh ha hd hno)
  (simp only [mv-k-ownfwd] at hk)
  (simp only [mv-k-home] at hh)
  (have pp := (mv-copy-proj s w i v))
  (intros u j hu hdj hf)
  (rw [(And.left (And.right (And.right pp)))] at hu)
  (rw [(And.left (And.right (And.right (And.right (And.right (And.right pp))))))] at hdj)
  (rw [(And.left (And.right pp)) (mv-copy-h-old s w i v _ (And.left (hh u j hu hdj)))])
  (cases huj (Bool.and (Nat.beq u w) (Nat.beq j i)))
  (case [true]
    (have q := huj) (simp only [Bool.and_eq_true Nat.beq_eq] at q)
    (rw [(And.left q) (And.right q)])
    (exact hno))
  (case [false]
    (have hn2 (Not (And (= u w) (= j i))))
    (intro c) (rw [(And.left c) (And.right c) Nat.beq_refl Nat.beq_refl] at huj) (cases huj)
    (rw [(mv-copy-fwd s w i v u j hn2)] at hf)
    (exact (hk u j hu hdj hf))))

(a/theorem mv-ownfwd-create [s :- MSt, w :- Nat, i :- Nat, y :- Nat]
  (=> (mv-k-ownfwd s) (mv-k-home s) (= (MW.fwd ((:fam s) w) i) 0)
      (forall [x :- Nat] (=> (= ((:act s) x) true) (= (((:dom s) x) i) false)))
      (mv-k-ownfwd (mv-create s w i y)))
  (intros hk hh hf0 hfr)
  (simp only [mv-k-ownfwd] at hk)
  (simp only [mv-k-home] at hh)
  (have pp := (mv-create-proj s w i y))
  (intros u j hu hdj hf)
  (rw [(And.left (And.right (And.right pp)))] at hu)
  (rw [(And.left (And.right pp))] at hf)
  (have cdm := (mv-create-dom s w i y u j hfr hu hdj))
  (cases cdm)
  (case [inl c]
    (rw [(And.left c) (And.right c)] at hf)
    (exact (absurd hf0 hf)))
  (case [inr c]
    (have co := (mv-create-other s w i y u j (And.left c)))
    (rw [(And.left co) (mv-create-h-old s w i y _ (And.left (hh u j hu (And.right c))))])
    (exact (hk u j hu (And.right c) hf))))

;; ---------------------------------------------------------------------------
;; Fork (`fork-world*`) keeps the invariant

;; the fork's child id and token are fresh: no active lineage names them
(a/defn mv-fresh-for [c :- Nat, t :- Nat, e :- MEnt] Prop
  (And (Not (= (:own e) c)) (Not (= (:tok e) t))))

(a/defn mv-fork-W [s :- MSt, w :- Nat, t :- Nat] MW
  (MW.mk (+ (:ord ((:fam s) w)) 1) (MW.fwd ((:fam s) w)) (:lin ((:fam s) w))
         (List.append (:cells ((:fam s) w)) (List.cons MCell (MCell.mk (:ord ((:fam s) w)) t) (List.nil MCell)))))

(a/defn mv-fork-C [s :- MSt, w :- Nat, t :- Nat] MW
  (MW.mk 0 (fn [x :- Nat] 0)
         (List.cons MEnt (MEnt.mk w (:ord ((:fam s) w)) t (MW.fwd ((:fam s) w))) (:lin ((:fam s) w)))
         (List.nil MCell)))

(a/theorem mv-fork-fam-c [s :- MSt, w :- Nat, c :- Nat, t :- Nat, b :- Bool]
  (= ((:fam (mv-fork s w c t b)) c) (mv-fork-C s w t))
  (simp only [mv-fork mv-upd-same mv-fork-C]))

(a/theorem mv-fork-fam-w [s :- MSt, w :- Nat, c :- Nat, t :- Nat, b :- Bool]
  (=> (Not (= w c)) (= ((:fam (mv-fork s w c t b)) w) (mv-fork-W s w t)))
  (intro hne)
  (simp only [mv-fork (mv-upd-other _ c _ w hne) mv-upd-same mv-fork-W]))

(a/theorem mv-fork-fam-x [s :- MSt, w :- Nat, c :- Nat, t :- Nat, b :- Bool, x :- Nat]
  (=> (Not (= x c)) (Not (= x w)) (= ((:fam (mv-fork s w c t b)) x) ((:fam s) x)))
  (intros h1 h2)
  (simp only [mv-fork (mv-upd-other _ c _ x h1) (mv-upd-other _ w _ x h2)]))

;; every world other than the child keeps its copy map and lineage; ordinals and cells only grow
(a/theorem mv-fork-fam-keep [s :- MSt, w :- Nat, c :- Nat, t :- Nat, b :- Bool, x :- Nat]
  (=> (Not (= w c)) (Not (= x c))
      (And (= (:lin ((:fam (mv-fork s w c t b)) x)) (:lin ((:fam s) x)))
           (And (forall [j :- Nat] (= (MW.fwd ((:fam (mv-fork s w c t b)) x) j) (MW.fwd ((:fam s) x) j)))
                (And (<= (:ord ((:fam s) x)) (:ord ((:fam (mv-fork s w c t b)) x)))
                     (forall [f :- Nat, k :- Nat]
                       (=> (= (mv-has-cell (:cells ((:fam s) x)) f k) true)
                           (= (mv-has-cell (:cells ((:fam (mv-fork s w c t b)) x)) f k) true)))))))
  (intros hwc hxc)
  (cases hxw (Nat.beq x w))
  (case [false]
    (rw [(mv-fork-fam-x s w c t b x hxc (Nat.ne_of_beq_eq_false hxw))])
    (apply And.intro) (rfl)
    (apply And.intro) (intro j) (rfl)
    (apply And.intro) (exact (Nat.le_refl _))
    (intros f k hc) (exact hc))
  (case [true]
    (have e := (Eq.symm (Nat.eq_of_beq_eq_true hxw))) (subst e)
    (rw [(mv-fork-fam-w s w c t b hwc)])
    (apply And.intro) (rfl)
    (apply And.intro) (intro j) (rfl)
    (apply And.intro) (show (<= (:ord ((:fam s) w)) (+ (:ord ((:fam s) w)) 1))) (omega)
    (intros f k hc) (exact (mv-has-cell-app _ _ f k hc))))

;; token states: sharing never ends a token, keeps shared ones, shares the head
(a/theorem mv-shr-live [v :- Nat] (=> (Not (= v 2)) (= (mv-shr v) 1))
  (intro h) (simp only [mv-shr (mv-nbeq-ne v 2 h)]))

(a/theorem mv-share-ne2 [ts :- (=> Nat Nat), l :- (List MEnt), x :- Nat]
  (=> (Not (= (ts x) 2)) (Not (= (mv-share ts l x) 2)))
  (intro hx)
  (cases l)
  (case [nil] (simp only [mv-share]) (exact hx))
  (case [cons e r]
    (simp only [mv-share])
    (cases hxe (Nat.beq x (:tok e)))
    (case [false] (rw [(mv-upd-other ts (:tok e) _ x (Nat.ne_of_beq_eq_false hxe))]) (exact hx))
    (case [true]
      (have ex := (Nat.eq_of_beq_eq_true hxe)) (rw [ex mv-upd-same]) (rw [ex] at hx)
      (rw [(mv-shr-live _ hx)]) (intro q) (cases q))))

(a/theorem mv-share-one [ts :- (=> Nat Nat), l :- (List MEnt), x :- Nat]
  (=> (= (ts x) 1) (= (mv-share ts l x) 1))
  (intro hx)
  (have hx2 (Not (= (ts x) 2))) (rw [hx]) (intro q) (cases q)
  (cases l)
  (case [nil] (simp only [mv-share]) (exact hx))
  (case [cons e r]
    (simp only [mv-share])
    (cases hxe (Nat.beq x (:tok e)))
    (case [false] (rw [(mv-upd-other ts (:tok e) _ x (Nat.ne_of_beq_eq_false hxe))]) (exact hx))
    (case [true]
      (have ex := (Nat.eq_of_beq_eq_true hxe)) (rw [ex mv-upd-same]) (rw [ex] at hx2)
      (exact (mv-shr-live _ hx2)))))

(a/theorem mv-share-head [ts :- (=> Nat Nat), e :- MEnt, r :- (List MEnt)]
  (=> (Not (= (ts (:tok e)) 2)) (= (mv-share ts (List.cons MEnt e r) (:tok e)) 1))
  (intro h2)
  (simp only [mv-share mv-upd-same])
  (exact (mv-shr-live _ h2)))

;; THE FORK VIEW: the child reads every id of the parent's domain as the parent read it
(a/theorem mv-fork-res-c [s :- MSt, w :- Nat, c :- Nat, t :- Nat, b :- Bool, j :- Nat]
  (=> (mv-k-row s) (mv-k-fwd s) (mv-k-ownfwd s) (= ((:act s) w) true) (= (((:dom s) w) j) true)
      (< ((:home s) j) (:n s)) (forall [a :- Nat] (=> (< a (:n s)) (Not (= (:ow ((:h s) a)) c))))
      (= (mv-res (:h s) (:home s) c ((:fam (mv-fork s w c t b)) c) j)
         (mv-res (:h s) (:home s) w ((:fam s) w) j)))
  (intros hrow hfwd hof ha hd hhn hfc)
  (simp only [mv-k-row] at hrow)
  (simp only [mv-k-fwd] at hfwd)
  (simp only [mv-k-ownfwd] at hof)
  (rw [(mv-fork-fam-c s w c t b)])
  (have hnc := (hfc _ hhn))
  (simp only [mv-res mv-fork-C (mv-nbeq-ne _ _ hnc) Nat.beq_refl mv-scan])
  (cases hf (Nat.beq (MW.fwd ((:fam s) w) j) 0))
  (case [false]
    ;; the parent's copy, unchanged since the fork (its stamp is not newer than the fork's ordinal)
    (have hf2 := (Nat.ne_of_beq_eq_false hf))
    (have q := (hfwd w j hf2))
    (have qr := (hrow _ (And.left q)))
    (rw [(And.right (And.right q))] at qr)
    (have hle (= (Nat.ble (:so ((:h s) (MW.fwd ((:fam s) w) j))) (:ord ((:fam s) w))) true))
    (simp only [Nat.ble_eq]) (exact (And.left qr))
    (have hno := (hof w j ha hd hf2))
    (simp only [hf mv-vat hle (mv-nbeq-ne _ _ hno)]))
  (case [true]
    (cases ho (Nat.beq (:ow ((:h s) ((:home s) j))) w))
    (case [true]
      ;; the parent's own row, unchanged since the fork
      (have qr := (hrow _ hhn))
      (rw [(Nat.eq_of_beq_eq_true ho)] at qr)
      (have hle (= (Nat.ble (:so ((:h s) ((:home s) j))) (:ord ((:fam s) w))) true))
      (simp only [Nat.ble_eq]) (exact (And.left qr))
      (simp only [hf ho mv-vat hle]))
    (case [false]
      ;; read through the parent's own lineage, at the same ordinals
      (simp only [hf ho]))))

(a/theorem mv-fork-proj [s :- MSt, w :- Nat, c :- Nat, t :- Nat, b :- Bool]
  (And (= (:h (mv-fork s w c t b)) (:h s))
       (And (= (:n (mv-fork s w c t b)) (:n s))
            (And (= (:home (mv-fork s w c t b)) (:home s))
                 (= (:ts (mv-fork s w c t b)) (mv-upd (mv-share (:ts s) (:lin ((:fam s) w))) t 0)))))
  (simp only [mv-fork and_self]))

;; a world other than the child keeps its activity, base flag, domain and table
(a/theorem mv-fork-other [s :- MSt, w :- Nat, c :- Nat, t :- Nat, b :- Bool, x :- Nat]
  (=> (Not (= x c))
      (And (= ((:act (mv-fork s w c t b)) x) ((:act s) x))
           (And (= ((:bas (mv-fork s w c t b)) x) ((:bas s) x))
                (And (= ((:dom (mv-fork s w c t b)) x) ((:dom s) x))
                     (= ((:tab (mv-fork s w c t b)) x) ((:tab s) x))))))
  (intro hx)
  (simp only [mv-fork (mv-upd-other (:act s) c _ x hx) (mv-upd-other (:bas s) c _ x hx)
              (mv-upd-other (:dom s) c _ x hx) (mv-upd-other (:tab s) c _ x hx) and_self]))

(a/theorem mv-fork-child [s :- MSt, w :- Nat, c :- Nat, t :- Nat, b :- Bool]
  (And (= ((:act (mv-fork s w c t b)) c) true)
       (And (= ((:bas (mv-fork s w c t b)) c) b)
            (And (= ((:dom (mv-fork s w c t b)) c) ((:dom s) w))
                 (= ((:tab (mv-fork s w c t b)) c) ((:tab s) w)))))
  (simp only [mv-fork mv-upd-same and_self]))

;; the token state after the fork: the new token is live, nothing ends, shared stays shared
(a/theorem mv-fork-ts-other [s :- MSt, w :- Nat, c :- Nat, t :- Nat, b :- Bool, x :- Nat]
  (=> (Not (= x t)) (= ((:ts (mv-fork s w c t b)) x) (mv-share (:ts s) (:lin ((:fam s) w)) x)))
  (intro hx)
  (rw [(And.right (And.right (And.right (mv-fork-proj s w c t b)))) (mv-upd-other _ t _ x hx)]))

(a/theorem mv-has-cell-last [cs :- (List MCell), o :- Nat, t :- Nat]
  (= (mv-has-cell (List.append cs (List.cons MCell (MCell.mk o t) (List.nil MCell))) o t) true)
  (induction cs)
  (case [nil] (simp only [List.append mv-has-cell Nat.beq_refl Bool.and_self Bool.true_or]))
  (case [cons d r ih] (simp only [List.append mv-has-cell ih Bool.or_true])))

(a/theorem mv-allE-mono2 [P :- (=> MEnt Prop), Q :- (=> MEnt Prop), R :- (=> MEnt Prop), l :- (List MEnt)]
  (=> (forall [e :- MEnt] (=> (P e) (Q e) (R e))) (mv-allE P l) (mv-allE Q l) (mv-allE R l))
  (intros hpq hp hq)
  (induction l)
  (case [nil] (simp only [mv-allE]))
  (case [cons e r ih]
    (simp only [mv-allE] at hp hq)
    (simp only [mv-allE])
    (exact (And.intro (hpq e (And.left hp) (And.left hq)) (ih (And.right hp) (And.right hq))))))

;; the head token of a fresh lineage is not the fork's token
(a/theorem mv-ht-fresh [c :- Nat, t :- Nat, l :- (List MEnt), x :- Nat]
  (=> (mv-allE (mv-fresh-for c t) l) (= (mv-ht l) (Option.some Nat x)) (Not (= x t)))
  (intros hf hh)
  (cases l)
  (case [nil] (simp only [mv-ht] at hh) (cases hh))
  (case [cons e r]
    (simp only [mv-ht] at hh)
    (simp only [mv-allE mv-fresh-for] at hf)
    (have ex := (Option.some.inj hh))
    (rw [(Eq.symm ex)])
    (exact (And.right (And.left hf)))))

;; resolution depends on a world's state only through its copy of the id and its lineage
(a/theorem mv-res-W [h :- (=> Nat MRow), home :- (=> Nat Nat), u :- Nat, W :- MW, W2 :- MW, j :- Nat]
  (=> (= (MW.fwd W2 j) (MW.fwd W j)) (= (:lin W2) (:lin W)) (= (mv-res h home u W2 j) (mv-res h home u W j)))
  (intros hf hl)
  (simp only [mv-res hf hl]))

(a/theorem mv-fork-ent [s :- MSt, w :- Nat, c :- Nat, t :- Nat, b :- Bool, e :- MEnt]
  (=> (Not (= w c)) (mv-ent-ok s e) (mv-fresh-for c t e) (mv-ent-ok (mv-fork s w c t b) e))
  (intros hwc he hfr)
  (simp only [mv-fresh-for] at hfr)
  (have pp := (mv-fork-proj s w c t b))
  (have fk := (mv-fork-fam-keep s w c t b (:own e) hwc (And.left hfr)))
  (have hn (<= (:n s) (:n (mv-fork s w c t b)))) (rw [(And.left (And.right pp))]) (exact (Nat.le_refl _))
  (have hh (forall [a :- Nat] (=> (< a (:n s)) (= ((:h (mv-fork s w c t b)) a) ((:h s) a)))))
  (intros a ha) (rw [(And.left pp)])
  (apply (mv-ent-ok-ext s _ e hn hh))
  (exact (And.left (And.right (And.right fk))))
  (exact ((And.right (And.right (And.right fk))) (:f e) (:tok e)))
  (rw [(mv-fork-ts-other s w c t b (:tok e) (And.right hfr))])
  (simp only [mv-ent-ok] at he)
  (exact (mv-share-ne2 _ _ _ (And.left (And.right he))))
  (exact he))

(a/theorem mv-fork-ent-new [s :- MSt, w :- Nat, c :- Nat, t :- Nat, b :- Bool]
  (=> (Not (= w c)) (mv-k-fwd s)
      (mv-ent-ok (mv-fork s w c t b) (MEnt.mk w (:ord ((:fam s) w)) t (MW.fwd ((:fam s) w)))))
  (intros hwc hf)
  (simp only [mv-k-fwd] at hf)
  (have pp := (mv-fork-proj s w c t b))
  (simp only [mv-ent-ok])
  (rw [(mv-upd-other _ c _ w hwc) mv-upd-same mv-upd-same])
  (apply And.intro) (show (< (:ord ((:fam s) w)) (+ (:ord ((:fam s) w)) 1))) (omega)
  (apply And.intro) (intro q) (cases q)
  (apply And.intro) (exact (mv-has-cell-last _ _ _))
  (intros i hm)
  (exact (hf w i hm)))

;; the fork's preconditions: the parent is an active non-basis world, the child id and the token
;; are fresh (no row is owned by the child; no active lineage names the child or the token)
(a/defn mv-fork-pre [s :- MSt, w :- Nat, c :- Nat, t :- Nat] Prop
  (And (= ((:act s) w) true)
       (And (= ((:bas s) w) false)
            (And (= ((:act s) c) false)
                 (And (forall [a :- Nat] (=> (< a (:n s)) (Not (= (:ow ((:h s) a)) c))))
                      (forall [u :- Nat] (=> (= ((:act s) u) true) (mv-allE (mv-fresh-for c t) (:lin ((:fam s) u))))))))))

(a/theorem mv-fork-wc [s :- MSt, w :- Nat, c :- Nat, t :- Nat]
  (=> (mv-fork-pre s w c t) (Not (= w c)))
  (intro hp) (simp only [mv-fork-pre] at hp)
  (intro e) (have q := (And.left (And.right (And.right hp)))) (rw [(Eq.symm e) (And.left hp)] at q) (cases q))

(a/theorem mv-allE-tl [P :- (=> MEnt Prop), l :- (List MEnt)] (=> (mv-allE P l) (mv-allE P (mv-tl l)))
  (intro h) (cases l)
  (case [nil] (simp only [mv-tl mv-allE]))
  (case [cons e r] (simp only [mv-allE] at h) (simp only [mv-tl]) (exact (And.right h))))

(a/theorem mv-fork-k-row [s :- MSt, w :- Nat, c :- Nat, t :- Nat, b :- Bool]
  (=> (mv-k-row s) (mv-fork-pre s w c t) (mv-k-row (mv-fork s w c t b)))
  (intros hr hp)
  (have hwc := (mv-fork-wc s w c t hp))
  (simp only [mv-fork-pre] at hp)
  (simp only [mv-k-row] at hr)
  (have pp := (mv-fork-proj s w c t b))
  (intros a ha)
  (rw [(And.left (And.right pp))] at ha)
  (rw [(And.left pp)])
  (have q := (hr a ha))
  (have fk := (mv-fork-fam-keep s w c t b (:ow ((:h s) a)) hwc ((And.left (And.right (And.right (And.right hp)))) a ha)))
  (exact (And.intro (Nat.le_trans (And.left q) (And.left (And.right (And.right fk)))) (And.right q))))

(a/theorem mv-fork-k-fwd [s :- MSt, w :- Nat, c :- Nat, t :- Nat, b :- Bool]
  (=> (mv-k-fwd s) (mv-fork-pre s w c t) (mv-k-fwd (mv-fork s w c t b)))
  (intros hf hp)
  (have hwc := (mv-fork-wc s w c t hp))
  (simp only [mv-k-fwd] at hf)
  (have pp := (mv-fork-proj s w c t b))
  (intros u j hne)
  (rw [(And.left pp) (And.left (And.right pp))])
  (cases huc (Nat.beq u c))
  (case [true]
    (rw [(Nat.eq_of_beq_eq_true huc) (mv-fork-fam-c s w c t b)] at hne)
    (exact (absurd (Eq.refl 0) hne)))
  (case [false]
    (have fk := (mv-fork-fam-keep s w c t b u hwc (Nat.ne_of_beq_eq_false huc)))
    (rw [((And.left (And.right fk)) j)] at hne)
    (rw [((And.left (And.right fk)) j)])
    (exact (hf u j hne))))

(a/theorem mv-fork-k-lin [s :- MSt, w :- Nat, c :- Nat, t :- Nat, b :- Bool]
  (=> (mv-k-fwd s) (mv-k-lin s) (mv-fork-pre s w c t) (mv-k-lin (mv-fork s w c t b)))
  (intros hf hl hp)
  (have hwc := (mv-fork-wc s w c t hp))
  (have hp2 := hp)
  (simp only [mv-fork-pre] at hp2)
  (have hfr := (And.right (And.right (And.right (And.right hp2)))))
  (simp only [mv-k-lin] at hl)
  (have tr (forall [e :- MEnt] (=> (mv-ent-ok s e) (mv-fresh-for c t e) (mv-ent-ok (mv-fork s w c t b) e))))
  (intros e he hfe) (exact (mv-fork-ent s w c t b e hwc he hfe))
  (intros u hu)
  (cases huc (Nat.beq u c))
  (case [true]
    (rw [(Nat.eq_of_beq_eq_true huc) (mv-fork-fam-c s w c t b)])
    (simp only [mv-fork-C mv-allE])
    (exact (And.intro (mv-fork-ent-new s w c t b hwc hf)
                      (mv-allE-mono2 _ _ _ _ tr (hl w (And.left hp2)) (hfr w (And.left hp2))))))
  (case [false]
    (have hnc := (Nat.ne_of_beq_eq_false huc))
    (rw [(And.left (mv-fork-other s w c t b u hnc))] at hu)
    (rw [(And.left (mv-fork-fam-keep s w c t b u hwc hnc))])
    (exact (mv-allE-mono2 _ _ _ _ tr (hl u hu) (hfr u hu)))))

(a/theorem mv-fork-k-home [s :- MSt, w :- Nat, c :- Nat, t :- Nat, b :- Bool]
  (=> (mv-k-home s) (mv-fork-pre s w c t) (mv-k-home (mv-fork s w c t b)))
  (intros hh hp)
  (have hp2 := hp)
  (simp only [mv-fork-pre] at hp2)
  (simp only [mv-k-home] at hh)
  (have pp := (mv-fork-proj s w c t b))
  (intros u j hu hd)
  (rw [(And.left pp) (And.left (And.right pp)) (And.left (And.right (And.right pp)))])
  (cases huc (Nat.beq u c))
  (case [true]
    (have e := (Nat.eq_of_beq_eq_true huc))
    (rw [e (And.left (And.right (And.right (mv-fork-child s w c t b))))] at hd)
    (exact (hh w j (And.left hp2) hd)))
  (case [false]
    (have fo := (mv-fork-other s w c t b u (Nat.ne_of_beq_eq_false huc)))
    (rw [(And.left fo)] at hu) (rw [(And.left (And.right (And.right fo)))] at hd)
    (exact (hh u j hu hd))))

;; the parent's lineage, read below the child's new entry, is shared after the fork
(a/defn mv-notdead [ts :- (=> Nat Nat), e :- MEnt] Prop (Not (= (ts (:tok e)) 2)))

(a/theorem mv-shared-after [ts :- (=> Nat Nat), ts2 :- (=> Nat Nat), l :- (List MEnt), c :- Nat, t :- Nat]
  (=> (mv-allE (mv-notdead ts) l) (mv-allE (mv-fresh-for c t) l) (mv-allE (mv-shared-tok ts) (mv-tl l))
      (forall [x :- Nat] (=> (Not (= x t)) (= (ts2 x) (mv-share ts l x))))
      (mv-allE (mv-shared-tok ts2) l))
  (intros he hf hs ets)
  (cases l)
  (case [nil] (simp only [mv-allE]))
  (case [cons e0 r]
    (simp only [mv-allE] at he hf)
    (simp only [mv-tl] at hs)
    (simp only [mv-allE])
    (apply And.intro)
    (simp only [mv-shared-tok])
    (simp only [mv-fresh-for] at hf)
    (rw [(ets (:tok e0) (And.right (And.left hf)))])
    (simp only [mv-notdead] at he)
    (exact (mv-share-head _ e0 r (And.left he)))
    (have tr (forall [e :- MEnt] (=> (mv-shared-tok ts e) (mv-fresh-for c t e) (mv-shared-tok ts2 e))))
    (intros e hse hfe)
    (simp only [mv-shared-tok] at hse)
    (simp only [mv-fresh-for] at hfe)
    (simp only [mv-shared-tok])
    (rw [(ets (:tok e) (And.right hfe))])
    (exact (mv-share-one _ _ _ hse))
    (exact (mv-allE-mono2 _ _ _ _ tr hs (And.right hf)))))

(a/theorem mv-fork-shared-lin [s :- MSt, w :- Nat, c :- Nat, t :- Nat, b :- Bool]
  (=> (mv-allE (mv-ent-ok s) (:lin ((:fam s) w))) (mv-allE (mv-fresh-for c t) (:lin ((:fam s) w)))
      (mv-allE (mv-shared-tok (:ts s)) (mv-tl (:lin ((:fam s) w))))
      (mv-allE (mv-shared-tok (:ts (mv-fork s w c t b))) (:lin ((:fam s) w))))
  (intros he hf hs)
  (have nd (mv-allE (mv-notdead (:ts s)) (:lin ((:fam s) w))))
  (apply (mv-allE-mono (mv-ent-ok s) _ _ _ he))
  (intros e h1) (simp only [mv-ent-ok] at h1) (simp only [mv-notdead]) (exact (And.left (And.right h1)))
  (exact (mv-shared-after (:ts s) _ _ c t nd hf hs (fn [x :- Nat, hx :- (Not (= x t))] (mv-fork-ts-other s w c t b x hx)))))

(a/theorem mv-fork-k-share [s :- MSt, w :- Nat, c :- Nat, t :- Nat, b :- Bool]
  (=> (mv-k-lin s) (mv-k-share s) (mv-fork-pre s w c t) (mv-k-share (mv-fork s w c t b)))
  (intros hl hk hp)
  (have hwc := (mv-fork-wc s w c t hp))
  (have hp2 := hp)
  (simp only [mv-fork-pre] at hp2)
  (have ha := (And.left hp2))
  (have hfr := (And.right (And.right (And.right (And.right hp2)))))
  (simp only [mv-k-lin] at hl)
  (simp only [mv-k-share] at hk)
  (apply And.intro)
  ;; tails are shared
  (intros u hu)
  (cases huc (Nat.beq u c))
  (case [true]
    (rw [(Nat.eq_of_beq_eq_true huc) (mv-fork-fam-c s w c t b)])
    (simp only [mv-fork-C mv-tl])
    (exact (mv-fork-shared-lin s w c t b (hl w ha) (hfr w ha) ((And.left hk) w ha))))
  (case [false]
    (have hnc := (Nat.ne_of_beq_eq_false huc))
    (rw [(And.left (mv-fork-other s w c t b u hnc))] at hu)
    (rw [(And.left (mv-fork-fam-keep s w c t b u hwc hnc))])
    (have tr (forall [e :- MEnt] (=> (mv-shared-tok (:ts s) e) (mv-fresh-for c t e)
                                     (mv-shared-tok (:ts (mv-fork s w c t b)) e))))
    (intros e hse hfe)
    (simp only [mv-shared-tok] at hse)
    (simp only [mv-fresh-for] at hfe)
    (show (= ((:ts (mv-fork s w c t b)) (:tok e)) 1))
    (rw [(mv-fork-ts-other s w c t b (:tok e) (And.right hfe))])
    (exact (mv-share-one _ _ _ hse))
    (exact (mv-allE-mono2 _ _ _ _ tr ((And.left hk) u hu) (mv-allE-tl _ _ (hfr u hu)))))
  ;; two active worlds with the same head token: it is shared
  (intros u v x hu hv hne h1 h2)
  (cases huc (Nat.beq u c))
  (case [true]
    (have eu := (Nat.eq_of_beq_eq_true huc))
    (rw [eu (mv-fork-fam-c s w c t b)] at h1)
    (simp only [mv-fork-C mv-ht] at h1)
    (have ex := (Option.some.inj h1))
    (have hvc (Not (= v c))) (intro e) (exact (hne (Eq.trans eu (Eq.symm e))))
    (rw [(And.left (mv-fork-other s w c t b v hvc))] at hv)
    (rw [(And.left (mv-fork-fam-keep s w c t b v hwc hvc))] at h2)
    (exfalso) (exact ((mv-ht-fresh c t _ x (hfr v hv) h2) (Eq.symm ex))))
  (case [false]
    (have hnc := (Nat.ne_of_beq_eq_false huc))
    (cases hvc0 (Nat.beq v c))
    (case [true]
      (have ev := (Nat.eq_of_beq_eq_true hvc0))
      (rw [ev (mv-fork-fam-c s w c t b)] at h2)
      (simp only [mv-fork-C mv-ht] at h2)
      (have ex := (Option.some.inj h2))
      (rw [(And.left (mv-fork-other s w c t b u hnc))] at hu)
      (rw [(And.left (mv-fork-fam-keep s w c t b u hwc hnc))] at h1)
      (exfalso) (exact ((mv-ht-fresh c t _ x (hfr u hu) h1) (Eq.symm ex))))
    (case [false]
      (have hvc := (Nat.ne_of_beq_eq_false hvc0))
      (rw [(And.left (mv-fork-other s w c t b u hnc))] at hu)
      (rw [(And.left (mv-fork-other s w c t b v hvc))] at hv)
      (rw [(And.left (mv-fork-fam-keep s w c t b u hwc hnc))] at h1)
      (rw [(And.left (mv-fork-fam-keep s w c t b v hwc hvc))] at h2)
      (have hxt := (mv-ht-fresh c t _ x (hfr u hu) h1))
      (rw [(mv-fork-ts-other s w c t b x hxt)])
      (exact (mv-share-one _ _ _ ((And.right hk) u v x hu hv hne h1 h2))))))

(a/theorem mv-fork-k-bas [s :- MSt, w :- Nat, c :- Nat, t :- Nat, b :- Bool]
  (=> (mv-k-bas s) (mv-fork-pre s w c t) (mv-k-bas (mv-fork s w c t b)))
  (intros hk hp)
  (have hwc := (mv-fork-wc s w c t hp))
  (have hp2 := hp)
  (simp only [mv-fork-pre] at hp2)
  (simp only [mv-k-bas] at hk)
  (have pp := (mv-fork-proj s w c t b))
  (intros u hu hbu)
  (rw [(And.left pp) (And.left (And.right pp))])
  (cases huc (Nat.beq u c))
  (case [true]
    (have e := (Nat.eq_of_beq_eq_true huc))
    (rw [e (mv-fork-fam-c s w c t b)])
    (apply And.intro)
    (intro j) (rfl)
    (exact (And.left (And.right (And.right (And.right hp2))))))
  (case [false]
    (have hnc := (Nat.ne_of_beq_eq_false huc))
    (have fo := (mv-fork-other s w c t b u hnc))
    (rw [(And.left fo)] at hu) (rw [(And.left (And.right fo))] at hbu)
    (have q := (hk u hu hbu))
    (have fk := (mv-fork-fam-keep s w c t b u hwc hnc))
    (apply And.intro)
    (intro j) (rw [((And.left (And.right fk)) j)]) (exact ((And.left q) j))
    (exact (And.right q))))

(a/theorem mv-fork-ref [s :- MSt, w :- Nat, c :- Nat, t :- Nat, b :- Bool]
  (=> (mv-inv s) (mv-k-ownfwd s) (mv-fork-pre s w c t) (mv-ref (mv-fork s w c t b)))
  (intros hinv hof hp)
  (have hwc := (mv-fork-wc s w c t hp))
  (have hp2 := hp)
  (simp only [mv-fork-pre] at hp2)
  (have ha := (And.left hp2))
  (have hrow := (And.left hinv))
  (have hfwd := (And.left (And.right hinv)))
  (have hhome := (And.left (And.right (And.right (And.right hinv)))))
  (have href := (And.right (And.right (And.right (And.right (And.right (And.right hinv)))))))
  (simp only [mv-ref] at href)
  (simp only [mv-k-home] at hhome)
  (have pp := (mv-fork-proj s w c t b))
  (intros u j hu hd)
  (rw [(And.left pp) (And.left (And.right (And.right pp)))])
  (cases huc (Nat.beq u c))
  (case [true]
    (have e := (Nat.eq_of_beq_eq_true huc))
    (have ch := (mv-fork-child s w c t b))
    (rw [e (And.left (And.right (And.right ch)))] at hd)
    (rw [e (And.right (And.right (And.right ch)))])
    (rw [(mv-fork-res-c s w c t b j hrow hfwd hof ha hd (And.left (hhome w j ha hd))
                       (And.left (And.right (And.right (And.right hp2)))))])
    (exact (href w j ha hd)))
  (case [false]
    (have hnc := (Nat.ne_of_beq_eq_false huc))
    (have fo := (mv-fork-other s w c t b u hnc))
    (have fk := (mv-fork-fam-keep s w c t b u hwc hnc))
    (rw [(And.left fo)] at hu) (rw [(And.left (And.right (And.right fo)))] at hd)
    (rw [(And.right (And.right (And.right fo)))
         (mv-res-W _ _ u _ _ j ((And.left (And.right fk)) j) (And.left fk))])
    (exact (href u j hu hd))))

(a/theorem mv-fork-ownfwd [s :- MSt, w :- Nat, c :- Nat, t :- Nat, b :- Bool]
  (=> (mv-k-ownfwd s) (mv-fork-pre s w c t) (mv-k-ownfwd (mv-fork s w c t b)))
  (intros hk hp)
  (have hwc := (mv-fork-wc s w c t hp))
  (simp only [mv-k-ownfwd] at hk)
  (have pp := (mv-fork-proj s w c t b))
  (intros u j hu hd hf)
  (rw [(And.left pp) (And.left (And.right (And.right pp)))])
  (cases huc (Nat.beq u c))
  (case [true]
    (rw [(Nat.eq_of_beq_eq_true huc) (mv-fork-fam-c s w c t b)] at hf)
    (exfalso) (exact (hf (Eq.refl 0))))
  (case [false]
    (have hnc := (Nat.ne_of_beq_eq_false huc))
    (have fo := (mv-fork-other s w c t b u hnc))
    (have fk := (mv-fork-fam-keep s w c t b u hwc hnc))
    (rw [(And.left fo)] at hu) (rw [(And.left (And.right (And.right fo)))] at hd)
    (rw [((And.left (And.right fk)) j)] at hf)
    (exact (hk u j hu hd hf))))

;; FORK (`fork-world*`, host fork, the `(fork)` effect, a savepoint basis when b): the invariant
;; is kept; the child reads the parent's tables (mv-fork-res-c)
(a/theorem mv-fork-inv [s :- MSt, w :- Nat, c :- Nat, t :- Nat, b :- Bool]
  (=> (mv-inv s) (mv-k-ownfwd s) (mv-fork-pre s w c t)
      (And (mv-inv (mv-fork s w c t b)) (mv-k-ownfwd (mv-fork s w c t b))))
  (intros hinv hof hp)
  (apply And.intro)
  (apply And.intro) (exact (mv-fork-k-row s w c t b (And.left hinv) hp))
  (apply And.intro) (exact (mv-fork-k-fwd s w c t b (And.left (And.right hinv)) hp))
  (apply And.intro) (exact (mv-fork-k-lin s w c t b (And.left (And.right hinv)) (And.left (And.right (And.right hinv))) hp))
  (apply And.intro) (exact (mv-fork-k-home s w c t b (And.left (And.right (And.right (And.right hinv)))) hp))
  (apply And.intro) (exact (mv-fork-k-share s w c t b (And.left (And.right (And.right hinv)))
                                            (And.left (And.right (And.right (And.right (And.right hinv))))) hp))
  (apply And.intro) (exact (mv-fork-k-bas s w c t b (And.left (And.right (And.right (And.right (And.right (And.right hinv)))))) hp))
  (exact (mv-fork-ref s w c t b hinv hof hp))
  (exact (mv-fork-ownfwd s w c t b hof hp)))

;; ---------------------------------------------------------------------------
;; Fewer active worlds, tokens ending: finish, drop, collect

;; a state with the same rows, homes, worlds, bases, domains and tables, fewer active worlds,
;; whose active lineages name no ended token and which keeps sharing, keeps the invariant
(a/theorem mv-shrink [s :- MSt, s2 :- MSt]
  (=> (mv-inv s) (mv-k-ownfwd s)
      (= (:h s2) (:h s)) (= (:n s2) (:n s)) (= (:home s2) (:home s)) (= (:fam s2) (:fam s))
      (= (:bas s2) (:bas s)) (= (:dom s2) (:dom s)) (= (:tab s2) (:tab s))
      (forall [x :- Nat] (=> (= ((:act s2) x) true) (= ((:act s) x) true)))
      (forall [u :- Nat] (=> (= ((:act s2) u) true) (mv-allE (mv-notdead (:ts s2)) (:lin ((:fam s) u)))))
      (mv-k-share s2)
      (And (mv-inv s2) (mv-k-ownfwd s2)))
  (intros hinv hof eh en em ef eb ed et hact hnd hsh)
  (have hrow := (And.left hinv))
  (have hfwd := (And.left (And.right hinv)))
  (have hlin := (And.left (And.right (And.right hinv))))
  (have hhome := (And.left (And.right (And.right (And.right hinv)))))
  (have hbas := (And.left (And.right (And.right (And.right (And.right (And.right hinv)))))))
  (have href := (And.right (And.right (And.right (And.right (And.right (And.right hinv)))))))
  (simp only [mv-k-row] at hrow)
  (simp only [mv-k-fwd] at hfwd)
  (simp only [mv-k-lin] at hlin)
  (simp only [mv-k-home] at hhome)
  (simp only [mv-k-bas] at hbas)
  (simp only [mv-ref] at href)
  (simp only [mv-k-ownfwd] at hof)
  (apply And.intro)
  (apply And.intro)
  (intros a ha) (rw [en] at ha) (rw [eh ef]) (exact (hrow a ha))
  (apply And.intro)
  (intros u j hne) (rw [ef] at hne) (rw [eh en ef]) (exact (hfwd u j hne))
  (apply And.intro)
  (intros u hu)
  (rw [ef])
  (have tr (forall [e :- MEnt] (=> (mv-ent-ok s e) (mv-notdead (:ts s2) e) (mv-ent-ok s2 e))))
  (intros e he hn)
  (simp only [mv-ent-ok] at he)
  (simp only [mv-notdead] at hn)
  (simp only [mv-ent-ok])
  (rw [ef eh en])
  (exact (And.intro (And.left he) (And.intro hn (And.right (And.right he)))))
  (exact (mv-allE-mono2 _ _ _ _ tr (hlin u (hact u hu)) (hnd u hu)))
  (apply And.intro)
  (intros u j hu hd) (rw [ed] at hd) (rw [em en eh]) (exact (hhome u j (hact u hu) hd))
  (apply And.intro)
  (exact hsh)
  (apply And.intro)
  (intros u hu hbu) (rw [eb] at hbu) (rw [ef en eh]) (exact (hbas u (hact u hu) hbu))
  (intros u j hu hd) (rw [ed] at hd) (rw [eh em ef et]) (exact (href u j (hact u hu) hd))
  (intros u j hu hd hf) (rw [ed] at hd) (rw [ef] at hf) (rw [eh em]) (exact (hof u j (hact u hu) hd hf)))

;; DROP: a world is collected (or a publication disposed)
(a/theorem mv-drop-inv [s :- MSt, w :- Nat]
  (=> (mv-inv s) (mv-k-ownfwd s) (And (mv-inv (mv-drop s w)) (mv-k-ownfwd (mv-drop s w))))
  (intros hinv hof)
  (have hlin := (And.left (And.right (And.right hinv))))
  (have hsh := (And.left (And.right (And.right (And.right (And.right hinv))))))
  (simp only [mv-k-lin] at hlin)
  (have hact (forall [x :- Nat] (=> (= ((:act (mv-drop s w)) x) true) (= ((:act s) x) true))))
  (intros x hx)
  (cases hxw (Nat.beq x w))
  (case [true] (rw [(Nat.eq_of_beq_eq_true hxw)] at hx) (simp only [mv-drop mv-upd-same] at hx) (cases hx))
  (case [false] (simp only [mv-drop (mv-upd-other (:act s) w _ x (Nat.ne_of_beq_eq_false hxw))] at hx) (exact hx))
  (apply (mv-shrink s (mv-drop s w) hinv hof (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _) hact))
  (intros u hu)
  (apply (mv-allE-mono (mv-ent-ok s) _ _ _ (hlin u (hact u hu))))
  (intros e he) (simp only [mv-ent-ok] at he) (simp only [mv-notdead]) (exact (And.left (And.right he)))
  (simp only [mv-k-share] at hsh)
  (apply And.intro)
  (intros u hu) (exact ((And.left hsh) u (hact u hu)))
  (intros u v x hu hv hne h1 h2) (exact ((And.right hsh) u v x (hact u hu) (hact v hv) hne h1 h2)))

(a/theorem mv-fin-one [ts :- (=> Nat Nat), l :- (List MEnt), x :- Nat]
  (=> (= (ts x) 1) (= (mv-fin ts l x) 1))
  (intro hx)
  (cases l)
  (case [nil] (simp only [mv-fin]) (exact hx))
  (case [cons e r]
    (simp only [mv-fin])
    (cases hxe (Nat.beq x (:tok e)))
    (case [false] (rw [(mv-upd-other ts (:tok e) _ x (Nat.ne_of_beq_eq_false hxe))]) (exact hx))
    (case [true]
      (have ex := (Nat.eq_of_beq_eq_true hxe)) (rw [ex mv-upd-same]) (rw [ex] at hx)
      (rw [hx]))))

;; entry e of another active world: if it names the head token of lineage lw, that token is shared
(a/defn mv-wtok-shared [ts :- (=> Nat Nat), lw :- (List MEnt), e :- MEnt] Prop
  (forall [y :- Nat] (=> (= (mv-ht lw) (Option.some Nat y)) (= (:tok e) y) (= (ts y) 1))))

;; finishing lw's owner leaves such an entry's token alive
(a/theorem mv-fin-notdead [ts :- (=> Nat Nat), lw :- (List MEnt), e :- MEnt]
  (=> (Not (= (ts (:tok e)) 2)) (mv-wtok-shared ts lw e) (Not (= (mv-fin ts lw (:tok e)) 2)))
  (intros hnd hw)
  (simp only [mv-wtok-shared] at hw)
  (cases lw)
  (case [nil] (simp only [mv-fin]) (exact hnd))
  (case [cons e0 r]
    (cases hx (Nat.beq (:tok e) (:tok e0)))
    (case [false]
      (simp only [mv-fin])
      (rw [(mv-upd-other ts (:tok e0) _ (:tok e) (Nat.ne_of_beq_eq_false hx))])
      (exact hnd))
    (case [true]
      (have ex := (Nat.eq_of_beq_eq_true hx))
      (have h1 := (hw (:tok e0) (Eq.refl _) ex))
      (rw [ex (mv-fin-one ts _ (:tok e0) h1)])
      (intro q) (cases q))))

;; every entry of an active world u other than w satisfies it (heads by pairwise sharing, the rest
;; by tail sharing)
(a/theorem mv-wtok-lin [s :- MSt, w :- Nat, u :- Nat]
  (=> (mv-k-share s) (= ((:act s) w) true) (= ((:act s) u) true) (Not (= u w))
      (mv-allE (mv-wtok-shared (:ts s) (:lin ((:fam s) w))) (:lin ((:fam s) u))))
  (intros hk hw hu hne)
  (simp only [mv-k-share] at hk)
  (have ht := ((And.left hk) u hu))
  (have hp (forall [y :- Nat] (=> (= (mv-ht (:lin ((:fam s) u))) (Option.some Nat y))
                                  (= (mv-ht (:lin ((:fam s) w))) (Option.some Nat y)) (= ((:ts s) y) 1))))
  (intros y h1 h2) (exact ((And.right hk) u w y hu hw hne h1 h2))
  (cases hl (:lin ((:fam s) u)))
  (case [nil] (simp only [mv-allE]))
  (case [cons e r]
    (rw [hl] at ht hp)
    (simp only [mv-tl] at ht)
    (simp only [mv-allE])
    (apply And.intro)
    (simp only [mv-wtok-shared])
    (intros y hy ey) (rw [(Eq.symm ey)] at hy) (rw [(Eq.symm ey)])
    (exact (hp (:tok e) (Eq.refl _) hy))
    (apply (mv-allE-mono (mv-shared-tok (:ts s)) _ _ _ ht))
    (intros x hx) (simp only [mv-shared-tok] at hx) (simp only [mv-wtok-shared])
    (intros y hy ey) (rw [(Eq.symm ey)]) (exact hx)))

(a/theorem mv-finish-proj [s :- MSt, w :- Nat]
  (And (= (:act (mv-finish s w)) (mv-upd (:act s) w false)) (= (:ts (mv-finish s w)) (mv-fin (:ts s) (:lin ((:fam s) w)))))
  (simp only [mv-finish and_self]))

(a/theorem mv-finish-act [s :- MSt, w :- Nat, x :- Nat]
  (=> (= ((:act (mv-finish s w)) x) true) (And (= ((:act s) x) true) (Not (= x w))))
  (intro hx)
  (rw [(And.left (mv-finish-proj s w))] at hx)
  (cases hxw (Nat.beq x w))
  (case [true] (rw [(Nat.eq_of_beq_eq_true hxw) mv-upd-same] at hx) (cases hx))
  (case [false]
    (have hne := (Nat.ne_of_beq_eq_false hxw))
    (rw [(mv-upd-other (:act s) w _ x hne)] at hx)
    (exact (And.intro hx hne))))

;; FINISH (`maybe-finish-token!`): w's token ends unless shared; nothing active reads through it
(a/theorem mv-finish-inv [s :- MSt, w :- Nat]
  (=> (mv-inv s) (mv-k-ownfwd s) (= ((:act s) w) true)
      (And (mv-inv (mv-finish s w)) (mv-k-ownfwd (mv-finish s w))))
  (intros hinv hof ha)
  (have hlin := (And.left (And.right (And.right hinv))))
  (have hsh := (And.left (And.right (And.right (And.right (And.right hinv))))))
  (have hsh2 := hsh)
  (simp only [mv-k-lin] at hlin)
  (simp only [mv-k-share] at hsh2)
  (have ets := (And.right (mv-finish-proj s w)))
  (have hact (forall [x :- Nat] (=> (= ((:act (mv-finish s w)) x) true) (= ((:act s) x) true))))
  (intros x hx) (exact (And.left (mv-finish-act s w x hx)))
  (apply (mv-shrink s (mv-finish s w) hinv hof (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _) hact))
  ;; no active lineage names an ended token
  (intros u hu)
  (have fa := (mv-finish-act s w u hu))
  (have tr (forall [e :- MEnt] (=> (mv-ent-ok s e) (mv-wtok-shared (:ts s) (:lin ((:fam s) w)) e)
                                   (mv-notdead (:ts (mv-finish s w)) e))))
  (intros e he hws)
  (simp only [mv-ent-ok] at he)
  (show (Not (= ((:ts (mv-finish s w)) (:tok e)) 2)))
  (rw [ets])
  (exact (mv-fin-notdead _ _ e (And.left (And.right he)) hws))
  (exact (mv-allE-mono2 _ _ _ _ tr (hlin u (And.left fa)) (mv-wtok-lin s w u hsh ha (And.left fa) (And.right fa))))
  ;; sharing is kept (finishing only ends live tokens)
  (apply And.intro)
  (intros u hu)
  (have fa := (mv-finish-act s w u hu))
  (rw [ets])
  (apply (mv-allE-mono (mv-shared-tok (:ts s)) _ _ _ ((And.left hsh2) u (And.left fa))))
  (intros e he) (simp only [mv-shared-tok] at he) (simp only [mv-shared-tok]) (exact (mv-fin-one _ _ _ he))
  (intros u v x hu hv hne h1 h2)
  (rw [ets])
  (exact (mv-fin-one _ _ _ ((And.right hsh2) u v x (hact u hu) (hact v hv) hne h1 h2))))

;; COLLECT: an unreachable token (named by no active lineage) ends
(a/theorem mv-collect-inv [s :- MSt, t :- Nat]
  (=> (mv-inv s) (mv-k-ownfwd s)
      (forall [u :- Nat] (=> (= ((:act s) u) true) (mv-allE (mv-fresh-for u t) (:lin ((:fam s) u)))))
      (And (mv-inv (mv-collect s t)) (mv-k-ownfwd (mv-collect s t))))
  (intros hinv hof hfr)
  (have hlin := (And.left (And.right (And.right hinv))))
  (have hsh := (And.left (And.right (And.right (And.right (And.right hinv))))))
  (simp only [mv-k-lin] at hlin)
  (simp only [mv-k-share] at hsh)
  (have ets (= (:ts (mv-collect s t)) (mv-upd (:ts s) t 2))) (simp only [mv-collect])
  (have hact (forall [x :- Nat] (=> (= ((:act (mv-collect s t)) x) true) (= ((:act s) x) true))))
  (intros x hx) (exact hx)
  (apply (mv-shrink s (mv-collect s t) hinv hof (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _) (Eq.refl _) hact))
  (intros u hu)
  (have tr (forall [e :- MEnt] (=> (mv-ent-ok s e) (mv-fresh-for u t e) (mv-notdead (:ts (mv-collect s t)) e))))
  (intros e he hfe)
  (simp only [mv-ent-ok] at he) (simp only [mv-fresh-for] at hfe)
  (show (Not (= ((:ts (mv-collect s t)) (:tok e)) 2))) (rw [ets (mv-upd-other (:ts s) t _ (:tok e) (And.right hfe))])
  (exact (And.left (And.right he)))
  (exact (mv-allE-mono2 _ _ _ _ tr (hlin u hu) (hfr u hu)))
  (apply And.intro)
  (intros u hu)
  (rw [ets])
  (have tr2 (forall [e :- MEnt] (=> (mv-shared-tok (:ts s) e) (mv-fresh-for u t e) (mv-shared-tok (mv-upd (:ts s) t 2) e))))
  (intros e he hfe)
  (simp only [mv-shared-tok] at he) (simp only [mv-fresh-for] at hfe)
  (simp only [mv-shared-tok (mv-upd-other (:ts s) t _ (:tok e) (And.right hfe))]) (exact he)
  (exact (mv-allE-mono2 _ _ _ _ tr2 ((And.left hsh) u hu) (mv-allE-tl _ _ (hfr u hu))))
  (intros u v x hu hv hne h1 h2)
  (rw [ets (mv-upd-other (:ts s) t _ x (mv-ht-fresh u t _ x (hfr u hu) h1))])
  (exact ((And.right hsh) u v x hu hv hne h1 h2)))

;; ---------------------------------------------------------------------------
;; Savepoint instances (`instance-world*`, S3) keep the invariant

(a/defn mv-notown [c :- Nat, e :- MEnt] Prop (Not (= (:own e) c)))

(a/defn mv-inst-pre [s :- MSt, b :- Nat, c :- Nat] Prop
  (And (= ((:act s) b) true)
       (And (= ((:bas s) b) true)
            (And (= ((:act s) c) false)
                 (And (forall [a :- Nat] (=> (< a (:n s)) (Not (= (:ow ((:h s) a)) c))))
                      (forall [u :- Nat] (=> (= ((:act s) u) true) (mv-allE (mv-notown c) (:lin ((:fam s) u))))))))))

(a/theorem mv-inst-proj [s :- MSt, b :- Nat, c :- Nat]
  (And (= (:h (mv-inst s b c)) (:h s))
       (And (= (:n (mv-inst s b c)) (:n s))
            (And (= (:home (mv-inst s b c)) (:home s))
                 (= (:ts (mv-inst s b c)) (mv-share (:ts s) (:lin ((:fam s) b)))))))
  (simp only [mv-inst and_self]))

(a/theorem mv-inst-other [s :- MSt, b :- Nat, c :- Nat, x :- Nat]
  (=> (Not (= x c))
      (And (= ((:fam (mv-inst s b c)) x) ((:fam s) x))
           (And (= ((:act (mv-inst s b c)) x) ((:act s) x))
                (And (= ((:bas (mv-inst s b c)) x) ((:bas s) x))
                     (And (= ((:dom (mv-inst s b c)) x) ((:dom s) x))
                          (= ((:tab (mv-inst s b c)) x) ((:tab s) x)))))))
  (intro hx)
  (simp only [mv-inst (mv-upd-other (:fam s) c _ x hx) (mv-upd-other (:act s) c _ x hx) (mv-upd-other (:bas s) c _ x hx)
              (mv-upd-other (:dom s) c _ x hx) (mv-upd-other (:tab s) c _ x hx) and_self]))

(a/theorem mv-inst-child [s :- MSt, b :- Nat, c :- Nat]
  (And (= ((:fam (mv-inst s b c)) c) (MW.mk 0 (fn [x :- Nat] 0) (:lin ((:fam s) b)) (List.nil MCell)))
       (And (= ((:act (mv-inst s b c)) c) true)
            (And (= ((:bas (mv-inst s b c)) c) false)
                 (And (= ((:dom (mv-inst s b c)) c) ((:dom s) b)) (= ((:tab (mv-inst s b c)) c) ((:tab s) b))))))
  (simp only [mv-inst mv-upd-same and_self]))

(a/theorem mv-inst-ent [s :- MSt, b :- Nat, c :- Nat, e :- MEnt]
  (=> (mv-ent-ok s e) (mv-notown c e) (mv-ent-ok (mv-inst s b c) e))
  (intros he hno)
  (simp only [mv-notown] at hno)
  (have pp := (mv-inst-proj s b c))
  (have fo := (mv-inst-other s b c (:own e) hno))
  (have hn (<= (:n s) (:n (mv-inst s b c)))) (rw [(And.left (And.right pp))]) (exact (Nat.le_refl _))
  (have hh (forall [a :- Nat] (=> (< a (:n s)) (= ((:h (mv-inst s b c)) a) ((:h s) a)))))
  (intros a ha) (rw [(And.left pp)])
  (apply (mv-ent-ok-ext s _ e hn hh))
  (rw [(And.left fo)]) (exact (Nat.le_refl _))
  (intro hc) (rw [(And.left fo)]) (exact hc)
  (rw [(And.right (And.right (And.right pp)))])
  (simp only [mv-ent-ok] at he)
  (exact (mv-share-ne2 _ _ _ (And.left (And.right he))))
  (exact he))

;; an instance reads what its basis reads: the basis owns no row and has no copy
(a/theorem mv-inst-res-c [s :- MSt, b :- Nat, c :- Nat, j :- Nat]
  (=> (mv-k-bas s) (= ((:act s) b) true) (= ((:bas s) b) true) (< ((:home s) j) (:n s))
      (forall [a :- Nat] (=> (< a (:n s)) (Not (= (:ow ((:h s) a)) c))))
      (= (mv-res (:h s) (:home s) c ((:fam (mv-inst s b c)) c) j) (mv-res (:h s) (:home s) b ((:fam s) b) j)))
  (intros hk ha hb hhn hfc)
  (simp only [mv-k-bas] at hk)
  (have q := (hk b ha hb))
  (rw [(And.left (mv-inst-child s b c))])
  (simp only [mv-res (mv-nbeq-ne _ _ (hfc _ hhn)) (mv-nbeq-ne _ _ ((And.right q) _ hhn)) ((And.left q) j) Nat.beq_refl]))

(a/theorem mv-inst-k-share [s :- MSt, b :- Nat, c :- Nat]
  (=> (mv-k-lin s) (mv-k-share s) (mv-inst-pre s b c) (mv-k-share (mv-inst s b c)))
  (intros hl hk hp)
  (have hp2 := hp)
  (simp only [mv-inst-pre] at hp2)
  (have hb := (And.left hp2))
  (have hcb (Not (= b c))) (intro e) (have q := (And.left (And.right (And.right hp2)))) (rw [(Eq.symm e) hb] at q) (cases q)
  (simp only [mv-k-lin] at hl)
  (simp only [mv-k-share] at hk)
  (have ets := (And.right (And.right (And.right (mv-inst-proj s b c)))))
  (have tr (forall [e :- MEnt] (=> (mv-shared-tok (:ts s) e) (mv-shared-tok (:ts (mv-inst s b c)) e))))
  (intros e he) (simp only [mv-shared-tok] at he) (show (= ((:ts (mv-inst s b c)) (:tok e)) 1))
  (rw [ets]) (exact (mv-share-one _ _ _ he))
  ;; the basis's head token, which the instance's lineage starts with, is shared now
  (have hb1 (forall [x :- Nat] (=> (= (mv-ht (:lin ((:fam s) b))) (Option.some Nat x)) (= ((:ts (mv-inst s b c)) x) 1))))
  (intros x hx)
  (rw [ets])
  (have hlb := (hl b hb))
  (cases hlb2 (:lin ((:fam s) b)))
  (case [nil] (rw [hlb2] at hx) (simp only [mv-ht] at hx) (cases hx))
  (case [cons e0 r]
    (rw [hlb2] at hx hlb)
    (simp only [mv-ht] at hx)
    (have ex := (Option.some.inj hx))
    (rw [(Eq.symm ex)])
    (simp only [mv-allE mv-ent-ok] at hlb)
    (exact (mv-share-head _ e0 r (And.left (And.right (And.left hlb))))))
  (apply And.intro)
  (intros u hu)
  (cases huc (Nat.beq u c))
  (case [true]
    (rw [(Nat.eq_of_beq_eq_true huc) (And.left (mv-inst-child s b c))])
    (exact (mv-allE-mono _ _ _ tr ((And.left hk) b hb))))
  (case [false]
    (have io := (mv-inst-other s b c u (Nat.ne_of_beq_eq_false huc)))
    (rw [(And.left (And.right io))] at hu) (rw [(And.left io)])
    (exact (mv-allE-mono _ _ _ tr ((And.left hk) u hu))))
  (intros u v x hu hv hne h1 h2)
  (cases huc (Nat.beq u c))
  (case [true]
    (rw [(Nat.eq_of_beq_eq_true huc) (And.left (mv-inst-child s b c))] at h1)
    (exact (hb1 x h1)))
  (case [false]
    (have io := (mv-inst-other s b c u (Nat.ne_of_beq_eq_false huc)))
    (cases hvc (Nat.beq v c))
    (case [true]
      (rw [(Nat.eq_of_beq_eq_true hvc) (And.left (mv-inst-child s b c))] at h2)
      (exact (hb1 x h2)))
    (case [false]
      (have io2 := (mv-inst-other s b c v (Nat.ne_of_beq_eq_false hvc)))
      (rw [(And.left (And.right io))] at hu) (rw [(And.left io)] at h1)
      (rw [(And.left (And.right io2))] at hv) (rw [(And.left io2)] at h2)
      (rw [ets])
      (exact (mv-share-one _ _ _ ((And.right hk) u v x hu hv hne h1 h2))))))

;; INSTANCE (`instance-world*`, S3): the invariant is kept; the instance reads the basis's tables
(a/theorem mv-inst-inv [s :- MSt, b :- Nat, c :- Nat]
  (=> (mv-inv s) (mv-k-ownfwd s) (mv-inst-pre s b c)
      (And (mv-inv (mv-inst s b c)) (mv-k-ownfwd (mv-inst s b c))))
  (intros hinv hof hp)
  (have hp2 := hp)
  (simp only [mv-inst-pre] at hp2)
  (have hb := (And.left hp2))
  (have hbb := (And.left (And.right hp2)))
  (have hfc := (And.left (And.right (And.right (And.right hp2)))))
  (have hno := (And.right (And.right (And.right (And.right hp2)))))
  (have hrow := (And.left hinv))
  (have hfwd := (And.left (And.right hinv)))
  (have hlin := (And.left (And.right (And.right hinv))))
  (have hhome := (And.left (And.right (And.right (And.right hinv)))))
  (have hsh := (And.left (And.right (And.right (And.right (And.right hinv))))))
  (have hbas := (And.left (And.right (And.right (And.right (And.right (And.right hinv)))))))
  (have href := (And.right (And.right (And.right (And.right (And.right (And.right hinv)))))))
  (have hbas2 := hbas)
  (simp only [mv-k-row] at hrow)
  (simp only [mv-k-fwd] at hfwd)
  (simp only [mv-k-lin] at hlin)
  (simp only [mv-k-home] at hhome)
  (simp only [mv-k-bas] at hbas)
  (simp only [mv-ref] at href)
  (simp only [mv-k-ownfwd] at hof)
  (have pp := (mv-inst-proj s b c))
  (have ch := (mv-inst-child s b c))
  (apply And.intro)
  (apply And.intro)
  ;; rows
  (intros a ha)
  (rw [(And.left (And.right pp))] at ha)
  (rw [(And.left pp) (And.left (mv-inst-other s b c _ (hfc a ha)))])
  (exact (hrow a ha))
  (apply And.intro)
  ;; copy maps
  (intros u j hne)
  (rw [(And.left pp) (And.left (And.right pp))])
  (cases huc (Nat.beq u c))
  (case [true] (rw [(Nat.eq_of_beq_eq_true huc) (And.left ch)] at hne) (exfalso) (exact (hne (Eq.refl 0))))
  (case [false]
    (have io := (mv-inst-other s b c u (Nat.ne_of_beq_eq_false huc)))
    (rw [(And.left io)] at hne) (rw [(And.left io)])
    (exact (hfwd u j hne)))
  (apply And.intro)
  ;; lineages
  (intros u hu)
  (have tr (forall [e :- MEnt] (=> (mv-ent-ok s e) (mv-notown c e) (mv-ent-ok (mv-inst s b c) e))))
  (intros e he hne) (exact (mv-inst-ent s b c e he hne))
  (cases huc (Nat.beq u c))
  (case [true]
    (rw [(Nat.eq_of_beq_eq_true huc) (And.left ch)])
    (exact (mv-allE-mono2 _ _ _ _ tr (hlin b hb) (hno b hb))))
  (case [false]
    (have io := (mv-inst-other s b c u (Nat.ne_of_beq_eq_false huc)))
    (rw [(And.left (And.right io))] at hu) (rw [(And.left io)])
    (exact (mv-allE-mono2 _ _ _ _ tr (hlin u hu) (hno u hu))))
  (apply And.intro)
  ;; creators' rows
  (intros u j hu hd)
  (rw [(And.left pp) (And.left (And.right pp)) (And.left (And.right (And.right pp)))])
  (cases huc (Nat.beq u c))
  (case [true]
    (rw [(Nat.eq_of_beq_eq_true huc) (And.left (And.right (And.right (And.right ch))))] at hd)
    (exact (hhome b j hb hd)))
  (case [false]
    (have io := (mv-inst-other s b c u (Nat.ne_of_beq_eq_false huc)))
    (rw [(And.left (And.right io))] at hu) (rw [(And.left (And.right (And.right (And.right io))))] at hd)
    (exact (hhome u j hu hd)))
  (apply And.intro)
  ;; sharing
  (exact (mv-inst-k-share s b c (And.left (And.right (And.right hinv))) hsh hp))
  (apply And.intro)
  ;; bases
  (intros u hu hbu)
  (rw [(And.left pp) (And.left (And.right pp))])
  (cases huc (Nat.beq u c))
  (case [true]
    (rw [(Nat.eq_of_beq_eq_true huc) (And.left (And.right (And.right ch)))] at hbu) (cases hbu))
  (case [false]
    (have io := (mv-inst-other s b c u (Nat.ne_of_beq_eq_false huc)))
    (rw [(And.left (And.right io))] at hu) (rw [(And.left (And.right (And.right io)))] at hbu)
    (rw [(And.left io)])
    (exact (hbas u hu hbu)))
  ;; refinement
  (intros u j hu hd)
  (rw [(And.left pp) (And.left (And.right (And.right pp)))])
  (cases huc (Nat.beq u c))
  (case [true]
    (have e := (Nat.eq_of_beq_eq_true huc))
    (rw [e (And.left (And.right (And.right (And.right ch))))] at hd)
    (rw [e (And.right (And.right (And.right (And.right ch))))])
    (rw [(mv-inst-res-c s b c j hbas2 hb hbb (And.left (hhome b j hb hd)) hfc)])
    (exact (href b j hb hd)))
  (case [false]
    (have io := (mv-inst-other s b c u (Nat.ne_of_beq_eq_false huc)))
    (rw [(And.left (And.right io))] at hu) (rw [(And.left (And.right (And.right (And.right io))))] at hd)
    (rw [(And.left io) (And.right (And.right (And.right (And.right io))))])
    (exact (href u j hu hd)))
  ;; own copies
  (intros u j hu hd hf)
  (rw [(And.left pp) (And.left (And.right (And.right pp)))])
  (cases huc (Nat.beq u c))
  (case [true] (rw [(Nat.eq_of_beq_eq_true huc) (And.left ch)] at hf) (exfalso) (exact (hf (Eq.refl 0))))
  (case [false]
    (have io := (mv-inst-other s b c u (Nat.ne_of_beq_eq_false huc)))
    (rw [(And.left (And.right io))] at hu) (rw [(And.left (And.right (And.right (And.right io))))] at hd)
    (rw [(And.left io)] at hf)
    (exact (hof u j hu hd hf))))

;; ---------------------------------------------------------------------------
;; Every reachable family state satisfies the invariant

;; the operations of a family, each with the preconditions the engine guarantees
(a/inductive MReach [s0 MSt] :in Prop :indices [s MSt]
  (start [s MSt] [e (= s s0)] :where [s])
  (write [s MSt] [w Nat] [i Nat] [y Nat] [r (MReach s0 s)]
         [ha (= ((:act s) w) true)] [hd (= (((:dom s) w) i) true)]
         [hp (Or (= (:ow ((:h s) ((:home s) i))) w) (Not (= (MW.fwd ((:fam s) w) i) 0)))]
         :where [(mv-write s w i y)])
  (copy [s MSt] [w Nat] [i Nat] [v Nat] [r (MReach s0 s)]
        [ha (= ((:act s) w) true)] [hd (= (((:dom s) w) i) true)] [hb (= ((:bas s) w) false)]
        [hno (Not (= (:ow ((:h s) ((:home s) i))) w))] [hf (= (MW.fwd ((:fam s) w) i) 0)]
        [hv (= (mv-res (:h s) (:home s) w ((:fam s) w) i) (Option.some Nat v))]
        :where [(mv-copy s w i v)])
  (create [s MSt] [w Nat] [i Nat] [y Nat] [r (MReach s0 s)]
          [ha (= ((:act s) w) true)] [hb (= ((:bas s) w) false)] [hf (= (MW.fwd ((:fam s) w) i) 0)]
          [hfr (forall [x :- Nat] (=> (= ((:act s) x) true) (= (((:dom s) x) i) false)))]
          :where [(mv-create s w i y)])
  (fork [s MSt] [w Nat] [c Nat] [t Nat] [b Bool] [r (MReach s0 s)] [hp (mv-fork-pre s w c t)]
        :where [(mv-fork s w c t b)])
  (inst [s MSt] [b Nat] [c Nat] [r (MReach s0 s)] [hp (mv-inst-pre s b c)] :where [(mv-inst s b c)])
  (prune [s MSt] [a Nat] [r (MReach s0 s)] :where [(mv-prune s a)])
  (finish [s MSt] [w Nat] [r (MReach s0 s)] [ha (= ((:act s) w) true)] :where [(mv-finish s w)])
  (drop [s MSt] [w Nat] [r (MReach s0 s)] :where [(mv-drop s w)])
  (collect [s MSt] [t Nat] [r (MReach s0 s)]
           [hfr (forall [u :- Nat] (=> (= ((:act s) u) true) (mv-allE (mv-fresh-for u t) (:lin ((:fam s) u)))))]
           :where [(mv-collect s t)]))

(a/defn mv-good [s :- MSt] Prop (And (mv-inv s) (And (mv-k-ownfwd s) (< 0 (:n s)))))

(a/theorem mv-reach-good [s0 :- MSt, s :- MSt]
  (=> (mv-good s0) (MReach s0 s) (mv-good s))
  (intros h0 hr)
  (induction hr)
  (case [start s1 e] (rw [e]) (exact h0))
  (case [write s1 w i y r ha hd hp ih]
    (simp only [mv-good] at ih)
    (exact (And.intro (mv-write-inv s1 w i y (And.left ih) ha hd hp)
             (And.intro (mv-ownfwd-write s1 w i y (And.left (And.right ih)))
                        (Eq.mpr (congrArg (LT.lt 0) (mv-write-n s1 w i y)) (And.right (And.right ih)))))))
  (case [copy s1 w i v r ha hd hb hno hf hv ih]
    (simp only [mv-good] at ih)
    (have pn := (And.left (mv-copy-proj s1 w i v)))
    (apply And.intro)
    (exact (mv-copy-inv s1 w i v (And.left ih) (And.right (And.right ih)) ha hd hb hno hf hv))
    (apply And.intro)
    (exact (mv-ownfwd-copy s1 w i v (And.left (And.right ih)) (And.left (And.right (And.right (And.right (And.left ih))))) ha hd hno))
    (rw [pn]) (omega))
  (case [create s1 w i y r ha hb hf hfr ih]
    (simp only [mv-good] at ih)
    (have pn := (And.left (mv-create-proj s1 w i y)))
    (apply And.intro)
    (exact (mv-create-inv s1 w i y (And.left ih) ha hb hfr))
    (apply And.intro)
    (exact (mv-ownfwd-create s1 w i y (And.left (And.right ih)) (And.left (And.right (And.right (And.right (And.left ih))))) hf hfr))
    (rw [pn]) (omega))
  (case [fork s1 w c t b r hp ih]
    (simp only [mv-good] at ih)
    (have fi := (mv-fork-inv s1 w c t b (And.left ih) (And.left (And.right ih)) hp))
    (apply And.intro) (exact (And.left fi))
    (apply And.intro) (exact (And.right fi))
    (rw [(And.left (And.right (mv-fork-proj s1 w c t b)))]) (exact (And.right (And.right ih))))
  (case [inst s1 b c r hp ih]
    (simp only [mv-good] at ih)
    (have fi := (mv-inst-inv s1 b c (And.left ih) (And.left (And.right ih)) hp))
    (apply And.intro) (exact (And.left fi))
    (apply And.intro) (exact (And.right fi))
    (rw [(And.left (And.right (mv-inst-proj s1 b c)))]) (exact (And.right (And.right ih))))
  (case [prune s1 a r ih]
    (simp only [mv-good] at ih)
    (apply And.intro) (exact (mv-prune-inv s1 a (And.left ih)))
    (apply And.intro) (exact (mv-ownfwd-prune s1 a (And.left (And.right ih))))
    (rw [(And.left (mv-prune-proj s1 a))]) (exact (And.right (And.right ih))))
  (case [finish s1 w r ha ih]
    (simp only [mv-good] at ih)
    (have fi := (mv-finish-inv s1 w (And.left ih) (And.left (And.right ih)) ha))
    (exact (And.intro (And.left fi) (And.intro (And.right fi) (And.right (And.right ih))))))
  (case [drop s1 w r ih]
    (simp only [mv-good] at ih)
    (have fi := (mv-drop-inv s1 w (And.left ih) (And.left (And.right ih))))
    (exact (And.intro (And.left fi) (And.intro (And.right fi) (And.right (And.right ih))))))
  (case [collect s1 t r hfr ih]
    (simp only [mv-good] at ih)
    (have fi := (mv-collect-inv s1 t (And.left ih) (And.left (And.right ih)) hfr))
    (exact (And.intro (And.left fi) (And.intro (And.right fi) (And.right (And.right ih)))))))

;; the start of a family: one root world 0, no rows (address 0 is reserved: 0 means \"no copy\")
(a/defn mv-init [] MSt
  (MSt.mk (fn [a :- Nat] (MRow.mk 0 0 0 0 (List.nil MVer))) 1 (fn [i :- Nat] 0)
          (fn [w :- Nat] (MW.mk 0 (fn [i :- Nat] 0) (List.nil MEnt) (List.nil MCell)))
          (fn [w :- Nat] (Nat.beq w 0)) (fn [w :- Nat] false) (fn [t :- Nat] 0)
          (fn [w :- Nat] (fn [i :- Nat] false)) (fn [w :- Nat] (fn [i :- Nat] 0))))

(a/theorem mv-init-good [] (mv-good mv-init)
  (simp only [mv-good])
  (apply And.intro)
  (apply And.intro)
  (intros a ha) (simp only [mv-init mv-vlt]) (exact (And.intro (Nat.le_refl 0) True.intro))
  (apply And.intro)
  (intros u j hne) (exact (absurd (Eq.refl 0) hne))
  (apply And.intro)
  (intros u hu) (simp only [mv-init mv-allE])
  (apply And.intro)
  (intros u j hu hd) (simp only [mv-init] at hd) (cases hd)
  (apply And.intro)
  (apply And.intro)
  (intros u hu) (simp only [mv-init mv-tl mv-allE])
  (intros u v x hu hv hne h1 h2) (simp only [mv-init mv-ht] at h1) (cases h1)
  (apply And.intro)
  (intros u hu hb) (simp only [mv-init] at hb) (cases hb)
  (intros u j hu hd) (simp only [mv-init] at hd) (cases hd)
  (apply And.intro)
  (intros u j hu hd hf) (simp only [mv-init] at hd) (cases hd)
  (simp only [mv-init]) (omega))

;; ===========================================================================
;; MAIN THEOREMS

;; OBLIGATION 1 (fork view) with 2 (barrier) and 3 (reclamation): in every family state the engine
;; reaches, every active world (root, fork at any depth, savepoint instance) reads every id of its
;; tables exactly as the value-copy model (spindel.v2.sys) has it: what it wrote itself, else the
;; state at its fork, never a newer write of an ancestor, never a missing version.
(a/theorem mv-refinement [s :- MSt, u :- Nat, i :- Nat]
  (=> (MReach mv-init s) (= ((:act s) u) true) (= (((:dom s) u) i) true)
      (= (mv-res (:h s) (:home s) u ((:fam s) u) i) (Option.some Nat (((:tab s) u) i))))
  (intros hr hu hd)
  (have g := (mv-reach-good mv-init s mv-init-good hr))
  (simp only [mv-good] at g)
  (have href := (And.right (And.right (And.right (And.right (And.right (And.right (And.left g))))))))
  (simp only [mv-ref] at href)
  (exact (href u i hu hd)))

;; `version-of` never throws \"MVCC: no version for a live fork\" in a reachable state
(a/theorem mv-no-missing-version [s :- MSt, u :- Nat, i :- Nat]
  (=> (MReach mv-init s) (= ((:act s) u) true) (= (((:dom s) u) i) true)
      (Not (= (mv-res (:h s) (:home s) u ((:fam s) u) i) (Option.none Nat))))
  (intros hr hu hd)
  (rw [(mv-refinement s u i hr hu hd)])
  (intro q) (cases q))

;; every lineage entry of an active world reads through a live token registered with its owner
(a/theorem mv-tokens-live [s :- MSt, u :- Nat]
  (=> (MReach mv-init s) (= ((:act s) u) true) (mv-allE (mv-ent-ok s) (:lin ((:fam s) u))))
  (intros hr hu)
  (have g := (mv-reach-good mv-init s mv-init-good hr))
  (simp only [mv-good] at g)
  (have hl := (And.left (And.right (And.right (And.left g)))))
  (simp only [mv-k-lin] at hl)
  (exact (hl u hu)))

;; ===========================================================================
;; OBLIGATION 4: the row monitor protocol (design §2.5, §7; spec answers A4, A5), interleaved
;;
;; One row, its owner and one fork reader at ordinal f < o (the owner's ordinal). Every step is
;; one thread's step; any interleaving is allowed.
;;   owner: o-acq (take the monitor, row stamped before o) | o-fast (row stamped o: no monitor,
;;          the `rv` fast path) | o-pres (under the monitor: `preserve!`) | o-rel | o-tear (an
;;          UNMONITORED partial change of the value: any number, any values) | o-done |
;;          o-prune (under the monitor; serialized with the owner, A4)
;;   reader (`version-of`): r-acq | r-stamp (reads the stamp) | r-copy (reads the value if the
;;          stamp is not newer than f, else the versions: a clone, never the live row) | r-rel
;; The reader's clone is not atomic: the owner may act between r-stamp and r-copy.
;; Claim: the reader's copy is the row's state at its fork, V0.

(a/structure MI [] (so Nat) (val Nat) (vers (List MVer)) (m Nat) (opc Nat) (rpc Nat) (ls Nat) (res (Option Nat)))

(a/defn mi-row [x :- MI] MRow (MRow.mk 0 0 (:so x) (:val x) (:vers x)))

(a/inductive MIReach [cs (List MCell) ts (=> Nat Nat) o Nat f Nat x0 MI] :in Prop :indices [x MI]
  (init [x MI] [e (= x x0)] :where [x])
  (oacq [x MI] [r (MIReach cs ts o f x0 x)] [h1 (= (:opc x) 0)] [h2 (= (:m x) 0)] [h3 (< (:so x) o)]
        :where [(MI.mk (:so x) (:val x) (:vers x) 1 1 (:rpc x) (:ls x) (:res x))])
  (ofast [x MI] [r (MIReach cs ts o f x0 x)] [h1 (= (:opc x) 0)] [h3 (= (:so x) o)]
         :where [(MI.mk (:so x) (:val x) (:vers x) (:m x) 3 (:rpc x) (:ls x) (:res x))])
  (opres [x MI] [r (MIReach cs ts o f x0 x)] [h1 (= (:opc x) 1)]
         :where [(MI.mk o (:val x) (:vers (mv-pres cs ts o (mi-row x))) (:m x) 2 (:rpc x) (:ls x) (:res x))])
  (orel [x MI] [r (MIReach cs ts o f x0 x)] [h1 (= (:opc x) 2)]
        :where [(MI.mk (:so x) (:val x) (:vers x) 0 3 (:rpc x) (:ls x) (:res x))])
  (otear [x MI] [z Nat] [r (MIReach cs ts o f x0 x)] [h1 (= (:opc x) 3)]
         :where [(MI.mk (:so x) z (:vers x) (:m x) 3 (:rpc x) (:ls x) (:res x))])
  (odone [x MI] [r (MIReach cs ts o f x0 x)] [h1 (= (:opc x) 3)]
         :where [(MI.mk (:so x) (:val x) (:vers x) (:m x) 0 (:rpc x) (:ls x) (:res x))])
  (oprune [x MI] [r (MIReach cs ts o f x0 x)] [h1 (= (:opc x) 0)] [h2 (= (:m x) 0)]
          :where [(MI.mk (:so x) (:val x) (mv-prune-vs cs ts (:vers x)) (:m x) (:opc x) (:rpc x) (:ls x) (:res x))])
  (racq [x MI] [r (MIReach cs ts o f x0 x)] [h1 (= (:rpc x) 0)] [h2 (= (:m x) 0)]
        :where [(MI.mk (:so x) (:val x) (:vers x) 2 (:opc x) 1 (:ls x) (:res x))])
  (rstamp [x MI] [r (MIReach cs ts o f x0 x)] [h1 (= (:rpc x) 1)]
          :where [(MI.mk (:so x) (:val x) (:vers x) (:m x) (:opc x) 2 (:so x) (:res x))])
  (rcopy [x MI] [r (MIReach cs ts o f x0 x)] [h1 (= (:rpc x) 2)]
         :where [(MI.mk (:so x) (:val x) (:vers x) (:m x) (:opc x) 3 (:ls x)
                        (if (Nat.ble (:ls x) f) (Option.some Nat (:val x)) (mv-look (:vers x) f)))])
  (rrel [x MI] [r (MIReach cs ts o f x0 x)] [h1 (= (:rpc x) 3)]
        :where [(MI.mk (:so x) (:val x) (:vers x) 0 (:opc x) 4 (:ls x) (:res x))]))

;; the protocol invariant over the fields of the state
(a/defn mi-inv-f [o :- Nat, f :- Nat, V0 :- Nat, so :- Nat, val :- Nat, vers :- (List MVer), m :- Nat, opc :- Nat,
                  rpc :- Nat, ls :- Nat, res :- (Option Nat)] Prop
  (And (=> (<= 1 opc) (<= opc 2) (= m 1))                                   ; owner in its critical section
  (And (=> (<= 1 rpc) (<= rpc 3) (= m 2))                                   ; reader in its critical section
  (And (<= so o)
  (And (= (mv-vlt so vers) true)
  (And (=> (<= so f) (And (= val V0) (<= opc 1)))                           ; not restamped: unchanged
  (And (=> (< f so) (= (mv-look vers f) (Option.some Nat V0)))              ; restamped: the version is kept
  (And (=> (<= 2 rpc) (<= rpc 3) (= ls so))                                 ; the stamp the reader saw holds
  (And (=> (<= 3 rpc) (= res (Option.some Nat V0)))                         ; the reader's copy
       (=> (<= 2 opc) (= so o)))))))))))                                     ; the owner changes only restamped rows

(a/defn mi-inv [o :- Nat, f :- Nat, V0 :- Nat, x :- MI] Prop
  (mi-inv-f o f V0 (:so x) (:val x) (:vers x) (:m x) (:opc x) (:rpc x) (:ls x) (:res x)))

(a/theorem mi-oacq [o :- Nat, f :- Nat, V0 :- Nat, so :- Nat, val :- Nat, vers :- (List MVer), m :- Nat, opc :- Nat,
                    rpc :- Nat, ls :- Nat, res :- (Option Nat)]
  (=> (mi-inv-f o f V0 so val vers m opc rpc ls res) (= opc 0) (= m 0)
      (mi-inv-f o f V0 so val vers 1 1 rpc ls res))
  (intros h ho hm)
  (obtain [a1 a2 a3 a4 a5 a6 a7 a8 a9] := h)
  (unfold mi-inv-f)
  (apply And.intro) (intros q1 q2) (rfl)
  (apply And.intro) (intros q1 q2) (have q := (a2 q1 q2)) (omega)
  (apply And.intro) (exact a3)
  (apply And.intro) (exact a4)
  (apply And.intro) (intro q) (have p := (a5 q)) (exact (And.intro (And.left p) (Nat.le_refl 1)))
  (apply And.intro) (exact a6)
  (apply And.intro) (exact a7)
  (apply And.intro) (exact a8)
  (intro q) (omega))

(a/theorem mi-ofast [o :- Nat, f :- Nat, V0 :- Nat, so :- Nat, val :- Nat, vers :- (List MVer), m :- Nat, opc :- Nat,
                     rpc :- Nat, ls :- Nat, res :- (Option Nat)]
  (=> (< f o) (mi-inv-f o f V0 so val vers m opc rpc ls res) (= opc 0) (= so o)
      (mi-inv-f o f V0 so val vers m 3 rpc ls res))
  (intros hfo h ho hs)
  (obtain [a1 a2 a3 a4 a5 a6 a7 a8 a9] := h)
  (unfold mi-inv-f)
  (apply And.intro) (intros q1 q2) (omega)
  (apply And.intro) (exact a2)
  (apply And.intro) (exact a3)
  (apply And.intro) (exact a4)
  (apply And.intro) (intro q) (omega)
  (apply And.intro) (exact a6)
  (apply And.intro) (exact a7)
  (apply And.intro) (exact a8)
  (intro q) (exact hs))

(a/theorem mi-pres-so [cs :- (List MCell), ts :- (=> Nat Nat), o :- Nat, x :- MRow]
  (=> (<= (:so x) o) (= (:so (mv-pres cs ts o x)) o))
  (intro h)
  (cases hb (Nat.blt (:so x) o))
  (case [true] (simp only [mv-pres hb]))
  (case [false] (have q := (mv-blt-f _ _ hb)) (simp only [mv-pres hb]) (omega)))

;; the version a fork at f < o reads survives `preserve!` (the barrier lemma, read side)
(a/theorem mi-pres-look [cs :- (List MCell), ts :- (=> Nat Nat), o :- Nat, f :- Nat, x :- MRow, V0 :- Nat]
  (=> (< f o) (<= (:so x) o) (= (mv-vlt (:so x) (:vers x)) true) (= (mv-live-in cs ts f f) true)
      (= (mv-vat x f) (Option.some Nat V0))
      (= (mv-look (:vers (mv-pres cs ts o x)) f) (Option.some Nat V0)))
  (intros hfo hso hv hl hx)
  (have hp := (mv-vat-pres cs ts o x (:val x) f hfo hso hv hl))
  (rw [hx] at hp)
  (have hpo := (mi-pres-so cs ts o x hso))
  (have hb (= (Nat.ble (:so (mv-setv (mv-pres cs ts o x) (:val x))) f) false))
  (simp only [mv-setv]) (rw [hpo]) (exact (mv-ble-of-lt o f hfo))
  (simp only [mv-vat hb] at hp)
  (exact hp))

(a/theorem mi-opres [cs :- (List MCell), ts :- (=> Nat Nat), o :- Nat, f :- Nat, V0 :- Nat, so :- Nat, val :- Nat,
                     vers :- (List MVer), m :- Nat, opc :- Nat, rpc :- Nat, ls :- Nat, res :- (Option Nat)]
  (=> (< f o) (= (mv-live-in cs ts f f) true) (mi-inv-f o f V0 so val vers m opc rpc ls res) (= opc 1)
      (mi-inv-f o f V0 o val (:vers (mv-pres cs ts o (MRow.mk 0 0 so val vers))) m 2 rpc ls res))
  (intros hfo hl h ho)
  (obtain [a1 a2 a3 a4 a5 a6 a7 a8 a9] := h)
  (have hm (= m 1)) (apply a1) (omega) (omega)
  (have hx (= (mv-vat (MRow.mk 0 0 so val vers) f) (Option.some Nat V0)))
  (cases hsf (Nat.ble so f))
  (case [true]
    (have q := (a5 (Nat.le_of_ble_eq_true hsf)))
    (simp only [mv-vat hsf]) (rw [(And.left q)]))
  (case [false]
    (simp only [mv-vat hsf]) (exact (a6 (mv-ble-f so f hsf))))
  (have hpv := (mv-pres-row cs ts o (MRow.mk 0 0 so val vers) val a3 a4))
  (have hpo := (mi-pres-so cs ts o (MRow.mk 0 0 so val vers) a3))
  (unfold mi-inv-f)
  (apply And.intro) (intros q1 q2) (exact hm)
  (apply And.intro) (intros q1 q2) (have q := (a2 q1 q2)) (omega)
  (apply And.intro) (exact (Nat.le_refl o))
  (apply And.intro)
  (have hv2 := (And.right hpv)) (simp only [mv-setv] at hv2) (rw [hpo] at hv2) (exact hv2)
  (apply And.intro) (intro q) (omega)
  (apply And.intro) (intro q) (exact (mi-pres-look cs ts o f (MRow.mk 0 0 so val vers) V0 hfo a3 a4 hl hx))
  (apply And.intro) (intros q1 q2) (have q0 (<= 1 rpc)) (omega) (have q := (a2 q0 q2)) (omega)
  (apply And.intro) (exact a8)
  (intro q) (rfl))

(a/theorem mi-orel [o :- Nat, f :- Nat, V0 :- Nat, so :- Nat, val :- Nat, vers :- (List MVer), m :- Nat, opc :- Nat,
                    rpc :- Nat, ls :- Nat, res :- (Option Nat)]
  (=> (< f o) (mi-inv-f o f V0 so val vers m opc rpc ls res) (= opc 2)
      (mi-inv-f o f V0 so val vers 0 3 rpc ls res))
  (intros hfo h ho)
  (obtain [a1 a2 a3 a4 a5 a6 a7 a8 a9] := h)
  (have hm (= m 1)) (apply a1) (omega) (omega)
  (have hs (= so o)) (apply a9) (omega)
  (unfold mi-inv-f)
  (apply And.intro) (intros q1 q2) (omega)
  (apply And.intro) (intros q1 q2) (have q := (a2 q1 q2)) (omega)
  (apply And.intro) (exact a3)
  (apply And.intro) (exact a4)
  (apply And.intro) (intro q) (omega)
  (apply And.intro) (exact a6)
  (apply And.intro) (intros q1 q2) (have q0 (<= 1 rpc)) (omega) (have q := (a2 q0 q2)) (omega)
  (apply And.intro) (exact a8)
  (intro q) (exact hs))

;; an unmonitored change of a restamped row (owner, `rv` fast path) disturbs no reader
(a/theorem mi-otear [o :- Nat, f :- Nat, V0 :- Nat, so :- Nat, val :- Nat, vers :- (List MVer), m :- Nat, opc :- Nat,
                     rpc :- Nat, ls :- Nat, res :- (Option Nat), z :- Nat]
  (=> (< f o) (mi-inv-f o f V0 so val vers m opc rpc ls res) (= opc 3)
      (mi-inv-f o f V0 so z vers m 3 rpc ls res))
  (intros hfo h ho)
  (obtain [a1 a2 a3 a4 a5 a6 a7 a8 a9] := h)
  (have hs (= so o)) (apply a9) (omega)
  (unfold mi-inv-f)
  (apply And.intro) (intros q1 q2) (omega)
  (apply And.intro) (exact a2)
  (apply And.intro) (exact a3)
  (apply And.intro) (exact a4)
  (apply And.intro) (intro q) (omega)
  (apply And.intro) (exact a6)
  (apply And.intro) (exact a7)
  (apply And.intro) (exact a8)
  (intro q) (exact hs))

(a/theorem mi-odone [o :- Nat, f :- Nat, V0 :- Nat, so :- Nat, val :- Nat, vers :- (List MVer), m :- Nat, opc :- Nat,
                     rpc :- Nat, ls :- Nat, res :- (Option Nat)]
  (=> (< f o) (mi-inv-f o f V0 so val vers m opc rpc ls res) (= opc 3)
      (mi-inv-f o f V0 so val vers m 0 rpc ls res))
  (intros hfo h ho)
  (obtain [a1 a2 a3 a4 a5 a6 a7 a8 a9] := h)
  (have hs (= so o)) (apply a9) (omega)
  (unfold mi-inv-f)
  (apply And.intro) (intros q1 q2) (omega)
  (apply And.intro) (exact a2)
  (apply And.intro) (exact a3)
  (apply And.intro) (exact a4)
  (apply And.intro) (intro q) (omega)
  (apply And.intro) (exact a6)
  (apply And.intro) (exact a7)
  (apply And.intro) (exact a8)
  (intro q) (omega))

(a/theorem mi-oprune [cs :- (List MCell), ts :- (=> Nat Nat), o :- Nat, f :- Nat, V0 :- Nat, so :- Nat, val :- Nat,
                      vers :- (List MVer), m :- Nat, opc :- Nat, rpc :- Nat, ls :- Nat, res :- (Option Nat)]
  (=> (= (mv-live-in cs ts f f) true) (mi-inv-f o f V0 so val vers m opc rpc ls res) (= opc 0) (= m 0)
      (mi-inv-f o f V0 so val (mv-prune-vs cs ts vers) m opc rpc ls res))
  (intros hl h ho hm)
  (obtain [a1 a2 a3 a4 a5 a6 a7 a8 a9] := h)
  (unfold mi-inv-f)
  (apply And.intro) (exact a1)
  (apply And.intro) (exact a2)
  (apply And.intro) (exact a3)
  (apply And.intro) (exact (mv-vlt-prune cs ts so vers a4))
  (apply And.intro) (exact a5)
  (apply And.intro) (intro q) (rw [(mv-look-prune cs ts f vers hl)]) (exact (a6 q))
  (apply And.intro) (exact a7)
  (apply And.intro) (exact a8)
  (exact a9))

(a/theorem mi-racq [o :- Nat, f :- Nat, V0 :- Nat, so :- Nat, val :- Nat, vers :- (List MVer), m :- Nat, opc :- Nat,
                    rpc :- Nat, ls :- Nat, res :- (Option Nat)]
  (=> (mi-inv-f o f V0 so val vers m opc rpc ls res) (= rpc 0) (= m 0)
      (mi-inv-f o f V0 so val vers 2 opc 1 ls res))
  (intros h hr hm)
  (obtain [a1 a2 a3 a4 a5 a6 a7 a8 a9] := h)
  (unfold mi-inv-f)
  (apply And.intro) (intros q1 q2) (have q := (a1 q1 q2)) (omega)
  (apply And.intro) (intros q1 q2) (rfl)
  (apply And.intro) (exact a3)
  (apply And.intro) (exact a4)
  (apply And.intro) (exact a5)
  (apply And.intro) (exact a6)
  (apply And.intro) (intros q1 q2) (omega)
  (apply And.intro) (intro q) (omega)
  (exact a9))

(a/theorem mi-rstamp [o :- Nat, f :- Nat, V0 :- Nat, so :- Nat, val :- Nat, vers :- (List MVer), m :- Nat, opc :- Nat,
                      rpc :- Nat, ls :- Nat, res :- (Option Nat)]
  (=> (mi-inv-f o f V0 so val vers m opc rpc ls res) (= rpc 1)
      (mi-inv-f o f V0 so val vers m opc 2 so res))
  (intros h hr)
  (obtain [a1 a2 a3 a4 a5 a6 a7 a8 a9] := h)
  (have hm (= m 2)) (apply a2) (omega) (omega)
  (unfold mi-inv-f)
  (apply And.intro) (exact a1)
  (apply And.intro) (intros q1 q2) (exact hm)
  (apply And.intro) (exact a3)
  (apply And.intro) (exact a4)
  (apply And.intro) (exact a5)
  (apply And.intro) (exact a6)
  (apply And.intro) (intros q1 q2) (rfl)
  (apply And.intro) (intro q) (omega)
  (exact a9))

;; the reader's copy: the stamp it saw is the row's stamp (the owner cannot restamp while the
;; reader holds the monitor), so it reads the unchanged value or the kept version
(a/theorem mi-rcopy [o :- Nat, f :- Nat, V0 :- Nat, so :- Nat, val :- Nat, vers :- (List MVer), m :- Nat, opc :- Nat,
                     rpc :- Nat, ls :- Nat, res :- (Option Nat)]
  (=> (mi-inv-f o f V0 so val vers m opc rpc ls res) (= rpc 2)
      (mi-inv-f o f V0 so val vers m opc 3 ls
                (if (Nat.ble ls f) (Option.some Nat val) (mv-look vers f))))
  (intros h hr)
  (obtain [a1 a2 a3 a4 a5 a6 a7 a8 a9] := h)
  (have hm (= m 2)) (apply a2) (omega) (omega)
  (have hls (= ls so)) (apply a7) (omega) (omega)
  (unfold mi-inv-f)
  (apply And.intro) (exact a1)
  (apply And.intro) (intros q1 q2) (exact hm)
  (apply And.intro) (exact a3)
  (apply And.intro) (exact a4)
  (apply And.intro) (exact a5)
  (apply And.intro) (exact a6)
  (apply And.intro) (intros q1 q2) (exact hls)
  (apply And.intro)
  (intro q)
  (rw [hls])
  (cases hsf (Nat.ble so f))
  (case [true] (simp only [hsf]) (rw [(And.left (a5 (Nat.le_of_ble_eq_true hsf)))]))
  (case [false] (simp only [hsf]) (exact (a6 (mv-ble-f so f hsf))))
  (exact a9))

(a/theorem mi-rrel [o :- Nat, f :- Nat, V0 :- Nat, so :- Nat, val :- Nat, vers :- (List MVer), m :- Nat, opc :- Nat,
                    rpc :- Nat, ls :- Nat, res :- (Option Nat)]
  (=> (mi-inv-f o f V0 so val vers m opc rpc ls res) (= rpc 3)
      (mi-inv-f o f V0 so val vers 0 opc 4 ls res))
  (intros h hr)
  (obtain [a1 a2 a3 a4 a5 a6 a7 a8 a9] := h)
  (have hm (= m 2)) (apply a2) (omega) (omega)
  (unfold mi-inv-f)
  (apply And.intro) (intros q1 q2) (have q := (a1 q1 q2)) (omega)
  (apply And.intro) (intros q1 q2) (omega)
  (apply And.intro) (exact a3)
  (apply And.intro) (exact a4)
  (apply And.intro) (exact a5)
  (apply And.intro) (exact a6)
  (apply And.intro) (intros q1 q2) (omega)
  (apply And.intro) (intro q) (have q3 (<= 3 rpc)) (omega) (exact (a8 q3))
  (exact a9))

(a/theorem mi-reach-inv [cs :- (List MCell), ts :- (=> Nat Nat), o :- Nat, f :- Nat, V0 :- Nat, x0 :- MI, x :- MI]
  (=> (< f o) (= (mv-live-in cs ts f f) true) (mi-inv o f V0 x0) (MIReach cs ts o f x0 x) (mi-inv o f V0 x))
  (intros hfo hl h0 hr)
  (induction hr)
  (case [init y e] (rw [e]) (exact h0))
  (case [oacq y r h1 h2 h3 ih] (exact (mi-oacq o f V0 _ _ _ _ _ _ _ _ ih h1 h2)))
  (case [ofast y r h1 h3 ih] (exact (mi-ofast o f V0 _ _ _ _ _ _ _ _ hfo ih h1 h3)))
  (case [opres y r h1 ih] (exact (mi-opres cs ts o f V0 _ _ _ _ _ _ _ _ hfo hl ih h1)))
  (case [orel y r h1 ih] (exact (mi-orel o f V0 _ _ _ _ _ _ _ _ hfo ih h1)))
  (case [otear y z r h1 ih] (exact (mi-otear o f V0 _ _ _ _ _ _ _ _ z hfo ih h1)))
  (case [odone y r h1 ih] (exact (mi-odone o f V0 _ _ _ _ _ _ _ _ hfo ih h1)))
  (case [oprune y r h1 h2 ih] (exact (mi-oprune cs ts o f V0 _ _ _ _ _ _ _ _ hl ih h1 h2)))
  (case [racq y r h1 h2 ih] (exact (mi-racq o f V0 _ _ _ _ _ _ _ _ ih h1 h2)))
  (case [rstamp y r h1 ih] (exact (mi-rstamp o f V0 _ _ _ _ _ _ _ _ ih h1)))
  (case [rcopy y r h1 ih] (exact (mi-rcopy o f V0 _ _ _ _ _ _ _ _ ih h1)))
  (case [rrel y r h1 ih] (exact (mi-rrel o f V0 _ _ _ _ _ _ _ _ ih h1))))

;; OBLIGATION 4: under every interleaving of the owner (barrier under the monitor, then
;; unmonitored changes; pruning serialized with it) and a fork reader (a non-atomic clone under the
;; monitor), a reader that has taken its copy holds the row's state at its fork
(a/theorem mi-protocol [cs :- (List MCell), ts :- (=> Nat Nat), o :- Nat, f :- Nat, V0 :- Nat, x0 :- MI, x :- MI]
  (=> (< f o) (= (mv-live-in cs ts f f) true) (mi-inv o f V0 x0) (MIReach cs ts o f x0 x)
      (<= 3 (:rpc x)) (= (:res x) (Option.some Nat V0)))
  (intros hfo hl h0 hr hrpc)
  (have q := (mi-reach-inv cs ts o f V0 x0 x hfo hl h0 hr))
  (obtain [a1 a2 a3 a4 a5 a6 a7 a8 a9] := q)
  (exact (a8 hrpc)))

;; the starts the claim covers: the row unchanged since the fork, or already holding its version
(a/theorem mi-start [o :- Nat, f :- Nat, V0 :- Nat, so :- Nat, vers :- (List MVer)]
  (=> (<= so o) (= (mv-vlt so vers) true)
      (Or (<= so f) (= (mv-look vers f) (Option.some Nat V0)))
      (mi-inv o f V0 (MI.mk so V0 vers 0 0 0 0 (Option.none Nat))))
  (intros hso hv hst)
  (unfold mi-inv mi-inv-f)
  (apply And.intro) (intros q1 q2) (omega)
  (apply And.intro) (intros q1 q2) (omega)
  (apply And.intro) (exact hso)
  (apply And.intro) (exact hv)
  (apply And.intro) (intro q) (exact (And.intro (Eq.refl V0) (Nat.zero_le 1)))
  (apply And.intro) (intro q)
  (cases hst) (case [inl h1] (exfalso) (omega)) (case [inr h2] (exact h2))
  (apply And.intro) (intros q1 q2) (omega)
  (apply And.intro) (intro q) (omega)
  (intro q) (omega))
