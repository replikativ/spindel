(ns spindel.v2.cow
  "Layer 2, physical: copy-on-write rows (engine `rows.cljc`, `rv`, `resolve-row`, `own-copy!`,
  `fork-world*`), kernel-checked (Init only). See notes/LAYER2.md.

  State: a heap `h : address -> PRow` (logical id, owner epoch, value, references as addresses), the
  next free address `n`, `orig : id -> address` (the first row of an id) and per world a `PView`
  (epoch, forward map id -> address of its copy, 0 = none) with a domain `d : id -> Bool`.
  `ver orig v i` is the address of the version of i the world reads; `view h orig v i` is the abstract
  row (value, referenced ids). References abstract to ids, so path compression is invisible.

  Operations: `copy-heap`/`copy-view` (own-copy!), `write-heap`, `rotate` (a fork gives both worlds
  a fresh epoch and keeps the forward map), `alloc-heap`.

  Per world: `wf` (versions exist, carry their id, references are valid addresses), `own` (a row
  carrying the world's epoch is the world's version of its id), `ro` (a stored reference without a
  forward entry is the original row). Between worlds: `excl` (a world sees no row carrying a given
  epoch). A family (`fam`, `dom`, `live` indexed by Nat): `fin1` (every live world has wf, own, ro),
  `fin2` (live worlds have distinct epochs and exclude each other).

  Theorems:
    views      fork-view, copy-view-self/-other, write-view-self/-other, alloc-view-other
               (a fork, a copy and an allocation change no view; a write changes one row of one world)
    engine     rv-fast (the epoch check reads the right row), rv-slow (so does `resolve-row`)
    isolation  write-isolated, fam-write-isolated
    family     fin1/fin2 kept by copy, write, reepoch + spawn (= fork), alloc, release; fin1-empty,
               fin2-single (the start)

  Not here: the storage bound F5 (in this model the rows a family can read are the images of `ver`
  over the live domains, so the bound is immediate), removal of forward entries."
  (:require [ansatz.core :as a]))

(a/load-init!)

;; a physical row: logical id, owner epoch, opaque value, references (addresses)
(a/structure PRow [] (id Nat) (epoch Nat) (val Nat) (refs (List Nat)))

;; function update at a Nat key
(a/defn fupd [A :- Type :implicit, f :- (=> Nat A), k :- Nat, v :- A] (=> Nat A)
  (fn [x :- Nat] (if (Nat.beq x k) v (f x))))

(a/theorem nbeq-ne [a :- Nat, b :- Nat] (=> (Not (= a b)) (= (Nat.beq a b) false))
  (intro hne)
  (cases hab (Nat.beq a b))
  (rfl)
  (exact (absurd (Nat.eq_of_beq_eq_true hab) hne)))

(a/theorem fupd-same [A :- Type :implicit, f :- (=> Nat A), k :- Nat, v :- A]
  (= (fupd f k v k) v)
  (simp only [fupd Nat.beq_refl]))

(a/theorem fupd-other [A :- Type :implicit, f :- (=> Nat A), k :- Nat, v :- A, x :- Nat]
  (=> (Not (= x k)) (= (fupd f k v x) (f x)))
  (intro h) (simp only [fupd (nbeq-ne x k h)]))

;; a world's physical view: its epoch and its forward map (id -> address of its copy, 0 = none)
(a/structure PView [] (epoch Nat) (fwd (=> Nat Nat)))

;; the address of the version of logical row i that the view sees
(a/defn ver [orig :- (=> Nat Nat), v :- PView, i :- Nat] Nat
  (if (Nat.beq (PView.fwd v i) 0) (orig i) (PView.fwd v i)))

;; abstract row: value and referenced logical ids
(a/structure ARow [] (val Nat) (rids (List Nat)))

(a/defn rids [h :- (=> Nat PRow), rs :- (List Nat)] (List Nat)
  (match rs [nil (List.nil Nat)] [(cons r t) (List.cons Nat (:id (h r)) (rids h t))]))

(a/defn content [h :- (=> Nat PRow), a :- Nat] ARow
  (ARow.mk (:val (h a)) (rids h (:refs (h a)))))

;; the abstract table a world reads: logical id -> abstract row
(a/defn view [h :- (=> Nat PRow), orig :- (=> Nat Nat), v :- PView, i :- Nat] ARow
  (content h (ver orig v i)))

;; ---------------------------------------------------------------------------
;; Frame lemmas for the abstraction

(a/defn all-lt [n :- Nat, rs :- (List Nat)] Bool
  (match rs [nil true] [(cons r t) (Bool.and (Nat.blt r n) (all-lt n t))]))

(a/theorem rids-frame [h :- (=> Nat PRow), h2 :- (=> Nat PRow), rs :- (List Nat)]
  (=> (forall [r :- Nat] (= (:id (h2 r)) (:id (h r)))) (= (rids h2 rs) (rids h rs)))
  (intro hid)
  (induction rs)
  (case [nil] (simp only [rids]))
  (case [cons r t ih] (simp only [rids ih (hid r)])))

(a/theorem rids-frame-lt [h :- (=> Nat PRow), h2 :- (=> Nat PRow), n :- Nat, rs :- (List Nat)]
  (=> (forall [r :- Nat] (=> (< r n) (= (:id (h2 r)) (:id (h r)))))
      (= (all-lt n rs) true)
      (= (rids h2 rs) (rids h rs)))
  (intro hid)
  (induction rs)
  (case [nil] (intro hl) (simp only [rids]))
  (case [cons r t ih]
    (intro hl)
    (simp only [all-lt Bool.and_eq_true Nat.blt_eq] at hl)
    (simp only [rids (ih (And.right hl)) (hid r (And.left hl))])))

;; ---------------------------------------------------------------------------
;; Operations

;; own-copy! : the view's version of i is cloned to the fresh address n with the view's epoch
(a/defn copy-heap [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, v :- PView, i :- Nat] (=> Nat PRow)
  (fupd h n (PRow.mk (:id (h (ver orig v i))) (:epoch v) (:val (h (ver orig v i))) (:refs (h (ver orig v i))))))

(a/defn copy-view [n :- Nat, v :- PView, i :- Nat] PView
  (PView.mk (:epoch v) (fupd (PView.fwd v) i n)))

;; a write to the row at address a (the engine writes only rows the world owns)
(a/defn write-heap [h :- (=> Nat PRow), a :- Nat, x :- Nat, rs :- (List Nat)] (=> Nat PRow)
  (fupd h a (PRow.mk (:id (h a)) (:epoch (h a)) x rs)))

;; fork-world* : both worlds take a fresh epoch and keep the forward map
(a/defn rotate [v :- PView, e :- Nat] PView (PView.mk e (PView.fwd v)))

;; ---------------------------------------------------------------------------
;; P-fork: epoch rotation changes no view

(a/theorem fork-view [h :- (=> Nat PRow), orig :- (=> Nat Nat), v :- PView, e :- Nat, i :- Nat]
  (= (view h orig (rotate v e) i) (view h orig v i))
  (rfl))

;; ---------------------------------------------------------------------------
;; P-view: copy on access changes no view

(a/theorem copy-id-lt [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, v :- PView, i :- Nat, r :- Nat]
  (=> (< r n) (= (:id (copy-heap h orig n v i r)) (:id (h r))))
  (intro hl)
  (have hne (Not (= r n))) (omega)
  (simp only [copy-heap fupd (nbeq-ne r n hne)]))

(a/theorem content-copy-old [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, v :- PView, i :- Nat, a :- Nat]
  (=> (< a n) (= (all-lt n (:refs (h a))) true)
      (= (content (copy-heap h orig n v i) a) (content h a)))
  (intros hl hr)
  (have hne (Not (= a n))) (omega)
  (have e (= (copy-heap h orig n v i a) (h a))) (simp only [copy-heap fupd (nbeq-ne a n hne)])
  (simp only [content e])
  (rw [(rids-frame-lt h (copy-heap h orig n v i) n (:refs (h a)) (fn [r :- Nat] (copy-id-lt h orig n v i r)) hr)]))

(a/theorem content-copy-new [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, v :- PView, i :- Nat]
  (=> (= (all-lt n (:refs (h (ver orig v i)))) true)
      (= (content (copy-heap h orig n v i) n) (content h (ver orig v i))))
  (intro hr)
  (have e (= (copy-heap h orig n v i n)
             (PRow.mk (:id (h (ver orig v i))) (:epoch v) (:val (h (ver orig v i))) (:refs (h (ver orig v i))))))
  (simp only [copy-heap fupd-same])
  (simp only [content e])
  (rw [(rids-frame-lt h (copy-heap h orig n v i) n (:refs (h (ver orig v i))) (fn [r :- Nat] (copy-id-lt h orig n v i r)) hr)]))

(a/theorem ver-copy-self [orig :- (=> Nat Nat), n :- Nat, v :- PView, i :- Nat]
  (=> (< 0 n) (= (ver orig (copy-view n v i) i) n))
  (intro hp)
  (have hz (= (Nat.beq n 0) false)) (apply nbeq-ne) (omega)
  (simp only [ver copy-view fupd-same hz]))

(a/theorem ver-copy-other [orig :- (=> Nat Nat), n :- Nat, v :- PView, i :- Nat, j :- Nat]
  (=> (Not (= j i)) (= (ver orig (copy-view n v i) j) (ver orig v j)))
  (intro hne)
  (simp only [ver copy-view (fupd-other (PView.fwd v) i n j hne)]))

;; the copying world reads the same table after the copy
(a/theorem copy-view-self [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, v :- PView, i :- Nat, j :- Nat]
  (=> (< 0 n) (< (ver orig v j) n) (= (all-lt n (:refs (h (ver orig v j)))) true)
      (= (view (copy-heap h orig n v i) orig (copy-view n v i) j) (view h orig v j)))
  (intros hp hl hr)
  (cases hji (Nat.beq j i))
  (case [false]
    (have hne (Not (= j i))) (exact (Nat.ne_of_beq_eq_false hji))
    (simp only [view (ver-copy-other orig n v i j hne)])
    (exact (content-copy-old h orig n v i (ver orig v j) hl hr)))
  (case [true]
    (have e (= j i)) (exact (Nat.eq_of_beq_eq_true hji))
    (subst e)
    (simp only [view (ver-copy-self orig n v j hp)])
    (exact (content-copy-new h orig n v j hr))))

;; every other world reads the same table after the copy
(a/theorem copy-view-other [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, v :- PView, i :- Nat,
                            u :- PView, j :- Nat]
  (=> (< (ver orig u j) n) (= (all-lt n (:refs (h (ver orig u j)))) true)
      (= (view (copy-heap h orig n v i) orig u j) (view h orig u j)))
  (intros hl hr)
  (simp only [view])
  (exact (content-copy-old h orig n v i (ver orig u j) hl hr)))

;; ---------------------------------------------------------------------------
;; P-write: a write changes the written row and nothing else

(a/theorem write-id [h :- (=> Nat PRow), a :- Nat, x :- Nat, rs :- (List Nat), r :- Nat]
  (= (:id (write-heap h a x rs r)) (:id (h r)))
  (cases hra (Nat.beq r a))
  (case [false] (simp only [write-heap fupd hra]))
  (case [true]
    (have e (= r a)) (exact (Nat.eq_of_beq_eq_true hra))
    (subst e)
    (simp only [write-heap fupd-same])))

(a/theorem content-write-other [h :- (=> Nat PRow), a :- Nat, x :- Nat, rs :- (List Nat), b :- Nat]
  (=> (Not (= b a)) (= (content (write-heap h a x rs) b) (content h b)))
  (intro hne)
  (have e (= (write-heap h a x rs b) (h b))) (simp only [write-heap fupd (nbeq-ne b a hne)])
  (simp only [content e])
  (rw [(rids-frame h (write-heap h a x rs) (:refs (h b)) (fn [r :- Nat] (write-id h a x rs r)))]))

(a/theorem content-write-self [h :- (=> Nat PRow), a :- Nat, x :- Nat, rs :- (List Nat)]
  (= (content (write-heap h a x rs) a) (ARow.mk x (rids h rs)))
  (have e (= (write-heap h a x rs a) (PRow.mk (:id (h a)) (:epoch (h a)) x rs))) (simp only [write-heap fupd-same])
  (simp only [content e])
  (rw [(rids-frame h (write-heap h a x rs) rs (fn [r :- Nat] (write-id h a x rs r)))]))

;; a view that sees no row with the written row's epoch reads the same table
(a/theorem write-view-other [h :- (=> Nat PRow), orig :- (=> Nat Nat), a :- Nat, x :- Nat, rs :- (List Nat),
                             u :- PView, j :- Nat]
  (=> (Not (= (:epoch (h (ver orig u j))) (:epoch (h a))))
      (= (view (write-heap h a x rs) orig u j) (view h orig u j)))
  (intro hne)
  (have hb (Not (= (ver orig u j) a))) (intro e) (rw [e] at hne) (exact (hne (Eq.refl _)))
  (simp only [view])
  (exact (content-write-other h a x rs (ver orig u j) hb)))

;; the writing world reads the new row at i and the same table elsewhere
(a/theorem write-view-self [h :- (=> Nat PRow), orig :- (=> Nat Nat), v :- PView, i :- Nat, x :- Nat, rs :- (List Nat)]
  (= (view (write-heap h (ver orig v i) x rs) orig v i) (ARow.mk x (rids h rs)))
  (simp only [view])
  (exact (content-write-self h (ver orig v i) x rs)))

;; ---------------------------------------------------------------------------
;; Invariants. `d` is the world's domain (the logical ids it has), `n` the next free address.

;; every row of the domain has a version at a valid address, with the right id and valid references
(a/defn wf [h :- (=> Nat PRow), n :- Nat, orig :- (=> Nat Nat), v :- PView, d :- (=> Nat Bool)] Prop
  (forall [j :- Nat] (=> (= (d j) true)
    (And (< (ver orig v j) n)
         (And (= (:id (h (ver orig v j))) j)
              (= (all-lt n (:refs (h (ver orig v j)))) true))))))

;; a row carrying the world's epoch is the world's version of its id (the fast path of `rv`)
(a/defn own [h :- (=> Nat PRow), n :- Nat, orig :- (=> Nat Nat), v :- PView, d :- (=> Nat Bool)] Prop
  (forall [a :- Nat] (=> (< a n) (= (:epoch (h a)) (:epoch v)) (= (d (:id (h a))) true)
                         (= a (ver orig v (:id (h a)))))))

;; world u (domain du) sees no row carrying epoch e
(a/defn excl [h :- (=> Nat PRow), orig :- (=> Nat Nat), e :- Nat, u :- PView, du :- (=> Nat Bool)] Prop
  (forall [j :- Nat] (=> (= (du j) true) (Not (= (:epoch (h (ver orig u j))) e)))))

(a/theorem all-lt-succ [n :- Nat, rs :- (List Nat)]
  (=> (= (all-lt n rs) true) (= (all-lt (+ n 1) rs) true))
  (induction rs)
  (case [nil] (intro h) (simp only [all-lt]))
  (case [cons r t ih]
    (intro h)
    (simp only [all-lt Bool.and_eq_true Nat.blt_eq] at h)
    (simp only [all-lt Bool.and_eq_true Nat.blt_eq])
    (have q := (And.left h))
    (have q2 (< r (+ n 1))) (omega)
    (exact (And.intro q2 (ih (And.right h))))))

;; --- isolation of a write, from the invariant
(a/theorem write-isolated [h :- (=> Nat PRow), orig :- (=> Nat Nat), v :- PView, a :- Nat, x :- Nat, rs :- (List Nat),
                           u :- PView, du :- (=> Nat Bool), j :- Nat]
  (=> (excl h orig (:epoch v) u du) (= (:epoch (h a)) (:epoch v)) (= (du j) true)
      (= (view (write-heap h a x rs) orig u j) (view h orig u j)))
  (intros hx he hd)
  (simp only [excl] at hx)
  (have q := (hx j hd))
  (rw [(Eq.symm he)] at q)
  (exact (write-view-other h orig a x rs u j q)))

;; --- copy on access keeps every view of every well-formed world
(a/theorem copy-keeps-self [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, v :- PView, d :- (=> Nat Bool),
                            i :- Nat, j :- Nat]
  (=> (wf h n orig v d) (< 0 n) (= (d j) true)
      (= (view (copy-heap h orig n v i) orig (copy-view n v i) j) (view h orig v j)))
  (intros hw hp hd)
  (simp only [wf] at hw)
  (have q := (hw j hd))
  (exact (copy-view-self h orig n v i j hp (And.left q) (And.right (And.right q)))))

(a/theorem copy-keeps-other [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, v :- PView, i :- Nat,
                             u :- PView, du :- (=> Nat Bool), j :- Nat]
  (=> (wf h n orig u du) (= (du j) true)
      (= (view (copy-heap h orig n v i) orig u j) (view h orig u j)))
  (intros hw hd)
  (simp only [wf] at hw)
  (have q := (hw j hd))
  (exact (copy-view-other h orig n v i u j (And.left q) (And.right (And.right q)))))

;; ---------------------------------------------------------------------------
;; The invariants are kept by copy on access

(a/theorem copy-heap-old [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, v :- PView, i :- Nat, a :- Nat]
  (=> (< a n) (= (copy-heap h orig n v i a) (h a)))
  (intro hl)
  (have hne (Not (= a n))) (omega)
  (simp only [copy-heap fupd (nbeq-ne a n hne)]))

(a/theorem copy-heap-new [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, v :- PView, i :- Nat]
  (= (copy-heap h orig n v i n)
     (PRow.mk (:id (h (ver orig v i))) (:epoch v) (:val (h (ver orig v i))) (:refs (h (ver orig v i)))))
  (simp only [copy-heap fupd-same]))

(a/theorem wf-copy-self [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, v :- PView, d :- (=> Nat Bool), i :- Nat]
  (=> (wf h n orig v d) (< 0 n) (= (d i) true)
      (wf (copy-heap h orig n v i) (+ n 1) orig (copy-view n v i) d))
  (intros hw hp hdi)
  (simp only [wf] at hw)
  (simp only [wf])
  (intros j hd)
  (cases hji (Nat.beq j i))
  (case [false]
    (have hne (Not (= j i))) (exact (Nat.ne_of_beq_eq_false hji))
    (have q := (hw j hd))
    (have l := (And.left q))
    (simp only [(ver-copy-other orig n v i j hne) (copy-heap-old h orig n v i (ver orig v j) l)])
    (have l2 (< (ver orig v j) (+ n 1))) (omega)
    (exact (And.intro l2 (And.intro (And.left (And.right q)) (all-lt-succ n _ (And.right (And.right q)))))))
  (case [true]
    (have e (= j i)) (exact (Nat.eq_of_beq_eq_true hji))
    (subst e)
    (have q := (hw j hd))
    (simp only [(ver-copy-self orig n v j hp) copy-heap-new])
    (have l2 (< n (+ n 1))) (omega)
    (exact (And.intro l2 (And.intro (And.left (And.right q)) (all-lt-succ n _ (And.right (And.right q))))))))

(a/theorem wf-copy-other [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, v :- PView, i :- Nat,
                          u :- PView, du :- (=> Nat Bool)]
  (=> (wf h n orig u du) (wf (copy-heap h orig n v i) (+ n 1) orig u du))
  (intro hw)
  (simp only [wf] at hw)
  (simp only [wf])
  (intros j hd)
  (have q := (hw j hd))
  (have l := (And.left q))
  (simp only [(copy-heap-old h orig n v i (ver orig u j) l)])
  (have l2 (< (ver orig u j) (+ n 1))) (omega)
  (exact (And.intro l2 (And.intro (And.left (And.right q)) (all-lt-succ n _ (And.right (And.right q)))))))

(a/theorem own-copy-self [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, v :- PView, d :- (=> Nat Bool), i :- Nat]
  (=> (wf h n orig v d) (own h n orig v d) (Not (= (:epoch (h (ver orig v i))) (:epoch v))) (= (d i) true) (< 0 n)
      (own (copy-heap h orig n v i) (+ n 1) orig (copy-view n v i) d))
  (intros hw ho hno hdi hp)
  (simp only [own] at ho)
  (simp only [wf] at hw)
  (simp only [own])
  (intros a ha he hda)
  (cases han (Nat.beq a n))
  (case [false]
    (have hne (Not (= a n))) (exact (Nat.ne_of_beq_eq_false han))
    (have l (< a n)) (omega)
    (have e1 := (copy-heap-old h orig n v i a l))
    (rw [e1] at he) (rw [e1] at hda) (rw [e1])
    (have o := (ho a l he hda))
    (cases hii (Nat.beq (:id (h a)) i))
    (case [false]
      (have hn2 (Not (= (:id (h a)) i))) (exact (Nat.ne_of_beq_eq_false hii))
      (rw [(ver-copy-other orig n v i (:id (h a)) hn2)]) (exact o))
    (case [true]
      (have e2 (= (:id (h a)) i)) (exact (Nat.eq_of_beq_eq_true hii))
      (rw [e2] at o) (rw [o] at he) (exact (absurd he hno))))
  (case [true]
    (have e (= a n)) (exact (Nat.eq_of_beq_eq_true han))
    (rw [e])
    (have q := (hw i hdi))
    (simp only [copy-heap-new (And.left (And.right q)) (ver-copy-self orig n v i hp)])))

(a/theorem own-copy-other [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, v :- PView, i :- Nat,
                           u :- PView, du :- (=> Nat Bool)]
  (=> (own h n orig u du) (Not (= (:epoch v) (:epoch u)))
      (own (copy-heap h orig n v i) (+ n 1) orig u du))
  (intros ho hne2)
  (simp only [own] at ho)
  (simp only [own])
  (intros a ha he hda)
  (cases han (Nat.beq a n))
  (case [false]
    (have hne (Not (= a n))) (exact (Nat.ne_of_beq_eq_false han))
    (have l (< a n)) (omega)
    (have e1 := (copy-heap-old h orig n v i a l))
    (rw [e1] at he) (rw [e1] at hda) (rw [e1])
    (exact (ho a l he hda)))
  (case [true]
    (have e (= a n)) (exact (Nat.eq_of_beq_eq_true han))
    (rw [e] at he)
    (simp only [copy-heap-new] at he)
    (exact (absurd he hne2))))

(a/theorem excl-copy-other [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, v :- PView, i :- Nat, e :- Nat,
                            u :- PView, du :- (=> Nat Bool)]
  (=> (wf h n orig u du) (excl h orig e u du) (excl (copy-heap h orig n v i) orig e u du))
  (intros hw hx)
  (simp only [wf] at hw)
  (simp only [excl] at hx)
  (simp only [excl])
  (intros j hd)
  (rw [(copy-heap-old h orig n v i (ver orig u j) (And.left (hw j hd)))])
  (exact (hx j hd)))

(a/theorem excl-copy-self [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, v :- PView, d :- (=> Nat Bool),
                           i :- Nat, e :- Nat]
  (=> (wf h n orig v d) (excl h orig e v d) (Not (= (:epoch v) e)) (< 0 n)
      (excl (copy-heap h orig n v i) orig e (copy-view n v i) d))
  (intros hw hx hne2 hp)
  (simp only [wf] at hw)
  (simp only [excl] at hx)
  (simp only [excl])
  (intros j hd)
  (cases hji (Nat.beq j i))
  (case [false]
    (have hne (Not (= j i))) (exact (Nat.ne_of_beq_eq_false hji))
    (rw [(ver-copy-other orig n v i j hne)])
    (rw [(copy-heap-old h orig n v i (ver orig v j) (And.left (hw j hd)))])
    (exact (hx j hd)))
  (case [true]
    (have e2 (= j i)) (exact (Nat.eq_of_beq_eq_true hji))
    (rw [e2])
    (rw [(ver-copy-self orig n v i hp)])
    (simp only [copy-heap-new])
    (exact hne2)))

;; ---------------------------------------------------------------------------
;; The invariants are kept by a write

(a/theorem write-epoch [h :- (=> Nat PRow), a :- Nat, x :- Nat, rs :- (List Nat), r :- Nat]
  (= (:epoch (write-heap h a x rs r)) (:epoch (h r)))
  (cases hra (Nat.beq r a))
  (case [false] (simp only [write-heap fupd hra]))
  (case [true]
    (have e (= r a)) (exact (Nat.eq_of_beq_eq_true hra))
    (subst e)
    (simp only [write-heap fupd-same])))

(a/theorem wf-write [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, a :- Nat, x :- Nat, rs :- (List Nat),
                     u :- PView, du :- (=> Nat Bool)]
  (=> (wf h n orig u du) (= (all-lt n rs) true) (wf (write-heap h a x rs) n orig u du))
  (intros hw hr)
  (simp only [wf] at hw)
  (simp only [wf])
  (intros j hd)
  (have q := (hw j hd))
  (simp only [write-id])
  (cases hja (Nat.beq (ver orig u j) a))
  (case [false]
    (simp only [write-heap fupd hja])
    (exact q))
  (case [true]
    (have e (= (ver orig u j) a)) (exact (Nat.eq_of_beq_eq_true hja))
    (simp only [write-heap fupd hja])
    (exact (And.intro (And.left q) (And.intro (And.left (And.right q)) hr)))))

(a/theorem own-write [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, a :- Nat, x :- Nat, rs :- (List Nat),
                      u :- PView, du :- (=> Nat Bool)]
  (=> (own h n orig u du) (own (write-heap h a x rs) n orig u du))
  (intro ho)
  (simp only [own] at ho)
  (simp only [own write-id write-epoch])
  (exact ho))

(a/theorem excl-write [h :- (=> Nat PRow), orig :- (=> Nat Nat), a :- Nat, x :- Nat, rs :- (List Nat), e :- Nat,
                       u :- PView, du :- (=> Nat Bool)]
  (=> (excl h orig e u du) (excl (write-heap h a x rs) orig e u du))
  (intro hx)
  (simp only [excl] at hx)
  (simp only [excl write-epoch])
  (exact hx))

;; ---------------------------------------------------------------------------
;; The invariants are kept by a fork (both worlds take an epoch no row carries)

(a/theorem wf-rotate [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, v :- PView, d :- (=> Nat Bool), e :- Nat]
  (=> (wf h n orig v d) (wf h n orig (rotate v e) d))
  (intro hw) (exact hw))

(a/theorem own-rotate [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, v :- PView, d :- (=> Nat Bool), e :- Nat]
  (=> (forall [a :- Nat] (=> (< a n) (Not (= (:epoch (h a)) e))))
      (own h n orig (rotate v e) d))
  (intro hf)
  (simp only [own])
  (intros a ha he hda)
  (exact (absurd he (hf a ha))))

(a/theorem excl-fresh [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, e :- Nat, u :- PView, du :- (=> Nat Bool)]
  (=> (wf h n orig u du) (forall [a :- Nat] (=> (< a n) (Not (= (:epoch (h a)) e))))
      (excl h orig e u du))
  (intros hw hf)
  (simp only [wf] at hw)
  (simp only [excl])
  (intros j hd)
  (exact (hf (ver orig u j) (And.left (hw j hd)))))

(a/theorem excl-rotate [h :- (=> Nat PRow), orig :- (=> Nat Nat), v :- PView, d :- (=> Nat Bool), e :- Nat, e2 :- Nat]
  (=> (excl h orig e2 v d) (excl h orig e2 (rotate v e) d))
  (intro hx) (exact hx))

;; ---------------------------------------------------------------------------
;; The fast path of `rv`: a row carrying the world's epoch is what the world reads for its id

(a/theorem rv-fast [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, v :- PView, d :- (=> Nat Bool), a :- Nat]
  (=> (own h n orig v d) (< a n) (= (:epoch (h a)) (:epoch v)) (= (d (:id (h a))) true)
      (= (view h orig v (:id (h a))) (content h a)))
  (intros ho hl he hd)
  (simp only [own] at ho)
  (have q := (ho a hl he hd))
  (simp only [view])
  (rw [(Eq.symm q)]))

;; ---------------------------------------------------------------------------
;; Allocation: a new logical row i at the fresh address n, owned by the allocating world

(a/defn alloc-heap [h :- (=> Nat PRow), n :- Nat, i :- Nat, e :- Nat, x :- Nat, rs :- (List Nat)] (=> Nat PRow)
  (fupd h n (PRow.mk i e x rs)))

(a/theorem alloc-heap-old [h :- (=> Nat PRow), n :- Nat, i :- Nat, e :- Nat, x :- Nat, rs :- (List Nat), a :- Nat]
  (=> (< a n) (= (alloc-heap h n i e x rs a) (h a)))
  (intro hl)
  (have hne (Not (= a n))) (omega)
  (simp only [alloc-heap fupd (nbeq-ne a n hne)]))

(a/theorem alloc-heap-new [h :- (=> Nat PRow), n :- Nat, i :- Nat, e :- Nat, x :- Nat, rs :- (List Nat)]
  (= (alloc-heap h n i e x rs n) (PRow.mk i e x rs))
  (simp only [alloc-heap fupd-same]))

(a/theorem ver-alloc-other [orig :- (=> Nat Nat), n :- Nat, i :- Nat, u :- PView, j :- Nat]
  (=> (Not (= j i)) (= (ver (fupd orig i n) u j) (ver orig u j)))
  (intro hne)
  (simp only [ver fupd (nbeq-ne j i hne)]))

(a/theorem ver-alloc-self [orig :- (=> Nat Nat), n :- Nat, i :- Nat, v :- PView]
  (=> (= (PView.fwd v i) 0) (= (ver (fupd orig i n) v i) n))
  (intro hz)
  (simp only [ver hz fupd-same Nat.beq_refl]))

(a/theorem alloc-id-lt [h :- (=> Nat PRow), n :- Nat, i :- Nat, e :- Nat, x :- Nat, rs :- (List Nat), r :- Nat]
  (=> (< r n) (= (:id (alloc-heap h n i e x rs r)) (:id (h r))))
  (intro hl)
  (rw [(alloc-heap-old h n i e x rs r hl)]))

;; a world that does not have i reads the same table after the allocation
(a/theorem alloc-view-other [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, i :- Nat, e :- Nat, x :- Nat,
                             rs :- (List Nat), u :- PView, du :- (=> Nat Bool), j :- Nat]
  (=> (wf h n orig u du) (= (du i) false) (= (du j) true)
      (= (view (alloc-heap h n i e x rs) (fupd orig i n) u j) (view h orig u j)))
  (intros hw hi hd)
  (simp only [wf] at hw)
  (have q := (hw j hd))
  (have hne (Not (= j i))) (intro e2) (rw [e2] at hd) (rw [hi] at hd) (simp at hd)
  (simp only [view (ver-alloc-other orig n i u j hne) content (alloc-heap-old h n i e x rs (ver orig u j) (And.left q))])
  (rw [(rids-frame-lt h (alloc-heap h n i e x rs) n (:refs (h (ver orig u j)))
                      (fn [r :- Nat] (alloc-id-lt h n i e x rs r)) (And.right (And.right q)))]))

(a/theorem wf-alloc-other [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, i :- Nat, e :- Nat, x :- Nat,
                           rs :- (List Nat), u :- PView, du :- (=> Nat Bool)]
  (=> (wf h n orig u du) (= (du i) false)
      (wf (alloc-heap h n i e x rs) (+ n 1) (fupd orig i n) u du))
  (intros hw hi)
  (simp only [wf] at hw)
  (simp only [wf])
  (intros j hd)
  (have q := (hw j hd))
  (have hne (Not (= j i))) (intro e2) (rw [e2] at hd) (rw [hi] at hd) (simp at hd)
  (simp only [(ver-alloc-other orig n i u j hne) (alloc-heap-old h n i e x rs (ver orig u j) (And.left q))])
  (have l2 (< (ver orig u j) (+ n 1))) (omega)
  (exact (And.intro l2 (And.intro (And.left (And.right q)) (all-lt-succ n _ (And.right (And.right q)))))))

(a/theorem wf-alloc-self [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, i :- Nat, x :- Nat,
                          rs :- (List Nat), v :- PView, d :- (=> Nat Bool)]
  (=> (wf h n orig v d) (= (PView.fwd v i) 0) (= (d i) false) (= (all-lt (+ n 1) rs) true)
      (wf (alloc-heap h n i (:epoch v) x rs) (+ n 1) (fupd orig i n) v (fupd d i Bool.true)))
  (intros hw hz hi hr)
  (simp only [wf] at hw)
  (simp only [wf])
  (intros j hd)
  (cases hji (Nat.beq j i))
  (case [false]
    (have hne (Not (= j i))) (exact (Nat.ne_of_beq_eq_false hji))
    (simp only [fupd hji] at hd)
    (have q := (hw j hd))
    (simp only [(ver-alloc-other orig n i v j hne) (alloc-heap-old h n i (:epoch v) x rs (ver orig v j) (And.left q))])
    (have l2 (< (ver orig v j) (+ n 1))) (omega)
    (exact (And.intro l2 (And.intro (And.left (And.right q)) (all-lt-succ n _ (And.right (And.right q)))))))
  (case [true]
    (have e2 (= j i)) (exact (Nat.eq_of_beq_eq_true hji))
    (rw [e2])
    (simp only [(ver-alloc-self orig n i v hz) alloc-heap-new])
    (have l2 (< n (+ n 1))) (omega)
    (exact (And.intro l2 (And.intro True.intro hr)))))

(a/theorem own-alloc-self [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, i :- Nat, x :- Nat,
                           rs :- (List Nat), v :- PView, d :- (=> Nat Bool)]
  (=> (own h n orig v d) (forall [a :- Nat] (=> (< a n) (Not (= (:id (h a)) i)))) (= (PView.fwd v i) 0)
      (own (alloc-heap h n i (:epoch v) x rs) (+ n 1) (fupd orig i n) v (fupd d i Bool.true)))
  (intros ho hf hz)
  (simp only [own] at ho)
  (simp only [own])
  (intros a ha he hda)
  (cases han (Nat.beq a n))
  (case [false]
    (have hne (Not (= a n))) (exact (Nat.ne_of_beq_eq_false han))
    (have l (< a n)) (omega)
    (have e1 := (alloc-heap-old h n i (:epoch v) x rs a l))
    (rw [e1] at he) (rw [e1] at hda) (rw [e1])
    (have hn2 := (hf a l))
    (simp only [fupd (nbeq-ne (:id (h a)) i hn2)] at hda)
    (rw [(ver-alloc-other orig n i v (:id (h a)) hn2)])
    (exact (ho a l he hda)))
  (case [true]
    (have e (= a n)) (exact (Nat.eq_of_beq_eq_true han))
    (rw [e])
    (simp only [alloc-heap-new (ver-alloc-self orig n i v hz)])))

(a/theorem own-alloc-other [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, i :- Nat, e :- Nat, x :- Nat,
                            rs :- (List Nat), u :- PView, du :- (=> Nat Bool)]
  (=> (own h n orig u du) (forall [a :- Nat] (=> (< a n) (Not (= (:id (h a)) i)))) (Not (= e (:epoch u)))
      (own (alloc-heap h n i e x rs) (+ n 1) (fupd orig i n) u du))
  (intros ho hf hne2)
  (simp only [own] at ho)
  (simp only [own])
  (intros a ha he hda)
  (cases han (Nat.beq a n))
  (case [false]
    (have hne (Not (= a n))) (exact (Nat.ne_of_beq_eq_false han))
    (have l (< a n)) (omega)
    (have e1 := (alloc-heap-old h n i e x rs a l))
    (rw [e1] at he) (rw [e1] at hda) (rw [e1])
    (rw [(ver-alloc-other orig n i u (:id (h a)) (hf a l))])
    (exact (ho a l he hda)))
  (case [true]
    (have e3 (= a n)) (exact (Nat.eq_of_beq_eq_true han))
    (rw [e3] at he)
    (simp only [alloc-heap-new] at he)
    (exact (absurd he hne2))))

(a/theorem excl-alloc-other [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, i :- Nat, e :- Nat, x :- Nat,
                             rs :- (List Nat), e2 :- Nat, u :- PView, du :- (=> Nat Bool)]
  (=> (wf h n orig u du) (= (du i) false) (excl h orig e2 u du)
      (excl (alloc-heap h n i e x rs) (fupd orig i n) e2 u du))
  (intros hw hi hx)
  (simp only [wf] at hw)
  (simp only [excl] at hx)
  (simp only [excl])
  (intros j hd)
  (have hne (Not (= j i))) (intro e3) (rw [e3] at hd) (rw [hi] at hd) (simp at hd)
  (rw [(ver-alloc-other orig n i u j hne)])
  (rw [(alloc-heap-old h n i e x rs (ver orig u j) (And.left (hw j hd)))])
  (exact (hx j hd)))

(a/theorem excl-alloc-self [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, i :- Nat, x :- Nat,
                            rs :- (List Nat), e2 :- Nat, v :- PView, d :- (=> Nat Bool)]
  (=> (wf h n orig v d) (excl h orig e2 v d) (Not (= (:epoch v) e2)) (= (PView.fwd v i) 0)
      (excl (alloc-heap h n i (:epoch v) x rs) (fupd orig i n) e2 v (fupd d i Bool.true)))
  (intros hw hx hne2 hz)
  (simp only [wf] at hw)
  (simp only [excl] at hx)
  (simp only [excl])
  (intros j hd)
  (cases hji (Nat.beq j i))
  (case [false]
    (have hne (Not (= j i))) (exact (Nat.ne_of_beq_eq_false hji))
    (simp only [fupd hji] at hd)
    (rw [(ver-alloc-other orig n i v j hne)])
    (rw [(alloc-heap-old h n i (:epoch v) x rs (ver orig v j) (And.left (hw j hd)))])
    (exact (hx j hd)))
  (case [true]
    (have e3 (= j i)) (exact (Nat.eq_of_beq_eq_true hji))
    (rw [e3])
    (rw [(ver-alloc-self orig n i v hz)])
    (simp only [alloc-heap-new])
    (exact hne2)))

;; ---------------------------------------------------------------------------
;; The slow path of `rv` (`resolve-row`): through the forward map, else the reference itself.
;; A stored reference without a forward entry must therefore be the original row of its id.

(a/defn rsrc [h :- (=> Nat PRow), v :- PView, r :- Nat] Nat
  (if (Nat.beq (PView.fwd v (:id (h r))) 0) r (PView.fwd v (:id (h r)))))

(a/defn rok [h :- (=> Nat PRow), orig :- (=> Nat Nat), v :- PView, r :- Nat] Bool
  (Bool.or (Bool.not (Nat.beq (PView.fwd v (:id (h r))) 0)) (Nat.beq r (orig (:id (h r))))))

(a/defn all-rok [h :- (=> Nat PRow), orig :- (=> Nat Nat), v :- PView, rs :- (List Nat)] Bool
  (match rs [nil true] [(cons r t) (Bool.and (rok h orig v r) (all-rok h orig v t))]))

(a/theorem rv-slow [h :- (=> Nat PRow), orig :- (=> Nat Nat), v :- PView, r :- Nat]
  (=> (= (rok h orig v r) true) (= (rsrc h v r) (ver orig v (:id (h r)))))
  (intro hk)
  (cases hz (Nat.beq (PView.fwd v (:id (h r))) 0))
  (case [false] (simp only [rsrc ver hz]))
  (case [true]
    (simp only [rok hz Bool.not_true Bool.false_or] at hk)
    (have e := (Nat.eq_of_beq_eq_true hk))
    (simp only [rsrc ver hz])
    (exact e)))

(a/theorem all-rok-imp [h :- (=> Nat PRow), orig :- (=> Nat Nat), v :- PView,
                        h2 :- (=> Nat PRow), orig2 :- (=> Nat Nat), v2 :- PView, n :- Nat, rs :- (List Nat)]
  (=> (forall [r :- Nat] (=> (< r n) (= (rok h orig v r) true) (= (rok h2 orig2 v2 r) true)))
      (= (all-lt n rs) true) (= (all-rok h orig v rs) true)
      (= (all-rok h2 orig2 v2 rs) true))
  (intro hp)
  (induction rs)
  (case [nil] (intros hl hk) (simp only [all-rok]))
  (case [cons r t ih]
    (intros hl hk)
    (simp only [all-lt Bool.and_eq_true Nat.blt_eq] at hl)
    (simp only [all-rok Bool.and_eq_true] at hk)
    (simp only [all-rok Bool.and_eq_true])
    (exact (And.intro (hp r (And.left hl) (And.left hk)) (ih (And.right hl) (And.right hk))))))

;; every reference stored in a row the world reads resolves by the slow path
(a/defn ro [h :- (=> Nat PRow), orig :- (=> Nat Nat), v :- PView, d :- (=> Nat Bool)] Prop
  (forall [j :- Nat] (=> (= (d j) true) (= (all-rok h orig v (:refs (h (ver orig v j)))) true))))

(a/theorem rok-copy-self [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, v :- PView, i :- Nat, r :- Nat]
  (=> (< 0 n) (< r n) (= (rok h orig v r) true)
      (= (rok (copy-heap h orig n v i) orig (copy-view n v i) r) true))
  (intros hp hl hk)
  (have e1 := (copy-heap-old h orig n v i r hl))
  (cases hii (Nat.beq (:id (h r)) i))
  (case [false]
    (simp only [rok e1 copy-view fupd hii])
    (simp only [rok] at hk)
    (exact hk))
  (case [true]
    (have hz (= (Nat.beq n 0) false)) (apply nbeq-ne) (omega)
    (simp only [rok e1 copy-view fupd hii hz Bool.not_false Bool.true_or])))

(a/theorem rok-copy-other [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, v :- PView, i :- Nat, u :- PView, r :- Nat]
  (=> (< r n) (= (rok h orig u r) true)
      (= (rok (copy-heap h orig n v i) orig u r) true))
  (intros hl hk)
  (have e1 := (copy-heap-old h orig n v i r hl))
  (simp only [rok e1])
  (simp only [rok] at hk)
  (exact hk))

(a/theorem ro-copy-self [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, v :- PView, d :- (=> Nat Bool), i :- Nat]
  (=> (wf h n orig v d) (ro h orig v d) (< 0 n)
      (ro (copy-heap h orig n v i) orig (copy-view n v i) d))
  (intros hw hr hp)
  (simp only [wf] at hw)
  (simp only [ro] at hr)
  (simp only [ro])
  (intros j hd)
  (cases hji (Nat.beq j i))
  (case [false]
    (have hne (Not (= j i))) (exact (Nat.ne_of_beq_eq_false hji))
    (have q := (hw j hd))
    (rw [(ver-copy-other orig n v i j hne)])
    (rw [(copy-heap-old h orig n v i (ver orig v j) (And.left q))])
    (exact (all-rok-imp h orig v (copy-heap h orig n v i) orig (copy-view n v i) n (:refs (h (ver orig v j)))
                        (fn [r :- Nat] (rok-copy-self h orig n v i r hp)) (And.right (And.right q)) (hr j hd))))
  (case [true]
    (have e2 (= j i)) (exact (Nat.eq_of_beq_eq_true hji))
    (rw [e2] at hd)
    (rw [e2])
    (have q := (hw i hd))
    (rw [(ver-copy-self orig n v i hp)])
    (simp only [copy-heap-new])
    (exact (all-rok-imp h orig v (copy-heap h orig n v i) orig (copy-view n v i) n (:refs (h (ver orig v i)))
                        (fn [r :- Nat] (rok-copy-self h orig n v i r hp)) (And.right (And.right q)) (hr i hd)))))

(a/theorem ro-copy-other [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, v :- PView, i :- Nat,
                          u :- PView, du :- (=> Nat Bool)]
  (=> (wf h n orig u du) (ro h orig u du) (ro (copy-heap h orig n v i) orig u du))
  (intros hw hr)
  (simp only [wf] at hw)
  (simp only [ro] at hr)
  (simp only [ro])
  (intros j hd)
  (have q := (hw j hd))
  (rw [(copy-heap-old h orig n v i (ver orig u j) (And.left q))])
  (exact (all-rok-imp h orig u (copy-heap h orig n v i) orig u n (:refs (h (ver orig u j)))
                      (fn [r :- Nat] (rok-copy-other h orig n v i u r)) (And.right (And.right q)) (hr j hd))))

(a/theorem all-rok-write [h :- (=> Nat PRow), orig :- (=> Nat Nat), a :- Nat, x :- Nat, rs :- (List Nat),
                          u :- PView, l :- (List Nat)]
  (= (all-rok (write-heap h a x rs) orig u l) (all-rok h orig u l))
  (induction l)
  (case [nil] (simp only [all-rok]))
  (case [cons r t ih] (simp only [all-rok rok write-id ih])))

;; the writing world: the new references must resolve
(a/theorem ro-write-self [h :- (=> Nat PRow), orig :- (=> Nat Nat), a :- Nat, x :- Nat, rs :- (List Nat),
                          u :- PView, du :- (=> Nat Bool)]
  (=> (ro h orig u du) (= (all-rok h orig u rs) true) (ro (write-heap h a x rs) orig u du))
  (intros hr hk)
  (simp only [ro] at hr)
  (simp only [ro all-rok-write])
  (intros j hd)
  (cases hja (Nat.beq (ver orig u j) a))
  (case [false] (simp only [write-heap fupd hja]) (exact (hr j hd)))
  (case [true] (simp only [write-heap fupd hja]) (exact hk)))

;; a world that does not see the written row
(a/theorem ro-write-other [h :- (=> Nat PRow), orig :- (=> Nat Nat), a :- Nat, x :- Nat, rs :- (List Nat),
                           u :- PView, du :- (=> Nat Bool)]
  (=> (ro h orig u du) (excl h orig (:epoch (h a)) u du) (ro (write-heap h a x rs) orig u du))
  (intros hr hx)
  (simp only [ro] at hr)
  (simp only [excl] at hx)
  (simp only [ro all-rok-write])
  (intros j hd)
  (have hne (Not (= (ver orig u j) a))) (intro e) (have q := (hx j hd)) (rw [e] at q) (exact (q (Eq.refl _)))
  (simp only [write-heap fupd (nbeq-ne (ver orig u j) a hne)])
  (exact (hr j hd)))

(a/theorem ro-rotate [h :- (=> Nat PRow), orig :- (=> Nat Nat), v :- PView, d :- (=> Nat Bool), e :- Nat]
  (=> (ro h orig v d) (ro h orig (rotate v e) d))
  (intro hr) (exact hr))

(a/theorem rok-alloc [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, i :- Nat, e :- Nat, x :- Nat,
                      rs :- (List Nat), u :- PView, r :- Nat]
  (=> (forall [a :- Nat] (=> (< a n) (Not (= (:id (h a)) i)))) (< r n) (= (rok h orig u r) true)
      (= (rok (alloc-heap h n i e x rs) (fupd orig i n) u r) true))
  (intros hf hl hk)
  (have e1 := (alloc-heap-old h n i e x rs r hl))
  (simp only [rok e1 fupd (nbeq-ne (:id (h r)) i (hf r hl))])
  (simp only [rok] at hk)
  (exact hk))

(a/theorem ro-alloc-other [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, i :- Nat, e :- Nat, x :- Nat,
                           rs :- (List Nat), u :- PView, du :- (=> Nat Bool)]
  (=> (wf h n orig u du) (ro h orig u du) (= (du i) false)
      (forall [a :- Nat] (=> (< a n) (Not (= (:id (h a)) i))))
      (ro (alloc-heap h n i e x rs) (fupd orig i n) u du))
  (intros hw hr hi hf)
  (simp only [wf] at hw)
  (simp only [ro] at hr)
  (simp only [ro])
  (intros j hd)
  (have q := (hw j hd))
  (have hne (Not (= j i))) (intro e3) (rw [e3] at hd) (rw [hi] at hd) (simp at hd)
  (rw [(ver-alloc-other orig n i u j hne)])
  (rw [(alloc-heap-old h n i e x rs (ver orig u j) (And.left q))])
  (exact (all-rok-imp h orig u (alloc-heap h n i e x rs) (fupd orig i n) u n (:refs (h (ver orig u j)))
                      (fn [r :- Nat] (rok-alloc h orig n i e x rs u r hf)) (And.right (And.right q)) (hr j hd))))

(a/theorem ro-alloc-self [h :- (=> Nat PRow), orig :- (=> Nat Nat), n :- Nat, i :- Nat, x :- Nat,
                          rs :- (List Nat), v :- PView, d :- (=> Nat Bool)]
  (=> (wf h n orig v d) (ro h orig v d) (= (PView.fwd v i) 0)
      (forall [a :- Nat] (=> (< a n) (Not (= (:id (h a)) i))))
      (= (all-rok (alloc-heap h n i (:epoch v) x rs) (fupd orig i n) v rs) true)
      (ro (alloc-heap h n i (:epoch v) x rs) (fupd orig i n) v (fupd d i Bool.true)))
  (intros hw hr hz hf hk)
  (simp only [wf] at hw)
  (simp only [ro] at hr)
  (simp only [ro])
  (intros j hd)
  (cases hji (Nat.beq j i))
  (case [false]
    (have hne (Not (= j i))) (exact (Nat.ne_of_beq_eq_false hji))
    (simp only [fupd hji] at hd)
    (have q := (hw j hd))
    (rw [(ver-alloc-other orig n i v j hne)])
    (rw [(alloc-heap-old h n i (:epoch v) x rs (ver orig v j) (And.left q))])
    (exact (all-rok-imp h orig v (alloc-heap h n i (:epoch v) x rs) (fupd orig i n) v n (:refs (h (ver orig v j)))
                        (fn [r :- Nat] (rok-alloc h orig n i (:epoch v) x rs v r hf)) (And.right (And.right q)) (hr j hd))))
  (case [true]
    (have e3 (= j i)) (exact (Nat.eq_of_beq_eq_true hji))
    (rw [e3])
    (rw [(ver-alloc-self orig n i v hz)])
    (simp only [alloc-heap-new])
    (exact hk)))

;; ---------------------------------------------------------------------------
;; A family of worlds: `fam k` is world k's view, `dom k` its domain, `live k` whether it exists

;; every live world is well-formed
(a/defn fin1 [h :- (=> Nat PRow), n :- Nat, orig :- (=> Nat Nat), fam :- (=> Nat PView),
              dom :- (=> Nat (=> Nat Bool)), live :- (=> Nat Bool)] Prop
  (forall [k :- Nat] (=> (= (live k) true)
    (And (wf h n orig (fam k) (dom k)) (And (own h n orig (fam k) (dom k)) (ro h orig (fam k) (dom k)))))))

;; two live worlds have different epochs and neither sees a row the other owns
(a/defn fin2 [h :- (=> Nat PRow), orig :- (=> Nat Nat), fam :- (=> Nat PView),
              dom :- (=> Nat (=> Nat Bool)), live :- (=> Nat Bool)] Prop
  (forall [k :- Nat, k2 :- Nat] (=> (= (live k) true) (= (live k2) true) (Not (= k k2))
    (And (Not (= (:epoch (fam k)) (:epoch (fam k2))))
         (excl h orig (:epoch (fam k)) (fam k2) (dom k2))))))

(a/theorem fin1-copy [h :- (=> Nat PRow), n :- Nat, orig :- (=> Nat Nat), fam :- (=> Nat PView),
                      dom :- (=> Nat (=> Nat Bool)), live :- (=> Nat Bool), k :- Nat, i :- Nat]
  (=> (fin1 h n orig fam dom live) (fin2 h orig fam dom live) (= (live k) true) (< 0 n) (= (dom k i) true)
      (Not (= (:epoch (h (ver orig (fam k) i))) (:epoch (fam k))))
      (fin1 (copy-heap h orig n (fam k) i) (+ n 1) orig (fupd fam k (copy-view n (fam k) i)) dom live))
  (intros h1 h2 hlk hp hdi hno)
  (simp only [fin1] at h1)
  (simp only [fin2] at h2)
  (simp only [fin1])
  (intros k1 hl1)
  (cases hk (Nat.beq k1 k))
  (case [false]
    (have hne (Not (= k1 k))) (exact (Nat.ne_of_beq_eq_false hk))
    (have hne2 (Not (= k k1))) (intro e) (exact (hne (Eq.symm e)))
    (simp only [fupd hk])
    (have q := (h1 k1 hl1))
    (have p := (h2 k k1 hlk hl1 hne2))
    (exact (And.intro (wf-copy-other h orig n (fam k) i (fam k1) (dom k1) (And.left q))
             (And.intro (own-copy-other h orig n (fam k) i (fam k1) (dom k1) (And.left (And.right q)) (And.left p))
                        (ro-copy-other h orig n (fam k) i (fam k1) (dom k1) (And.left q) (And.right (And.right q)))))))
  (case [true]
    (have e (= k1 k)) (exact (Nat.eq_of_beq_eq_true hk))
    (rw [e])
    (simp only [fupd-same])
    (have q := (h1 k hlk))
    (exact (And.intro (wf-copy-self h orig n (fam k) (dom k) i (And.left q) hp hdi)
             (And.intro (own-copy-self h orig n (fam k) (dom k) i (And.left q) (And.left (And.right q)) hno hdi hp)
                        (ro-copy-self h orig n (fam k) (dom k) i (And.left q) (And.right (And.right q)) hp))))))

(a/theorem fin2-copy [h :- (=> Nat PRow), n :- Nat, orig :- (=> Nat Nat), fam :- (=> Nat PView),
                      dom :- (=> Nat (=> Nat Bool)), live :- (=> Nat Bool), k :- Nat, i :- Nat]
  (=> (fin1 h n orig fam dom live) (fin2 h orig fam dom live) (= (live k) true) (< 0 n)
      (fin2 (copy-heap h orig n (fam k) i) orig (fupd fam k (copy-view n (fam k) i)) dom live))
  (intros h1 h2 hlk hp)
  (simp only [fin1] at h1)
  (simp only [fin2] at h2)
  (simp only [fin2])
  (intros k1 k2 hl1 hl2 hne12)
  (cases hk1 (Nat.beq k1 k))
  (case [false]
    (have hn1 (Not (= k1 k))) (exact (Nat.ne_of_beq_eq_false hk1))
    (cases hk2 (Nat.beq k2 k))
    (case [false]
      (simp only [fupd hk1 hk2])
      (have p := (h2 k1 k2 hl1 hl2 hne12))
      (exact (And.intro (And.left p)
               (excl-copy-other h orig n (fam k) i (:epoch (fam k1)) (fam k2) (dom k2) (And.left (h1 k2 hl2)) (And.right p)))))
    (case [true]
      (have e (= k2 k)) (exact (Nat.eq_of_beq_eq_true hk2))
      (rw [e])
      (simp only [fupd hk1 fupd-same])
      (have p := (h2 k1 k hl1 hlk hn1))
      (have ps (Not (= (:epoch (fam k)) (:epoch (fam k1))))) (intro e3) (exact ((And.left p) (Eq.symm e3)))
      (exact (And.intro (And.left p)
               (excl-copy-self h orig n (fam k) (dom k) i (:epoch (fam k1)) (And.left (h1 k hlk)) (And.right p) ps hp)))))
  (case [true]
    (have e (= k1 k)) (exact (Nat.eq_of_beq_eq_true hk1))
    (have hn2 (Not (= k k2))) (intro e3) (exact (hne12 (Eq.trans e e3)))
    (have hk2 (= (Nat.beq k2 k) false)) (apply nbeq-ne) (intro e3) (exact (hn2 (Eq.symm e3)))
    (rw [e])
    (simp only [fupd hk2 fupd-same])
    (have p := (h2 k k2 hlk hl2 hn2))
    (exact (And.intro (And.left p)
             (excl-copy-other h orig n (fam k) i (:epoch (fam k)) (fam k2) (dom k2) (And.left (h1 k2 hl2)) (And.right p))))))

;; --- a write by world k to a row it owns
(a/theorem fin1-write [h :- (=> Nat PRow), n :- Nat, orig :- (=> Nat Nat), fam :- (=> Nat PView),
                       dom :- (=> Nat (=> Nat Bool)), live :- (=> Nat Bool), k :- Nat, a :- Nat, x :- Nat, rs :- (List Nat)]
  (=> (fin1 h n orig fam dom live) (fin2 h orig fam dom live) (= (live k) true)
      (= (:epoch (h a)) (:epoch (fam k))) (= (all-lt n rs) true) (= (all-rok h orig (fam k) rs) true)
      (fin1 (write-heap h a x rs) n orig fam dom live))
  (intros h1 h2 hlk he hr hk)
  (simp only [fin1] at h1)
  (simp only [fin2] at h2)
  (simp only [fin1])
  (intros k1 hl1)
  (have q := (h1 k1 hl1))
  (cases hkk (Nat.beq k1 k))
  (case [false]
    (have hne (Not (= k1 k))) (exact (Nat.ne_of_beq_eq_false hkk))
    (have hne2 (Not (= k k1))) (intro e) (exact (hne (Eq.symm e)))
    (have p := (And.right (h2 k k1 hlk hl1 hne2)))
    (rw [(Eq.symm he)] at p)
    (exact (And.intro (wf-write h orig n a x rs (fam k1) (dom k1) (And.left q) hr)
             (And.intro (own-write h orig n a x rs (fam k1) (dom k1) (And.left (And.right q)))
                        (ro-write-other h orig a x rs (fam k1) (dom k1) (And.right (And.right q)) p)))))
  (case [true]
    (have e (= k1 k)) (exact (Nat.eq_of_beq_eq_true hkk))
    (rw [e] at q)
    (rw [e])
    (exact (And.intro (wf-write h orig n a x rs (fam k) (dom k) (And.left q) hr)
             (And.intro (own-write h orig n a x rs (fam k) (dom k) (And.left (And.right q)))
                        (ro-write-self h orig a x rs (fam k) (dom k) (And.right (And.right q)) hk))))))

(a/theorem fin2-write [h :- (=> Nat PRow), orig :- (=> Nat Nat), fam :- (=> Nat PView),
                       dom :- (=> Nat (=> Nat Bool)), live :- (=> Nat Bool), a :- Nat, x :- Nat, rs :- (List Nat)]
  (=> (fin2 h orig fam dom live) (fin2 (write-heap h a x rs) orig fam dom live))
  (intro h2)
  (simp only [fin2] at h2)
  (simp only [fin2])
  (intros k1 k2 hl1 hl2 hne)
  (have p := (h2 k1 k2 hl1 hl2 hne))
  (exact (And.intro (And.left p) (excl-write h orig a x rs (:epoch (fam k1)) (fam k2) (dom k2) (And.right p)))))

;; --- the isolation statement for a family: a write by world k changes no other live world's table
(a/theorem fam-write-isolated [h :- (=> Nat PRow), orig :- (=> Nat Nat), fam :- (=> Nat PView),
                               dom :- (=> Nat (=> Nat Bool)), live :- (=> Nat Bool), k :- Nat, a :- Nat, x :- Nat,
                               rs :- (List Nat), k2 :- Nat, j :- Nat]
  (=> (fin2 h orig fam dom live) (= (live k) true) (= (live k2) true) (Not (= k k2))
      (= (:epoch (h a)) (:epoch (fam k))) (= (dom k2 j) true)
      (= (view (write-heap h a x rs) orig (fam k2) j) (view h orig (fam k2) j)))
  (intros h2 hlk hl2 hne he hd)
  (simp only [fin2] at h2)
  (exact (write-isolated h orig (fam k) a x rs (fam k2) (dom k2) j (And.right (h2 k k2 hlk hl2 hne)) he hd)))

;; --- fork, first half: world k takes an epoch e that no row and no other live world carries
(a/theorem fin1-reepoch [h :- (=> Nat PRow), n :- Nat, orig :- (=> Nat Nat), fam :- (=> Nat PView),
                         dom :- (=> Nat (=> Nat Bool)), live :- (=> Nat Bool), k :- Nat, e :- Nat]
  (=> (fin1 h n orig fam dom live) (forall [a :- Nat] (=> (< a n) (Not (= (:epoch (h a)) e))))
      (fin1 h n orig (fupd fam k (rotate (fam k) e)) dom live))
  (intros h1 hf)
  (simp only [fin1] at h1)
  (simp only [fin1])
  (intros k1 hl1)
  (have q := (h1 k1 hl1))
  (cases hkk (Nat.beq k1 k))
  (case [false] (simp only [fupd hkk]) (exact q))
  (case [true]
    (have e2 (= k1 k)) (exact (Nat.eq_of_beq_eq_true hkk))
    (rw [e2] at q)
    (rw [e2])
    (simp only [fupd-same])
    (exact (And.intro (wf-rotate h orig n (fam k) (dom k) e (And.left q))
             (And.intro (own-rotate h orig n (fam k) (dom k) e hf)
                        (ro-rotate h orig (fam k) (dom k) e (And.right (And.right q))))))))

(a/theorem fin2-reepoch [h :- (=> Nat PRow), n :- Nat, orig :- (=> Nat Nat), fam :- (=> Nat PView),
                         dom :- (=> Nat (=> Nat Bool)), live :- (=> Nat Bool), k :- Nat, e :- Nat]
  (=> (fin1 h n orig fam dom live) (fin2 h orig fam dom live)
      (forall [a :- Nat] (=> (< a n) (Not (= (:epoch (h a)) e))))
      (forall [k2 :- Nat] (=> (= (live k2) true) (Not (= (:epoch (fam k2)) e))))
      (fin2 h orig (fupd fam k (rotate (fam k) e)) dom live))
  (intros h1 h2 hf hw)
  (simp only [fin1] at h1)
  (simp only [fin2] at h2)
  (simp only [fin2])
  (intros k1 k2 hl1 hl2 hne12)
  (cases hk1 (Nat.beq k1 k))
  (case [false]
    (cases hk2 (Nat.beq k2 k))
    (case [false] (simp only [fupd hk1 hk2]) (exact (h2 k1 k2 hl1 hl2 hne12)))
    (case [true]
      (have e2 (= k2 k)) (exact (Nat.eq_of_beq_eq_true hk2))
      (rw [e2] at hne12)
      (rw [e2] at hl2)
      (rw [e2])
      (simp only [fupd hk1 fupd-same])
      (have p := (h2 k1 k hl1 hl2 hne12))
      (exact (And.intro (hw k1 hl1) (excl-rotate h orig (fam k) (dom k) e (:epoch (fam k1)) (And.right p))))))
  (case [true]
    (have e1 (= k1 k)) (exact (Nat.eq_of_beq_eq_true hk1))
    (have hk2 (= (Nat.beq k2 k) false)) (apply nbeq-ne) (intro e3) (exact (hne12 (Eq.trans e1 (Eq.symm e3))))
    (rw [e1])
    (simp only [fupd hk2 fupd-same])
    (have ps (Not (= e (:epoch (fam k2))))) (intro e3) (exact ((hw k2 hl2) (Eq.symm e3)))
    (exact (And.intro ps (excl-fresh h orig n e (fam k2) (dom k2) (And.left (h1 k2 hl2)) hf)))))

;; --- fork, second half: a new world m with world k's forward map and domain, at an epoch e that no
;; row and no live world carries. World k must see no row of its own epoch (true after `reepoch`).
(a/theorem fin1-spawn [h :- (=> Nat PRow), n :- Nat, orig :- (=> Nat Nat), fam :- (=> Nat PView),
                       dom :- (=> Nat (=> Nat Bool)), live :- (=> Nat Bool), k :- Nat, m :- Nat, e :- Nat]
  (=> (fin1 h n orig fam dom live) (= (live k) true)
      (forall [a :- Nat] (=> (< a n) (Not (= (:epoch (h a)) e))))
      (fin1 h n orig (fupd fam m (rotate (fam k) e)) (fupd dom m (dom k)) (fupd live m Bool.true)))
  (intros h1 hlk hf)
  (simp only [fin1] at h1)
  (simp only [fin1])
  (intros k1 hl1)
  (cases hkm (Nat.beq k1 m))
  (case [false]
    (simp only [fupd hkm] at hl1)
    (simp only [fupd hkm])
    (exact (h1 k1 hl1)))
  (case [true]
    (have e2 (= k1 m)) (exact (Nat.eq_of_beq_eq_true hkm))
    (rw [e2])
    (simp only [fupd-same])
    (have q := (h1 k hlk))
    (exact (And.intro (wf-rotate h orig n (fam k) (dom k) e (And.left q))
             (And.intro (own-rotate h orig n (fam k) (dom k) e hf)
                        (ro-rotate h orig (fam k) (dom k) e (And.right (And.right q))))))))

(a/theorem fin2-spawn [h :- (=> Nat PRow), n :- Nat, orig :- (=> Nat Nat), fam :- (=> Nat PView),
                       dom :- (=> Nat (=> Nat Bool)), live :- (=> Nat Bool), k :- Nat, m :- Nat, e :- Nat]
  (=> (fin1 h n orig fam dom live) (fin2 h orig fam dom live) (= (live k) true)
      (forall [a :- Nat] (=> (< a n) (Not (= (:epoch (h a)) e))))
      (forall [k2 :- Nat] (=> (= (live k2) true) (Not (= (:epoch (fam k2)) e))))
      (excl h orig (:epoch (fam k)) (fam k) (dom k))
      (fin2 h orig (fupd fam m (rotate (fam k) e)) (fupd dom m (dom k)) (fupd live m Bool.true)))
  (intros h1 h2 hlk hf hw hself)
  (simp only [fin1] at h1)
  (simp only [fin2] at h2)
  (simp only [fin2])
  (intros k1 k2 hl1 hl2 hne12)
  (cases hk1 (Nat.beq k1 m))
  (case [false]
    (simp only [fupd hk1] at hl1)
    (cases hk2 (Nat.beq k2 m))
    (case [false]
      (simp only [fupd hk2] at hl2)
      (simp only [fupd hk1 hk2])
      (exact (h2 k1 k2 hl1 hl2 hne12)))
    (case [true]
      (have e2 (= k2 m)) (exact (Nat.eq_of_beq_eq_true hk2))
      (rw [e2])
      (simp only [fupd hk1 fupd-same])
      (cases hkk (Nat.beq k1 k))
      (case [false]
        (have hne (Not (= k1 k))) (exact (Nat.ne_of_beq_eq_false hkk))
        (have p := (h2 k1 k hl1 hlk hne))
        (exact (And.intro (hw k1 hl1) (excl-rotate h orig (fam k) (dom k) e (:epoch (fam k1)) (And.right p)))))
      (case [true]
        (have e3 (= k1 k)) (exact (Nat.eq_of_beq_eq_true hkk))
        (rw [e3])
        (exact (And.intro (hw k hlk) (excl-rotate h orig (fam k) (dom k) e (:epoch (fam k)) hself))))))
  (case [true]
    (have e1 (= k1 m)) (exact (Nat.eq_of_beq_eq_true hk1))
    (have hk2 (= (Nat.beq k2 m) false)) (apply nbeq-ne) (intro e3) (exact (hne12 (Eq.trans e1 (Eq.symm e3))))
    (simp only [fupd hk2] at hl2)
    (rw [e1])
    (simp only [fupd hk2 fupd-same])
    (have ps (Not (= e (:epoch (fam k2))))) (intro e3) (exact ((hw k2 hl2) (Eq.symm e3)))
    (exact (And.intro ps (excl-fresh h orig n e (fam k2) (dom k2) (And.left (h1 k2 hl2)) hf)))))

;; after `reepoch` world k sees no row of its own epoch
(a/theorem reepoch-self [h :- (=> Nat PRow), n :- Nat, orig :- (=> Nat Nat), v :- PView, d :- (=> Nat Bool), e :- Nat]
  (=> (wf h n orig v d) (forall [a :- Nat] (=> (< a n) (Not (= (:epoch (h a)) e))))
      (excl h orig (:epoch (rotate v e)) (rotate v e) d))
  (intros hw hf)
  (exact (excl-fresh h orig n e (rotate v e) d (wf-rotate h orig n v d e hw) hf)))

;; --- allocation by world k of a logical id i that no live world has and no row carries
(a/theorem fin1-alloc [h :- (=> Nat PRow), n :- Nat, orig :- (=> Nat Nat), fam :- (=> Nat PView),
                       dom :- (=> Nat (=> Nat Bool)), live :- (=> Nat Bool), k :- Nat, i :- Nat, x :- Nat, rs :- (List Nat)]
  (=> (fin1 h n orig fam dom live) (fin2 h orig fam dom live) (= (live k) true)
      (forall [k2 :- Nat] (=> (= (live k2) true) (= (dom k2 i) false)))
      (= (PView.fwd (fam k) i) 0)
      (forall [a :- Nat] (=> (< a n) (Not (= (:id (h a)) i))))
      (= (all-lt (+ n 1) rs) true)
      (= (all-rok (alloc-heap h n i (:epoch (fam k)) x rs) (fupd orig i n) (fam k) rs) true)
      (fin1 (alloc-heap h n i (:epoch (fam k)) x rs) (+ n 1) (fupd orig i n) fam
            (fupd dom k (fupd (dom k) i Bool.true)) live))
  (intros h1 h2 hlk hd hz hf hr hk)
  (simp only [fin1] at h1)
  (simp only [fin2] at h2)
  (simp only [fin1])
  (intros k1 hl1)
  (have q := (h1 k1 hl1))
  (cases hkk (Nat.beq k1 k))
  (case [false]
    (have hne (Not (= k1 k))) (exact (Nat.ne_of_beq_eq_false hkk))
    (have hne2 (Not (= k k1))) (intro e) (exact (hne (Eq.symm e)))
    (rw [(fupd-other dom k (fupd (dom k) i Bool.true) k1 hne)])
    (have p := (And.left (h2 k k1 hlk hl1 hne2)))
    (exact (And.intro (wf-alloc-other h orig n i (:epoch (fam k)) x rs (fam k1) (dom k1) (And.left q) (hd k1 hl1))
             (And.intro (own-alloc-other h orig n i (:epoch (fam k)) x rs (fam k1) (dom k1) (And.left (And.right q)) hf p)
                        (ro-alloc-other h orig n i (:epoch (fam k)) x rs (fam k1) (dom k1) (And.left q)
                                        (And.right (And.right q)) (hd k1 hl1) hf)))))
  (case [true]
    (have e (= k1 k)) (exact (Nat.eq_of_beq_eq_true hkk))
    (rw [e] at q)
    (rw [e])
    (rw [(fupd-same dom k (fupd (dom k) i Bool.true))])
    (exact (And.intro (wf-alloc-self h orig n i x rs (fam k) (dom k) (And.left q) hz (hd k hlk) hr)
             (And.intro (own-alloc-self h orig n i x rs (fam k) (dom k) (And.left (And.right q)) hf hz)
                        (ro-alloc-self h orig n i x rs (fam k) (dom k) (And.left q) (And.right (And.right q)) hz hf hk))))))

(a/theorem fin2-alloc [h :- (=> Nat PRow), n :- Nat, orig :- (=> Nat Nat), fam :- (=> Nat PView),
                       dom :- (=> Nat (=> Nat Bool)), live :- (=> Nat Bool), k :- Nat, i :- Nat, x :- Nat, rs :- (List Nat)]
  (=> (fin1 h n orig fam dom live) (fin2 h orig fam dom live) (= (live k) true)
      (forall [k2 :- Nat] (=> (= (live k2) true) (= (dom k2 i) false)))
      (= (PView.fwd (fam k) i) 0)
      (fin2 (alloc-heap h n i (:epoch (fam k)) x rs) (fupd orig i n) fam
            (fupd dom k (fupd (dom k) i Bool.true)) live))
  (intros h1 h2 hlk hd hz)
  (simp only [fin1] at h1)
  (simp only [fin2] at h2)
  (simp only [fin2])
  (intros k1 k2 hl1 hl2 hne12)
  (have p := (h2 k1 k2 hl1 hl2 hne12))
  (cases hkk (Nat.beq k2 k))
  (case [false]
    (have hne (Not (= k2 k))) (exact (Nat.ne_of_beq_eq_false hkk))
    (rw [(fupd-other dom k (fupd (dom k) i Bool.true) k2 hne)])
    (exact (And.intro (And.left p)
             (excl-alloc-other h orig n i (:epoch (fam k)) x rs (:epoch (fam k1)) (fam k2) (dom k2)
                               (And.left (h1 k2 hl2)) (hd k2 hl2) (And.right p)))))
  (case [true]
    (have e (= k2 k)) (exact (Nat.eq_of_beq_eq_true hkk))
    (rw [e] at p)
    (rw [e])
    (rw [(fupd-same dom k (fupd (dom k) i Bool.true))])
    (have ps (Not (= (:epoch (fam k)) (:epoch (fam k1))))) (intro e3) (exact ((And.left p) (Eq.symm e3)))
    (exact (And.intro (And.left p)
             (excl-alloc-self h orig n i x rs (:epoch (fam k1)) (fam k) (dom k) (And.left (h1 k hlk)) (And.right p) ps hz)))))

;; --- release of world k, and the start (no world has a row)
(a/theorem fin1-release [h :- (=> Nat PRow), n :- Nat, orig :- (=> Nat Nat), fam :- (=> Nat PView),
                         dom :- (=> Nat (=> Nat Bool)), live :- (=> Nat Bool), k :- Nat]
  (=> (fin1 h n orig fam dom live) (fin1 h n orig fam dom (fupd live k Bool.false)))
  (intro h1)
  (simp only [fin1] at h1)
  (simp only [fin1])
  (intros k1 hl1)
  (cases hkk (Nat.beq k1 k))
  (case [false] (simp only [fupd hkk] at hl1) (exact (h1 k1 hl1)))
  (case [true] (simp only [fupd hkk] at hl1) (simp at hl1)))

(a/theorem fin2-release [h :- (=> Nat PRow), orig :- (=> Nat Nat), fam :- (=> Nat PView),
                         dom :- (=> Nat (=> Nat Bool)), live :- (=> Nat Bool), k :- Nat]
  (=> (fin2 h orig fam dom live) (fin2 h orig fam dom (fupd live k Bool.false)))
  (intro h2)
  (simp only [fin2] at h2)
  (simp only [fin2])
  (intros k1 k2 hl1 hl2 hne)
  (cases hk1 (Nat.beq k1 k))
  (case [true] (simp only [fupd hk1] at hl1) (simp at hl1))
  (case [false]
    (simp only [fupd hk1] at hl1)
    (cases hk2 (Nat.beq k2 k))
    (case [true] (simp only [fupd hk2] at hl2) (simp at hl2))
    (case [false] (simp only [fupd hk2] at hl2) (exact (h2 k1 k2 hl1 hl2 hne)))))

(a/theorem wf-empty [h :- (=> Nat PRow), n :- Nat, orig :- (=> Nat Nat), v :- PView, d :- (=> Nat Bool)]
  (=> (forall [j :- Nat] (= (d j) false)) (wf h n orig v d))
  (intro hd) (simp only [wf]) (intros j hj) (rw [(hd j)] at hj) (simp at hj))

(a/theorem own-empty [h :- (=> Nat PRow), n :- Nat, orig :- (=> Nat Nat), v :- PView, d :- (=> Nat Bool)]
  (=> (forall [j :- Nat] (= (d j) false)) (own h n orig v d))
  (intro hd) (simp only [own]) (intros a ha he hj) (rw [(hd (:id (h a)))] at hj) (simp at hj))

(a/theorem ro-empty [h :- (=> Nat PRow), orig :- (=> Nat Nat), v :- PView, d :- (=> Nat Bool)]
  (=> (forall [j :- Nat] (= (d j) false)) (ro h orig v d))
  (intro hd) (simp only [ro]) (intros j hj) (rw [(hd j)] at hj) (simp at hj))

(a/theorem fin1-empty [h :- (=> Nat PRow), n :- Nat, orig :- (=> Nat Nat), fam :- (=> Nat PView),
                       dom :- (=> Nat (=> Nat Bool)), live :- (=> Nat Bool)]
  (=> (forall [k :- Nat, j :- Nat] (= (dom k j) false)) (fin1 h n orig fam dom live))
  (intro hd)
  (simp only [fin1])
  (intros k hl)
  (exact (And.intro (wf-empty h n orig (fam k) (dom k) (hd k))
           (And.intro (own-empty h n orig (fam k) (dom k) (hd k)) (ro-empty h orig (fam k) (dom k) (hd k))))))

(a/theorem fin2-single [h :- (=> Nat PRow), orig :- (=> Nat Nat), fam :- (=> Nat PView),
                        dom :- (=> Nat (=> Nat Bool)), live :- (=> Nat Bool)]
  (=> (forall [k :- Nat, k2 :- Nat] (=> (= (live k) true) (= (live k2) true) (= k k2)))
      (fin2 h orig fam dom live))
  (intro hs)
  (simp only [fin2])
  (intros k1 k2 hl1 hl2 hne)
  (exact (absurd (hs k1 k2 hl1 hl2) hne)))
