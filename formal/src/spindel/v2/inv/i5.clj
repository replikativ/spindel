(ns spindel.v2.inv.i5
  "Literal I5, dep-final clause (§6: no armed dep edge has a final debtor, `lit-i5-dep-final`)
  through `world-step`, kernel-checked (Init only).

  Bundle i5-dep-final xd w = well-formed w && every armed dep edge has a non-final debtor or one in the
  exempt list xd (`dfk`, finality read from the source and task tables: `fin-st`, equal to
  `deb-final`). The bundle goes through the generic step tree (spindel.v2.pres.tree) by its table.
  Primitive edits: an edge edit that keeps (kind, phase, debtor) (`ek5`), a source/task edit that
  keeps the row's finality (`sfin`, `task-done`), new sources/tasks are not final, a new edge is
  fine (`dfk`, given at the call site), edge removals and filters only drop rows. Arming sites
  with a guard: `dep-consumed`/`consume-entry` (re-arm only a non-final debtor, Z#39; the rows
  with that id share its debtor: p3's `edge-debtor-kept`), T7 (`track-fin`: an open trackable source is not
  final; a closed one consumes the edge, Z#48), reactivation (`react-ok`, Z#51). Writes, post,
  release and take keep the source's finality (signal/cell, mailbox, semaphore).

  Finality sites discharge in the same commit (the crux): the escape predicate `jw xd esc w`
  (every edge is fine or escapes by `esc`) and `jw-fire-edge` (T9 on edge y discharges y: a fire
  removes it, marks it fired, or re-arms it only on a non-final debtor; memberships only shrink)
    close/detach (Z#53)  `i5-dep-final-wake-final`: after `wake-closed` every armed dep edge on the closed
                         source is a non-member (members were listed and fired), so T10's
                         `finalize-one` removes it (`close-end`)
    T14, T12, deliver    `i5-dep-final-fold-all`: the fired list holds every dep edge on the debtor
    T6 (await)           `i5-dep-final-await-raw`: an armed member edge on a final debtor is its debtor's
                         recorded pair (`esc6`), and the fast path fires it (a final debtor is
                         fast-ready: `fast-not-final`) while it is a member; after the activation
                         resolved (Z#61) it stays exempt as a non-member pair (`escn`) until the T10
                         of await-post removes it (`jw-fin-fold`)

  Theorems:
    step-i5-dep-final                      i5-dep-final xd w, rule-r-safe raw -> i5-dep-final xd (world-step w it)
    chain-to-i5-dep-final = chain-to-i1-scopes && i5-dep-final []           step-chain-to-i5-dep-final, chain-to-i5-dep-final-empty
    step-lit-i5-dep-final-total  chain-to-i5-dep-final w -> lit-i5-dep-final (world-step w it)   (literal I5, dep-final)"
  (:require [ansatz.core :as a]
            [spindel.v2.pres.exempt :as exempt]
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
            [spindel.v2.inv.i1-scopes :refer :all]))

;; ===========================================================================
;; Part A. Finality, the bundle, its primitives
;; ===========================================================================

;; ---- finality of a debtor read from the source and task tables
(a/defn sfin [s :- SourceRow] Bool (Bool.or (Bool.not (:open s)) (source-delivered s)))
(a/defn find-or [A :- Type :implicit, g :- (=> A Bool), k :- Bool, o :- (Option A)] Bool
  (match o [none k] [(some r) (g r)]))
(a/defn fin-st [xs :- (List SourceRow), ts :- (List TaskRow), d :- Nat] Bool
  (find-or sfin (find-or task-done false (tbl-find task-id d ts)) (tbl-find source-id d xs)))
(a/theorem deb-final-st [w :- World, d :- Nat] (= (deb-final w d) (fin-st (:sources w) (:tasks w) d))
  (have e1 (= (source-find w d) (tbl-find source-id d (:sources w)))) (rfl)
  (have e2 (= (task-find w d) (tbl-find task-id d (:tasks w)))) (rfl)
  (cases hs (tbl-find source-id d (:sources w)))
  (case [some s] (simp only [deb-final fin-st e1 e2 hs find-or sfin]))
  (case [none]
    (cases ht (tbl-find task-id d (:tasks w)))
    (case [none] (simp only [deb-final fin-st e1 e2 hs ht find-or]))
    (case [some t] (simp only [deb-final fin-st e1 e2 hs ht find-or task-done]))))

;; an armed dep edge has a non-final debtor (F) or an exempt one (xd)
(a/defn dfk [xd :- (List Nat), F :- (=> Nat Bool), e :- EdgeRow] Bool
  (Bool.or (Bool.or (Bool.not (Nat.beq (:kind e) ek-dep))
                    (Bool.or (Bool.not (Nat.beq (:phase e) ph-armed)) (Bool.not (F (:debtor e)))))
           (reach-mem (:debtor e) xd)))
(a/defn i5-dep-final-rest [xd :- (List Nat), w :- World] Bool (tbl-all (dfk xd (fin-st (:sources w) (:tasks w))) (:edges w)))
(a/defn i5-dep-final [xd :- (List Nat), w :- World] Bool (Bool.and (well-formed w) (i5-dep-final-rest xd w)))

(a/theorem i5-dep-final-well-formed [xd :- (List Nat), w :- World] (=> (= (i5-dep-final xd w) true) (= (well-formed w) true))
  (intro h) (simp only [i5-dep-final Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem i5-dep-final-rest-of [xd :- (List Nat), w :- World] (=> (= (i5-dep-final xd w) true) (= (i5-dep-final-rest xd w) true))
  (intro h) (simp only [i5-dep-final Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem i5-dep-final-intro [xd :- (List Nat), w :- World]
  (=> (= (well-formed w) true) (= (i5-dep-final-rest xd w) true) (= (i5-dep-final xd w) true))
  (intros h1 h2) (simp only [i5-dep-final h1 h2 Bool.and_self]))
(a/theorem i5-dep-final-parts [xd :- (List Nat), w :- World]
  (=> (= (i5-dep-final xd w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (i5-dep-final-well-formed xd w h))))

;; with no exemption, the rest is literal I5's dep-final clause
(a/theorem dfk-nil [F :- (=> Nat Bool), e :- EdgeRow]
  (= (dfk (List.nil Nat) F e) (Bool.or (Bool.not (Nat.beq (:kind e) ek-dep))
                                       (Bool.or (Bool.not (Nat.beq (:phase e) ph-armed)) (Bool.not (F (:debtor e))))))
  (simp only [dfk reach-mem Bool.or_false]))
(a/theorem i5-dep-final-lit [w :- World] (=> (= (i5-dep-final-rest (List.nil Nat) w) true) (= (lit-i5-dep-final w) true))
  (intro h)
  (simp only [i5-dep-final-rest] at h)
  (simp only [lit-i5-dep-final])
  (apply (tbl-all-mono EdgeRow _ _ _ (:edges w) h))
  (intros e he)
  (simp only [dfk-nil] at he)
  (simp only [dep-final-ok deb-final-st])
  (exact he))

;; finality only lost, exemption only grown
(a/theorem dfk-mono [xd :- (List Nat), yd :- (List Nat), F :- (=> Nat Bool), G :- (=> Nat Bool), e :- EdgeRow]
  (=> (forall [d :- Nat] (=> (= (G d) true) (= (F d) true)))
      (forall [d :- Nat] (=> (= (reach-mem d xd) true) (= (reach-mem d yd) true)))
      (= (dfk xd F e) true) (= (dfk yd G e) true))
  (intros hg hx h)
  (simp only [dfk Bool.or_eq_true] at h)
  (simp only [dfk Bool.or_eq_true])
  (cases h)
  (case [inr b] (exact (Or.inr (hx _ b))))
  (case [inl a]
    (apply Or.inl)
    (cases a)
    (case [inl a1] (exact (Or.inl a1)))
    (case [inr a2]
      (apply Or.inr)
      (cases a2)
      (case [inl b1] (exact (Or.inl b1)))
      (case [inr b2]
        (apply Or.inr)
        (cases hG (G (:debtor e)))
        (case [false] (rfl))
        (case [true] (have q := (hg _ hG)) (rw [q] at b2) (simp at b2))))))

;; ---- fin-st under the table edits
(a/theorem find-or-upd [A :- Type, idf :- (=> A Nat), x :- Nat, f :- (=> A A), g :- (=> A Bool), k :- Bool, d :- Nat,
                        hid :- (forall [r :- A] (= (idf (f r)) (idf r))), hg :- (forall [r :- A] (= (g (f r)) (g r))),
                        xs :- (List A)]
  (= (find-or g k (tbl-find idf d (tbl-upd idf x f xs))) (find-or g k (tbl-find idf d xs)))
  (induction xs)
  (case [nil] (simp only [tbl-upd tbl-find]))
  (case [cons h t ih]
    (cases hx (Nat.beq (idf h) x))
    (case [false]
      (cases hd (Nat.beq (idf h) d))
      (case [false] (simp only [tbl-upd hx tbl-find hd ih]))
      (case [true] (simp only [tbl-upd hx tbl-find hd find-or])))
    (case [true]
      (cases hd (Nat.beq (idf h) d))
      (case [false] (simp only [tbl-upd hx tbl-find (hid h) hd ih]))
      (case [true] (simp only [tbl-upd hx tbl-find (hid h) hd find-or (hg h)])))))

(a/theorem fin-st-supd [x :- Nat, f :- (=> SourceRow SourceRow),
                        hid :- (forall [s :- SourceRow] (= (source-id (f s)) (source-id s))),
                        hg :- (forall [s :- SourceRow] (= (sfin (f s)) (sfin s))),
                        xs :- (List SourceRow), ts :- (List TaskRow), d :- Nat]
  (= (fin-st (tbl-upd source-id x f xs) ts d) (fin-st xs ts d))
  (simp only [fin-st])
  (exact (find-or-upd SourceRow source-id x f sfin _ d hid hg xs)))
(a/theorem fin-st-tupd [x :- Nat, f :- (=> TaskRow TaskRow),
                        hid :- (forall [t :- TaskRow] (= (task-id (f t)) (task-id t))),
                        hg :- (forall [t :- TaskRow] (= (task-done (f t)) (task-done t))),
                        xs :- (List SourceRow), ts :- (List TaskRow), d :- Nat]
  (= (fin-st xs (tbl-upd task-id x f ts) d) (fin-st xs ts d))
  (simp only [fin-st])
  (rw [(find-or-upd TaskRow task-id x f task-done false d hid hg ts)]))

(a/theorem find-or-keep [A :- Type, K :- (=> Nat Bool), idf :- (=> A Nat), g :- (=> A Bool), k :- Bool, d :- Nat, xs :- (List A)]
  (= (find-or g k (tbl-find idf d (tbl-keep K idf xs))) (if (K d) (find-or g k (tbl-find idf d xs)) k))
  (induction xs)
  (case [nil] (cases hk (K d)) (all_goals (simp only [tbl-keep tbl-find find-or hk])))
  (case [cons h t ih]
    (cases hd (Nat.beq (idf h) d))
    (case [false]
      (cases hk (K (idf h)))
      (case [false] (simp only [tbl-keep hk tbl-find hd ih]))
      (case [true] (simp only [tbl-keep hk tbl-find hd ih])))
    (case [true]
      (have e (= (idf h) d)) (exact (Nat.eq_of_beq_eq_true hd))
      (cases hk (K (idf h)))
      (case [false] (have hk2 (= (K d) false)) (rw [← e]) (exact hk) (simp only [tbl-keep hk tbl-find hd ih hk2]))
      (case [true] (have hk2 (= (K d) true)) (rw [← e]) (exact hk) (simp only [tbl-keep hk tbl-find hd hk2])))))

(a/theorem fin-st-keep [K :- (=> Nat Bool), xs :- (List SourceRow), ts :- (List TaskRow), d :- Nat]
  (=> (= (fin-st (tbl-keep K source-id xs) (tbl-keep K task-id ts) d) true) (= (fin-st xs ts d) true))
  (intro h)
  (simp only [fin-st find-or-keep] at h)
  (cases hk (K d))
  (case [false] (simp only [hk find-or] at h) (cases h))
  (case [true] (simp only [hk] at h) (simp only [fin-st]) (exact h)))

(a/theorem find-or-cons [A :- Type, idf :- (=> A Nat), g :- (=> A Bool), k :- Bool, d :- Nat, r :- A, xs :- (List A)]
  (=> (= (g r) false) (= (find-or g k (tbl-find idf d (List.cons A r xs))) true) (= (find-or g k (tbl-find idf d xs)) true))
  (intros hr h)
  (cases hd (Nat.beq (idf r) d))
  (case [false] (simp only [tbl-find hd] at h) (exact h))
  (case [true] (simp only [tbl-find hd find-or hr] at h) (cases h)))

(a/theorem fin-st-sins [r :- SourceRow, xs :- (List SourceRow), ts :- (List TaskRow), d :- Nat]
  (=> (= (sfin r) false) (= (fin-st (List.cons SourceRow r xs) ts d) true) (= (fin-st xs ts d) true))
  (intros hr h) (simp only [fin-st] at h) (simp only [fin-st])
  (exact (find-or-cons SourceRow source-id sfin _ d r xs hr h)))

(a/theorem find-or-k [A :- Type, g :- (=> A Bool), k :- Bool, k2 :- Bool, o :- (Option A)]
  (=> (=> (= k true) (= k2 true)) (= (find-or g k o) true) (= (find-or g k2 o) true))
  (intros hk h)
  (cases o)
  (case [none] (simp only [find-or] at h) (simp only [find-or]) (exact (hk h)))
  (case [some r] (simp only [find-or] at h) (simp only [find-or]) (exact h)))

(a/theorem fin-st-tins [r :- TaskRow, xs :- (List SourceRow), ts :- (List TaskRow), d :- Nat]
  (=> (= (task-done r) false) (= (fin-st xs (List.cons TaskRow r ts) d) true) (= (fin-st xs ts d) true))
  (intros hr h) (simp only [fin-st] at h) (simp only [fin-st])
  (exact (find-or-k SourceRow sfin _ _ _ (find-or-cons TaskRow task-id task-done false d r ts hr) h)))

;; ---- the rest under edits: finality only lost, edges filtered or keyed edits

(a/structure EK5 [] (kind Nat) (phase Nat) (debtor Nat))
(a/defn ek5 [e :- EdgeRow] EK5 (EK5.mk (:kind e) (:phase e) (:debtor e)))
(a/defn dfk5 [xd :- (List Nat), F :- (=> Nat Bool), k :- EK5] Bool
  (Bool.or (Bool.or (Bool.not (Nat.beq (:kind k) ek-dep))
                    (Bool.or (Bool.not (Nat.beq (:phase k) ph-armed)) (Bool.not (F (:debtor k)))))
           (reach-mem (:debtor k) xd)))
(a/theorem dfk-ek [xd :- (List Nat), F :- (=> Nat Bool), e :- EdgeRow] (= (dfk xd F e) (dfk5 xd F (ek5 e))) (rfl))
(a/theorem dfk-key [xd :- (List Nat), F :- (=> Nat Bool), e :- EdgeRow, e2 :- EdgeRow]
  (=> (= (ek5 e2) (ek5 e)) (= (dfk xd F e) true) (= (dfk xd F e2) true))
  (intros he h) (rw [dfk-ek] at h) (rw [dfk-ek he]) (exact h))

(a/theorem fin-same [w :- World, w2 :- World]
  (=> (= (:sources w2) (:sources w)) (= (:tasks w2) (:tasks w))
      (forall [d :- Nat] (=> (= (fin-st (:sources w2) (:tasks w2) d) true) (= (fin-st (:sources w) (:tasks w) d) true))))
  (intros h1 h2 d hd) (rw [h1 h2] at hd) (exact hd))

(a/theorem g5r-gen [xd :- (List Nat), w :- World, w2 :- World]
  (=> (forall [d :- Nat] (=> (= (fin-st (:sources w2) (:tasks w2) d) true) (= (fin-st (:sources w) (:tasks w) d) true)))
      (= (tbl-all (dfk xd (fin-st (:sources w) (:tasks w))) (:edges w2)) true) (= (i5-dep-final-rest xd w2) true))
  (intros hd h)
  (simp only [i5-dep-final-rest])
  (exact (tbl-all-mono EdgeRow _ _
           (fn [e :- EdgeRow, h1 :- (= (dfk xd (fin-st (:sources w) (:tasks w)) e) true)]
             (dfk-mono xd xd _ _ e hd (fn [d :- Nat, hx :- (= (reach-mem d xd) true)] hx) h1))
           (:edges w2) h)))

(a/theorem g5r-same [xd :- (List Nat), w :- World, w2 :- World]
  (=> (= (:sources w2) (:sources w)) (= (:tasks w2) (:tasks w))
      (= (tbl-all (dfk xd (fin-st (:sources w) (:tasks w))) (:edges w2)) true) (= (i5-dep-final-rest xd w2) true))
  (intros h1 h2 h) (exact (g5r-gen xd w w2 (fin-same w w2 h1 h2) h)))

(a/theorem g5r-remove-edge [xd :- (List Nat), w :- World, x :- Nat] (=> (= (i5-dep-final-rest xd w) true) (= (i5-dep-final-rest xd (remove-edge w x)) true))
  (intro h)
  (simp only [i5-dep-final-rest] at h)
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]) (simp only [i5-dep-final-rest]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [remove-edge hf hm])
      (exact (g5r-same xd w (edge-del w x) (rfl) (rfl) (all-sub-del EdgeRow _ edge-id x (:edges w) h))))
    (case [true] (simp only [remove-edge hf hm])
      (exact (g5r-same xd w (comp-upd (edge-del w x) (:creditor e) comp-dec-pending) (rfl) (rfl)
               (all-sub-del EdgeRow _ edge-id x (:edges w) h))))))

(a/theorem g5r-edge-upd [xd :- (List Nat), w :- World, x :- Nat, f :- (=> EdgeRow EdgeRow),
                         hk :- (forall [e :- EdgeRow] (= (ek5 (f e)) (ek5 e)))]
  (=> (= (i5-dep-final-rest xd w) true) (= (i5-dep-final-rest xd (edge-upd w x f)) true))
  (intro h)
  (simp only [i5-dep-final-rest] at h)
  (exact (g5r-same xd w (edge-upd w x f) (rfl) (rfl)
           (tbl-all-upd EdgeRow edge-id x f _ _
             (fn [d :- EdgeRow, hd :- (= (dfk xd (fin-st (:sources w) (:tasks w)) d) true), hx :- (= (Nat.beq (edge-id d) x) true)]
               (dfk-key xd _ d (f d) (hk d) hd))
             (fn [d :- EdgeRow, hd :- (= (dfk xd (fin-st (:sources w) (:tasks w)) d) true), hx :- (= (Nat.beq (edge-id d) x) false)] hd)
             (:edges w) h))))

(a/theorem g5r-mark-edge [xd :- (List Nat), w :- World, x :- Nat] (=> (= (i5-dep-final-rest xd w) true) (= (i5-dep-final-rest xd (mark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [true] (simp only [mark-edge hf hm]) (exact h))
    (case [false] (simp only [mark-edge hf hm])
      (have h1 := (g5r-edge-upd xd w x (edge-set-marked true) (fn [q :- EdgeRow] (Eq.refl (ek5 q))) h))
      (simp only [i5-dep-final-rest] at h1)
      (exact (g5r-same xd (edge-upd w x (edge-set-marked true)) (comp-upd (edge-upd w x (edge-set-marked true)) (:creditor e) comp-inc-pending)
               (rfl) (rfl) h1)))))

(a/theorem g5r-unmark-edge [xd :- (List Nat), w :- World, x :- Nat] (=> (= (i5-dep-final-rest xd w) true) (= (i5-dep-final-rest xd (unmark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]) (exact h))
  (case [some e]
    (cases hm (:marked e))
    (case [false] (simp only [unmark-edge hf hm]) (exact h))
    (case [true] (simp only [unmark-edge hf hm])
      (have h1 := (g5r-edge-upd xd w x (edge-set-marked false) (fn [q :- EdgeRow] (Eq.refl (ek5 q))) h))
      (simp only [i5-dep-final-rest] at h1)
      (exact (g5r-same xd (edge-upd w x (edge-set-marked false)) (comp-upd (edge-upd w x (edge-set-marked false)) (:creditor e) comp-dec-pending)
               (rfl) (rfl) h1)))))

(a/theorem g5r-drop-cred [xd :- (List Nat), w :- World, a :- Nat] (=> (= (i5-dep-final-rest xd w) true) (= (i5-dep-final-rest xd (drop-cred-edges w a)) true))
  (intro h) (simp only [i5-dep-final-rest] at h)
  (exact (g5r-same xd w (drop-cred-edges w a) (rfl) (rfl) (tbl-all-filter EdgeRow _ (cred-ne a) (:edges w) h))))
(a/theorem g5r-drop-act [xd :- (List Nat), w :- World, a :- Nat] (=> (= (i5-dep-final-rest xd w) true) (= (i5-dep-final-rest xd (drop-act w a)) true))
  (intro h) (exact (g5r-drop-cred xd w a h)))
(a/theorem g5r-drop-edges [xd :- (List Nat), w :- World, p :- (=> EdgeRow Bool)] (=> (= (i5-dep-final-rest xd w) true) (= (i5-dep-final-rest xd (drop-edges w p)) true))
  (intro h) (simp only [i5-dep-final-rest] at h)
  (exact (g5r-same xd w (drop-edges w p) (rfl) (rfl) (tbl-all-filter EdgeRow _ p (:edges w) h))))

;; ---- the bundle's primitives with an extra fact

(a/theorem i5-dep-final-edge-upd [xd :- (List Nat), w :- World, x :- Nat, f :- (=> EdgeRow EdgeRow),
                        hid :- (forall [e :- EdgeRow] (= (edge-id (f e)) (edge-id e))),
                        hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                        hc :- (forall [e :- EdgeRow] (= (:creditor (f e)) (:creditor e))),
                        hd :- (forall [e :- EdgeRow] (= (:debtor (f e)) (:debtor e))),
                        hm :- (forall [e :- EdgeRow] (= (:marked (f e)) (:marked e))),
                        hk5 :- (forall [e :- EdgeRow] (= (ek5 (f e)) (ek5 e)))]
  (=> (= (i5-dep-final xd w) true) (= (i5-dep-final xd (edge-upd w x f)) true))
  (intro h)
  (exact (i5-dep-final-intro xd _ (well-formed-edge-upd w x f hid hk hc hd hm (i5-dep-final-well-formed xd w h)) (g5r-edge-upd xd w x f hk5 (i5-dep-final-rest-of xd w h)))))

(a/theorem edge-set-phase-dfk [xd :- (List Nat), F :- (=> Nat Bool), p :- Nat, e :- EdgeRow]
  (=> (= (Nat.beq p ph-armed) false) (= (dfk xd F (edge-set-phase p e)) true))
  (intro hp) (simp only [dfk edge-set-phase hp Bool.not_false Bool.true_or Bool.or_true]))

(a/theorem i5-dep-final-edge-set-phase [xd :- (List Nat), w :- World, x :- Nat, p :- Nat, hp :- (= (Nat.beq p ph-armed) false)]
  (=> (= (i5-dep-final xd w) true) (= (i5-dep-final xd (edge-upd w x (edge-set-phase p))) true))
  (intro h)
  (have r := (i5-dep-final-rest-of xd w h))
  (simp only [i5-dep-final-rest] at r)
  (exact (i5-dep-final-intro xd _ (well-formed-edge-set-phase w x p (i5-dep-final-well-formed xd w h))
           (g5r-same xd w (edge-upd w x (edge-set-phase p)) (rfl) (rfl)
             (tbl-all-upd EdgeRow edge-id x (edge-set-phase p) (dfk xd (fin-st (:sources w) (:tasks w))) (dfk xd (fin-st (:sources w) (:tasks w)))
               (fn [d :- EdgeRow, h1 :- (= (dfk xd (fin-st (:sources w) (:tasks w)) d) true), hx :- (= (Nat.beq (edge-id d) x) true)]
                 (edge-set-phase-dfk xd (fin-st (:sources w) (:tasks w)) p d hp))
               (fn [d :- EdgeRow, h1 :- (= (dfk xd (fin-st (:sources w) (:tasks w)) d) true), hx :- (= (Nat.beq (edge-id d) x) false)] h1)
               (:edges w) r)))))

(a/theorem i5-dep-final-source-upd [xd :- (List Nat), w :- World, x :- Nat, f :- (=> SourceRow SourceRow),
                          hid :- (forall [s :- SourceRow] (= (source-id (f s)) (source-id s))),
                          hg :- (forall [s :- SourceRow] (= (sfin (f s)) (sfin s)))]
  (=> (= (i5-dep-final xd w) true) (= (i5-dep-final xd (source-upd w x f)) true))
  (intro h)
  (have r := (i5-dep-final-rest-of xd w h))
  (simp only [i5-dep-final-rest] at r)
  (have e (forall [d :- Nat] (=> (= (fin-st (:sources (source-upd w x f)) (:tasks (source-upd w x f)) d) true)
                                 (= (fin-st (:sources w) (:tasks w) d) true))))
  (intros d hd) (simp only [source-upd set-sources fin-st-supd x f hid hg] at hd) (exact hd)
  (exact (i5-dep-final-intro xd _ (well-formed-source-upd w x f hid (i5-dep-final-well-formed xd w h)) (g5r-gen xd w (source-upd w x f) e r))))

(a/theorem i5-dep-final-task-upd [xd :- (List Nat), w :- World, x :- Nat, f :- (=> TaskRow TaskRow),
                        hid :- (forall [t :- TaskRow] (= (task-id (f t)) (task-id t))),
                        hg :- (forall [t :- TaskRow] (= (task-done (f t)) (task-done t)))]
  (=> (= (i5-dep-final xd w) true) (= (i5-dep-final xd (task-upd w x f)) true))
  (intro h)
  (have r := (i5-dep-final-rest-of xd w h))
  (simp only [i5-dep-final-rest] at r)
  (have e (forall [d :- Nat] (=> (= (fin-st (:sources (task-upd w x f)) (:tasks (task-upd w x f)) d) true)
                                 (= (fin-st (:sources w) (:tasks w) d) true))))
  (intros d hd) (simp only [task-upd set-tasks fin-st-tupd x f hid hg] at hd) (exact hd)
  (exact (i5-dep-final-intro xd _ (well-formed-task-upd w x f hid (i5-dep-final-well-formed xd w h)) (g5r-gen xd w (task-upd w x f) e r))))

(a/theorem sfin-new-source [id :- Nat, o :- Nat, k :- Nat, v :- Nat] (= (sfin (new-source id o k v)) false)
  (simp only [sfin new-source source-delivered Bool.not_true Bool.false_or])
  (have z (= (Nat.blt 0 0) false)) (rfl)
  (simp only [z Bool.and_false]))

;; C0: every fresh source row (new-source, new-link, new-stream) is open with version 0
(a/theorem sfin-mk [id :- Nat, o :- Nat, k :- Nat, v :- Nat, hd :- Nat, q :- (List Nat), rt :- Nat, n :- Nat, t :- Nat, fl :- Bool, mx :- Nat]
  (= (sfin (SourceRow.mk id o k v 0 true hd q rt n t fl mx)) false)
  (simp only [sfin source-delivered Bool.not_true Bool.false_or])
  (have z (= (Nat.blt 0 0) false)) (rfl)
  (simp only [z Bool.and_false]))

(a/theorem i5-dep-final-source-ins [xd :- (List Nat), w :- World, r :- SourceRow, hs :- (= (sfin r) false)]
  (=> (= (source-id r) (:next-id w)) (= (i5-dep-final xd w) true) (= (i5-dep-final xd (bump (source-ins w r))) true))
  (intros hi h)
  (have rr := (i5-dep-final-rest-of xd w h))
  (simp only [i5-dep-final-rest] at rr)
  (have e (forall [d :- Nat] (=> (= (fin-st (:sources (bump (source-ins w r))) (:tasks (bump (source-ins w r))) d) true)
                                 (= (fin-st (:sources w) (:tasks w) d) true))))
  (intros d hd) (simp only [bump set-next-id source-ins set-sources tbl-ins] at hd) (exact (fin-st-sins r _ _ d hs hd))
  (exact (i5-dep-final-intro xd _ (well-formed-source-ins-fresh w r hi (i5-dep-final-well-formed xd w h)) (g5r-gen xd w (bump (source-ins w r)) e rr))))

(a/theorem i5-dep-final-task-ins [xd :- (List Nat), w :- World, r :- TaskRow, hs :- (= (task-done r) false)]
  (=> (= (task-id r) (:next-id w)) (= (i5-dep-final xd w) true) (= (i5-dep-final xd (bump (task-ins w r))) true))
  (intros hi h)
  (have rr := (i5-dep-final-rest-of xd w h))
  (simp only [i5-dep-final-rest] at rr)
  (have e (forall [d :- Nat] (=> (= (fin-st (:sources (bump (task-ins w r))) (:tasks (bump (task-ins w r))) d) true)
                                 (= (fin-st (:sources w) (:tasks w) d) true))))
  (intros d hd) (simp only [bump set-next-id task-ins set-tasks tbl-ins] at hd) (exact (fin-st-tins r _ _ d hs hd))
  (exact (i5-dep-final-intro xd _ (well-formed-task-ins-fresh w r hi (i5-dep-final-well-formed xd w h)) (g5r-gen xd w _ e rr))))

(a/theorem i5-dep-final-insert-edge-fresh [xd :- (List Nat), w :- World, e :- EdgeRow, hd :- (= (dfk xd (fin-st (:sources w) (:tasks w)) e) true)]
  (=> (= (edge-ok-in w e) true) (= (i5-dep-final xd w) true) (= (i5-dep-final xd (insert-edge-fresh w e)) true))
  (intros he h)
  (have rr := (i5-dep-final-rest-of xd w h))
  (simp only [i5-dep-final-rest] at rr)
  (have r2 (= (tbl-all (dfk xd (fin-st (:sources w) (:tasks w))) (:edges (insert-edge-fresh w e))) true))
  (simp only [insert-edge-fresh bump set-next-id insert-edge edge-ins set-edges tbl-ins tbl-all rr Bool.and_true])
  (exact hd)
  (exact (i5-dep-final-intro xd _ (well-formed-insert-edge-fresh w e he (i5-dep-final-well-formed xd w h)) (g5r-same xd w (insert-edge-fresh w e) (rfl) (rfl) r2))))

(a/theorem i5-dep-final-insert-edge-checked [xd :- (List Nat), w :- World, e :- EdgeRow, hd :- (= (dfk xd (fin-st (:sources w) (:tasks w)) e) true)]
  (=> (= (i5-dep-final xd w) true) (= (i5-dep-final xd (insert-edge-checked w e)) true))
  (intro h)
  (cases hk (edge-ok-in w e))
  (simp only [insert-edge-checked hk]) (exact h)
  (simp only [insert-edge-checked hk]) (exact (i5-dep-final-insert-edge-fresh xd w e hd hk h)))

(a/theorem i5-dep-final-filter-world [xd :- (List Nat), w :- World, K :- (=> Nat Bool)]
  (=> (= (i5-dep-final xd w) true) (= (filter-safe-for K w) true) (= (i5-dep-final xd (filter-world K w)) true))
  (intros h hf)
  (have rr := (i5-dep-final-rest-of xd w h))
  (simp only [i5-dep-final-rest] at rr)
  (have e (forall [d :- Nat] (=> (= (fin-st (:sources (filter-world K w)) (:tasks (filter-world K w)) d) true)
                                 (= (fin-st (:sources w) (:tasks w) d) true))))
  (intros d hd) (simp only [filter-world] at hd) (exact (fin-st-keep K _ _ d hd))
  (have r2 (= (tbl-all (dfk xd (fin-st (:sources w) (:tasks w))) (:edges (filter-world K w))) true))
  (simp only [filter-world])
  (exact (tbl-all-keep EdgeRow K edge-id _ _ (fn [q :- EdgeRow, h1 :- (= (dfk xd (fin-st (:sources w) (:tasks w)) q) true), h2 :- (= (K (edge-id q)) true)] h1) (:edges w) rr))
  (exact (i5-dep-final-intro xd _ (well-formed-filter-world w K (i5-dep-final-well-formed xd w h) hf) (g5r-gen xd w (filter-world K w) e r2))))

;; i5-dep-final's exempt form (spindel.v2.pres.exempt; recorded, no aliases yet): finality sites discharge in
;; the same commit through the escape predicate `jw` (see the namespace docstring)
(exempt/defexempt 'i5-dep-final
  :form "i5-dep-final xd w" :ids "debtor ids: an armed dep edge on a final debtor in xd is allowed" :commit "i5-dep-final [] (chain-to-i5-dep-final)")
(def G5 (mk-bundle 'i5-dep-final '[x5d :- (List Nat)] "i5-dep-final-"
          {'well-formed-edge-upd ['(fn [e :- EdgeRow] (Eq.refl (ek5 e))) 8]
           'well-formed-source-upd ['(fn [s :- SourceRow] (Eq.refl (sfin s))) 4]
           'well-formed-task-upd ['(fn [t :- TaskRow] (Eq.refl (task-done t))) 4]
           'well-formed-source-ins-fresh ['(sfin-mk _ _ _ _ _ _ _ _ _ _ _) 2]
           'well-formed-task-ins-fresh ['(Eq.refl false) 2]
           'well-formed-insert-edge-fresh ['(Eq.refl true) 2]
           'well-formed-insert-edge-checked ['(Eq.refl true) 2]
           'well-formed-edge-set-phase ['(Eq.refl false) 3]
           'well-formed-serve-or ['(fn [s :- SourceRow] (Eq.refl (sfin s))) 5]}))
(swap! (:renames G5) assoc 'well-formed-parts 'i5-dep-final-parts 'well-formed-edge-upd 'i5-dep-final-edge-upd 'well-formed-source-upd 'i5-dep-final-source-upd
       'well-formed-task-upd 'i5-dep-final-task-upd 'well-formed-source-ins-fresh 'i5-dep-final-source-ins 'well-formed-task-ins-fresh 'i5-dep-final-task-ins
       'well-formed-insert-edge-fresh 'i5-dep-final-insert-edge-fresh 'well-formed-insert-edge-checked 'i5-dep-final-insert-edge-checked
       'well-formed-filter-world 'i5-dep-final-filter-world 'well-formed-edge-set-phase 'i5-dep-final-edge-set-phase)
(defpart G5 :reads '[edges sources tasks])
(prim! G5 'well-formed-remove-edge '(g5r-remove-edge x5d w x R))
(prim! G5 'well-formed-mark-edge '(g5r-mark-edge x5d w x R))
(prim! G5 'well-formed-unmark-edge '(g5r-unmark-edge x5d w x R))
(prim! G5 'well-formed-drop-cred-edges '(g5r-drop-cred x5d w a R))
(prim! G5 'well-formed-drop-act '(g5r-drop-act x5d w a R))
(prim! G5 'well-formed-drop-edges '(g5r-drop-edges x5d w p R))
;; i5-dep-final on the generic tree (spindel.v2.pres.tree): its table. Its own proofs follow.
(tree/part! G5
  :over '{well-formed-serve-or      i5-dep-final-serve-or
          well-formed-dep-consumed  i5-dep-final-dep-consumed
          well-formed-consume-entry i5-dep-final-consume-entry
          well-formed-dispatch-raw  i5-dep-final-dispatch-raw
          well-formed-write-raw     i5-dep-final-write-raw
          well-formed-t-post        i5-dep-final-t-post
          well-formed-t-release     i5-dep-final-t-release
          well-formed-t-take        i5-dep-final-t-take
          well-formed-deliver-res   i5-dep-final-deliver-res
          well-formed-append-raw    i5-dep-final-append-raw
          well-formed-t-append      i5-dep-final-t-append
          well-formed-close-source-ended i5-dep-final-close-source-ended
          well-formed-detach-source i5-dep-final-detach-source
          well-formed-debtor-side   i5-dep-final-debtor-side
          well-formed-complete-body i5-dep-final-complete-body
          well-formed-t-deliver     i5-dep-final-t-deliver
          well-formed-react-add     i5-dep-final-react-add
          well-formed-track-raw     i5-dep-final-track-raw
          well-formed-await-raw     i5-dep-final-await-raw
          well-formed-t2-write            i5-dep-final-t2-write}
  ;; ---- facts from the path: the fired or consumed edge is the world's (the companion edge-debtor-kept); T7's
  ;; source is trackable
  :ctx '{well-formed-dep-consumed  [(= (edge-debtor-kept (:id e) (:debtor e) w) true)]
         well-formed-consume-entry [(= (edge-debtor-kept (:id e) (:debtor e) w) true)]
         well-formed-track-raw     [(= (trackable s) true)]}
  :pass '{well-formed-fire-edge   {well-formed-fire-dep [(edge-debtor-kept-of-mem w e (base-of w h) (tbl-find-mem EdgeRow edge-id x e (:edges w) hf))]}   ; edge-find found it
          well-formed-settle-edge {well-formed-fire-dep [(edge-debtor-kept-of-mem w e (base-of w h) (tbl-find-mem EdgeRow edge-id x e (:edges w) hf))]}
          well-formed-t7-track          {well-formed-track-raw [hk]}})                                                                         ; T7's guard


;; ---- an edit of edge id y whose new rows are fine (edge-debtor-kept: the rows with id y have debtor d)

(a/theorem i5-dep-final-edge-upd-q [xd :- (List Nat), w :- World, x :- Nat, f :- (=> EdgeRow EdgeRow),
                          hid :- (forall [e :- EdgeRow] (= (edge-id (f e)) (edge-id e))),
                          hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                          hc :- (forall [e :- EdgeRow] (= (:creditor (f e)) (:creditor e))),
                          hd :- (forall [e :- EdgeRow] (= (:debtor (f e)) (:debtor e))),
                          hm :- (forall [e :- EdgeRow] (= (:marked (f e)) (:marked e))),
                          q :- (= (tbl-all (same-id-then edge-id x (fn [r :- EdgeRow] (dfk xd (fin-st (:sources w) (:tasks w)) (f r)))) (:edges w)) true)]
  (=> (= (i5-dep-final xd w) true) (= (i5-dep-final xd (edge-upd w x f)) true))
  (intro h)
  (have r := (i5-dep-final-rest-of xd w h))
  (simp only [i5-dep-final-rest] at r)
  (have b := (tbl-all-mono2 EdgeRow (dfk xd (fin-st (:sources w) (:tasks w)))
               (same-id-then edge-id x (fn [r :- EdgeRow] (dfk xd (fin-st (:sources w) (:tasks w)) (f r))))
               (both (dfk xd (fin-st (:sources w) (:tasks w))) (same-id-then edge-id x (fn [r :- EdgeRow] (dfk xd (fin-st (:sources w) (:tasks w)) (f r)))))
               (fn [e :- EdgeRow, h1 :- (= (dfk xd (fin-st (:sources w) (:tasks w)) e) true),
                    h2 :- (= (same-id-then edge-id x (fn [r :- EdgeRow] (dfk xd (fin-st (:sources w) (:tasks w)) (f r))) e) true)]
                 (both-of EdgeRow _ _ e h1 h2))
               (:edges w) r q))
  (have r2 (= (tbl-all (dfk xd (fin-st (:sources w) (:tasks w))) (:edges (edge-upd w x f))) true))
  (simp only [edge-upd set-edges])
  (apply (tbl-all-upd EdgeRow edge-id x f _ _ _ _ (:edges w) b))
  (intros e hb hx)
  (have s := (both-right EdgeRow _ _ e hb))
  (simp only [same-id-then hx Bool.not_true Bool.false_or] at s)
  (exact s)
  (intros e hb hx)
  (exact (both-left EdgeRow _ _ e hb))
  (exact (i5-dep-final-intro xd _ (well-formed-edge-upd w x f hid hk hc hd hm (i5-dep-final-well-formed xd w h)) (g5r-same xd w (edge-upd w x f) (rfl) (rfl) r2))))

(a/theorem i5-dep-final-edge-debtor-kept-q [xd :- (List Nat), kxy :- Nat, kxd :- Nat, w :- World, f :- (=> EdgeRow EdgeRow),
                    hf :- (forall [r :- EdgeRow] (=> (= (Nat.beq (:debtor r) kxd) true) (= (dfk xd (fin-st (:sources w) (:tasks w)) (f r)) true)))]
  (=> (= (edge-debtor-kept-rest kxy kxd w) true)
      (= (tbl-all (same-id-then edge-id kxy (fn [r :- EdgeRow] (dfk xd (fin-st (:sources w) (:tasks w)) (f r)))) (:edges w)) true))
  (intro h)
  (simp only [edge-debtor-kept-rest Bool.and_eq_true] at h)
  (apply (tbl-all-mono EdgeRow (deb-at kxy kxd) _ _ (:edges w) (And.right h)))
  (intros r hr)
  (cases hx (Nat.beq (:id r) kxy))
  (case [false] (have hx2 (= (Nat.beq (edge-id r) kxy) false)) (exact hx) (simp only [same-id-then hx2 Bool.not_false Bool.true_or]))
  (case [true]
    (have hx2 (= (Nat.beq (edge-id r) kxy) true)) (exact hx)
    (simp only [deb-at hx Bool.not_true Bool.false_or] at hr)
    (simp only [same-id-then hx2 Bool.not_true Bool.false_or])
    (exact (hf r hr))))

;; a row with a non-final debtor is fine
(a/theorem dfk-nonfinal [xd :- (List Nat), F :- (=> Nat Bool), e :- EdgeRow]
  (=> (= (F (:debtor e)) false) (= (dfk xd F e) true))
  (intro h) (simp only [dfk h Bool.not_false Bool.or_true Bool.true_or]))

(a/theorem rearm-ok [xd :- (List Nat), w :- World, d :- Nat, v :- Nat, ver :- Nat, r :- EdgeRow]
  (=> (= (deb-final w d) false) (= (Nat.beq (:debtor r) d) true)
      (= (dfk xd (fin-st (:sources w) (:tasks w)) (edge-rearm v ver r)) true))
  (intros hf h)
  (have e (= (:debtor r) d)) (exact (Nat.eq_of_beq_eq_true h))
  (have f2 (= (fin-st (:sources w) (:tasks w) (:debtor (edge-rearm v ver r))) false))
  (simp only [edge-rearm e]) (rw [← deb-final-st]) (exact hf)
  (exact (dfk-nonfinal xd _ _ f2)))

(a/theorem setarm-ok [xd :- (List Nat), w :- World, d :- Nat, r :- EdgeRow]
  (=> (= (deb-final w d) false) (= (Nat.beq (:debtor r) d) true)
      (= (dfk xd (fin-st (:sources w) (:tasks w)) (edge-set-phase ph-armed r)) true))
  (intros hf h)
  (have e (= (:debtor r) d)) (exact (Nat.eq_of_beq_eq_true h))
  (have f2 (= (fin-st (:sources w) (:tasks w) (:debtor (edge-set-phase ph-armed r))) false))
  (simp only [edge-set-phase e]) (rw [← deb-final-st]) (exact hf)
  (exact (dfk-nonfinal xd _ _ f2)))


(tree/restate! G5 '[well-formed-remove-edge])
(a/theorem i5-dep-final-dep-consumed [x5d :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (edge-debtor-kept (:id e) (:debtor e) w) true) (= (i5-dep-final x5d w) true) (= (i5-dep-final x5d (dep-consumed w e)) true))
  (intros hx h)
  (cases hf (deb-final w (:debtor e)))
  (simp only [dep-consumed hf])
  (exact (i5-dep-final-edge-upd-q x5d w (:id e) (edge-rearm (deb-value w (:debtor e)) (deb-version w (:debtor e)))
           (edge-rearm-edge-id _ _) (edge-rearm-kind _ _) (edge-rearm-creditor _ _) (edge-rearm-debtor _ _) (edge-rearm-marked _ _)
           (i5-dep-final-edge-debtor-kept-q x5d (:id e) (:debtor e) w _ (fn [r :- EdgeRow, hr :- (= (Nat.beq (:debtor r) (:debtor e)) true)] (rearm-ok x5d w (:debtor e) (deb-value w (:debtor e)) (deb-version w (:debtor e)) r hf hr)) (edge-debtor-kept-rest-of _ _ w hx)) h))
  (simp only [dep-consumed hf]) (exact (i5-dep-final-remove-edge x5d w (:id e) h)))

(tree/restate! G5 '[well-formed-fire-edge])
(a/theorem i5-dep-final-serve-or [x5d :- (List Nat), w :- World, x :- Nat, res :- RunResult, keep :- (=> SourceRow SourceRow),
                        hk :- (forall [s :- SourceRow] (= (source-id (keep s)) (source-id s))),
                        hg :- (forall [s :- SourceRow] (= (sfin (keep s)) (sfin s)))]
  (=> (= (i5-dep-final x5d w) true) (= (i5-dep-final x5d (serve-or w x res keep)) true))
  (intro h)
  (cases hz (Nat.beq (oldest-waiter w x) 0))
  (simp only [serve-or hz]) (exact (i5-dep-final-fire-edge x5d res w _ h))
  (simp only [serve-or hz]) (exact (i5-dep-final-source-upd x5d w x keep hk hg h)))

(tree/restate! G5 '[well-formed-edge-set-phase well-formed-remove-edge])
(a/theorem i5-dep-final-consume-entry [x5d :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (edge-debtor-kept (:id e) (:debtor e) w) true) (= (i5-dep-final x5d w) true) (= (i5-dep-final x5d (consume-entry w e)) true))
  (intros hx h)
  (cases hf (deb-final w (:debtor e)))
  (cases hr (Nat.beq (:cont e) cont-restart))
  (simp only [consume-entry hr hf])
  (exact (i5-dep-final-edge-upd-q x5d w (:id e) (edge-rearm (deb-value w (:debtor e)) (deb-version w (:debtor e)))
           (edge-rearm-edge-id _ _) (edge-rearm-kind _ _) (edge-rearm-creditor _ _) (edge-rearm-debtor _ _) (edge-rearm-marked _ _)
           (i5-dep-final-edge-debtor-kept-q x5d (:id e) (:debtor e) w _ (fn [r :- EdgeRow, hr :- (= (Nat.beq (:debtor r) (:debtor e)) true)] (rearm-ok x5d w (:debtor e) (deb-value w (:debtor e)) (deb-version w (:debtor e)) r hf hr)) (edge-debtor-kept-rest-of _ _ w hx)) h))
  (simp only [consume-entry hr hf])
  (exact (i5-dep-final-edge-upd-q x5d w (:id e) (edge-set-phase ph-armed)
           (edge-set-phase-edge-id _) (edge-set-phase-kind _) (edge-set-phase-creditor _) (edge-set-phase-debtor _) (edge-set-phase-marked _)
           (i5-dep-final-edge-debtor-kept-q x5d (:id e) (:debtor e) w _ (fn [r :- EdgeRow, hr :- (= (Nat.beq (:debtor r) (:debtor e)) true)] (setarm-ok x5d w (:debtor e) r hf hr)) (edge-debtor-kept-rest-of _ _ w hx)) h))
  (simp only [consume-entry hf]) (exact (i5-dep-final-remove-edge x5d w (:id e) h)))

(a/theorem find-or-upd-at [A :- Type, idf :- (=> A Nat), x :- Nat, f :- (=> A A), g :- (=> A Bool), k :- Bool, d :- Nat, s :- A,
                           hid :- (forall [r :- A] (= (idf (f r)) (idf r))), hg :- (= (g (f s)) (g s)), xs :- (List A)]
  (=> (= (tbl-find idf x xs) (Option.some A s))
      (= (find-or g k (tbl-find idf d (tbl-upd idf x f xs))) (find-or g k (tbl-find idf d xs))))
  (induction xs)
  (case [nil] (intro h) (simp only [tbl-find] at h) (cases h))
  (case [cons h t ih]
    (intro hs)
    (cases hx (Nat.beq (idf h) x))
    (case [false]
      (simp only [tbl-find hx] at hs)
      (cases hd (Nat.beq (idf h) d))
      (case [false] (simp only [tbl-upd hx tbl-find hd (ih hs)]))
      (case [true] (simp only [tbl-upd hx tbl-find hd find-or])))
    (case [true]
      (simp only [tbl-find hx Option.some.injEq] at hs)
      (rw [← hs] at hg)
      (have ex (= (idf h) x)) (exact (Nat.eq_of_beq_eq_true hx))
      (have hd2 (= (Nat.beq (idf (f h)) d) (Nat.beq (idf h) d))) (rw [hid])
      (cases hd (Nat.beq (idf h) d))
      (case' [false])
      (have ne (= (Nat.beq d x) false))
      (cases q (Nat.beq d x))
      (case' [false]) (rfl)
      (have ed (= d x)) (exact (Nat.eq_of_beq_eq_true q)) (rw [← ex] at ed) (rw [ed] at hd) (simp [Nat.beq_refl] at hd)
      (simp only [tbl-upd hx tbl-find hd2 hd (tbl-find-upd-ne A idf x d f hid t ne)])
      (simp only [tbl-upd hx tbl-find hd2 hd find-or hg]))))

(a/theorem i5-dep-final-source-upd-at [xd :- (List Nat), w :- World, x :- Nat, f :- (=> SourceRow SourceRow), s :- SourceRow,
                             hid :- (forall [q :- SourceRow] (= (source-id (f q)) (source-id q))), hg :- (= (sfin (f s)) (sfin s))]
  (=> (= (source-find w x) (Option.some SourceRow s)) (= (i5-dep-final xd w) true) (= (i5-dep-final xd (source-upd w x f)) true))
  (intros hs h)
  (have r := (i5-dep-final-rest-of xd w h))
  (simp only [i5-dep-final-rest] at r)
  (have e (forall [d :- Nat] (=> (= (fin-st (:sources (source-upd w x f)) (:tasks (source-upd w x f)) d) true)
                                 (= (fin-st (:sources w) (:tasks w) d) true))))
  (intros d hd)
  (simp only [source-upd set-sources fin-st (find-or-upd-at SourceRow source-id x f sfin (find-or task-done false (tbl-find task-id d (:tasks w))) d s hid hg (:sources w) hs)] at hd)
  (simp only [fin-st]) (exact hd)
  (exact (i5-dep-final-intro xd _ (well-formed-source-upd w x f hid (i5-dep-final-well-formed xd w h)) (g5r-gen xd w (source-upd w x f) e r))))

(a/theorem sfin-write [v :- Nat, s :- SourceRow] (=> (= (writable s) true) (= (sfin (source-write v s)) (sfin s)))
  (intro h)
  (simp only [writable Bool.and_eq_true Bool.or_eq_true] at h)
  (have nd (= (once-kind (:kind s)) false))
  (have hk := (And.right h))
  (cases hk)
  (case [inl a] (have e (= (:kind s) sk-signal)) (exact (Nat.eq_of_beq_eq_true a)) (simp only [e once-kind]))
  (case [inr b] (have e (= (:kind s) sk-cell)) (exact (Nat.eq_of_beq_eq_true b)) (simp only [e once-kind]))
  (simp only [sfin source-write source-delivered nd Bool.false_and]))
(a/theorem sfin-bump [k :- Nat, s :- SourceRow] (=> (= (open-kind k s) true) (= (once-kind k) false) (= (sfin (source-bump s)) (sfin s)))
  (intros h hk)
  (simp only [open-kind Bool.and_eq_true] at h)
  (have e (= (:kind s) k)) (exact (Nat.eq_of_beq_eq_true (And.left h)))
  (simp only [sfin source-bump source-delivered e hk Bool.false_and]))
(a/theorem sfin-consume [s :- SourceRow] (=> (= (takeable s) true) (= (sfin (source-consume s)) (sfin s)))
  (intro h)
  (simp only [takeable Bool.or_eq_true] at h)
  (have nd (= (once-kind (:kind s)) false))
  (cases h)
  (case [inl a] (have e (= (:kind s) sk-mailbox)) (exact (Nat.eq_of_beq_eq_true a)) (simp only [e once-kind]))
  (case [inr b] (have e (= (:kind s) sk-semaphore)) (exact (Nat.eq_of_beq_eq_true b)) (simp only [e once-kind]))
  (cases ha (source-available s)) (all_goals (cases hm (Nat.beq (:kind s) sk-mailbox)))
  (all_goals (simp only [sfin source-consume ha hm source-delivered nd Bool.false_and])))

(tree/restate! G5 '[well-formed-fire-edge well-formed-nat-fold well-formed-mark-edge])
(a/theorem i5-dep-final-write-raw [x5d :- (List Nat), w :- World, x :- Nat, v :- Nat, s :- SourceRow]
  (=> (= (source-find w x) (Option.some SourceRow s)) (= (writable s) true) (= (i5-dep-final x5d w) true) (= (i5-dep-final x5d (write-raw w x v)) true))
  (intros hs hw h)
  (simp only [write-raw])
  (exact (i5-dep-final-nat-fold x5d mark-edge (i5-dep-final-mark-edge x5d) (mark-targets (dirty-set w x) (:edges w)) _
           (i5-dep-final-nat-fold x5d (fire-edge (RunResult.mk res-ok v)) (i5-dep-final-fire-edge x5d (RunResult.mk res-ok v))
             (edges-onto x (:edges w)) _
             (i5-dep-final-source-upd-at x5d w x (source-write v) s (source-write-source-id v) (sfin-write v s hw) hs h)))))
(a/theorem i5-dep-final-t2-write [x5d :- (List Nat), w :- World, x :- Nat, v :- Nat]   ; T2 hands its guard's row to the write
  (=> (= (i5-dep-final x5d w) true) (= (i5-dep-final x5d (:world (t2-write w x v))) true))
  (intro h)
  (cases hs (source-find w x)) (case' [some s]) (case' [none])
  (simp only [t2-write hs refuse]) (exact h)
  (cases hg (writable s))
  (simp only [t2-write hs hg refuse]) (exact h)
  (simp only [t2-write hs hg accept]) (exact (i5-dep-final-write-raw x5d w x v s hs hg h)))

(a/theorem i5-dep-final-t-post [x5d :- (List Nat), w :- World, x :- Nat, v :- Nat]
  (=> (= (i5-dep-final x5d w) true) (= (i5-dep-final x5d (:world (t-post w x v))) true))
  (intro h)
  (cases hs (source-find w x)) (case' [some s]) (case' [none])
  (simp only [t-post hs refuse]) (exact h)
  (cases hg (open-kind sk-mailbox s))
  (simp only [t-post hs hg refuse]) (exact h)
  (simp only [t-post hs hg accept post-raw])
  (exact (i5-dep-final-serve-or x5d (source-upd w x source-bump) x _ (source-enqueue v) (source-enqueue-id v) (fn [q :- SourceRow] (Eq.refl (sfin q)))
           (i5-dep-final-source-upd-at x5d w x source-bump s source-bump-id (sfin-bump sk-mailbox s hg (rfl)) hs h))))

(a/theorem i5-dep-final-t-release [x5d :- (List Nat), w :- World, x :- Nat]
  (=> (= (i5-dep-final x5d w) true) (= (i5-dep-final x5d (:world (t-release w x))) true))
  (intro h)
  (cases hs (source-find w x)) (case' [some s]) (case' [none])
  (simp only [t-release hs refuse]) (exact h)
  (cases hg (releasable s))
  (simp only [t-release hs hg refuse]) (exact h)
  (simp only [t-release hs hg accept release-raw])
  (exact (i5-dep-final-serve-or x5d (source-upd w x source-bump) x _ source-permit source-permit-id (fn [q :- SourceRow] (Eq.refl (sfin q)))
           (i5-dep-final-source-upd-at x5d w x source-bump s source-bump-id (sfin-bump sk-semaphore s (releasable-open s hg) (rfl)) hs h))))

(tree/restate! G5 '[well-formed-take-park well-formed-run-upd well-formed-bump])
(a/theorem i5-dep-final-t-take [x5d :- (List Nat), w :- World, st :- Nat, x :- Nat, k :- Nat, fresh :- Nat]
  (=> (= (i5-dep-final x5d w) true) (= (i5-dep-final x5d (:world (t-take w st x k fresh))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t-take ht refuse]) (exact h)
  (cases hs (source-find w x)) (case' [some s]) (case' [none])
  (simp only [t-take ht hs refuse]) (exact h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (Bool.and (run-normal r) (takeable s))))
  (simp only [t-take ht hs hg refuse]) (exact h)
  (have tk (= (takeable s) true)) (simp only [Bool.and_eq_true] at hg) (exact (And.right (And.right hg)))
  (cases hv (take-ready s))
  (simp only [t-take ht hs hg hv accept]) (exact (i5-dep-final-take-park x5d w r x k h))
  (simp only [t-take ht hs hg hv accept take-now])
  (exact (i5-dep-final-bump x5d _ (i5-dep-final-bump x5d _ (i5-dep-final-run-upd x5d _ (:id r) run-tick run-tick-run-id
           (i5-dep-final-source-upd-at x5d w x source-consume s source-consume-id (sfin-consume s tk) hs h))))))

;; ===========================================================================
;; Part B. Fires discharge their edge (the escape predicate)
;; ===========================================================================

;; ===========================================================================
;; Fires discharge their edge: the escape predicate jn (an edge is fine, or escapes by esc over
;; the activations), jm (... or has id y)
;; ===========================================================================

(a/defn mem-in [i :- Nat, as :- (List ActRow)] Bool (tbl-any (act-has-member i) as))
(a/defn jn [xd :- (List Nat), F :- (=> Nat Bool), esc :- (=> (List ActRow) EdgeRow Bool), as :- (List ActRow), e :- EdgeRow] Bool
  (Bool.or (dfk xd F e) (esc as e)))
(a/defn jm [xd :- (List Nat), F :- (=> Nat Bool), esc :- (=> (List ActRow) EdgeRow Bool), as :- (List ActRow), y :- Nat, e :- EdgeRow] Bool
  (Bool.or (jn xd F esc as e) (Nat.beq (:id e) y)))
(a/defn jw [xd :- (List Nat), esc :- (=> (List ActRow) EdgeRow Bool), w :- World] Bool
  (tbl-all (jn xd (fin-st (:sources w) (:tasks w)) esc (:acts w)) (:edges w)))
(a/defn jwy [xd :- (List Nat), esc :- (=> (List ActRow) EdgeRow Bool), y :- Nat, w :- World] Bool
  (tbl-all (jm xd (fin-st (:sources w) (:tasks w)) esc (:acts w) y) (:edges w)))
(a/defn esc-mono [esc :- (=> (List ActRow) EdgeRow Bool)] Prop
  (forall [as :- (List ActRow), bs :- (List ActRow), e :- EdgeRow]
    (=> (forall [i :- Nat] (=> (= (mem-in i bs) true) (= (mem-in i as) true))) (= (esc as e) true) (= (esc bs e) true))))

;; ---- the source and task tables (finality) under the fire
(a/structure ST5 [] (srcs (List SourceRow)) (tsks (List TaskRow)))
(a/defn st5 [w :- World] ST5 (ST5.mk (:sources w) (:tasks w)))
(a/theorem st5-remove-edge [w :- World, y :- Nat] (= (st5 (remove-edge w y)) (st5 w))
  (cases hf (edge-find w y)) (case' [some e]) (case' [none])
  (simp only [remove-edge hf])
  (cases hm (:marked e))
  (all_goals (simp only [remove-edge hf hm])))
(a/theorem st5-fill-slot [w :- World, a :- ActRow, y :- Nat, v :- RunResult] (= (st5 (fill-slot w a y v)) (st5 w))
  (cases hm (act-ready (act-fill y v a)))
  (all_goals (simp only [fill-slot hm resume])))
(a/theorem st5-fire-dep [w :- World, e :- EdgeRow] (= (st5 (fire-dep w e)) (st5 w))
  (cases ha (act-with-member (:id e) (:acts w))) (case' [some a]) (case' [none])
  (simp only [fire-dep ha invalidate])
  (cases hc (Bool.and (run-current-of w (:run a) (:creditor e)) (deb-avail w (:debtor e))))
  (simp only [fire-dep ha hc invalidate])
  (simp only [fire-dep ha hc deliver-dep])
  (have e1 (= (st5 (dep-consumed w e)) (st5 w)))
  (cases hf (deb-final w (:debtor e)))
  (simp only [dep-consumed hf])
  (simp only [dep-consumed hf]) (exact (st5-remove-edge w (:id e)))
  (exact (Eq.trans (st5-fill-slot _ a _ _) e1)))
(a/theorem st5-fire-wait [res :- RunResult, w :- World, e :- EdgeRow] (= (st5 (fire-wait res w e)) (st5 w))
  (cases hc (Nat.beq (:creditor e) 0))
  (case [true] (simp only [fire-wait hc]) (exact (st5-remove-edge w (:id e))))
  (case [false]
    (simp only [fire-wait hc])
    (cases ha (act-find w (:creditor e))) (case' [some a]) (case' [none])
    (simp only [fire-wait-act ha])
    (cases hr (run-current w (:run a)))
    (simp only [fire-wait-act ha hr])
    (simp only [fire-wait-act ha hr]) (exact (st5-fill-slot _ a _ _))))
(a/theorem st5-fire-edge [res :- RunResult, w :- World, y :- Nat] (= (st5 (fire-edge res w y)) (st5 w))
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
  (simp only [fire-edge hf hp hk1 hk2]) (exact (st5-fire-wait res w e))
  (simp only [fire-edge hf hp hk1]) (exact (st5-fire-dep w e)))
(a/theorem st5-fold [f :- (=> World Nat World), hf :- (forall [w :- World, x :- Nat] (= (st5 (f w x)) (st5 w))), xs :- (List Nat)]
  (forall [w :- World] (= (st5 (nat-fold f w xs)) (st5 w)))
  (induction xs)
  (case [nil] (intro w) (simp only [nat-fold]))
  (case [cons h t ih] (intro w) (simp only [nat-fold]) (exact (Eq.trans (ih (f w h)) (hf w h)))))
(a/theorem fin-st5 [w :- World, w2 :- World, d :- Nat]
  (=> (= (st5 w2) (st5 w)) (= (fin-st (:sources w2) (:tasks w2) d) (fin-st (:sources w) (:tasks w) d)))
  (intro e)
  (have e1 (= (:sources w2) (:sources w))) (exact (congrArg (fn [q :- ST5] (:srcs q)) e))
  (have e2 (= (:tasks w2) (:tasks w))) (exact (congrArg (fn [q :- ST5] (:tsks q)) e))
  (rw [e1 e2]))

;; ---- memberships only shrink under the fills

(a/theorem mem-has-filter [x :- Nat, p :- (=> Member Bool), ms :- (List Member)]
  (=> (= (mem-has x (tbl-filter p ms)) true) (= (mem-has x ms) true))
  (induction ms)
  (case [nil] (intro h) (simp only [tbl-filter mem-has] at h) (cases h))
  (case [cons hd t ih]
    (intro h)
    (cases he (Nat.beq (:edge hd) x))
    (case [true] (simp only [mem-has he]))
    (case [false]
      (simp only [mem-has he])
      (cases hp (p hd))
      (case [false] (simp only [tbl-filter hp] at h) (exact (ih h)))
      (case [true] (simp only [tbl-filter hp mem-has he] at h) (exact (ih h))))))

(a/theorem mem-in-upd-fill [i :- Nat, x :- Nat, y :- Nat, v :- RunResult, as :- (List ActRow)]
  (=> (= (mem-in i (tbl-upd act-id x (act-fill y v) as)) true) (= (mem-in i as) true))
  (induction as)
  (case [nil] (intro h) (simp only [tbl-upd mem-in tbl-any] at h) (cases h))
  (case [cons hd t ih]
    (intro h)
    (simp only [mem-in] at ih)
    (cases hx (Nat.beq (act-id hd) x))
    (case [false]
      (simp only [tbl-upd hx mem-in tbl-any Bool.or_eq_true] at h)
      (simp only [mem-in tbl-any Bool.or_eq_true])
      (cases h) (case [inl a] (exact (Or.inl a))) (case [inr b] (exact (Or.inr (ih b)))))
    (case [true]
      (simp only [tbl-upd hx mem-in tbl-any Bool.or_eq_true] at h)
      (simp only [mem-in tbl-any Bool.or_eq_true])
      (cases h)
      (case [inl a] (simp only [act-has-member act-fill] at a) (simp only [act-has-member]) (exact (Or.inl (mem-has-filter i _ _ a))))
      (case [inr b] (exact (Or.inr (ih b)))))))

(a/theorem mem-in-del [i :- Nat, x :- Nat, as :- (List ActRow)]
  (=> (= (mem-in i (tbl-del act-id x as)) true) (= (mem-in i as) true))
  (induction as)
  (case [nil] (intro h) (simp only [tbl-del mem-in tbl-any] at h) (cases h))
  (case [cons hd t ih]
    (intro h)
    (simp only [mem-in] at ih)
    (simp only [mem-in tbl-any Bool.or_eq_true])
    (cases hx (Nat.beq (act-id hd) x))
    (case [false]
      (simp only [tbl-del hx mem-in tbl-any Bool.or_eq_true] at h)
      (cases h) (case [inl a] (exact (Or.inl a))) (case [inr b] (exact (Or.inr (ih b)))))
    (case [true] (simp only [tbl-del hx] at h) (exact (Or.inr (ih h))))))

;; ---- jw: the general frame (finality only lost, memberships only lost, edges given)
(a/theorem jw-gen [xd :- (List Nat), esc :- (=> (List ActRow) EdgeRow Bool), w :- World, w2 :- World]
  (=> (esc-mono esc)
      (forall [d :- Nat] (=> (= (fin-st (:sources w2) (:tasks w2) d) true) (= (fin-st (:sources w) (:tasks w) d) true)))
      (forall [i :- Nat] (=> (= (mem-in i (:acts w2)) true) (= (mem-in i (:acts w)) true)))
      (= (tbl-all (jn xd (fin-st (:sources w) (:tasks w)) esc (:acts w)) (:edges w2)) true)
      (= (jw xd esc w2) true))
  (intros hm hf ha h)
  (simp only [jw])
  (apply (tbl-all-mono EdgeRow _ _ _ (:edges w2) h))
  (intros e he)
  (simp only [jn Bool.or_eq_true] at he)
  (simp only [jn Bool.or_eq_true])
  (cases he)
  (case [inl a] (exact (Or.inl (dfk-mono xd xd _ _ e hf (fn [d :- Nat, hx :- (= (reach-mem d xd) true)] hx) a))))
  (case [inr b] (exact (Or.inr (hm _ _ e ha b)))))

(a/theorem jw-fill-slot [xd :- (List Nat), esc :- (=> (List ActRow) EdgeRow Bool), w :- World, a :- ActRow, y :- Nat, v :- RunResult]
  (=> (esc-mono esc) (= (jw xd esc w) true) (= (jw xd esc (fill-slot w a y v)) true))
  (intros hm h)
  (have hf := (fin-same w (fill-slot w a y v)
                (congrArg (fn [q :- ST5] (:srcs q)) (st5-fill-slot w a y v)) (congrArg (fn [q :- ST5] (:tsks q)) (st5-fill-slot w a y v))))
  (simp only [jw] at h)
  (cases hr (act-ready (act-fill y v a)))
  (case [false]
    (have e1 (= (fill-slot w a y v) (act-upd w (:id a) (act-fill y v)))) (simp only [fill-slot hr])
    (rw [e1]) (rw [e1] at hf)
    (exact (jw-gen xd esc w _ hm hf (fn [i :- Nat, hi :- (= (mem-in i (:acts (act-upd w (:id a) (act-fill y v)))) true)] (mem-in-upd-fill i (:id a) y v (:acts w) hi)) h)))
  (case [true]
    (have e1 (= (fill-slot w a y v) (resume w a))) (simp only [fill-slot hr])
    (rw [e1]) (rw [e1] at hf)
    (exact (jw-gen xd esc w _ hm hf (fn [i :- Nat, hi :- (= (mem-in i (:acts (resume w a))) true)] (mem-in-del i (:id a) (:acts w) hi))
             (tbl-all-filter EdgeRow _ (cred-ne (:id a)) (:edges w) h)))))

;; ---- the rows with id y (unique ids: they share the found row's kind, phase and debtor)
(a/defn ek-eq [e0 :- EdgeRow, r :- EdgeRow] Bool
  (Bool.and (Nat.beq (:kind r) (:kind e0)) (Bool.and (Nat.beq (:phase r) (:phase e0)) (Nat.beq (:debtor r) (:debtor e0)))))
(a/theorem ek-eq-refl [e0 :- EdgeRow] (= (ek-eq e0 e0) true) (simp only [ek-eq Nat.beq_refl Bool.and_self]))
(a/theorem rows-same [w :- World, y :- Nat, e0 :- EdgeRow]
  (=> (= (well-formed w) true) (= (edge-find w y) (Option.some EdgeRow e0))
      (= (tbl-all (same-id-then edge-id y (ek-eq e0)) (:edges w)) true))
  (intros h hf)
  (have m := (tbl-find-mem EdgeRow edge-id y e0 (:edges w) hf))
  (have i := (tbl-find-id EdgeRow edge-id y e0 (:edges w) hf))
  (have u := (uniq-all EdgeRow edge-id (ek-eq e0) e0 (:edges w) (edges-nodup w h) m (ek-eq-refl e0)))
  (rw [i] at u) (exact u))
(a/theorem same-id-mono [y :- Nat, P :- (=> EdgeRow Bool), Q :- (=> EdgeRow Bool),
                         h :- (forall [r :- EdgeRow] (=> (= (P r) true) (= (Q r) true))), es :- (List EdgeRow)]
  (=> (= (tbl-all (same-id-then edge-id y P) es) true) (= (tbl-all (same-id-then edge-id y Q) es) true))
  (intro hp)
  (apply (tbl-all-mono EdgeRow _ _ _ es hp))
  (intros r hr)
  (simp only [same-id-then Bool.or_eq_true] at hr)
  (simp only [same-id-then Bool.or_eq_true])
  (cases hr) (case [inl a] (exact (Or.inl a))) (case [inr b] (exact (Or.inr (h r b)))))
(a/theorem has-false-same [y :- Nat, P :- (=> EdgeRow Bool), es :- (List EdgeRow)]
  (=> (= (tbl-has edge-id y es) false) (= (tbl-all (same-id-then edge-id y P) es) true))
  (induction es)
  (case [nil] (intro h) (simp only [tbl-all]))
  (case [cons hd t ih]
    (intro h)
    (cases hx (Nat.beq (edge-id hd) y))
    (case [true] (simp only [tbl-has hx Bool.true_or] at h) (cases h))
    (case [false]
      (simp only [tbl-has hx Bool.false_or] at h)
      (simp only [tbl-all same-id-then hx Bool.not_false Bool.true_or Bool.true_and])
      (exact (ih h)))))
(a/theorem eq-kind [e0 :- EdgeRow, r :- EdgeRow] (=> (= (ek-eq e0 r) true) (= (:kind r) (:kind e0)))
  (intro h) (simp only [ek-eq Bool.and_eq_true] at h) (exact (Nat.eq_of_beq_eq_true (And.left h))))
(a/theorem eq-phase [e0 :- EdgeRow, r :- EdgeRow] (=> (= (ek-eq e0 r) true) (= (:phase r) (:phase e0)))
  (intro h) (simp only [ek-eq Bool.and_eq_true] at h) (exact (Nat.eq_of_beq_eq_true (And.left (And.right h)))))
(a/theorem eq-debtor [e0 :- EdgeRow, r :- EdgeRow] (=> (= (ek-eq e0 r) true) (= (:debtor r) (:debtor e0)))
  (intro h) (simp only [ek-eq Bool.and_eq_true] at h) (exact (Nat.eq_of_beq_eq_true (And.right (And.right h)))))
(a/theorem dfk-kind [xd :- (List Nat), F :- (=> Nat Bool), e :- EdgeRow]
  (=> (= (Nat.beq (:kind e) ek-dep) false) (= (dfk xd F e) true))
  (intro h) (simp only [dfk h Bool.not_false Bool.true_or]))
(a/theorem dfk-phase [xd :- (List Nat), F :- (=> Nat Bool), e :- EdgeRow]
  (=> (= (Nat.beq (:phase e) ph-armed) false) (= (dfk xd F e) true))
  (intro h) (simp only [dfk h Bool.not_false Bool.true_or Bool.or_true]))

;; ---- jwy: discharge edge y
(a/theorem jw-jwy [xd :- (List Nat), esc :- (=> (List ActRow) EdgeRow Bool), y :- Nat, w :- World]
  (=> (= (jw xd esc w) true) (= (jwy xd esc y w) true))
  (intro h) (simp only [jw] at h) (simp only [jwy])
  (apply (tbl-all-mono EdgeRow _ _ _ (:edges w) h))
  (intros e he) (simp only [jm he Bool.true_or]))
(a/theorem jwy-same [xd :- (List Nat), esc :- (=> (List ActRow) EdgeRow Bool), y :- Nat, w :- World]
  (=> (= (tbl-all (same-id-then edge-id y (dfk xd (fin-st (:sources w) (:tasks w)))) (:edges w)) true)
      (= (jwy xd esc y w) true) (= (jw xd esc w) true))
  (intros hq h) (simp only [jwy] at h) (simp only [jw])
  (apply (tbl-all-mono2 EdgeRow _ _ _ _ (:edges w) hq h))
  (intros e h1 h2)
  (simp only [jm Bool.or_eq_true] at h2)
  (cases h2)
  (case [inl a] (exact a))
  (case [inr b] (have b2 (= (Nat.beq (edge-id e) y) true)) (exact b)
    (simp only [same-id-then b2 Bool.not_true Bool.false_or] at h1) (simp only [jn h1 Bool.true_or])))
(a/theorem jwy-upd [xd :- (List Nat), esc :- (=> (List ActRow) EdgeRow Bool), y :- Nat, w :- World, f :- (=> EdgeRow EdgeRow)]
  (=> (= (tbl-all (same-id-then edge-id y (fn [r :- EdgeRow] (dfk xd (fin-st (:sources w) (:tasks w)) (f r)))) (:edges w)) true)
      (= (jwy xd esc y w) true) (= (jw xd esc (edge-upd w y f)) true))
  (intros hq h) (simp only [jwy] at h)
  (have b := (tbl-all-mono2 EdgeRow _ _ (both (same-id-then edge-id y (fn [r :- EdgeRow] (dfk xd (fin-st (:sources w) (:tasks w)) (f r))))
                                              (jm xd (fin-st (:sources w) (:tasks w)) esc (:acts w) y))
               (fn [e :- EdgeRow, h1 :- (= (same-id-then edge-id y (fn [r :- EdgeRow] (dfk xd (fin-st (:sources w) (:tasks w)) (f r))) e) true),
                    h2 :- (= (jm xd (fin-st (:sources w) (:tasks w)) esc (:acts w) y e) true)] (both-of EdgeRow _ _ e h1 h2))
               (:edges w) hq h))
  (simp only [jw edge-upd set-edges])
  (apply (tbl-all-upd EdgeRow edge-id y f _ _ _ _ (:edges w) b))
  (intros e hb hx)
  (have s := (both-left EdgeRow _ _ e hb))
  (simp only [same-id-then hx Bool.not_true Bool.false_or] at s)
  (simp only [jn s Bool.true_or])
  (intros e hb hx)
  (have s := (both-right EdgeRow _ _ e hb))
  (have hx2 (= (Nat.beq (:id e) y) false)) (exact hx)
  (simp only [jm hx2 Bool.or_false] at s)
  (exact s))
(a/theorem jwy-remove [xd :- (List Nat), esc :- (=> (List ActRow) EdgeRow Bool), y :- Nat, w :- World]
  (=> (= (jwy xd esc y w) true) (= (jw xd esc (remove-edge w y)) true))
  (intro h)
  (cases hf (edge-find w y))
  (case [none]
    (simp only [remove-edge hf])
    (exact (jwy-same xd esc y w (has-false-same y _ (:edges w) (tbl-find-none-has EdgeRow edge-id y (:edges w) hf)) h)))
  (case [some e]
    (simp only [jwy] at h)
    (have d := (tbl-all-del EdgeRow edge-id y (jm xd (fin-st (:sources w) (:tasks w)) esc (:acts w) y)
                 (jn xd (fin-st (:sources w) (:tasks w)) esc (:acts w))
                 (fn [r :- EdgeRow, h1 :- (= (jm xd (fin-st (:sources w) (:tasks w)) esc (:acts w) y r) true), hx :- (= (Nat.beq (edge-id r) y) false)]
                   (Eq.trans (Eq.symm (Bool.or_false (jn xd (fin-st (:sources w) (:tasks w)) esc (:acts w) r)))
                             (Eq.trans (congrArg (fn [b :- Bool] (Bool.or (jn xd (fin-st (:sources w) (:tasks w)) esc (:acts w) r) b)) (Eq.symm hx)) h1)))
                 (:edges w) h))
    (cases hm (:marked e))
    (case [false] (simp only [remove-edge hf hm]) (exact d))
    (case [true] (simp only [remove-edge hf hm]) (exact d))))

(a/theorem all-same-true [y :- Nat, P :- (=> EdgeRow Bool), h :- (forall [r :- EdgeRow] (= (P r) true)), es :- (List EdgeRow)]
  (= (tbl-all (same-id-then edge-id y P) es) true)
  (apply all-of-mem) (intros r hr) (simp only [same-id-then (h r) Bool.or_true]))
(a/theorem jw-comp-upd [xd :- (List Nat), esc :- (=> (List ActRow) EdgeRow Bool), w :- World, x :- Nat, f :- (=> CompRow CompRow)]
  (= (jw xd esc (comp-upd w x f)) (jw xd esc w)) (rfl))
(a/theorem find-id [w :- World, y :- Nat, e0 :- EdgeRow] (=> (= (edge-find w y) (Option.some EdgeRow e0)) (= (:id e0) y))
  (intro hf) (exact (tbl-find-id EdgeRow edge-id y e0 (:edges w) hf)))

(a/theorem jw-set-fired [xd :- (List Nat), esc :- (=> (List ActRow) EdgeRow Bool), w :- World, y :- Nat]
  (=> (= (jwy xd esc y w) true) (= (jw xd esc (edge-upd w y (edge-set-phase ph-fired))) true))
  (intro h)
  (exact (jwy-upd xd esc y w (edge-set-phase ph-fired)
           (all-same-true y _ (fn [r :- EdgeRow] (edge-set-phase-dfk xd (fin-st (:sources w) (:tasks w)) ph-fired r (rfl))) (:edges w)) h)))

(a/theorem jw-invalidate [xd :- (List Nat), esc :- (=> (List ActRow) EdgeRow Bool), w :- World, e0 :- EdgeRow]
  (=> (= (jwy xd esc (:id e0) w) true) (= (jw xd esc (invalidate w e0)) true))
  (intro h)
  (simp only [invalidate jw-comp-upd])
  (exact (jw-set-fired xd esc w (:id e0) h)))

(a/theorem jw-dep-consumed [xd :- (List Nat), esc :- (=> (List ActRow) EdgeRow Bool), w :- World, e0 :- EdgeRow]
  (=> (= (well-formed w) true) (= (edge-find w (:id e0)) (Option.some EdgeRow e0)) (= (jwy xd esc (:id e0) w) true)
      (= (jw xd esc (dep-consumed w e0)) true))
  (intros hs hf h)
  (cases hd (deb-final w (:debtor e0)))
  (case [true] (simp only [dep-consumed hd]) (exact (jwy-remove xd esc (:id e0) w h)))
  (case [false]
    (simp only [dep-consumed hd])
    (have q := (same-id-mono (:id e0) (ek-eq e0)
                 (fn [r :- EdgeRow] (dfk xd (fin-st (:sources w) (:tasks w)) (edge-rearm (deb-value w (:debtor e0)) (deb-version w (:debtor e0)) r)))
                 (fn [r :- EdgeRow, hr :- (= (ek-eq e0 r) true)]
                   (rearm-ok xd w (:debtor e0) _ _ r hd (Eq.trans (congrArg (fn [z :- Nat] (Nat.beq z (:debtor e0))) (eq-debtor e0 r hr)) (Nat.beq_refl _))))
                 (:edges w) (rows-same w (:id e0) e0 hs hf)))
    (exact (jwy-upd xd esc (:id e0) w _ q h))))

(a/theorem jw-fire-dep [xd :- (List Nat), esc :- (=> (List ActRow) EdgeRow Bool), w :- World, e0 :- EdgeRow]
  (=> (esc-mono esc) (= (well-formed w) true) (= (edge-find w (:id e0)) (Option.some EdgeRow e0)) (= (jwy xd esc (:id e0) w) true)
      (= (jw xd esc (fire-dep w e0)) true))
  (intros hm hs hf h)
  (cases ha (act-with-member (:id e0) (:acts w))) (case' [some a]) (case' [none])
  (simp only [fire-dep ha]) (exact (jw-invalidate xd esc w e0 h))
  (cases hc (Bool.and (run-current-of w (:run a) (:creditor e0)) (deb-avail w (:debtor e0))))
  (simp only [fire-dep ha hc]) (exact (jw-invalidate xd esc w e0 h))
  (simp only [fire-dep ha hc deliver-dep])
  (exact (jw-fill-slot xd esc _ a _ _ hm (jw-dep-consumed xd esc w e0 hs hf h))))

(a/theorem jw-fire-wait [xd :- (List Nat), esc :- (=> (List ActRow) EdgeRow Bool), res :- RunResult, w :- World, e0 :- EdgeRow]
  (=> (esc-mono esc) (= (jwy xd esc (:id e0) w) true) (= (jw xd esc (fire-wait res w e0)) true))
  (intros hm h)
  (cases hc (Nat.beq (:creditor e0) 0))
  (case [true] (simp only [fire-wait hc]) (exact (jwy-remove xd esc (:id e0) w h)))
  (case [false]
    (simp only [fire-wait hc])
    (have h1 := (jw-set-fired xd esc w (:id e0) h))
    (cases ha (act-find w (:creditor e0))) (case' [some a]) (case' [none])
    (simp only [fire-wait-act ha]) (exact h1)
    (cases hr (run-current w (:run a)))
    (simp only [fire-wait-act ha hr]) (exact h1)
    (simp only [fire-wait-act ha hr]) (exact (jw-fill-slot xd esc _ a _ _ hm h1))))

(a/theorem jw-not-dep [xd :- (List Nat), esc :- (=> (List ActRow) EdgeRow Bool), w :- World, e0 :- EdgeRow, f :- (=> EdgeRow EdgeRow),
                       hk :- (forall [r :- EdgeRow] (= (:kind (f r)) (:kind r)))]
  (=> (= (well-formed w) true) (= (edge-find w (:id e0)) (Option.some EdgeRow e0)) (= (Nat.beq (:kind e0) ek-dep) false)
      (= (tbl-all (same-id-then edge-id (:id e0) (fn [r :- EdgeRow] (dfk xd (fin-st (:sources w) (:tasks w)) (f r)))) (:edges w)) true))
  (intros hs hf hk0)
  (exact (same-id-mono (:id e0) (ek-eq e0) (fn [r :- EdgeRow] (dfk xd (fin-st (:sources w) (:tasks w)) (f r)))
           (fn [r :- EdgeRow, hr :- (= (ek-eq e0 r) true)]
             (dfk-kind xd (fin-st (:sources w) (:tasks w)) (f r) (Eq.trans (congrArg (fn [z :- Nat] (Nat.beq z ek-dep)) (Eq.trans (hk r) (eq-kind e0 r hr))) hk0)))
           (:edges w) (rows-same w (:id e0) e0 hs hf))))

(a/theorem jw-fire-observe [xd :- (List Nat), esc :- (=> (List ActRow) EdgeRow Bool), w :- World, e0 :- EdgeRow]
  (=> (= (well-formed w) true) (= (edge-find w (:id e0)) (Option.some EdgeRow e0)) (= (Nat.beq (:kind e0) ek-dep) false)
      (= (jwy xd esc (:id e0) w) true) (= (jw xd esc (fire-observe w e0)) true))
  (intros hs hf hk h)
  (cases ho (observe-new e0 (deb-version w (:debtor e0))))
  (case [false] (simp only [fire-observe ho])
    (exact (jwy-same xd esc (:id e0) w (jw-not-dep xd esc w e0 (fn [r :- EdgeRow] r) (fn [r :- EdgeRow] (Eq.refl (:kind r))) hs hf hk) h)))
  (case [true] (simp only [fire-observe ho])
    (exact (jwy-upd xd esc (:id e0) w _ (jw-not-dep xd esc w e0 (edge-set-seen (deb-version w (:debtor e0))) (edge-set-seen-kind _) hs hf hk) h))))

(a/theorem jw-fire-edge [xd :- (List Nat), esc :- (=> (List ActRow) EdgeRow Bool), res :- RunResult, w :- World, y :- Nat]
  (=> (esc-mono esc) (= (well-formed w) true) (= (jwy xd esc y w) true) (= (jw xd esc (fire-edge res w y)) true))
  (intros hm hs h)
  (cases hf (edge-find w y)) (case' [some e]) (case' [none])
  (simp only [fire-edge hf])
  (exact (jwy-same xd esc y w (has-false-same y _ (:edges w) (tbl-find-none-has EdgeRow edge-id y (:edges w) hf)) h))
  (have ey := (find-id w y e hf))
  (have hf2 (= (edge-find w (:id e)) (Option.some EdgeRow e))) (rw [ey]) (exact hf)
  (have h2 (= (jwy xd esc (:id e) w) true)) (rw [ey]) (exact h)
  (cases hp (Nat.beq (:phase e) ph-armed))
  (simp only [fire-edge hf hp])
  (exact (jwy-same xd esc y w
           (same-id-mono y (ek-eq e) (dfk xd (fin-st (:sources w) (:tasks w)))
             (fn [r :- EdgeRow, hr :- (= (ek-eq e r) true)]
               (dfk-phase xd (fin-st (:sources w) (:tasks w)) r (Eq.trans (congrArg (fn [z :- Nat] (Nat.beq z ph-armed)) (eq-phase e r hr)) hp)))
             (:edges w) (rows-same w y e hs hf))
           h))
  (cases hk1 (Nat.beq (:kind e) ek-dep))
  (cases hk2 (Nat.beq (:kind e) ek-wait))
  (cases hk3 (Nat.beq (:kind e) ek-observe))
  (simp only [fire-edge hf hp hk1 hk2 hk3 fire-savepoint-todo])
  (exact (jwy-same xd esc (:id e) w (jw-not-dep xd esc w e (fn [r :- EdgeRow] r) (fn [r :- EdgeRow] (Eq.refl (:kind r))) hs hf2 hk1) h2))
  (simp only [fire-edge hf hp hk1 hk2 hk3]) (exact (jw-fire-observe xd esc w e hs hf2 hk1 h2))
  (simp only [fire-edge hf hp hk1 hk2]) (exact (jw-fire-wait xd esc res w e hm h2))
  (simp only [fire-edge hf hp hk1]) (exact (jw-fire-dep xd esc w e hm hs hf2 h2)))

;; ---- a fold of fires over a list L of edge ids: L's edges escape before, are discharged after
(a/defn esc-l [L :- (List Nat), esc :- (=> (List ActRow) EdgeRow Bool), as :- (List ActRow), e :- EdgeRow] Bool
  (Bool.or (reach-mem (:id e) L) (esc as e)))
(a/theorem esc-l-mono [L :- (List Nat), esc :- (=> (List ActRow) EdgeRow Bool)] (=> (esc-mono esc) (esc-mono (esc-l L esc)))
  (intro hm)
  (simp only [esc-mono])
  (intros as bs e hi h)
  (simp only [esc-l Bool.or_eq_true] at h)
  (simp only [esc-l Bool.or_eq_true])
  (cases h) (case [inl a] (exact (Or.inl a))) (case [inr b] (exact (Or.inr (hm as bs e hi b)))))
(a/theorem jw-cons [xd :- (List Nat), esc :- (=> (List ActRow) EdgeRow Bool), y :- Nat, L :- (List Nat), w :- World]
  (=> (= (jw xd (esc-l (List.cons Nat y L) esc) w) true) (= (jwy xd (esc-l L esc) y w) true))
  (intro h) (simp only [jw] at h) (simp only [jwy])
  (apply (tbl-all-mono EdgeRow _ _ _ (:edges w) h))
  (intros e he)
  (cases hy (Nat.beq (:id e) y))
  (case [true] (simp only [jm hy Bool.or_true]))
  (case [false] (simp only [jn esc-l reach-mem hy] at he) (simp only [jm jn esc-l hy Bool.or_false]) (exact he)))
(a/theorem jw-nil [xd :- (List Nat), esc :- (=> (List ActRow) EdgeRow Bool), w :- World]
  (=> (= (jw xd (esc-l (List.nil Nat) esc) w) true) (= (jw xd esc w) true))
  (intro h) (simp only [jw jn esc-l reach-mem Bool.false_or] at h) (simp only [jw jn]) (exact h))
(a/theorem jw-fold [xd :- (List Nat), esc :- (=> (List ActRow) EdgeRow Bool), res :- RunResult, L :- (List Nat)]
  (forall [w :- World] (=> (esc-mono esc) (= (well-formed w) true) (= (jw xd (esc-l L esc) w) true)
                           (= (jw xd esc (nat-fold (fire-edge res) w L)) true)))
  (induction L)
  (case [nil] (intros w hm hs h) (simp only [nat-fold]) (exact (jw-nil xd esc w h)))
  (case [cons y t ih]
    (intros w hm hs h)
    (simp only [nat-fold])
    (exact (ih (fire-edge res w y) hm (well-formed-fire-edge res w y hs)
             (jw-fire-edge xd (esc-l t esc) res w y (esc-l-mono t esc hm) hs (jw-cons xd esc y t w h))))))

;; ---- a debtor made final: only x's finality is new

(a/theorem fin-supd-x [x :- Nat, f :- (=> SourceRow SourceRow), hid :- (forall [s :- SourceRow] (= (source-id (f s)) (source-id s))),
                       xs :- (List SourceRow), ts :- (List TaskRow), d :- Nat]
  (=> (= (fin-st (tbl-upd source-id x f xs) ts d) true) (Or (= (fin-st xs ts d) true) (= (Nat.beq d x) true)))
  (intro h)
  (cases hd (Nat.beq d x))
  (case [true] (exact (Or.inr (rfl))))
  (case [false] (simp only [fin-st (tbl-find-upd-ne SourceRow source-id x d f hid xs hd)] at h) (simp only [fin-st]) (exact (Or.inl h))))
(a/theorem fin-tupd-x [x :- Nat, f :- (=> TaskRow TaskRow), hid :- (forall [t :- TaskRow] (= (task-id (f t)) (task-id t))),
                       xs :- (List SourceRow), ts :- (List TaskRow), d :- Nat]
  (=> (= (fin-st xs (tbl-upd task-id x f ts) d) true) (Or (= (fin-st xs ts d) true) (= (Nat.beq d x) true)))
  (intro h)
  (cases hd (Nat.beq d x))
  (case [true] (exact (Or.inr (rfl))))
  (case [false] (simp only [fin-st (tbl-find-upd-ne TaskRow task-id x d f hid ts hd)] at h) (simp only [fin-st]) (exact (Or.inl h))))


(a/theorem dfk-up [xd :- (List Nat), F :- (=> Nat Bool), G :- (=> Nat Bool), x :- Nat, e :- EdgeRow]
  (=> (forall [d :- Nat] (=> (= (G d) true) (Or (= (F d) true) (= (Nat.beq d x) true))))
      (= (dfk xd F e) true) (= (Bool.or (dfk xd G e) (armed-dep-on x e)) true))
  (intros hg h)
  (cases hk (Nat.beq (:kind e) ek-dep))
  (case [false] (simp only [dfk-kind xd G e hk Bool.true_or]))
  (case [true]
    (cases hp (Nat.beq (:phase e) ph-armed))
    (case [false] (simp only [dfk-phase xd G e hp Bool.true_or]))
    (case [true]
      (cases hG (G (:debtor e)))
      (case [false] (simp only [dfk-nonfinal xd G e hG Bool.true_or]))
      (case [true]
        (have o := (hg _ hG))
        (cases o)
        (case [inl a]
          (simp only [dfk hk hp a Bool.not_true Bool.or_false Bool.false_or] at h)
          (simp only [dfk hk hp hG h Bool.not_true Bool.or_false Bool.false_or Bool.true_or]))
        (case [inr b] (simp only [armed-dep-on hk hp b Bool.and_self Bool.or_true]))))))


(a/theorem onto-mem [x :- Nat, e :- EdgeRow, es :- (List EdgeRow)]
  (=> (List.Mem e es) (= (armed-dep-on x e) true) (= (reach-mem (:id e) (edges-onto x es)) true))
  (induction es)
  (case [nil] (intros hm hp) (cases hm))
  (case [cons hd t ih]
    (intros hm hp)
    (cases hm)
    (case [head]
      (simp only [armed-dep-on Bool.and_eq_true] at hp)
      (simp only [edges-onto (And.left (And.right hp)) (And.left hp) Bool.true_or Bool.and_self reach-mem Nat.beq_refl]))
    (case [tail h2]
      (cases hq (Bool.and (Nat.beq (:debtor hd) x) (Bool.or (Nat.beq (:kind hd) ek-dep) (Nat.beq (:kind hd) ek-observe))))
      (case [false] (simp only [edges-onto hq]) (exact (ih h2 hp)))
      (case [true]
        (simp only [edges-onto hq reach-mem])
        (cases hb (Nat.beq (:id e) (:id hd))) (all_goals (simp only [hb (ih h2 hp)]))))))

;; the start of a discharging fold: after x became final, every bad edge is armed on x
(a/theorem jw-start [xd :- (List Nat), esc :- (=> (List ActRow) EdgeRow Bool), w :- World, w1 :- World, x :- Nat]
  (=> (forall [d :- Nat] (=> (= (fin-st (:sources w1) (:tasks w1) d) true)
                             (Or (= (fin-st (:sources w) (:tasks w) d) true) (= (Nat.beq d x) true))))
      (= (:edges w1) (:edges w))
      (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (= (armed-dep-on x e) true) (= (esc (:acts w1) e) true)))
      (= (i5-dep-final-rest xd w) true) (= (jw xd esc w1) true))
  (intros hf he hc h)
  (simp only [i5-dep-final-rest] at h)
  (simp only [jw he])
  (apply all-of-mem)
  (intros e hm)
  (have u := (dfk-up xd _ _ x e hf (tbl-all-mem EdgeRow _ e (:edges w) h hm)))
  (simp only [Bool.or_eq_true] at u)
  (cases u)
  (case [inl a] (simp only [jn a Bool.true_or]))
  (case [inr b] (simp only [jn (hc e hm b) Bool.or_true])))

(a/theorem jw-false-end [xd :- (List Nat), w :- World]
  (=> (= (jw xd (fn [as :- (List ActRow), e :- EdgeRow] false) w) true) (= (i5-dep-final-rest xd w) true))
  (intro h) (simp only [jw] at h) (simp only [i5-dep-final-rest])
  (apply (tbl-all-mono EdgeRow _ _ _ (:edges w) h))
  (intros e he) (simp only [jn Bool.or_false] at he) (exact he))
(a/theorem esc-false-mono [] (esc-mono (fn [as :- (List ActRow), e :- EdgeRow] false))
  (simp only [esc-mono]) (intros as bs e hi h) (exact h))

;; the closed-source escape: an armed member-free edge on x (T10 removes it)
(a/defn esc-cl [x :- Nat, as :- (List ActRow), e :- EdgeRow] Bool
  (Bool.and (Nat.beq (:debtor e) x) (Bool.not (mem-in (:id e) as))))
(a/theorem esc-cl-mono [x :- Nat] (esc-mono (esc-cl x))
  (simp only [esc-mono]) (intros as bs e hi h)
  (simp only [esc-cl Bool.and_eq_true] at h)
  (have h1 := (And.left h))
  (have h2 := (And.right h))
  (simp only [esc-cl h1 Bool.true_and])
  (cases hb (mem-in (:id e) bs))
  (case [false] (rfl))
  (case [true] (have z := (hi _ hb)) (rw [z] at h2) (simp at h2)))

;; ---- T10 on a source: one finalize-one (no computation is final, Z#32)
(a/theorem final-comp-false [w :- World, x :- Nat] (= (final-comp-id w x) false)
  (cases hc (comp-find w x))
  (case [none] (simp only [final-comp-id hc opt-test]))
  (case [some c] (simp only [final-comp-id hc opt-test comp-final])))
(a/theorem filter-final-nil [w :- World, xs :- (List Nat)] (= (tbl-filter (final-comp-id w) xs) (List.nil Nat))
  (induction xs)
  (case [nil] (simp only [tbl-filter]))
  (case [cons h t ih] (simp only [tbl-filter (final-comp-false w h) ih])))
(a/theorem fd-one [w :- World, x :- Nat] (= (t10-finalize-debtor w x) (finalize-one w x))
  (simp only [t10-finalize-debtor finalize-fuel finalize-loop filter-final-nil List.nil_append]))

(a/theorem tbl-all-filter-imp [A :- Type, P :- (=> A Bool), Q :- (=> A Bool), q :- (=> A Bool),
                               h :- (forall [a :- A] (=> (= (P a) true) (= (q a) true) (= (Q a) true))), xs :- (List A)]
  (=> (= (tbl-all P xs) true) (= (tbl-all Q (tbl-filter q xs)) true))
  (induction xs)
  (case [nil] (intro hp) (simp only [tbl-filter tbl-all]))
  (case [cons hd t ih]
    (intro hp)
    (simp only [tbl-all Bool.and_eq_true] at hp)
    (cases hq (q hd))
    (case [false] (simp only [tbl-filter hq]) (exact (ih (And.right hp))))
    (case [true] (simp only [tbl-filter hq tbl-all (h hd (And.left hp) hq) (ih (And.right hp)) Bool.and_self]))))

(a/theorem close-keep [xd :- (List Nat), F :- (=> Nat Bool), x :- Nat, as :- (List ActRow), e :- EdgeRow]
  (=> (= (jn xd F (esc-cl x) as e) true) (= (finalize-keeps as x e) true) (= (dfk xd F e) true))
  (intros h hk)
  (simp only [jn Bool.or_eq_true] at h)
  (cases h)
  (case [inl a] (exact a))
  (case [inr b]
    (simp only [esc-cl Bool.and_eq_true] at b)
    (have b1 := (And.left b)) (have b2 := (And.right b))
    (cases hd (Nat.beq (:kind e) ek-dep))
    (case [false] (exact (dfk-kind xd F e hd)))
    (case [true]
      (cases hp (Nat.beq (:phase e) ph-armed))
      (case [false] (exact (dfk-phase xd F e hp)))
      (case [true]
        (have m (= (tbl-any (act-has-member (:id e)) as) false)) (simp only [mem-in] at b2) (exact (bnot-true _ b2))
        (simp only [finalize-keeps finalize-drops hd hp b1 m Bool.not_false Bool.and_self Bool.not_true] at hk)
        (cases hk)))))

(a/theorem close-end [xd :- (List Nat), x :- Nat, w :- World]
  (=> (= (jw xd (esc-cl x) w) true) (= (i5-dep-final-rest xd (t10-finalize-debtor w x)) true))
  (intro h)
  (rw [fd-one])
  (simp only [jw] at h)
  (simp only [i5-dep-final-rest finalize-one drop-edges set-comps set-edges])
  (exact (tbl-all-filter-imp EdgeRow _ _ (finalize-keeps (:acts w) x)
           (fn [e :- EdgeRow, h1 :- (= (jn xd (fin-st (:sources w) (:tasks w)) (esc-cl x) (:acts w) e) true), h2 :- (= (finalize-keeps (:acts w) x e) true)]
             (close-keep xd _ x (:acts w) e h1 h2))
           (:edges w) h)))

;; ---- the discharging folds at the finality sites

;; close/detach (Z#53): the woken members are listed, a non-member armed edge on x escapes to T10
(a/theorem cw-mem [w :- World, x :- Nat, e :- EdgeRow]
  (=> (List.Mem e (:edges w)) (= (armed-dep-on x e) true) (= (mem-in (:id e) (:acts w)) true)
      (= (close-wakes (:acts w) x e) true))
  (intros hm ha hb)
  (have a2 := ha)
  (simp only [armed-dep-on Bool.and_eq_true] at a2)
  (have hd (= (Nat.beq (:debtor e) x) true)) (exact (And.left (And.right a2)))
  (have hk := (And.left a2))
  (simp only [mem-in] at hb)
  (simp only [close-wakes hd hk hb Bool.and_self Bool.or_true Bool.true_and]))

(a/theorem cw-esc [w :- World, x :- Nat, e :- EdgeRow]
  (=> (List.Mem e (:edges w)) (= (armed-dep-on x e) true)
      (= (esc-l (tbl-scan edge-id (close-wakes (:acts w) x) (:edges w)) (esc-cl x) (:acts w) e) true))
  (intros hm ha)
  (have a2 := ha)
  (simp only [armed-dep-on Bool.and_eq_true] at a2)
  (have hd (= (Nat.beq (:debtor e) x) true)) (exact (And.left (And.right a2)))
  (cases hb (mem-in (:id e) (:acts w)))
  (case [false] (simp only [esc-l esc-cl hd hb Bool.not_false Bool.and_self Bool.true_and Bool.or_true]))
  (case [true]
    (have r (= (reach-mem (:id e) (tbl-scan edge-id (close-wakes (:acts w) x) (:edges w))) true))
    (exact (scan-mem EdgeRow edge-id (close-wakes (:acts w) x) e (:edges w) hm (cw-mem w x e hm ha hb)))
    (simp only [esc-l r Bool.true_or])))

(a/theorem i5-dep-final-wake-final [xd :- (List Nat), w :- World, x :- Nat, f :- (=> SourceRow SourceRow),
                          hid :- (forall [s :- SourceRow] (= (source-id (f s)) (source-id s)))]
  (=> (= (i5-dep-final xd w) true) (= (i5-dep-final xd (t10-finalize-debtor (wake-closed (source-upd w x f) x) x)) true))
  (intro h)
  (have hs := (i5-dep-final-well-formed xd w h))
  (have hs1 := (well-formed-source-upd w x f hid hs))
  (have j0 (= (jw xd (esc-l (tbl-scan edge-id (close-wakes (:acts (source-upd w x f)) x) (:edges (source-upd w x f))) (esc-cl x))
                  (source-upd w x f)) true))
  (exact (jw-start xd _ w (source-upd w x f) x
           (fn [d :- Nat, hd :- (= (fin-st (:sources (source-upd w x f)) (:tasks (source-upd w x f)) d) true)]
             (fin-supd-x x f hid (:sources w) (:tasks w) d hd))
           (rfl)
           (fn [e :- EdgeRow, hm :- (List.Mem e (:edges w)), ha :- (= (armed-dep-on x e) true)] (cw-esc (source-upd w x f) x e hm ha))
           (i5-dep-final-rest-of xd w h)))
  (have j1 := (jw-fold xd (esc-cl x) (deb-result (source-upd w x f) x) (tbl-scan edge-id (close-wakes (:acts (source-upd w x f)) x) (:edges (source-upd w x f)))
                (source-upd w x f) (esc-cl-mono x) hs1 j0))
  (exact (i5-dep-final-intro xd _ (well-formed-t10-finalize-debtor _ x (well-formed-wake-closed _ x hs1)) (close-end xd x (wake-closed (source-upd w x f) x) j1))))

;; T12/T14 on task k, deliver on source x: every dep edge on the debtor is listed
(a/theorem i5-dep-final-fold-all [xd :- (List Nat), w :- World, w1 :- World, x :- Nat, res :- RunResult, L :- (List Nat)]
  (=> (= (well-formed w1) true)
      (forall [d :- Nat] (=> (= (fin-st (:sources w1) (:tasks w1) d) true)
                             (Or (= (fin-st (:sources w) (:tasks w) d) true) (= (Nat.beq d x) true))))
      (= (:edges w1) (:edges w))
      (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (= (armed-dep-on x e) true) (= (reach-mem (:id e) L) true)))
      (= (i5-dep-final xd w) true) (= (i5-dep-final xd (nat-fold (fire-edge res) w1 L)) true))
  (intros hs1 hf he hl h)
  (have j0 (= (jw xd (esc-l L (fn [as :- (List ActRow), e :- EdgeRow] false)) w1) true))
  (have hc (forall [e :- EdgeRow] (=> (List.Mem e (:edges w)) (= (armed-dep-on x e) true)
                                       (= (esc-l L (fn [as :- (List ActRow), e :- EdgeRow] false) (:acts w1) e) true))))
  (intros e hm ha) (simp only [esc-l (hl e hm ha) Bool.true_or])
  (exact (jw-start xd (esc-l L (fn [as :- (List ActRow), e :- EdgeRow] false)) w w1 x hf he hc (i5-dep-final-rest-of xd w h)))
  (have j1 := (jw-fold xd (fn [as :- (List ActRow), e :- EdgeRow] false) res L w1 esc-false-mono hs1 j0))
  (exact (i5-dep-final-intro xd _ (well-formed-nat-fold (fire-edge res) (well-formed-fire-edge res) L w1 hs1) (jw-false-end xd (nat-fold (fire-edge res) w1 L) j1))))

(a/theorem on-task-of [k :- Nat, e :- EdgeRow] (=> (= (armed-dep-on k e) true) (= (on-task k e) true))
  (intro h) (simp only [armed-dep-on Bool.and_eq_true] at h)
  (simp only [on-task (And.left h) (And.left (And.right h)) Bool.or_true Bool.and_self]))

(a/theorem i5-dep-final-task-fold [xd :- (List Nat), w :- World, k :- Nat, f :- (=> TaskRow TaskRow),
                         hid :- (forall [t :- TaskRow] (= (task-id (f t)) (task-id t))), res :- RunResult]
  (=> (= (i5-dep-final xd w) true)
      (= (i5-dep-final xd (nat-fold (fire-edge res) (task-upd w k f) (tbl-scan edge-id (on-task k) (:edges (task-upd w k f))))) true))
  (intro h)
  (exact (i5-dep-final-fold-all xd w (task-upd w k f) k res _ (well-formed-task-upd w k f hid (i5-dep-final-well-formed xd w h))
           (fn [d :- Nat, hd :- (= (fin-st (:sources (task-upd w k f)) (:tasks (task-upd w k f)) d) true)]
             (fin-tupd-x k f hid (:sources w) (:tasks w) d hd))
           (rfl)
           (fn [e :- EdgeRow, hm :- (List.Mem e (:edges w)), ha :- (= (armed-dep-on k e) true)]
             (scan-mem EdgeRow edge-id (on-task k) e (:edges w) hm (on-task-of k e ha)))
           h)))

(a/theorem edges-res-fold [zs :- (List Nat)] (forall [W :- World] (= (:edges (nat-fold res-cancel W zs)) (:edges W)))
  (induction zs)
  (case [nil] (intro W) (simp only [nat-fold]))
  (case [cons h t ih] (intro W) (simp only [nat-fold]) (exact (Eq.trans (ih (res-cancel W h)) (rfl)))))

(a/theorem i5-dep-final-ctask [xd :- (List Nat), w :- World, r :- RunRow, k :- Nat, res :- RunResult]
  (=> (= (i5-dep-final xd w) true)
      (= (i5-dep-final xd (nat-fold (fire-edge res) (cancel-res (task-upd w k (task-result-row res)) r) (tbl-scan edge-id (on-task k) (:edges w)))) true))
  (intro h)
  (have hs1 := (well-formed-cancel-res _ r (well-formed-task-upd w k (task-result-row res) (task-result-row-id res) (i5-dep-final-well-formed xd w h))))
  (have st := (st5-fold res-cancel (fn [W :- World, z :- Nat] (Eq.refl (st5 W))) (:resources r) (task-upd w k (task-result-row res))))
  (have hf (forall [d :- Nat] (=> (= (fin-st (:sources (cancel-res (task-upd w k (task-result-row res)) r)) (:tasks (cancel-res (task-upd w k (task-result-row res)) r)) d) true)
                                  (Or (= (fin-st (:sources w) (:tasks w) d) true) (= (Nat.beq d k) true)))))
  (intros d hd)
  (simp only [cancel-res] at hd)
  (rw [(fin-st5 (task-upd w k (task-result-row res)) (nat-fold res-cancel (task-upd w k (task-result-row res)) (:resources r)) d st)] at hd)
  (exact (fin-tupd-x k (task-result-row res) (task-result-row-id res) (:sources w) (:tasks w) d hd))
  (have he (= (:edges (cancel-res (task-upd w k (task-result-row res)) r)) (:edges w)))
  (simp only [cancel-res]) (exact (edges-res-fold (:resources r) (task-upd w k (task-result-row res))))
  (exact (i5-dep-final-fold-all xd w (cancel-res (task-upd w k (task-result-row res)) r) k res _ hs1 hf he
           (fn [e :- EdgeRow, hm :- (List.Mem e (:edges w)), ha :- (= (armed-dep-on k e) true)]
             (scan-mem EdgeRow edge-id (on-task k) e (:edges w) hm (on-task-of k e ha)))
           h)))

(a/theorem i5-dep-final-deliver-fire [xd :- (List Nat), w :- World, x :- Nat, v :- Nat]
  (=> (= (i5-dep-final xd w) true) (= (i5-dep-final xd (deliver-fire w x v)) true))
  (intro h)
  (simp only [deliver-fire])
  (exact (i5-dep-final-fold-all xd w (source-upd w x (source-write v)) x (RunResult.mk res-ok v) (edges-onto x (:edges w))
           (well-formed-source-upd w x (source-write v) (source-write-source-id v) (i5-dep-final-well-formed xd w h))
           (fn [d :- Nat, hd :- (= (fin-st (:sources (source-upd w x (source-write v))) (:tasks (source-upd w x (source-write v))) d) true)]
             (fin-supd-x x (source-write v) (source-write-source-id v) (:sources w) (:tasks w) d hd))
           (rfl)
           (fn [e :- EdgeRow, hm :- (List.Mem e (:edges w)), ha :- (= (armed-dep-on x e) true)] (onto-mem x e (:edges w) hm ha))
           h)))

(a/theorem i5-dep-final-deliver-fire-res [xd :- (List Nat), w :- World, x :- Nat, v :- Nat, res :- RunResult]
  (=> (= (i5-dep-final xd w) true) (= (i5-dep-final xd (nat-fold (fire-edge res) (source-upd w x (source-write v)) (edges-onto x (:edges w)))) true))
  (intro h)
  (exact (i5-dep-final-fold-all xd w (source-upd w x (source-write v)) x res (edges-onto x (:edges w))
           (well-formed-source-upd w x (source-write v) (source-write-source-id v) (i5-dep-final-well-formed xd w h))
           (fn [d :- Nat, hd :- (= (fin-st (:sources (source-upd w x (source-write v))) (:tasks (source-upd w x (source-write v))) d) true)]
             (fin-supd-x x (source-write v) (source-write-source-id v) (:sources w) (:tasks w) d hd))
           (rfl)
           (fn [e :- EdgeRow, hm :- (List.Mem e (:edges w)), ha :- (= (armed-dep-on x e) true)] (onto-mem x e (:edges w) hm ha))
           h)))

;; C0: a link's realization is a deliver with a result (rule.clj `deliver-res`)
(tree/restate! G5 '[well-formed-fire-edge well-formed-nat-fold well-formed-t10-finalize-debtor])
(a/theorem i5-dep-final-deliver-res [x5d :- (List Nat), w :- World, x :- Nat, v :- Nat, res :- RunResult]
  (=> (= (i5-dep-final x5d w) true) (= (i5-dep-final x5d (deliver-res w x v res)) true))
  (intro h)
  (simp only [deliver-res])
  (exact (i5-dep-final-t10-finalize-debtor x5d _ x (i5-dep-final-nat-fold x5d (fire-edge res) (i5-dep-final-fire-edge x5d res) _ _
           (i5-dep-final-deliver-fire-res x5d w x v res h)))))

(a/theorem sfin-stream-tail [t :- Nat, s :- SourceRow] (=> (= (Nat.beq (:kind s) sk-stream) true) (= (sfin (stream-set-tail t s)) (sfin s)))
  (intro h)
  (have e (= (:kind s) sk-stream)) (exact (Nat.eq_of_beq_eq_true h))
  (simp only [sfin stream-set-tail source-delivered e once-kind Bool.false_and]))

;; C0 append: the stream's row keeps sfin (a stream is never once-delivered), with the guard's row
(tree/restate! G5 '[well-formed-realize-link well-formed-source-ins-fresh])
(a/theorem i5-dep-final-append-raw [x5d :- (List Nat), w :- World, x :- Nat, v :- Nat, old :- Nat, s :- SourceRow]
  (=> (= (source-find w x) (Option.some SourceRow s)) (= (Nat.beq (:kind s) sk-stream) true) (= (i5-dep-final x5d w) true)
      (= (i5-dep-final x5d (append-raw w x v old)) true))
  (intros hs hk h)
  (simp only [append-raw])
  (exact (i5-dep-final-realize-link x5d _ old v false _
           (i5-dep-final-source-ins x5d (source-upd w x (stream-set-tail (:next-id w))) (new-link (:next-id w) root-scope-id x)
             (sfin-mk _ _ _ _ _ _ _ _ _ _ _) (rfl)
             (i5-dep-final-source-upd-at x5d w x (stream-set-tail (:next-id w)) s (stream-set-tail-id _) (sfin-stream-tail _ s hk) hs h)))))
(a/theorem i5-dep-final-t-append [x5d :- (List Nat), w :- World, x :- Nat, v :- Nat, t :- Nat]
  (=> (= (i5-dep-final x5d w) true) (= (i5-dep-final x5d (:world (t-append w x v t))) true))
  (intro h)
  (cases hf (source-find w x)) (case' [some s]) (case' [none])
  (simp only [t-append hf refuse]) (exact h)
  (cases hg (Bool.and (open-kind sk-stream s) (Bool.and (Nat.beq t (:next-id w)) (link-pending w (:tail s)))))
  (simp only [t-append hf hg refuse]) (exact h)
  (cases hk (Nat.beq (:kind s) sk-stream))
  (case [false] (simp only [open-kind hk Bool.false_and] at hg) (cases hg))
  (case [true] (simp only [t-append hf hg accept]) (exact (i5-dep-final-append-raw x5d w x v _ s hf hk h))))

(a/theorem i5-dep-final-close-source-ended [x5d :- (List Nat), w :- World, x :- Nat]
  (=> (= (i5-dep-final x5d w) true) (= (i5-dep-final x5d (close-source-ended w x)) true))
  (intro h) (simp only [close-source-ended]) (exact (i5-dep-final-wake-final x5d w x source-close-row source-close-row-id h)))
(a/theorem i5-dep-final-detach-source [x5d :- (List Nat), w :- World, x :- Nat]
  (=> (= (i5-dep-final x5d w) true) (= (i5-dep-final x5d (detach-source w x)) true))
  (intro h) (simp only [detach-source]) (exact (i5-dep-final-wake-final x5d w x source-detach-row source-detach-row-id h)))

(tree/restate! G5 '[well-formed-fire-waits-cancelled well-formed-invalidate-dependents well-formed-t10-finalize-debtor well-formed-clear-rtasks])
(a/theorem i5-dep-final-debtor-side [x5d :- (List Nat), w :- World, r :- RunRow]
  (=> (= (i5-dep-final x5d w) true) (= (i5-dep-final x5d (debtor-side w r)) true))
  (intro h)
  (cases hc (comp-find w (:of r))) (case' [some c]) (case' [none])
  (simp only [debtor-side hc fire-task-cancelled])
  (exact (i5-dep-final-clear-rtasks x5d _ (:of r) (i5-dep-final-t10-finalize-debtor x5d _ (:of r) (i5-dep-final-task-fold x5d w (:of r) task-cancel-result task-cancel-result-id res-cancelled h))))
  (cases he (Nat.beq (:epoch r) (:epoch c)))
  (simp only [debtor-side hc he]) (exact h)
  (simp only [debtor-side hc he])
  (exact (i5-dep-final-invalidate-dependents x5d _ (:of r) (i5-dep-final-fire-waits-cancelled x5d w (:of r) h))))

(tree/restate! G5 '[well-formed-settle well-formed-cancel-res well-formed-comp-upd])
(a/theorem i5-dep-final-complete-body [x5d :- (List Nat), w :- World, r :- RunRow, res :- RunResult]
  (=> (= (i5-dep-final x5d w) true) (= (i5-dep-final x5d (:world (complete-body w r res))) true))
  (intro h)
  (cases hc (comp-find w (:of r)))
  (case [none]
    (cases hk (task-find w (:of r)))
    (case [none] (simp only [complete-body hc hk]) (exact h))
    (case [some k]
      (simp only [complete-body hc hk complete-task])
      (exact (i5-dep-final-ctask x5d w r (:id k) res h))))
  (case [some c]
    (cases he (Nat.beq (:epoch r) (:epoch c)))
    (case [false] (simp only [complete-body hc he]) (exact h))
    (case [true]
      (simp only [complete-body hc he complete-comp])
      (exact (i5-dep-final-settle x5d _ (:id c) _ (i5-dep-final-cancel-res x5d _ r
               (i5-dep-final-comp-upd x5d w (:id c) (comp-result-row res (:epoch r)) (comp-result-row-id res (:epoch r))
                 (comp-result-row-pending res (:epoch r)) h)))))))

(tree/restate! G5 '[well-formed-fire-edge well-formed-nat-fold well-formed-t10-finalize-debtor])
(a/theorem i5-dep-final-t-deliver [x5d :- (List Nat), w :- World, x :- Nat, v :- Nat]
  (=> (= (i5-dep-final x5d w) true) (= (i5-dep-final x5d (:world (t-deliver w x v))) true))
  (intro h)
  (cases hs (source-find w x)) (case' [some s]) (case' [none])
  (simp only [t-deliver hs refuse]) (exact h)
  (cases hg (deliverable s))
  (simp only [t-deliver hs hg refuse]) (exact h)
  (simp only [t-deliver hs hg accept deliver-raw])
  (exact (i5-dep-final-t10-finalize-debtor x5d _ x (i5-dep-final-nat-fold x5d (fire-edge (RunResult.mk res-ok v)) (i5-dep-final-fire-edge x5d (RunResult.mk res-ok v)) _ _
           (i5-dep-final-deliver-fire x5d w x v h)))))

(a/theorem react-edge-ok [xd :- (List Nat), w :- World, c :- Nat, v :- Valid]
  (=> (= (deb-final w (:debtor v)) false) (= (dfk xd (fin-st (:sources w) (:tasks w)) (valid-edge w c v)) true))
  (intro hf)
  (have f2 (= (fin-st (:sources w) (:tasks w) (:debtor (valid-edge w c v))) false))
  (simp only [valid-edge]) (rw [← deb-final-st]) (exact hf)
  (exact (dfk-nonfinal xd _ _ f2)))
(tree/restate! G5 '[well-formed-raise-for])
(a/theorem i5-dep-final-react-add [x5d :- (List Nat), w :- World, c :- Nat, v :- Valid]
  (=> (= (i5-dep-final x5d w) true) (= (i5-dep-final x5d (react-add w c v)) true))
  (intro h)
  (cases hk (react-ok w c v))
  (simp only [react-add hk]) (exact h)
  (have nf (= (deb-final w (:debtor v)) false)) (simp only [react-ok Bool.and_eq_true] at hk) (exact (bnot-true _ (And.left hk)))
  (simp only [react-add hk])
  (exact (i5-dep-final-raise-for x5d _ c (:debtor v) (i5-dep-final-insert-edge-checked x5d w (valid-edge w c v) (react-edge-ok x5d w c v nf) h))))

;; ---- T7: a track arms its edge on an open trackable source, or Z#48 consumes it at once

(a/theorem fin-of-find [w :- World, x :- Nat, s :- SourceRow]
  (=> (= (source-find w x) (Option.some SourceRow s)) (= (fin-st (:sources w) (:tasks w) x) (sfin s)))
  (intro hs) (simp only [source-find] at hs) (simp only [fin-st hs find-or]))
(a/theorem sfin-track [s :- SourceRow] (=> (= (trackable s) true) (= (:open s) true) (= (sfin s) false))
  (intros ht ho)
  (simp only [trackable Bool.or_eq_true] at ht)
  (have nd (= (once-kind (:kind s)) false))
  (cases ht)
  (case [inl a] (have e (= (:kind s) sk-signal)) (exact (Nat.eq_of_beq_eq_true a)) (simp only [e once-kind]))
  (case [inr b] (have e (= (:kind s) sk-cell)) (exact (Nat.eq_of_beq_eq_true b)) (simp only [e once-kind]))
  (simp only [sfin ho source-delivered nd Bool.not_true Bool.false_and Bool.false_or]))

(a/theorem jwy-ins [xd :- (List Nat), w :- World, e :- EdgeRow]
  (=> (= (i5-dep-final-rest xd w) true)
      (= (jwy xd (fn [as :- (List ActRow), q :- EdgeRow] false) (:next-id w) (insert-edge-fresh w e)) true))
  (intro h)
  (simp only [i5-dep-final-rest] at h)
  (simp only [jwy insert-edge-fresh bump set-next-id insert-edge edge-ins set-edges tbl-ins tbl-all])
  (have a (= (jm xd (fin-st (:sources w) (:tasks w)) (fn [as :- (List ActRow), q :- EdgeRow] false) (:acts w) (:next-id w)
               (edge-set-marked false (edge-set-id (:next-id w) e))) true))
  (simp only [jm edge-set-marked edge-set-id Nat.beq_refl Bool.or_true])
  (simp only [a Bool.true_and])
  (apply (tbl-all-mono EdgeRow _ _ _ (:edges w) h))
  (intros q hq) (simp only [jm jn hq Bool.true_or]))

(a/theorem jwy-upd-id [xd :- (List Nat), w :- World, y :- Nat, f :- (=> EdgeRow EdgeRow),
                       hid :- (forall [e :- EdgeRow] (= (edge-id (f e)) (edge-id e)))]
  (=> (= (i5-dep-final-rest xd w) true) (= (jwy xd (fn [as :- (List ActRow), q :- EdgeRow] false) y (edge-upd w y f)) true))
  (intro h)
  (simp only [i5-dep-final-rest] at h)
  (simp only [jwy edge-upd set-edges])
  (apply (tbl-all-upd EdgeRow edge-id y f _ _ _ _ (:edges w) h))
  (intros q hq hx)
  (have hx2 (= (Nat.beq (:id (f q)) y) true)) (exact (Eq.trans (congrArg (fn [z :- Nat] (Nat.beq z y)) (hid q)) hx))
  (simp only [jm hx2 Bool.or_true])
  (intros q hq hx)
  (simp only [jm jn hq Bool.true_or]))

(a/theorem i5-dep-final-remove-jwy [xd :- (List Nat), w :- World, y :- Nat]
  (=> (= (well-formed (remove-edge w y)) true) (= (jwy xd (fn [as :- (List ActRow), q :- EdgeRow] false) y w) true)
      (= (i5-dep-final xd (remove-edge w y)) true))
  (intros hs h)
  (exact (i5-dep-final-intro xd _ hs (jw-false-end xd _ (jwy-remove xd (fn [as :- (List ActRow), q :- EdgeRow] false) y w h)))))

(a/theorem reread-ok5 [xd :- (List Nat), w :- World, d :- Nat, c :- Nat, s :- SourceRow, r :- EdgeRow]
  (=> (= (fin-st (:sources w) (:tasks w) d) false) (= (Nat.beq (:debtor r) d) true)
      (= (dfk xd (fin-st (:sources w) (:tasks w)) (edge-reread c s r)) true))
  (intros hf h)
  (have e (= (:debtor r) d)) (exact (Nat.eq_of_beq_eq_true h))
  (have f2 (= (fin-st (:sources w) (:tasks w) (:debtor (edge-reread c s r))) false))
  (simp only [edge-reread e]) (exact hf)
  (exact (dfk-nonfinal xd _ _ f2)))

(tree/restate! G5 '[well-formed-comp-upd well-formed-run-upd])
(a/theorem i5-dep-final-track-raw [x5d :- (List Nat), w :- World, r :- RunRow, x :- Nat, s :- SourceRow, k :- Nat]
  (=> (= (comp-has w (:of r)) true) (= (source-find w x) (Option.some SourceRow s)) (= (trackable s) true)
      (= (i5-dep-final x5d w) true) (= (i5-dep-final x5d (track-raw w r x s k)) true))
  (intros hc hs hk h)
  (have hs0 := (i5-dep-final-well-formed x5d w h))
  (have hr0 := (i5-dep-final-rest-of x5d w h))
  (have h2 (= (i5-dep-final x5d (match (site-edge (:edges w) (:of r) (:effect-index r) x)
                        [none (track-new w r x s k)]
                        [(some e) (comp-upd (track-fin s (:id e) (edge-upd w (:id e) (edge-reread (track-cont r k) s)))
                                            (:of r) (comp-consume-adopt (:effect-index r) x))])) true))
  (cases he (site-edge (:edges w) (:of r) (:effect-index r) x)) (case' [some e]) (case' [none])
  (simp only [track-new])
  (have ins := (track-edge-ok w r x s k hc hs))
  (have t1 (= (i5-dep-final x5d (track-fin s (:next-id w) (insert-edge-fresh w (track-edge r x s k)))) true))
  (cases ho (:open s))
  (case [true]
    (simp only [track-fin ho])
    (have fx (= (fin-st (:sources w) (:tasks w) (:debtor (track-edge r x s k))) false))
    (simp only [track-edge]) (rw [(fin-of-find w x s hs)]) (exact (sfin-track s hk ho))
    (exact (i5-dep-final-insert-edge-fresh x5d w (track-edge r x s k) (dfk-nonfinal x5d _ _ fx) ins h)))
  (case [false]
    (simp only [track-fin ho])
    (exact (i5-dep-final-remove-jwy x5d _ (:next-id w) (well-formed-remove-edge _ (:next-id w) (well-formed-insert-edge-fresh w (track-edge r x s k) ins hs0))
             (jwy-ins x5d w (track-edge r x s k) hr0))))
  (exact (i5-dep-final-comp-upd x5d _ (:of r) (comp-consume-adopt (:effect-index r) x) (comp-consume-adopt-comp-id _ _) (comp-consume-adopt-pending _ _) t1))
  (have sm := (site-edge-mem (:edges w) (:of r) (:effect-index r) x e he))
  (have kx0 := (edge-debtor-kept-of-mem w e hs0 (And.left sm)))
  (have t2 (= (i5-dep-final x5d (track-fin s (:id e) (edge-upd w (:id e) (edge-reread (track-cont r k) s)))) true))
  (cases ho (:open s))
  (case [true]
    (simp only [track-fin ho])
    (have fx (= (fin-st (:sources w) (:tasks w) x) false)) (rw [(fin-of-find w x s hs)]) (exact (sfin-track s hk ho))
    (have ex (= (:debtor e) x)) (exact (Nat.eq_of_beq_eq_true (And.right sm)))
    (have fx2 (= (fin-st (:sources w) (:tasks w) (:debtor e)) false)) (rw [ex]) (exact fx)
    (exact (i5-dep-final-edge-upd-q x5d w (:id e) (edge-reread (track-cont r k) s) (edge-reread-edge-id _ _) (edge-reread-kind _ _)
             (edge-reread-creditor _ _) (edge-reread-debtor _ _) (edge-reread-marked _ _)
             (i5-dep-final-edge-debtor-kept-q x5d (:id e) (:debtor e) w _
               (fn [q :- EdgeRow, hq :- (= (Nat.beq (:debtor q) (:debtor e)) true)] (reread-ok5 x5d w (:debtor e) (track-cont r k) s q fx2 hq))
               (edge-debtor-kept-rest-of _ _ w kx0)) h)))
  (case [false]
    (simp only [track-fin ho])
    (exact (i5-dep-final-remove-jwy x5d _ (:id e)
             (well-formed-remove-edge _ (:id e) (well-formed-edge-upd w (:id e) (edge-reread (track-cont r k) s) (edge-reread-edge-id _ _) (edge-reread-kind _ _)
               (edge-reread-creditor _ _) (edge-reread-debtor _ _) (edge-reread-marked _ _) hs0))
             (jwy-upd-id x5d w (:id e) (edge-reread (track-cont r k) s) (edge-reread-edge-id _ _) hr0))))
  (exact (i5-dep-final-comp-upd x5d _ (:of r) (comp-consume-adopt (:effect-index r) x) (comp-consume-adopt-comp-id _ _) (comp-consume-adopt-pending _ _) t2))
  (simp only [track-raw])
  (exact (i5-dep-final-run-upd x5d _ (:id r) run-tick run-tick-run-id h2)))
;; ===========================================================================
;; T6: member edges on final debtors are fired by the fast path in the same commit
;; ===========================================================================

(a/theorem distinct-acc-ok [xs :- (List Nat)]
  (forall [seen :- (List Nat)]
    (And (= (nat-nodup (nat-distinct-acc seen xs)) true)
         (forall [y :- Nat] (=> (= (nat-mem y (nat-distinct-acc seen xs)) true) (= (nat-mem y seen) false)))))
  (induction xs)
  (case [nil] (intro seen) (apply And.intro) (simp only [nat-distinct-acc nat-nodup]) (intros y h) (simp [nat-distinct-acc nat-mem] at h))
  (case [cons h t ih]
    (intro seen)
    (cases hm (nat-mem h seen))
    (case [true] (simp only [nat-distinct-acc hm]) (exact (ih seen)))
    (case [false]
      (have r := (ih (List.cons Nat h seen)))
      (have nh (= (nat-mem h (nat-distinct-acc (List.cons Nat h seen) t)) false))
      (cases q (nat-mem h (nat-distinct-acc (List.cons Nat h seen) t)))
      (case [false] (rfl))
      (case [true] (have z := ((And.right r) h q)) (simp [nat-mem Nat.beq_refl] at z))
      (simp only [nat-distinct-acc hm])
      (apply And.intro)
      (simp only [nat-nodup nh (And.left r) Bool.not_false Bool.and_self])
      (intros y hy)
      (simp only [nat-mem] at hy)
      (cases hb (Nat.beq h y))
      (case [true] (have e (= h y)) (exact (Nat.eq_of_beq_eq_true hb)) (rw [← e]) (exact hm))
      (case [false]
        (simp only [hb] at hy)
        (have z := ((And.right r) y hy))
        (simp only [nat-mem hb] at z)
        (exact z)))))
(a/theorem distinct-nodup [xs :- (List Nat)] (= (nat-nodup (nat-distinct xs)) true)
  (simp only [nat-distinct]) (exact (And.left (distinct-acc-ok xs (List.nil Nat)))))

(a/defn de-has [d :- Nat, ps :- (List DE)] Bool (tbl-any (fn [p :- DE] (Nat.beq (:deb p) d)) ps))
(a/theorem pair-edge-ne [d :- Nat, d2 :- Nat, n :- Nat, ps :- (List DE)]
  (=> (= (Nat.beq d2 d) false) (= (pair-edge d (List.cons DE (DE.mk d2 n) ps)) (pair-edge d ps)))
  (intro h) (simp only [pair-edge h]))
(a/theorem pair-edge-eq [d :- Nat, n :- Nat, ps :- (List DE)] (= (pair-edge d (List.cons DE (DE.mk d n) ps)) n)
  (simp only [pair-edge Nat.beq_refl]))

;; an armed edge on a final debtor that the fast path will fire: its debtor is a member debtor still
;; to be filled (D) and it is the debtor's recorded member edge
(a/defn esc6 [ps :- (List DE), D :- (List Nat), as :- (List ActRow), e :- EdgeRow] Bool
  (Bool.and (de-has (:debtor e) ps) (Bool.and (reach-mem (:debtor e) D) (Nat.beq (:id e) (pair-edge (:debtor e) ps)))))
(a/theorem esc6-mono [ps :- (List DE), D :- (List Nat)] (esc-mono (esc6 ps D))
  (simp only [esc-mono]) (intros as bs e hi h) (exact h))

(a/theorem de-has-cons-ne [d :- Nat, d2 :- Nat, n :- Nat, ps :- (List DE)]
  (=> (= (Nat.beq d2 d) false) (= (de-has d (List.cons DE (DE.mk d2 n) ps)) (de-has d ps)))
  (intro h) (simp only [de-has tbl-any h Bool.false_or]))

(a/theorem esc6-cons [ps :- (List DE), D :- (List Nat), d :- Nat, n :- Nat, as :- (List ActRow), e :- EdgeRow]
  (=> (= (de-has d ps) false) (= (esc6 ps D as e) true) (= (esc6 (List.cons DE (DE.mk d n) ps) D as e) true))
  (intros hd h)
  (simp only [esc6 Bool.and_eq_true] at h)
  (have h1 := (And.left h))
  (have ne (= (Nat.beq d (:debtor e)) false))
  (cases q (Nat.beq d (:debtor e)))
  (case [false] (rfl))
  (case [true] (have eq (= d (:debtor e))) (exact (Nat.eq_of_beq_eq_true q)) (rw [← eq] at h1) (rw [h1] at hd) (cases hd))
  (have e1 := (de-has-cons-ne (:debtor e) d n ps ne))
  (have e2 := (pair-edge-ne (:debtor e) d n ps ne))
  (simp only [esc6 e1 e2 Bool.and_eq_true])
  (exact h))

(a/theorem jw-pairs-cons [xd :- (List Nat), ps :- (List DE), D :- (List Nat), d :- Nat, n :- Nat, w :- World]
  (=> (= (de-has d ps) false) (= (jw xd (esc6 ps D) w) true) (= (jw xd (esc6 (List.cons DE (DE.mk d n) ps) D) w) true))
  (intros hd h) (simp only [jw] at h) (simp only [jw])
  (apply (tbl-all-mono EdgeRow _ _ _ (:edges w) h))
  (intros e he)
  (simp only [jn Bool.or_eq_true] at he)
  (simp only [jn Bool.or_eq_true])
  (cases he) (case [inl a] (exact (Or.inl a))) (case [inr b] (exact (Or.inr (esc6-cons ps D d n (:acts w) e hd b)))))

;; edits of computations (the I12 raise, adoption) and of activations leave jw (esc6 ...) alone
(a/theorem jw-raise-loop [xd :- (List Nat), esc :- (=> (List ActRow) EdgeRow Bool), fuel :- (List Nat)]
  (forall [d :- Nat, w :- World, todo :- (List RJ)] (= (jw xd esc (:world (raise-loop fuel d w todo))) (jw xd esc w)))
  (induction fuel)
  (case [nil] (intros d w todo) (cases todo) (all_goals (simp only [raise-loop])))
  (case [cons u f ih]
    (intros d w todo)
    (cases todo)
    (case [nil] (simp only [raise-loop]))
    (case [cons j t]
      (cases hd (Nat.beq (:node j) d))
      (case [true] (simp only [raise-loop hd]))
      (case [false]
        (cases hn (Nat.ble (:need j) (comp-rank w (:node j))))
        (case [true] (simp only [raise-loop hd hn]) (exact (ih d w t)))
        (case [false] (simp only [raise-loop hd hn]) (exact (Eq.trans (ih d _ _) (jw-comp-upd xd esc w (:node j) (comp-set-rank (:need j))))))))))
(a/theorem jw-raise-run [xd :- (List Nat), esc :- (=> (List ActRow) EdgeRow Bool), w :- World, c :- Nat, d :- Nat]
  (= (jw xd esc (:world (raise-run w c d))) (jw xd esc w))
  (cases hc (comp-has w d))
  (all_goals (simp only [raise-run hc]))
  (exact (jw-raise-loop xd esc _ d w _)))
(a/theorem jw6-act-upd [xd :- (List Nat), ps :- (List DE), D :- (List Nat), w :- World, a :- Nat, f :- (=> ActRow ActRow)]
  (= (jw xd (esc6 ps D) (act-upd w a f)) (jw xd (esc6 ps D) w))
  (rfl))

;; ---- stage 1: the member edges are wired (await-wire); each armed one on a final debtor is its
;; debtor's recorded pair

(a/theorem jw-ins-checked [xd :- (List Nat), esc :- (=> (List ActRow) EdgeRow Bool), W :- World, e0 :- EdgeRow]
  (=> (= (jn xd (fin-st (:sources W) (:tasks W)) esc (:acts W) (edge-set-marked false (edge-set-id (:next-id W) e0))) true)
      (= (jw xd esc W) true) (= (jw xd esc (insert-edge-checked W e0)) true))
  (intros h0 h)
  (cases hk (edge-ok-in W e0))
  (case [false] (simp only [insert-edge-checked hk]) (exact h))
  (case [true]
    (simp only [jw] at h)
    (simp only [jw insert-edge-checked hk insert-edge-fresh bump set-next-id insert-edge edge-ins set-edges tbl-ins tbl-all h0 h Bool.and_self])))

(a/theorem jw-upd-esc [xd :- (List Nat), esc :- (=> (List ActRow) EdgeRow Bool), W :- World, y :- Nat, f :- (=> EdgeRow EdgeRow)]
  (=> (= (tbl-all (same-id-then edge-id y (fn [r :- EdgeRow] (jn xd (fin-st (:sources W) (:tasks W)) esc (:acts W) (f r)))) (:edges W)) true)
      (= (jw xd esc W) true) (= (jw xd esc (edge-upd W y f)) true))
  (intros hq h) (simp only [jw] at h)
  (have b := (tbl-all-mono2 EdgeRow _ _ (both (same-id-then edge-id y (fn [r :- EdgeRow] (jn xd (fin-st (:sources W) (:tasks W)) esc (:acts W) (f r))))
                                              (jn xd (fin-st (:sources W) (:tasks W)) esc (:acts W)))
               (fn [e :- EdgeRow, h1 :- (= (same-id-then edge-id y (fn [r :- EdgeRow] (jn xd (fin-st (:sources W) (:tasks W)) esc (:acts W) (f r))) e) true),
                    h2 :- (= (jn xd (fin-st (:sources W) (:tasks W)) esc (:acts W) e) true)] (both-of EdgeRow _ _ e h1 h2))
               (:edges W) hq h))
  (simp only [jw edge-upd set-edges])
  (apply (tbl-all-upd EdgeRow edge-id y f _ _ _ _ (:edges W) b))
  (intros e hb hx)
  (have s := (both-left EdgeRow _ _ e hb))
  (simp only [same-id-then hx Bool.not_true Bool.false_or] at s)
  (exact s)
  (intros e hb hx)
  (exact (both-right EdgeRow _ _ e hb)))

(a/theorem esc6-new [ps :- (List DE), D :- (List Nat), d :- Nat, n :- Nat, as :- (List ActRow), row :- EdgeRow]
  (=> (= (:debtor row) d) (= (:id row) n) (= (reach-mem d D) true) (= (esc6 (List.cons DE (DE.mk d n) ps) D as row) true))
  (intros hd hi hm)
  (simp only [esc6 hd hi hm de-has tbl-any Nat.beq_refl Bool.true_or pair-edge-eq Bool.and_self]))
(a/theorem jn6-new [xd :- (List Nat), F :- (=> Nat Bool), ps :- (List DE), D :- (List Nat), d :- Nat, n :- Nat, as :- (List ActRow), row :- EdgeRow]
  (=> (= (:debtor row) d) (= (:id row) n) (= (reach-mem d D) true) (= (jn xd F (esc6 (List.cons DE (DE.mk d n) ps) D) as row) true))
  (intros hd hi hm) (simp only [jn (esc6-new ps D d n as row hd hi hm) Bool.or_true]))

(a/theorem await-edge-debtor [w :- World, r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, d :- Nat]
  (= (:debtor (await-edge w r a mode k d)) d)
  (cases h (as-dep w r d)) (all_goals (simp only [await-edge h])))

(a/theorem dehas-step [r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, acc :- AwAcc, d :- Nat, y :- Nat]
  (= (de-has y (:pairs (await-step r a mode k acc d))) (Bool.or (Nat.beq d y) (de-has y (:pairs acc))))
  (cases hd (as-dep (:world acc) r d))
  (case [false] (simp only [await-step hd de-has tbl-any]))
  (case [true]
    (cases hs (site-edge (:edges (:world acc)) (:of r) (:effect-index r) d))
    (case [none] (simp only [await-step hd hs de-has tbl-any]))
    (case [some e] (simp only [await-step hd hs de-has tbl-any]))))

(a/theorem edge-debtor-kept-same [kxy :- Nat, kxd :- Nat, w :- World, P :- (=> EdgeRow Bool),
                    hp :- (forall [r :- EdgeRow] (=> (= (Nat.beq (:debtor r) kxd) true) (= (Nat.beq (:id r) kxy) true) (= (P r) true)))]
  (=> (= (edge-debtor-kept-rest kxy kxd w) true) (= (tbl-all (same-id-then edge-id kxy P) (:edges w)) true))
  (intro h)
  (simp only [edge-debtor-kept-rest Bool.and_eq_true] at h)
  (apply (tbl-all-mono EdgeRow (deb-at kxy kxd) _ _ (:edges w) (And.right h)))
  (intros r hr)
  (cases hx (Nat.beq (:id r) kxy))
  (case [false] (have hx2 (= (Nat.beq (edge-id r) kxy) false)) (exact hx) (simp only [same-id-then hx2 Bool.not_false Bool.true_or]))
  (case [true]
    (have hx2 (= (Nat.beq (edge-id r) kxy) true)) (exact hx)
    (simp only [deb-at hx Bool.not_true Bool.false_or] at hr)
    (simp only [same-id-then hx2 Bool.not_true Bool.false_or])
    (exact (hp r hr hx))))

(a/theorem jw6-await-step [xd :- (List Nat), r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, acc :- AwAcc, d :- Nat, D :- (List Nat)]
  (=> (= (well-formed (:world acc)) true) (= (de-has d (:pairs acc)) false) (= (reach-mem d D) true)
      (= (jw xd (esc6 (:pairs acc) D) (:world acc)) true)
      (= (jw xd (esc6 (:pairs (await-step r a mode k acc d)) D) (:world (await-step r a mode k acc d))) true))
  (intros hs hd hm h)
  (have hn := (jw-pairs-cons xd (:pairs acc) D d (:next-id (:world acc)) (:world acc) hd h))
  (have ins := (jw-ins-checked xd (esc6 (List.cons DE (DE.mk d (:next-id (:world acc))) (:pairs acc)) D) (:world acc) (await-edge (:world acc) r a mode k d)
                 (jn6-new xd (fin-st (:sources (:world acc)) (:tasks (:world acc))) (:pairs acc) D d (:next-id (:world acc)) (:acts (:world acc))
                   (edge-set-marked false (edge-set-id (:next-id (:world acc)) (await-edge (:world acc) r a mode k d)))
                   (await-edge-debtor (:world acc) r a mode k d) (rfl) hm) hn))
  (cases hdp (as-dep (:world acc) r d))
  (case [false] (simp only [await-step hdp]) (exact ins))
  (case [true]
    (cases hse (site-edge (:edges (:world acc)) (:of r) (:effect-index r) d))
    (case [none]
      (simp only [await-step hdp hse await-new-dep])
      (rw [jw-comp-upd])
      (rw [jw-raise-run])
      (exact ins))
    (case [some e]
      (simp only [await-step hdp hse])
      (rw [jw-comp-upd])
      (have sm := (site-edge-mem (:edges (:world acc)) (:of r) (:effect-index r) d e hse))
      (have kx0 := (edge-debtor-kept-of-mem (:world acc) e hs (And.left sm)))
      (have ed (= (:debtor e) d)) (exact (Nat.eq_of_beq_eq_true (And.right sm)))
      (have q := (edge-debtor-kept-same (:id e) (:debtor e) (:world acc)
                   (fn [r0 :- EdgeRow] (jn xd (fin-st (:sources (:world acc)) (:tasks (:world acc))) (esc6 (List.cons DE (DE.mk d (:id e)) (:pairs acc)) D)
                                            (:acts (:world acc)) (edge-reawait (await-cont r mode k) r0)))
                   (fn [r0 :- EdgeRow, h1 :- (= (Nat.beq (:debtor r0) (:debtor e)) true), h2 :- (= (Nat.beq (:id r0) (:id e)) true)]
                     (jn6-new xd (fin-st (:sources (:world acc)) (:tasks (:world acc))) (:pairs acc) D d (:id e) (:acts (:world acc)) (edge-reawait (await-cont r mode k) r0)
                       (Eq.trans (Nat.eq_of_beq_eq_true h1) ed) (Nat.eq_of_beq_eq_true h2) hm))
                   (edge-debtor-kept-rest-of _ _ (:world acc) kx0)))
      (exact (jw-upd-esc xd _ (:world acc) (:id e) (edge-reawait (await-cont r mode k)) q
               (jw-pairs-cons xd (:pairs acc) D d (:id e) (:world acc) hd h))))))

(a/theorem jw6-await-wire [xd :- (List Nat), r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, D :- (List Nat), T :- (List Nat)]
  (forall [acc :- AwAcc]
    (=> (= (well-formed (:world acc)) true) (= (nat-nodup T) true)
        (forall [y :- Nat] (=> (= (nat-mem y T) true) (= (de-has y (:pairs acc)) false)))
        (forall [y :- Nat] (=> (= (nat-mem y T) true) (= (reach-mem y D) true)))
        (= (jw xd (esc6 (:pairs acc) D) (:world acc)) true)
        (= (jw xd (esc6 (:pairs (await-wire r a mode k acc T)) D) (:world (await-wire r a mode k acc T))) true)))
  (induction T)
  (case [nil] (intros acc hs hn hp hd h) (simp only [await-wire]) (exact h))
  (case [cons d t ih]
    (intros acc hs hn hp hd h)
    (simp only [await-wire])
    (simp only [nat-nodup Bool.and_eq_true] at hn)
    (have dt (= (nat-mem d t) false)) (exact (bnot-true _ (And.left hn)))
    (have md (= (nat-mem d (List.cons Nat d t)) true)) (simp only [nat-mem Nat.beq_refl])
    (have j1 := (jw6-await-step xd r a mode k acc d D hs (hp d md) (hd d md) h))
    (apply (ih (await-step r a mode k acc d) (well-formed-await-step r a mode k acc d hs) (And.right hn)))
    (intros y hy)
    (have ne (= (Nat.beq d y) false))
    (cases q (Nat.beq d y))
    (case [false] (rfl))
    (case [true] (have eq (= d y)) (exact (Nat.eq_of_beq_eq_true q)) (rw [← eq] at hy) (rw [dt] at hy) (cases hy))
    (have my (= (nat-mem y (List.cons Nat d t)) true)) (simp only [nat-mem ne hy Bool.false_or]) 
    (simp only [dehas-step ne (hp y my) Bool.false_or])
    (intros y hy)
    (have my (= (nat-mem y (List.cons Nat d t)) true)) (cases hb (Nat.beq d y)) (case [false] (simp only [nat-mem hb hy])) (case [true] (simp only [nat-mem hb]))
    (exact (hd y my))
    (exact j1)))

;; ---- stage 2: the fast path fills the member of every ready debtor (a final one is ready)
(a/theorem fast-not-final [w :- World, d :- Nat]
  (=> (= (well-formed w) true) (= (fast-ready w d) false) (= (fin-st (:sources w) (:tasks w) d) false))
  (intros hs hf)
  (cases hc (comp-find w d))
  (case [none]
    (simp only [fast-ready hc Bool.or_eq_false_iff] at hf)
    (rw [← deb-final-st]) (exact (And.left hf)))
  (case [some c]
    (have ch (= (comp-has w d) true)) (simp only [comp-has]) (exact (tbl-find-has CompRow comp-id d c (:comps w) hc))
    (have io := (And.right (And.right (well-formed-parts w hs))))
    (have ns (= (tbl-has source-id d (:sources w)) false))
    (cases q (tbl-has source-id d (:sources w)))
    (case [false] (rfl))
    (case [true] (have z := (comp-not-source w d io q)) (rw [ch] at z) (cases z))
    (have nt (= (tbl-has task-id d (:tasks w)) false))
    (rw [← (nat-mem-ids TaskRow task-id d (:tasks w))]) (exact (comp-not-task w d hs ch))
    (simp only [fin-st (find-none-of-has SourceRow source-id d (:sources w) ns) (find-none-of-has TaskRow task-id d (:tasks w) nt) find-or])))

(a/theorem esc6-step [ps :- (List DE), d :- Nat, t :- (List Nat), as :- (List ActRow), e :- EdgeRow]
  (=> (= (esc6 ps (List.cons Nat d t) as e) true) (= (Bool.or (esc6 ps t as e) (Nat.beq (:id e) (pair-edge d ps))) true))
  (intro h)
  (simp only [esc6 Bool.and_eq_true] at h)
  (have h1 := (And.left h)) (have h2 := (And.left (And.right h))) (have h3 := (And.right (And.right h)))
  (cases hb (Nat.beq (:debtor e) d))
  (case [true]
    (have eq (= (:debtor e) d)) (exact (Nat.eq_of_beq_eq_true hb))
    (rw [eq] at h3) (simp only [h3 Bool.or_true]))
  (case [false]
    (simp only [reach-mem hb] at h2)
    (simp only [esc6 h1 h2 h3 Bool.and_self Bool.true_or])))

(a/theorem esc6-nf [xd :- (List Nat), F :- (=> Nat Bool), ps :- (List DE), d :- Nat, t :- (List Nat), as :- (List ActRow), e :- EdgeRow]
  (=> (= (F d) false) (= (jn xd F (esc6 ps (List.cons Nat d t)) as e) true) (= (jn xd F (esc6 ps t) as e) true))
  (intros hf h)
  (simp only [jn Bool.or_eq_true] at h)
  (cases h)
  (case [inl a] (simp only [jn a Bool.true_or]))
  (case [inr b]
    (cases hb (Nat.beq (:debtor e) d))
    (case [true]
      (have eq (= (:debtor e) d)) (exact (Nat.eq_of_beq_eq_true hb))
      (have f2 (= (F (:debtor e)) false)) (rw [eq]) (exact hf)
      (simp only [jn (dfk-nonfinal xd F e f2) Bool.true_or]))
    (case [false]
      (simp only [esc6 Bool.and_eq_true] at b)
      (have b1 := (And.left b)) (have b2 := (And.left (And.right b))) (have b3 := (And.right (And.right b)))
      (simp only [reach-mem hb] at b2)
      (simp only [jn esc6 b1 b2 b3 Bool.and_self Bool.or_true]))))

;; Z#61: once the activation resolved (an `any`'s first fill, a failing `all`), a ready debtor's
;; pair edge is no member: the fast fill leaves it, and it stays exempt (`escn`: a pair edge of D
;; that is no member) until T10 after the fills removes it (or its debtor is not final)
(a/defn escn [ps :- (List DE), D :- (List Nat), as :- (List ActRow), e :- EdgeRow] Bool
  (Bool.and (esc6 ps D as e) (Bool.not (mem-in (:id e) as))))
(a/defn escf [ps :- (List DE), T :- (List Nat), D :- (List Nat), as :- (List ActRow), e :- EdgeRow] Bool
  (Bool.or (esc6 ps T as e) (escn ps D as e)))
(a/theorem escn-mono [ps :- (List DE), D :- (List Nat)] (esc-mono (escn ps D))
  (simp only [esc-mono]) (intros as bs e hi h)
  (cases hb (mem-in (:id e) bs))
  (case [false]
    (simp only [escn hb Bool.not_false Bool.and_true])
    (simp only [escn Bool.and_eq_true] at h) (exact (And.left h)))
  (case [true]
    (have z := (hi _ hb))
    (simp only [escn Bool.and_eq_true] at h)
    (have h2 := (And.right h)) (rw [z] at h2) (simp at h2)))
(a/theorem escf-mono [ps :- (List DE), T :- (List Nat), D :- (List Nat)] (esc-mono (escf ps T D))
  (simp only [esc-mono]) (intros as bs e hi h)
  (simp only [escf Bool.or_eq_true] at h)
  (cases h)
  (case [inl a] (simp only [escf Bool.or_eq_true]) (exact (Or.inl a)))
  (case [inr b] (simp only [escf Bool.or_eq_true]) (exact (Or.inr (escn-mono ps D as bs e hi b)))))

(a/theorem esc6-escf [xd :- (List Nat), F :- (=> Nat Bool), ps :- (List DE), T :- (List Nat), D :- (List Nat), as :- (List ActRow), e :- EdgeRow]
  (=> (= (jn xd F (esc6 ps T) as e) true) (= (jn xd F (escf ps T D) as e) true))
  (intro h)
  (simp only [jn Bool.or_eq_true] at h)
  (cases h)
  (case [inl a] (simp only [jn a Bool.true_or]))
  (case [inr b] (simp only [jn escf b Bool.true_or Bool.or_true])))
(a/theorem jw-escf [xd :- (List Nat), ps :- (List DE), T :- (List Nat), D :- (List Nat), w :- World]
  (=> (= (jw xd (esc6 ps T) w) true) (= (jw xd (escf ps T D) w) true))
  (intro h) (simp only [jw] at h) (simp only [jw])
  (apply (tbl-all-mono EdgeRow _ _ _ (:edges w) h))
  (intros e he) (exact (esc6-escf xd _ ps T D (:acts w) e he)))

(a/theorem escf-nf [xd :- (List Nat), F :- (=> Nat Bool), ps :- (List DE), d :- Nat, t :- (List Nat), D :- (List Nat), as :- (List ActRow), e :- EdgeRow]
  (=> (= (F d) false) (= (jn xd F (escf ps (List.cons Nat d t) D) as e) true) (= (jn xd F (escf ps t D) as e) true))
  (intros hf h)
  (simp only [jn Bool.or_eq_true] at h)
  (cases h)
  (case [inl a] (simp only [jn a Bool.true_or]))
  (case [inr b]
    (simp only [escf Bool.or_eq_true] at b)
    (cases b)
    (case [inr c] (simp only [jn escf c Bool.or_true]))
    (case [inl c]
      (have j0 (= (jn xd F (esc6 ps (List.cons Nat d t)) as e) true)) (simp only [jn c Bool.or_true])
      (exact (esc6-escf xd F ps t D as e (esc6-nf xd F ps d t as e hf j0))))))

(a/theorem escf-skip [xd :- (List Nat), F :- (=> Nat Bool), ps :- (List DE), d :- Nat, t :- (List Nat), D :- (List Nat), as :- (List ActRow), e :- EdgeRow]
  (=> (= (mem-in (pair-edge d ps) as) false) (= (reach-mem d D) true)
      (= (jn xd F (escf ps (List.cons Nat d t) D) as e) true) (= (jn xd F (escf ps t D) as e) true))
  (intros hm hd h)
  (simp only [jn Bool.or_eq_true] at h)
  (cases h)
  (case [inl a] (simp only [jn a Bool.true_or]))
  (case [inr b]
    (simp only [escf Bool.or_eq_true] at b)
    (cases b)
    (case [inr c] (simp only [jn escf c Bool.or_true]))
    (case [inl c]
      (simp only [esc6 Bool.and_eq_true] at c)
      (have b1 := (And.left c)) (have b2 := (And.left (And.right c))) (have b3 := (And.right (And.right c)))
      (cases hb (Nat.beq (:debtor e) d))
      (case [true]
        (have eq (= (:debtor e) d)) (exact (Nat.eq_of_beq_eq_true hb))
        (have ie (= (:id e) (pair-edge d ps))) (rw [← eq]) (exact (Nat.eq_of_beq_eq_true b3))
        (have nm (= (mem-in (:id e) as) false)) (rw [ie]) (exact hm)
        (have dD (= (reach-mem (:debtor e) D) true)) (rw [eq]) (exact hd)
        (simp only [jn escf escn esc6 b1 dD b3 nm Bool.not_false Bool.and_self Bool.or_true]))
      (case [false]
        (simp only [reach-mem hb] at b2)
        (simp only [jn escf esc6 b1 b2 b3 Bool.and_self Bool.true_or Bool.or_true])))))

(a/theorem escf-step [xd :- (List Nat), F :- (=> Nat Bool), ps :- (List DE), d :- Nat, t :- (List Nat), D :- (List Nat), as :- (List ActRow), e :- EdgeRow]
  (=> (= (jn xd F (escf ps (List.cons Nat d t) D) as e) true) (= (jm xd F (escf ps t D) as (pair-edge d ps) e) true))
  (intro h)
  (simp only [jn Bool.or_eq_true] at h)
  (cases h)
  (case [inl a] (simp only [jm jn a Bool.true_or]))
  (case [inr b]
    (simp only [escf Bool.or_eq_true] at b)
    (cases b)
    (case [inr c] (simp only [jm jn escf c Bool.or_true Bool.true_or]))
    (case [inl c]
      (have s := (esc6-step ps d t as e c))
      (simp only [Bool.or_eq_true] at s)
      (cases s)
      (case [inl s1] (simp only [jm jn escf s1 Bool.true_or Bool.or_true]))
      (case [inr s2] (simp only [jm s2 Bool.or_true])))))

(a/theorem jw6-fast [xd :- (List Nat), ps :- (List DE), T :- (List Nat), D :- (List Nat)]
  (forall [w :- World] (=> (= (well-formed w) true) (forall [y :- Nat] (=> (= (reach-mem y T) true) (= (reach-mem y D) true)))
                           (= (jw xd (escf ps T D) w) true)
                           (= (jw xd (escf ps (List.nil Nat) D) (nat-fold (fast-fill ps) w T)) true)))
  (induction T)
  (case [nil] (intros w hs hsub h) (simp only [nat-fold]) (exact h))
  (case [cons d t ih]
    (intros w hs hsub h)
    (simp only [nat-fold])
    (have hsub2 (forall [y :- Nat] (=> (= (reach-mem y t) true) (= (reach-mem y D) true))))
    (intros y hy) (apply hsub) (simp only [reach-mem])
    (cases hyd (Nat.beq y d))
    (case [false] (simp only [hyd]) (exact hy))
    (case [true] (simp only [hyd]))
    (apply (ih (fast-fill ps w d) (well-formed-fast-fill ps w d hs) hsub2))
    (cases hr (fast-ready w d))
    (case [false]
      (simp only [fast-fill hr])
      (have nf := (fast-not-final w d hs hr))
      (simp only [jw] at h) (simp only [jw])
      (apply (tbl-all-mono EdgeRow _ _ _ (:edges w) h))
      (intros e he) (exact (escf-nf xd _ ps d t D (:acts w) e nf he)))
    (case [true]
      (cases hm (still-member w (pair-edge d ps)))
      (case [false]
        (simp only [fast-fill hr hm])
        (have hm2 (= (mem-in (pair-edge d ps) (:acts w)) false)) (simp only [mem-in]) (simp only [still-member] at hm) (exact hm)
        (have hd (= (reach-mem d D) true)) (apply hsub) (simp only [reach-mem Nat.beq_refl])
        (simp only [jw] at h) (simp only [jw])
        (apply (tbl-all-mono EdgeRow _ _ _ (:edges w) h))
        (intros e he) (exact (escf-skip xd _ ps d t D (:acts w) e hm2 hd he)))
      (case [true]
        (simp only [fast-fill hr hm])
        (have j (= (jwy xd (escf ps t D) (pair-edge d ps) w) true))
        (simp only [jw] at h) (simp only [jwy])
        (apply (tbl-all-mono EdgeRow _ _ _ (:edges w) h))
        (intros e he) (exact (escf-step xd _ ps d t D (:acts w) e he))
        (exact (jw-fire-edge xd (escf ps t D) _ w (pair-edge d ps) (escf-mono ps t D) hs j))))))

;; after the fills only the non-member pair edges stay exempt; park-if keeps them; T10 on each
;; debtor discharges its own (a kept edge on a final debtor is not an armed dep edge)
(a/theorem jw6-escn [xd :- (List Nat), ps :- (List DE), D :- (List Nat), w :- World]
  (=> (= (jw xd (escf ps (List.nil Nat) D) w) true) (= (jw xd (escn ps D) w) true))
  (intro h) (simp only [jw] at h) (simp only [jw])
  (apply (tbl-all-mono EdgeRow _ _ _ (:edges w) h))
  (intros e he) (simp only [jn escf esc6 reach-mem Bool.false_and Bool.and_false Bool.false_or] at he) (simp only [jn]) (exact he))
(a/theorem jw-run-upd [xd :- (List Nat), esc :- (=> (List ActRow) EdgeRow Bool), w :- World, x :- Nat, f :- (=> RunRow RunRow)]
  (= (jw xd esc (run-upd w x f)) (jw xd esc w)) (rfl))
(a/theorem jw-park-if [xd :- (List Nat), esc :- (=> (List ActRow) EdgeRow Bool), w :- World, a :- Nat, rid :- Nat]
  (= (jw xd esc (park-if w a rid)) (jw xd esc w))
  (cases hc (act-has w a))
  (all_goals (simp only [park-if hc jw run-upd set-runs])))
(a/theorem escn-nf [xd :- (List Nat), F :- (=> Nat Bool), ps :- (List DE), d :- Nat, t :- (List Nat), as :- (List ActRow), e :- EdgeRow]
  (=> (= (F d) false) (= (jn xd F (escn ps (List.cons Nat d t)) as e) true) (= (jn xd F (escn ps t) as e) true))
  (intros hf h)
  (simp only [jn Bool.or_eq_true] at h)
  (cases h)
  (case [inl a] (simp only [jn a Bool.true_or]))
  (case [inr b]
    (cases hb (Nat.beq (:debtor e) d))
    (case [true]
      (have eq (= (:debtor e) d)) (exact (Nat.eq_of_beq_eq_true hb))
      (have f2 (= (F (:debtor e)) false)) (rw [eq]) (exact hf)
      (simp only [jn (dfk-nonfinal xd F e f2) Bool.true_or]))
    (case [false]
      (simp only [escn esc6 Bool.and_eq_true] at b)
      (have b1 := (And.left (And.left b))) (have b2 := (And.left (And.right (And.left b))))
      (have b3 := (And.right (And.right (And.left b)))) (have b4 := (And.right b))
      (simp only [reach-mem hb] at b2)
      (simp only [jn escn esc6 b1 b2 b3 b4 Bool.and_self Bool.or_true]))))
(a/theorem escn-keep [xd :- (List Nat), F :- (=> Nat Bool), ps :- (List DE), d :- Nat, t :- (List Nat), as :- (List ActRow), e :- EdgeRow]
  (=> (= (finalize-keeps as d e) true) (= (jn xd F (escn ps (List.cons Nat d t)) as e) true) (= (jn xd F (escn ps t) as e) true))
  (intros hk h)
  (simp only [jn Bool.or_eq_true] at h)
  (cases h)
  (case [inl a] (simp only [jn a Bool.true_or]))
  (case [inr b]
    (simp only [escn esc6 Bool.and_eq_true] at b)
    (have b1 := (And.left (And.left b))) (have b2 := (And.left (And.right (And.left b))))
    (have b3 := (And.right (And.right (And.left b)))) (have b4 := (And.right b))
    (cases hb (Nat.beq (:debtor e) d))
    (case [true]
      (have m (= (tbl-any (act-has-member (:id e)) as) false)) (simp only [mem-in] at b4) (exact (bnot-true _ b4))
      (cases hd (Nat.beq (:kind e) ek-dep))
      (case [false] (simp only [jn (dfk-kind xd F e hd) Bool.true_or]))
      (case [true]
        (cases hp (Nat.beq (:phase e) ph-armed))
        (case [false] (simp only [jn (dfk-phase xd F e hp) Bool.true_or]))
        (case [true]
          (simp only [finalize-keeps finalize-drops hd hp hb m Bool.not_false Bool.and_self Bool.not_true] at hk)
          (cases hk))))
    (case [false]
      (simp only [reach-mem hb] at b2)
      (simp only [jn escn esc6 b1 b2 b3 b4 Bool.and_self Bool.or_true]))))
(a/theorem jw-fin-one [xd :- (List Nat), ps :- (List DE), d :- Nat, t :- (List Nat), w :- World]
  (=> (= (jw xd (escn ps (List.cons Nat d t)) w) true) (= (jw xd (escn ps t) (finalize-if-final w d)) true))
  (intro h)
  (simp only [jw] at h)
  (cases hf (deb-final w d))
  (case [false]
    (simp only [finalize-if-final hf]) (simp only [jw])
    (have nf (= (fin-st (:sources w) (:tasks w) d) false)) (rw [← deb-final-st]) (exact hf)
    (apply (tbl-all-mono EdgeRow _ _ _ (:edges w) h))
    (intros e he) (exact (escn-nf xd _ ps d t (:acts w) e nf he)))
  (case [true]
    (simp only [finalize-if-final hf]) (rw [fd-one])
    (simp only [jw finalize-one drop-edges set-comps set-edges])
    (exact (tbl-all-filter-imp EdgeRow _ _ (finalize-keeps (:acts w) d)
             (fn [e :- EdgeRow, h1 :- (= (jn xd (fin-st (:sources w) (:tasks w)) (escn ps (List.cons Nat d t)) (:acts w) e) true),
                  h2 :- (= (finalize-keeps (:acts w) d e) true)]
               (escn-keep xd _ ps d t (:acts w) e h2 h1))
             (:edges w) h))))
(a/theorem jw-fin-fold [xd :- (List Nat), ps :- (List DE), D :- (List Nat)]
  (forall [w :- World] (=> (= (jw xd (escn ps D) w) true) (= (jw xd (escn ps (List.nil Nat)) (nat-fold finalize-if-final w D)) true)))
  (induction D)
  (case [nil] (intros w h) (simp only [nat-fold]) (exact h))
  (case [cons d t ih] (intros w h) (simp only [nat-fold]) (exact (ih _ (jw-fin-one xd ps d t w h)))))
(a/theorem jw-escn-end [xd :- (List Nat), ps :- (List DE), w :- World]
  (=> (= (jw xd (escn ps (List.nil Nat)) w) true) (= (i5-dep-final-rest xd w) true))
  (intro h) (simp only [jw] at h) (simp only [i5-dep-final-rest])
  (apply (tbl-all-mono EdgeRow _ _ _ (:edges w) h))
  (intros e he) (simp only [jn escn esc6 reach-mem Bool.false_and Bool.and_false Bool.or_false] at he) (exact he))

(a/theorem jw6-end [xd :- (List Nat), ps :- (List DE), w :- World]
  (=> (= (jw xd (esc6 ps (List.nil Nat)) w) true) (= (i5-dep-final-rest xd w) true))
  (intro h) (simp only [jw] at h) (simp only [i5-dep-final-rest])
  (apply (tbl-all-mono EdgeRow _ _ _ (:edges w) h))
  (intros e he) (simp only [jn esc6 reach-mem Bool.false_and Bool.and_false Bool.or_false] at he) (exact he))
(a/theorem jw6-start [xd :- (List Nat), D :- (List Nat), w :- World]
  (=> (= (i5-dep-final-rest xd w) true) (= (jw xd (esc6 (List.nil DE) D) w) true))
  (intro h) (simp only [i5-dep-final-rest] at h) (simp only [jw])
  (apply (tbl-all-mono EdgeRow _ _ _ (:edges w) h))
  (intros e he) (simp only [jn he Bool.true_or]))

(tree/restate! G5 '[well-formed-await-pre well-formed-park-if well-formed-finalize-if-final well-formed-nat-fold well-formed-fast-fill well-formed-act-upd])
(a/theorem i5-dep-final-await-raw [x5d :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (= (i5-dep-final x5d w) true) (= (i5-dep-final x5d (await-raw w r ds mode k mine)) true))
  (intro h)
  (have h0 := (i5-dep-final-await-pre x5d w r ds mode k mine h))
  (have hs0 := (i5-dep-final-well-formed x5d _ h0))
  (have j2 (= (jw x5d (esc6 (:pairs (await-acc w r ds mode k mine)) (nat-distinct ds)) (:world (await-acc w r ds mode k mine))) true))
  (exact (jw6-await-wire x5d r (:next-id w) mode k (nat-distinct ds) (nat-distinct ds)
           (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) hs0 (distinct-nodup ds)
           (fn [y :- Nat, hy :- (= (nat-mem y (nat-distinct ds)) true)] (Eq.refl false))
           (fn [y :- Nat, hy :- (= (nat-mem y (nat-distinct ds)) true)] (Eq.trans (reach-mem-nat-mem y (nat-distinct ds)) hy))
           (jw6-start x5d (nat-distinct ds) (await-pre w r ds mode k mine) (i5-dep-final-rest-of x5d _ h0))))
  (have hs2 (= (well-formed (:world (await-acc w r ds mode k mine))) true))
  (exact (well-formed-await-wire r (:next-id w) mode k (nat-distinct ds) (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) hs0))
  (have hs3 := (well-formed-act-upd (:world (await-acc w r ds mode k mine)) (:next-id w)
                 (act-set-members (mk-members (:pairs (await-acc w r ds mode k mine)) 0 ds))
                 (act-set-members-id (mk-members (:pairs (await-acc w r ds mode k mine)) 0 ds)) hs2))
  (have j3 := (Eq.trans (jw6-act-upd x5d (:pairs (await-acc w r ds mode k mine)) (nat-distinct ds) (:world (await-acc w r ds mode k mine)) (:next-id w)
                          (act-set-members (mk-members (:pairs (await-acc w r ds mode k mine)) 0 ds))) j2))
  (have j4 := (jw6-fast x5d (:pairs (await-acc w r ds mode k mine)) (nat-distinct ds) (nat-distinct ds) _ hs3
                (fn [y :- Nat, hy :- (= (reach-mem y (nat-distinct ds)) true)] hy)
                (jw-escf x5d (:pairs (await-acc w r ds mode k mine)) (nat-distinct ds) (nat-distinct ds) _ j3)))
  (have hs4 := (well-formed-nat-fold (fast-fill (:pairs (await-acc w r ds mode k mine))) (well-formed-fast-fill (:pairs (await-acc w r ds mode k mine)))
                 (nat-distinct ds) _ hs3))
  (have j5 := (jw6-escn x5d (:pairs (await-acc w r ds mode k mine)) (nat-distinct ds) _ j4))
  (have j6 := (Eq.trans (jw-park-if x5d (escn (:pairs (await-acc w r ds mode k mine)) (nat-distinct ds)) (nat-fold (fast-fill (:pairs (await-acc w r ds mode k mine))) (act-upd (:world (await-acc w r ds mode k mine)) (:next-id w) (act-set-members (mk-members (:pairs (await-acc w r ds mode k mine)) 0 ds))) (nat-distinct ds)) (:next-id w) (:id r)) j5))
  (have j7 := (jw-fin-fold x5d (:pairs (await-acc w r ds mode k mine)) (nat-distinct ds) _ j6))
  (have hs7 := (well-formed-nat-fold finalize-if-final well-formed-finalize-if-final (nat-distinct ds) _ (well-formed-park-if _ (:next-id w) (:id r) hs4)))
  (simp only [await-raw await-post])
  (exact (i5-dep-final-intro x5d _ hs7 (jw-escn-end x5d (:pairs (await-acc w r ds mode k mine)) _ j7))))

;; ===========================================================================
;; Part C. The copy, Rule R and the step
;; ===========================================================================

;; T11's dispatch: the entry edge is the world's (edge-debtor-kept through the cut); after the cascade's lemmas
(tree/restate! G5 '[well-formed-cancel-pred well-formed-cut-suffix well-formed-new-run-of])
(a/theorem i5-dep-final-dispatch-raw [x5d :- (List Nat), w :- World, c :- CompRow]
  (=> (= (i5-dep-final x5d w) true) (= (i5-dep-final x5d (dispatch-raw w c)) true))
  (intro h)
  (have h1 := (i5-dep-final-cancel-pred x5d w c h))
  (cases he (entry-edge w (:id c))) (case' [some e]) (case' [none])
  (simp only [dispatch-raw he])
  (exact (i5-dep-final-new-run-of x5d _ c 0 (i5-dep-final-cut-suffix x5d _ (:id c) false 0 0 h1)))
  (simp only [dispatch-raw he])
  (have k0 := (edge-debtor-kept-of-mem w e (i5-dep-final-well-formed x5d w h) (entry-mem w (:id c) e he)))
  (have k1 := (edge-debtor-kept-cut-suffix (:id e) (:debtor e) _ (:id c) true (:at e) (:id e) (edge-debtor-kept-cancel-pred (:id e) (:debtor e) w c k0)))
  (exact (i5-dep-final-new-run-of x5d _ c _ (i5-dep-final-consume-entry x5d _ e k1 (i5-dep-final-cut-suffix x5d _ (:id c) true (:at e) (:id e) h1)))))

(tree/restate! G5 '[well-formed-raw well-formed-normalize])

;; ===========================================================================
;; Rule R and the step
;; ===========================================================================

(a/theorem i5-dep-final-rule-r-round [xd :- (List Nat), w :- World]
  (=> (= (i5-dep-final xd w) true) (= (filter-safe (normalize w)) true) (= (i5-dep-final xd (rule-r-round w)) true))
  (intros h hf)
  (simp only [rule-r-round])
  (rw [rule-r-filter-eq])
  (exact (i5-dep-final-filter-world xd _ (keep-fn (normalize w)) (i5-dep-final-normalize xd w h) hf)))

(a/theorem i5-dep-final-rule-r-loop [xd :- (List Nat), fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (i5-dep-final xd w0) true) (= (rounds-safe-loop fuel w0) true) (= (i5-dep-final xd (rule-r-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 h hs) (simp only [rounds-safe-loop] at hs) (simp only [rule-r-loop]) (exact (i5-dep-final-rule-r-round xd w0 h hs)))
  (case [cons x f ih]
    (intros w0 h hs)
    (simp only [rounds-safe-loop Bool.and_eq_true] at hs)
    (have h1 := (i5-dep-final-rule-r-round xd w0 h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false] (simp only [ho] at hs) (simp only [rule-r-loop ho]) (exact (ih (rule-r-round w0) h1 (And.right hs))))
    (case [true] (simp only [rule-r-loop ho]) (exact h1))))

(a/theorem i5-dep-final-rule-r [xd :- (List Nat), w :- World] (=> (= (i5-dep-final xd w) true) (= (rule-r-safe w) true) (= (i5-dep-final xd (rule-r w)) true))
  (intros h hs) (simp only [rule-r-safe] at hs) (simp only [rule-r]) (exact (i5-dep-final-rule-r-loop xd (rule-r-fuel w) w h hs)))

(a/theorem step-i5-dep-final [xd :- (List Nat), w :- World, it :- Item]
  (=> (= (i5-dep-final xd w) true) (= (rule-r-safe (:world (raw w it))) true) (= (i5-dep-final xd (:world (world-step w it))) true))
  (intros h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true] (have e2 := (step-accepted w it ha)) (rw [e2]) (exact (i5-dep-final-rule-r xd (:world (raw w it)) (i5-dep-final-raw xd w it h) hs))))

(a/theorem i5-dep-final-empty [] (= (i5-dep-final (List.nil Nat) empty-world) true) (rfl))

;; the combined bundle: chain-to-i5-dep-final = chain-to-i1-scopes && i5-dep-final [] (no honest hypothesis)
(a/defn chain-to-i5-dep-final [w :- World] Bool (Bool.and (chain-to-i1-scopes w) (i5-dep-final (List.nil Nat) w)))
(a/theorem chain-to-i5-dep-final-parts [w :- World] (=> (= (chain-to-i5-dep-final w) true) (And (= (chain-to-i1-scopes w) true) (= (i5-dep-final (List.nil Nat) w) true)))
  (intro h) (simp only [chain-to-i5-dep-final Bool.and_eq_true] at h) (exact h))
(a/theorem chain-to-i5-dep-final-empty [] (= (chain-to-i5-dep-final empty-world) true) (rfl))
(a/theorem step-chain-to-i5-dep-final [w :- World, it :- Item] (=> (= (chain-to-i5-dep-final w) true) (= (chain-to-i5-dep-final (:world (world-step w it))) true))
  (intro h)
  (have p := (chain-to-i5-dep-final-parts w h))
  (have pe := (chain-to-i1-scopes-parts w (And.left p)))
  (have pd := (chain-to-i11a-parts w (And.left pe)))
  (have pc := (chain-to-i10-current-parts w (And.left pd)))
  (have a1 := (step-chain-to-i1-scopes w it (And.left p)))
  (have a2 := (step-i5-dep-final (List.nil Nat) w it (And.right p) (step-rule-r-safe w it (And.left pc))))
  (simp only [chain-to-i5-dep-final a1 a2 Bool.and_self]))

;; Theorem: literal I5, dep-final clause (no armed dep edge has a final debtor), through every step
(a/theorem step-lit-i5-dep-final-total [w :- World, it :- Item]
  (=> (= (chain-to-i5-dep-final w) true) (= (lit-i5-dep-final (:world (world-step w it))) true))
  (intro h) (exact (i5-dep-final-lit _ (i5-dep-final-rest-of (List.nil Nat) _ (And.right (chain-to-i5-dep-final-parts _ (step-chain-to-i5-dep-final w it h)))))))
(a/theorem lit-i5-dep-final-of [w :- World] (=> (= (chain-to-i5-dep-final w) true) (= (lit-i5-dep-final w) true))
  (intro h) (exact (i5-dep-final-lit w (i5-dep-final-rest-of (List.nil Nat) w (And.right (chain-to-i5-dep-final-parts w h))))))
