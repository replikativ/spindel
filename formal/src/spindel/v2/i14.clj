(ns spindel.v2.i14
  "I14 (engine-v2 spec, Z#60): the validity graph over idle computations (edges from each idle
  computation to the computation debtors of its validity entries) has no cycle, kernel-checked
  through `world-step` (Init only).

  Witness. A validity entry is recorded at demotion from a dep edge of C (rule.clj `edge-valid`);
  it carries two model-only fields (not projected): `stamp` = the allocator (next-id) and `crank` =
  C's I12 rank at that moment. An entry's key is (stamp, crank); `prec14 v u` (u below v) is
  stamp(v) < stamp(u), or equal stamps and crank(u) < crank(v). The invariant `iv14`: for every
  idle C and entry v of C
    (a) stamp(v) <= next-id;
    (b) for every computation row D with v's debtor id: stamp(v) < next-id or rank(D) < crank(v),
        and when D is idle, every entry u of D is below v.
  Along a validity path the entries strictly descend (`prec14` is transitive and irreflexive), so a
  cycle is impossible (`i14-acyclic`). Why it is preserved: Rule R does not allocate, so the
  demotions of one pass share their stamp and I12 orders them (a dep edge's debtor has a smaller
  rank); a later demotion has a larger stamp; ranks rise only after an allocation of the same
  transition (T6, T8, T22 allocate before any reactivation or I12 raise), when every stamp is below
  next-id; a dep edge never points at an idle computation between steps (`dna`)."
  (:require [ansatz.core :as a]
            [clojure.string :as str]
            [clojure.walk :as walk]
            [spindel.v2.state :refer :all]
            [spindel.v2.edits :refer :all]
            [spindel.v2.reach :refer :all]
            [spindel.v2.retain :refer :all]
            [spindel.v2.step :refer :all]
            [spindel.v2.rule :refer :all]
            [spindel.v2.engine :refer :all]
            [spindel.v2.rank :refer :all]
            [spindel.v2.rank-step :refer :all]
            [spindel.v2.casc :refer :all]
            [spindel.v2.acts :refer :all]
            [spindel.v2.inv :refer :all]
            [spindel.v2.lit :refer :all]
            [spindel.v2.idle :refer :all]
            [spindel.v2.p3 :refer :all]
            [spindel.v2.i10 :refer :all]
            [spindel.v2.i11 :refer :all]
            [spindel.v2.i1 :refer :all]
            [spindel.v2.i8 :refer :all]
            [spindel.v2.hm :refer :all]
            [spindel.v2.react :refer :all]))

;; ===========================================================================
;; Part A. Domination: list edits that only wake rows or drop rows
;; ===========================================================================

;; a row k is dominated by c: same id and rank; if k is idle, c is idle with the same validity
(a/structure C14 [] (id Nat) (idle Bool) (rank Nat) (val (List Valid)))
(a/defn ck14 [c :- CompRow] C14 (C14.mk (:id c) (:idle c) (:rank c) (:validity c)))
(a/defn dom14 [k :- CompRow, c :- CompRow] Prop
  (And (= (:id k) (:id c))
       (And (= (:rank k) (:rank c))
            (=> (= (:idle k) true) (And (= (:idle c) true) (= (:validity k) (:validity c)))))))

(a/theorem dom14-key [k :- CompRow, c :- CompRow] (=> (= (ck14 k) (ck14 c)) (dom14 k c))
  (intro h)
  (have e1 (= (:id k) (:id c))) (exact (congrArg (fn [q :- C14] (:id q)) h))
  (have e2 (= (:idle k) (:idle c))) (exact (congrArg (fn [q :- C14] (:idle q)) h))
  (have e3 (= (:rank k) (:rank c))) (exact (congrArg (fn [q :- C14] (:rank q)) h))
  (have e4 (= (:validity k) (:validity c))) (exact (congrArg (fn [q :- C14] (:val q)) h))
  (apply And.intro) (exact e1)
  (apply And.intro) (exact e3)
  (intro hi) (exact (And.intro (Eq.trans (Eq.symm e2) hi) e4)))
(a/theorem dom14-refl [c :- CompRow] (dom14 c c) (exact (dom14-key c c (Eq.refl (ck14 c)))))
(a/theorem dom14-wake [k :- CompRow, c :- CompRow]
  (=> (= (:id k) (:id c)) (= (:rank k) (:rank c)) (= (:idle k) false) (dom14 k c))
  (intros h1 h2 h3)
  (apply And.intro) (exact h1)
  (apply And.intro) (exact h2)
  (intro hi) (rw [h3] at hi) (cases hi))

;; P is closed under domination
(a/defn dcl14 [P :- (=> CompRow Bool)] Prop
  (forall [k :- CompRow, c :- CompRow] (=> (dom14 k c) (= (P c) true) (= (P k) true))))
;; cs2 keeps every dominated-closed fact of cs
(a/defn cpres [cs :- (List CompRow), cs2 :- (List CompRow)] Prop
  (forall [P :- (=> CompRow Bool)] (=> (dcl14 P) (= (tbl-all P cs) true) (= (tbl-all P cs2) true))))

(a/theorem cpres-refl [cs :- (List CompRow)] (cpres cs cs)
  (intros P hP h) (exact h))
(a/theorem cpres-trans [cs :- (List CompRow), cs2 :- (List CompRow), cs3 :- (List CompRow)]
  (=> (cpres cs cs2) (cpres cs2 cs3) (cpres cs cs3))
  (intros h1 h2 P hP h) (exact (h2 P hP (h1 P hP h))))
(a/theorem cpres-upd [x :- Nat, f :- (=> CompRow CompRow), hd :- (forall [c :- CompRow] (dom14 (f c) c)), cs :- (List CompRow)]
  (cpres cs (tbl-upd comp-id x f cs))
  (intros P hP h)
  (exact (tbl-all-upd CompRow comp-id x f P P
           (fn [r :- CompRow, h1 :- (= (P r) true), h2 :- (= (Nat.beq (comp-id r) x) true)] (hP (f r) r (hd r) h1))
           (fn [r :- CompRow, h1 :- (= (P r) true), h2 :- (= (Nat.beq (comp-id r) x) false)] h1)
           cs h)))
(a/theorem cpres-del [x :- Nat, cs :- (List CompRow)] (cpres cs (tbl-del comp-id x cs))
  (intros P hP h)
  (exact (tbl-all-del CompRow comp-id x P P
           (fn [r :- CompRow, h1 :- (= (P r) true), h2 :- (= (Nat.beq (comp-id r) x) false)] h1) cs h)))
(a/theorem cpres-keep [K :- (=> Nat Bool), cs :- (List CompRow)] (cpres cs (tbl-keep K comp-id cs))
  (intros P hP h)
  (exact (tbl-all-keep CompRow K comp-id P P
           (fn [r :- CompRow, h1 :- (= (P r) true), h2 :- (= (K (comp-id r)) true)] h1) cs h)))
(a/theorem cpres-resync [es :- (List EdgeRow), cs :- (List CompRow)] (cpres cs (comps-resync es cs))
  (intros P hP)
  (induction cs)
  (case [nil] (intro h) (simp only [comps-resync tbl-all]))
  (case [cons hd t ih]
    (intro h)
    (simp only [tbl-all Bool.and_eq_true] at h)
    (have a1 (= (P (comp-resync es hd)) true))
    (exact (hP (comp-resync es hd) hd (dom14-key (comp-resync es hd) hd (Eq.refl (ck14 hd))) (And.left h)))
    (simp only [comps-resync tbl-all a1 (ih (And.right h)) Bool.and_self])))
(a/theorem cpres-ins-wake [r :- CompRow, cs :- (List CompRow)]
  (=> (= (:idle r) false) (forall [P :- (=> CompRow Bool)] (=> (dcl14 P) (= (P r) true) (= (tbl-all P cs) true) (= (tbl-all P (tbl-ins r cs)) true))))
  (intros hi P hP h1 h2) (simp only [tbl-ins tbl-all h1 h2 Bool.and_self]))

;; ---- edges: same (kind, creditor, debtor)
(a/structure E14 [] (kind Nat) (cred Nat) (deb Nat))
(a/defn ek14 [e :- EdgeRow] E14 (E14.mk (:kind e) (:creditor e) (:debtor e)))
(a/defn ecl14 [P :- (=> EdgeRow Bool)] Prop
  (forall [k :- EdgeRow, e :- EdgeRow] (=> (= (ek14 k) (ek14 e)) (= (P e) true) (= (P k) true))))
(a/defn epres [es :- (List EdgeRow), es2 :- (List EdgeRow)] Prop
  (forall [P :- (=> EdgeRow Bool)] (=> (ecl14 P) (= (tbl-all P es) true) (= (tbl-all P es2) true))))

(a/theorem epres-refl [es :- (List EdgeRow)] (epres es es) (intros P hP h) (exact h))
(a/theorem epres-trans [es :- (List EdgeRow), es2 :- (List EdgeRow), es3 :- (List EdgeRow)]
  (=> (epres es es2) (epres es2 es3) (epres es es3))
  (intros h1 h2 P hP h) (exact (h2 P hP (h1 P hP h))))
(a/theorem ek14-of [e :- EdgeRow, k :- EdgeRow]
  (=> (= (:kind k) (:kind e)) (= (:creditor k) (:creditor e)) (= (:debtor k) (:debtor e)) (= (ek14 k) (ek14 e)))
  (intros h1 h2 h3) (simp only [ek14 h1 h2 h3]))
(a/theorem epres-upd [x :- Nat, f :- (=> EdgeRow EdgeRow),
                      hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                      hc :- (forall [e :- EdgeRow] (= (:creditor (f e)) (:creditor e))),
                      hd :- (forall [e :- EdgeRow] (= (:debtor (f e)) (:debtor e))), es :- (List EdgeRow)]
  (epres es (tbl-upd edge-id x f es))
  (intros P hP h)
  (exact (tbl-all-upd EdgeRow edge-id x f P P
           (fn [r :- EdgeRow, h1 :- (= (P r) true), h2 :- (= (Nat.beq (edge-id r) x) true)] (hP (f r) r (ek14-of r (f r) (hk r) (hc r) (hd r)) h1))
           (fn [r :- EdgeRow, h1 :- (= (P r) true), h2 :- (= (Nat.beq (edge-id r) x) false)] h1)
           es h)))
(a/theorem epres-del [x :- Nat, es :- (List EdgeRow)] (epres es (tbl-del edge-id x es))
  (intros P hP h)
  (exact (tbl-all-del EdgeRow edge-id x P P
           (fn [r :- EdgeRow, h1 :- (= (P r) true), h2 :- (= (Nat.beq (edge-id r) x) false)] h1) es h)))
(a/theorem epres-keep [K :- (=> Nat Bool), es :- (List EdgeRow)] (epres es (tbl-keep K edge-id es))
  (intros P hP h)
  (exact (tbl-all-keep EdgeRow K edge-id P P
           (fn [r :- EdgeRow, h1 :- (= (P r) true), h2 :- (= (K (edge-id r)) true)] h1) es h)))
(a/theorem epres-filter [p :- (=> EdgeRow Bool), es :- (List EdgeRow)] (epres es (tbl-filter p es))
  (intros P hP h) (exact (tbl-all-filter EdgeRow P p es h)))

;; ===========================================================================
;; Part B. The invariant
;; ===========================================================================

;; u below v
(a/defn prec14 [v :- Valid, u :- Valid] Bool
  (Bool.or (Nat.blt (:stamp v) (:stamp u)) (Bool.and (Nat.beq (:stamp u) (:stamp v)) (Nat.blt (:crank u) (:crank v)))))
;; entry v's obligation towards the computation row k (when k has v's debtor id)
(a/defn deb14 [n :- Nat, v :- Valid, k :- CompRow] Bool
  (Bool.or (Bool.not (Nat.beq (:id k) (:debtor v)))
           (Bool.and (Bool.or (Nat.blt (:stamp v) n) (Nat.blt (:rank k) (:crank v)))
                     (Bool.or (Bool.not (:idle k)) (tbl-all (prec14 v) (:validity k))))))
(a/defn ent14 [cs :- (List CompRow), n :- Nat, v :- Valid] Bool
  (Bool.and (Nat.ble (:stamp v) n) (tbl-all (deb14 n v) cs)))
(a/defn ivc14 [cs :- (List CompRow), n :- Nat, k :- CompRow] Bool
  (Bool.or (Bool.not (:idle k)) (tbl-all (ent14 cs n) (:validity k))))
(a/defn iv14 [cs :- (List CompRow), n :- Nat] Bool (tbl-all (ivc14 cs n) cs))

;; a dep edge on an idle computation has its debtor in xq (raw: the reactivation queue)
(a/defn dnaq14 [xq :- (List Nat), cs :- (List CompRow), e :- EdgeRow] Bool
  (Bool.or (Bool.not (Nat.beq (:kind e) ek-dep)) (Bool.or (reach-mem (:debtor e) xq) (awake cs (:debtor e)))))
;; every entry of an idle computation is below the allocator (strict window)
(a/defn stamp-lt [n :- Nat, v :- Valid] Bool (Nat.blt (:stamp v) n))
(a/defn swc14 [n :- Nat, k :- CompRow] Bool (Bool.or (Bool.not (:idle k)) (tbl-all (stamp-lt n) (:validity k))))

;; Rule R: dep edges on idle computations only within a pass (debtor in xd, creditor in xr)
(a/defn dnb14 [xd :- (List Nat), xr :- (List Nat), cs :- (List CompRow), e :- EdgeRow] Bool
  (Bool.or (Bool.not (Nat.beq (:kind e) ek-dep))
           (Bool.and (Bool.or (reach-mem (:debtor e) xd) (awake cs (:debtor e)))
                     (Bool.or (Bool.not (reach-mem (:debtor e) xd)) (reach-mem (:creditor e) xr)))))
(a/defn rgt14 [y :- Nat, r :- Nat, k :- CompRow] Bool (Bool.or (Bool.not (Nat.beq (:id k) y)) (Nat.blt r (:rank k))))
(a/defn dnu14 [n :- Nat, cs :- (List CompRow), y :- Nat, u :- Valid] Bool
  (Bool.and (Nat.beq (:stamp u) n) (tbl-all (rgt14 y (:crank u)) cs)))
(a/defn dnk14 [n :- Nat, cs :- (List CompRow), y :- Nat, d :- Nat, k :- CompRow] Bool
  (Bool.or (Bool.not (Bool.and (Nat.beq (:id k) d) (:idle k))) (tbl-all (dnu14 n cs y) (:validity k))))
(a/defn dne14 [xd :- (List Nat), n :- Nat, cs :- (List CompRow), e :- EdgeRow] Bool
  (Bool.or (Bool.not (Bool.and (Nat.beq (:kind e) ek-dep) (reach-mem (:debtor e) xd)))
           (tbl-all (dnk14 n cs (:creditor e) (:debtor e)) cs)))

;; ---- closure of the predicates under domination
(a/theorem dom14-idle [k :- CompRow, c :- CompRow]
  (=> (dom14 k c) (= (:idle k) true) (And (= (:idle c) true) (= (:validity k) (:validity c))))
  (intros hd hi) (exact ((And.right (And.right hd)) hi)))

(a/theorem dcl-deb14 [n :- Nat, v :- Valid] (dcl14 (deb14 n v))
  (intros k c hd hc)
  (have e1 := (And.left hd)) (have e2 := (And.left (And.right hd)))
  (simp only [deb14]) (rw [e1]) (rw [e2])
  (cases hb (Nat.beq (:id c) (:debtor v)))
  (case [false] (simp only [Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [deb14 hb Bool.not_true Bool.false_or Bool.and_eq_true] at hc)
    (simp only [Bool.not_true Bool.false_or Bool.and_eq_true])
    (apply And.intro) (exact (And.left hc))
    (cases hi (:idle k))
    (case [false] (simp only [Bool.not_false Bool.true_or]))
    (case [true]
      (have q := (dom14-idle k c hd hi))
      (have r := (And.right hc)) (simp only [(And.left q) Bool.not_true Bool.false_or] at r)
      (simp only [Bool.not_true Bool.false_or]) (rw [(And.right q)]) (exact r))))

(a/theorem dcl-ivc14 [cs :- (List CompRow), n :- Nat] (dcl14 (ivc14 cs n))
  (intros k c hd hc)
  (cases hi (:idle k))
  (case [false] (simp only [ivc14 hi Bool.not_false Bool.true_or]))
  (case [true]
    (have q := (dom14-idle k c hd hi))
    (simp only [ivc14 (And.left q) Bool.not_true Bool.false_or] at hc)
    (simp only [ivc14 hi Bool.not_true Bool.false_or]) (rw [(And.right q)]) (exact hc)))

(a/theorem dcl-nii [x :- Nat] (dcl14 (not-idle-if-id x))
  (intros k c hd hc)
  (cases hi (:idle k))
  (case [false] (simp only [not-idle-if-id hi Bool.not_false Bool.or_true]))
  (case [true]
    (have q := (dom14-idle k c hd hi))
    (simp only [not-idle-if-id (And.left q) Bool.not_true Bool.or_false] at hc)
    (simp only [not-idle-if-id hi Bool.not_true Bool.or_false]) (rw [(And.left hd)]) (exact hc)))

(a/theorem dcl-swc14 [n :- Nat] (dcl14 (swc14 n))
  (intros k c hd hc)
  (cases hi (:idle k))
  (case [false] (simp only [swc14 hi Bool.not_false Bool.true_or]))
  (case [true]
    (have q := (dom14-idle k c hd hi))
    (simp only [swc14 (And.left q) Bool.not_true Bool.false_or] at hc)
    (simp only [swc14 hi Bool.not_true Bool.false_or]) (rw [(And.right q)]) (exact hc)))

(a/theorem dcl-rgt14 [y :- Nat, r :- Nat] (dcl14 (rgt14 y r))
  (intros k c hd hc)
  (simp only [rgt14]) (rw [(And.left hd)]) (rw [(And.left (And.right hd))]) (exact hc))

(a/theorem awake-pres [cs :- (List CompRow), cs2 :- (List CompRow), x :- Nat]
  (=> (cpres cs cs2) (= (awake cs x) true) (= (awake cs2 x) true))
  (intros hp h) (simp only [awake] at h) (simp only [awake]) (exact (hp (not-idle-if-id x) (dcl-nii x) h)))

(a/theorem ent14-pres [cs :- (List CompRow), cs2 :- (List CompRow), n :- Nat, v :- Valid]
  (=> (cpres cs cs2) (= (ent14 cs n v) true) (= (ent14 cs2 n v) true))
  (intros hp h)
  (simp only [ent14 Bool.and_eq_true] at h)
  (simp only [ent14 Bool.and_eq_true])
  (exact (And.intro (And.left h) (hp (deb14 n v) (dcl-deb14 n v) (And.right h)))))

(a/theorem ivc14-pres [cs :- (List CompRow), cs2 :- (List CompRow), n :- Nat, k :- CompRow]
  (=> (cpres cs cs2) (= (ivc14 cs n k) true) (= (ivc14 cs2 n k) true))
  (intros hp h)
  (cases hi (:idle k))
  (case [false] (simp only [ivc14 hi Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [ivc14 hi Bool.not_true Bool.false_or] at h)
    (simp only [ivc14 hi Bool.not_true Bool.false_or])
    (exact (tbl-all-mono Valid (ent14 cs n) (ent14 cs2 n)
             (fn [v :- Valid, hv :- (= (ent14 cs n v) true)] (ent14-pres cs cs2 n v hp hv)) (:validity k) h))))

(a/theorem iv14-pres [cs :- (List CompRow), cs2 :- (List CompRow), n :- Nat]
  (=> (cpres cs cs2) (= (iv14 cs n) true) (= (iv14 cs2 n) true))
  (intros hp h)
  (simp only [iv14] at h) (simp only [iv14])
  (have h1 (= (tbl-all (ivc14 cs2 n) cs) true))
  (exact (tbl-all-mono CompRow (ivc14 cs n) (ivc14 cs2 n)
           (fn [k :- CompRow, hk :- (= (ivc14 cs n k) true)] (ivc14-pres cs cs2 n k hp hk)) cs h))
  (exact (hp (ivc14 cs2 n) (dcl-ivc14 cs2 n) h1)))

;; ---- a larger allocator
(a/theorem deb14-next [n :- Nat, m :- Nat, v :- Valid, k :- CompRow]
  (=> (<= n m) (= (deb14 n v k) true) (= (deb14 m v k) true))
  (intros hl h)
  (cases hb (Nat.beq (:id k) (:debtor v)))
  (case [false] (simp only [deb14 hb Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [deb14 hb Bool.not_true Bool.false_or Bool.and_eq_true Bool.or_eq_true] at h)
    (simp only [deb14 hb Bool.not_true Bool.false_or Bool.and_eq_true Bool.or_eq_true])
    (apply And.intro)
    (have hz := (And.left h))
    (cases hz)
    (case [inl a1] (apply Or.inl) (simp only [Nat.blt_eq] at a1) (simp only [Nat.blt_eq]) (omega))
    (case [inr a2] (exact (Or.inr a2)))
    (exact (And.right h))))
(a/theorem ent14-next [cs :- (List CompRow), n :- Nat, m :- Nat, v :- Valid]
  (=> (<= n m) (= (ent14 cs n v) true) (= (ent14 cs m v) true))
  (intros hl h)
  (simp only [ent14 Bool.and_eq_true] at h)
  (simp only [ent14 Bool.and_eq_true])
  (apply And.intro)
  (have a1 := (And.left h)) (simp only [Nat.ble_eq] at a1) (simp only [Nat.ble_eq]) (omega)
  (exact (tbl-all-mono CompRow (deb14 n v) (deb14 m v)
           (fn [k :- CompRow, hk :- (= (deb14 n v k) true)] (deb14-next n m v k hl hk)) cs (And.right h))))
(a/theorem iv14-next [cs :- (List CompRow), n :- Nat, m :- Nat]
  (=> (<= n m) (= (iv14 cs n) true) (= (iv14 cs m) true))
  (intros hl h)
  (simp only [iv14] at h) (simp only [iv14])
  (apply (tbl-all-mono CompRow (ivc14 cs n) (ivc14 cs m) _ cs h))
  (intros k hk)
  (cases hi (:idle k))
  (case [false] (simp only [ivc14 hi Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [ivc14 hi Bool.not_true Bool.false_or] at hk)
    (simp only [ivc14 hi Bool.not_true Bool.false_or])
    (exact (tbl-all-mono Valid (ent14 cs n) (ent14 cs m)
             (fn [v :- Valid, hv :- (= (ent14 cs n v) true)] (ent14-next cs n m v hl hv)) (:validity k) hk))))

;; ---- edges
(a/theorem ek14-parts [k :- EdgeRow, e :- EdgeRow]
  (=> (= (ek14 k) (ek14 e)) (And (= (:kind k) (:kind e)) (And (= (:creditor k) (:creditor e)) (= (:debtor k) (:debtor e)))))
  (intro h)
  (exact (And.intro (congrArg (fn [q :- E14] (:kind q)) h)
           (And.intro (congrArg (fn [q :- E14] (:cred q)) h) (congrArg (fn [q :- E14] (:deb q)) h)))))
(a/theorem ecl-dnaq14 [xq :- (List Nat), cs :- (List CompRow)] (ecl14 (dnaq14 xq cs))
  (intros k e he hp)
  (have p := (ek14-parts k e he))
  (simp only [dnaq14]) (rw [(And.left p)]) (rw [(And.right (And.right p))]) (exact hp))
(a/theorem ecl-dnb14 [xd :- (List Nat), xr :- (List Nat), cs :- (List CompRow)] (ecl14 (dnb14 xd xr cs))
  (intros k e he hp)
  (have p := (ek14-parts k e he))
  (simp only [dnb14]) (rw [(And.left p)]) (rw [(And.left (And.right p))]) (rw [(And.right (And.right p))]) (exact hp))
(a/theorem ecl-dne14 [xd :- (List Nat), n :- Nat, cs :- (List CompRow)] (ecl14 (dne14 xd n cs))
  (intros k e he hp)
  (have p := (ek14-parts k e he))
  (simp only [dne14]) (rw [(And.left p)]) (rw [(And.left (And.right p))]) (rw [(And.right (And.right p))]) (exact hp))
(a/theorem ecl-dep-active [cs :- (List CompRow)] (ecl14 (dep-active cs))
  (intros k e he hp)
  (have p := (ek14-parts k e he))
  (simp only [dep-active]) (rw [(And.left p)]) (rw [(And.left (And.right p))]) (exact hp))

(a/theorem dnaq14-pres [xq :- (List Nat), cs :- (List CompRow), cs2 :- (List CompRow), e :- EdgeRow]
  (=> (cpres cs cs2) (= (dnaq14 xq cs e) true) (= (dnaq14 xq cs2 e) true))
  (intros hp h)
  (cases hk (Nat.beq (:kind e) ek-dep))
  (case [false] (simp only [dnaq14 hk Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [dnaq14 hk Bool.not_true Bool.false_or Bool.or_eq_true] at h)
    (simp only [dnaq14 hk Bool.not_true Bool.false_or Bool.or_eq_true])
    (cases h)
    (case [inl a1] (exact (Or.inl a1)))
    (case [inr a2] (exact (Or.inr (awake-pres cs cs2 (:debtor e) hp a2))))))
(a/theorem dnb14-pres [xd :- (List Nat), xr :- (List Nat), cs :- (List CompRow), cs2 :- (List CompRow), e :- EdgeRow]
  (=> (cpres cs cs2) (= (dnb14 xd xr cs e) true) (= (dnb14 xd xr cs2 e) true))
  (intros hp h)
  (cases hk (Nat.beq (:kind e) ek-dep))
  (case [false] (simp only [dnb14 hk Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [dnb14 hk Bool.not_true Bool.false_or Bool.and_eq_true Bool.or_eq_true] at h)
    (simp only [dnb14 hk Bool.not_true Bool.false_or Bool.and_eq_true Bool.or_eq_true])
    (apply And.intro)
    (have hz := (And.left h))
    (cases hz)
    (case [inl a1] (exact (Or.inl a1)))
    (case [inr a2] (exact (Or.inr (awake-pres cs cs2 (:debtor e) hp a2))))
    (exact (And.right h))))
(a/theorem dep-active-pres [cs :- (List CompRow), cs2 :- (List CompRow), e :- EdgeRow]
  (=> (cpres cs cs2) (= (dep-active cs e) true) (= (dep-active cs2 e) true))
  (intros hp h)
  (cases hk (Nat.beq (:kind e) ek-dep))
  (case [false] (simp only [dep-active hk Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [dep-active hk Bool.not_true Bool.false_or] at h)
    (simp only [dep-active hk Bool.not_true Bool.false_or])
    (exact (hp (not-idle-if-id (:creditor e)) (dcl-nii (:creditor e)) h))))
(a/theorem dnu14-pres [n :- Nat, cs :- (List CompRow), cs2 :- (List CompRow), y :- Nat, u :- Valid]
  (=> (cpres cs cs2) (= (dnu14 n cs y u) true) (= (dnu14 n cs2 y u) true))
  (intros hp h)
  (simp only [dnu14 Bool.and_eq_true] at h) (simp only [dnu14 Bool.and_eq_true])
  (exact (And.intro (And.left h) (hp (rgt14 y (:crank u)) (dcl-rgt14 y (:crank u)) (And.right h)))))
(a/theorem dcl-dnk14 [n :- Nat, cs :- (List CompRow), y :- Nat, d :- Nat] (dcl14 (dnk14 n cs y d))
  (intros k c hd hc)
  (cases hi (:idle k))
  (case [false] (simp only [dnk14 hi Bool.and_false Bool.not_false Bool.true_or]))
  (case [true]
    (have q := (dom14-idle k c hd hi))
    (simp only [dnk14 (And.left q) Bool.and_true] at hc)
    (simp only [dnk14 hi Bool.and_true]) (rw [(And.left hd)]) (rw [(And.right q)]) (exact hc)))
(a/theorem dnk14-pres [n :- Nat, cs :- (List CompRow), cs2 :- (List CompRow), y :- Nat, d :- Nat, k :- CompRow]
  (=> (cpres cs cs2) (= (dnk14 n cs y d k) true) (= (dnk14 n cs2 y d k) true))
  (intros hp h)
  (cases hb (Bool.and (Nat.beq (:id k) d) (:idle k)))
  (case [false] (simp only [dnk14 hb Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [dnk14 hb Bool.not_true Bool.false_or] at h) (simp only [dnk14 hb Bool.not_true Bool.false_or])
    (exact (tbl-all-mono Valid (dnu14 n cs y) (dnu14 n cs2 y)
             (fn [u :- Valid, hu :- (= (dnu14 n cs y u) true)] (dnu14-pres n cs cs2 y u hp hu)) (:validity k) h))))
(a/theorem dne14-pres [xd :- (List Nat), n :- Nat, cs :- (List CompRow), cs2 :- (List CompRow), e :- EdgeRow]
  (=> (cpres cs cs2) (= (dne14 xd n cs e) true) (= (dne14 xd n cs2 e) true))
  (intros hp h)
  (cases hb (Bool.and (Nat.beq (:kind e) ek-dep) (reach-mem (:debtor e) xd)))
  (case [false] (simp only [dne14 hb Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [dne14 hb Bool.not_true Bool.false_or] at h) (simp only [dne14 hb Bool.not_true Bool.false_or])
    (have h1 (= (tbl-all (dnk14 n cs2 (:creditor e) (:debtor e)) cs) true))
    (exact (tbl-all-mono CompRow (dnk14 n cs (:creditor e) (:debtor e)) (dnk14 n cs2 (:creditor e) (:debtor e))
             (fn [k :- CompRow, hk :- (= (dnk14 n cs (:creditor e) (:debtor e) k) true)] (dnk14-pres n cs cs2 (:creditor e) (:debtor e) k hp hk))
             cs h))
    (exact (hp (dnk14 n cs2 (:creditor e) (:debtor e)) (dcl-dnk14 n cs2 (:creditor e) (:debtor e)) h1))))

;; ===========================================================================
;; Part C. The two bundles: vq (raw part) and vr (Rule R)
;; ===========================================================================

;; vq xq xw xs: iv14; a dep edge on an idle computation has its debtor in xq; the computations in
;; xw are awake; when xs, every entry of an idle computation is below the allocator
(a/defn vqk [xq :- (List Nat), xw :- (List Nat), xs :- Bool, cs :- (List CompRow), es :- (List EdgeRow), n :- Nat] Bool
  (Bool.and (iv14 cs n)
  (Bool.and (tbl-all (dnaq14 xq cs) es)
  (Bool.and (tbl-all (awake cs) xw) (Bool.or (Bool.not xs) (tbl-all (swc14 n) cs))))))
(a/defn vq-rest [xq :- (List Nat), xw :- (List Nat), xs :- Bool, w :- World] Bool (vqk xq xw xs (:comps w) (:edges w) (:next-id w)))
(a/defn vq [xq :- (List Nat), xw :- (List Nat), xs :- Bool, w :- World] Bool (Bool.and (inv-sample w) (vq-rest xq xw xs w)))

;; vr xd xr: iv14; a dep edge on an idle computation has its debtor in xd; a dep edge on a debtor
;; in xd has its creditor in xr and the debtor's entries (if idle) carry the allocator and a crank
;; below the creditor's rank; a dep edge's creditor is awake
(a/defn vrk [xd :- (List Nat), xr :- (List Nat), cs :- (List CompRow), es :- (List EdgeRow), n :- Nat] Bool
  (Bool.and (iv14 cs n)
  (Bool.and (tbl-all (dnb14 xd xr cs) es)
  (Bool.and (tbl-all (dne14 xd n cs) es) (tbl-all (dep-active cs) es)))))
(a/defn vr-rest [xd :- (List Nat), xr :- (List Nat), w :- World] Bool (vrk xd xr (:comps w) (:edges w) (:next-id w)))
(a/defn vr [xd :- (List Nat), xr :- (List Nat), w :- World] Bool (Bool.and (inv-sample w) (vr-rest xd xr w)))

(a/theorem vq-sample [xq :- (List Nat), xw :- (List Nat), xs :- Bool, w :- World] (=> (= (vq xq xw xs w) true) (= (inv-sample w) true))
  (intro h) (simp only [vq Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem vq-rest-of [xq :- (List Nat), xw :- (List Nat), xs :- Bool, w :- World] (=> (= (vq xq xw xs w) true) (= (vq-rest xq xw xs w) true))
  (intro h) (simp only [vq Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem vq-intro [xq :- (List Nat), xw :- (List Nat), xs :- Bool, w :- World]
  (=> (= (inv-sample w) true) (= (vq-rest xq xw xs w) true) (= (vq xq xw xs w) true))
  (intros h1 h2) (simp only [vq h1 h2 Bool.and_self]))
(a/theorem vq-parts [xq :- (List Nat), xw :- (List Nat), xs :- Bool, w :- World]
  (=> (= (vq xq xw xs w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (vq-sample xq xw xs w h))))
(a/theorem vr-sample [xd :- (List Nat), xr :- (List Nat), w :- World] (=> (= (vr xd xr w) true) (= (inv-sample w) true))
  (intro h) (simp only [vr Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem vr-rest-of [xd :- (List Nat), xr :- (List Nat), w :- World] (=> (= (vr xd xr w) true) (= (vr-rest xd xr w) true))
  (intro h) (simp only [vr Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem vr-intro [xd :- (List Nat), xr :- (List Nat), w :- World]
  (=> (= (inv-sample w) true) (= (vr-rest xd xr w) true) (= (vr xd xr w) true))
  (intros h1 h2) (simp only [vr h1 h2 Bool.and_self]))
(a/theorem vr-parts [xd :- (List Nat), xr :- (List Nat), w :- World]
  (=> (= (vr xd xr w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (vr-sample xd xr w h))))

(a/theorem vqk-parts [xq :- (List Nat), xw :- (List Nat), xs :- Bool, cs :- (List CompRow), es :- (List EdgeRow), n :- Nat]
  (=> (= (vqk xq xw xs cs es n) true)
      (And (= (iv14 cs n) true) (And (= (tbl-all (dnaq14 xq cs) es) true)
      (And (= (tbl-all (awake cs) xw) true) (= (Bool.or (Bool.not xs) (tbl-all (swc14 n) cs)) true)))))
  (intro h) (simp only [vqk Bool.and_eq_true] at h) (exact h))
(a/theorem vqk-intro [xq :- (List Nat), xw :- (List Nat), xs :- Bool, cs :- (List CompRow), es :- (List EdgeRow), n :- Nat]
  (=> (= (iv14 cs n) true) (= (tbl-all (dnaq14 xq cs) es) true) (= (tbl-all (awake cs) xw) true)
      (= (Bool.or (Bool.not xs) (tbl-all (swc14 n) cs)) true) (= (vqk xq xw xs cs es n) true))
  (intros h1 h2 h3 h4) (simp only [vqk h1 h2 h3 h4 Bool.and_self]))
(a/theorem vrk-parts [xd :- (List Nat), xr :- (List Nat), cs :- (List CompRow), es :- (List EdgeRow), n :- Nat]
  (=> (= (vrk xd xr cs es n) true)
      (And (= (iv14 cs n) true) (And (= (tbl-all (dnb14 xd xr cs) es) true)
      (And (= (tbl-all (dne14 xd n cs) es) true) (= (tbl-all (dep-active cs) es) true)))))
  (intro h) (simp only [vrk Bool.and_eq_true] at h) (exact h))
(a/theorem vrk-intro [xd :- (List Nat), xr :- (List Nat), cs :- (List CompRow), es :- (List EdgeRow), n :- Nat]
  (=> (= (iv14 cs n) true) (= (tbl-all (dnb14 xd xr cs) es) true) (= (tbl-all (dne14 xd n cs) es) true)
      (= (tbl-all (dep-active cs) es) true) (= (vrk xd xr cs es n) true))
  (intros h1 h2 h3 h4) (simp only [vrk h1 h2 h3 h4 Bool.and_self]))

;; ---- the frames
(a/theorem swc14-next [n :- Nat, m :- Nat, k :- CompRow] (=> (<= n m) (= (swc14 n k) true) (= (swc14 m k) true))
  (intros hl h)
  (cases hi (:idle k))
  (case [false] (simp only [swc14 hi Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [swc14 hi Bool.not_true Bool.false_or] at h) (simp only [swc14 hi Bool.not_true Bool.false_or])
    (apply (tbl-all-mono Valid (stamp-lt n) (stamp-lt m) _ (:validity k) h))
    (intros v hv) (simp only [stamp-lt Nat.blt_eq] at hv) (simp only [stamp-lt Nat.blt_eq]) (omega)))
(a/theorem sw-of-iv [cs :- (List CompRow), n :- Nat, m :- Nat] (=> (< n m) (= (iv14 cs n) true) (= (tbl-all (swc14 m) cs) true))
  (intros hl h)
  (simp only [iv14] at h)
  (apply (tbl-all-mono CompRow (ivc14 cs n) (swc14 m) _ cs h))
  (intros k hk)
  (cases hi (:idle k))
  (case [false] (simp only [swc14 hi Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [ivc14 hi Bool.not_true Bool.false_or] at hk) (simp only [swc14 hi Bool.not_true Bool.false_or])
    (apply (tbl-all-mono Valid (ent14 cs n) (stamp-lt m) _ (:validity k) hk))
    (intros v hv) (simp only [ent14 Bool.and_eq_true Nat.ble_eq] at hv) (simp only [stamp-lt Nat.blt_eq])
    (have z := (And.left hv)) (omega)))

(a/theorem vqk-frame [xq :- (List Nat), xw :- (List Nat), xs :- Bool, cs :- (List CompRow), es :- (List EdgeRow), n :- Nat,
                      cs2 :- (List CompRow), es2 :- (List EdgeRow), n2 :- Nat]
  (=> (cpres cs cs2) (epres es es2) (<= n n2) (= (vqk xq xw xs cs es n) true) (= (vqk xq xw xs cs2 es2 n2) true))
  (intros hc he hl h)
  (have p := (vqk-parts xq xw xs cs es n h))
  (have i1 := (iv14-next cs2 n n2 hl (iv14-pres cs cs2 n hc (And.left p))))
  (have i2a := (he (dnaq14 xq cs) (ecl-dnaq14 xq cs) (And.left (And.right p))))
  (have i2 := (tbl-all-mono EdgeRow (dnaq14 xq cs) (dnaq14 xq cs2)
                (fn [e :- EdgeRow, h1 :- (= (dnaq14 xq cs e) true)] (dnaq14-pres xq cs cs2 e hc h1)) es2 i2a))
  (have i3 := (tbl-all-mono Nat (awake cs) (awake cs2)
                (fn [y :- Nat, h1 :- (= (awake cs y) true)] (awake-pres cs cs2 y hc h1)) xw (And.left (And.right (And.right p)))))
  (have i4 (= (Bool.or (Bool.not xs) (tbl-all (swc14 n2) cs2)) true))
  (cases xs)
  (case [false] (simp only [Bool.not_false Bool.true_or]))
  (case [true]
    (have p4 := (And.right (And.right (And.right p))))
    (simp only [Bool.not_true Bool.false_or] at p4) (simp only [Bool.not_true Bool.false_or])
    (exact (tbl-all-mono CompRow (swc14 n) (swc14 n2) (fn [k :- CompRow, h1 :- (= (swc14 n k) true)] (swc14-next n n2 k hl h1))
             cs2 (hc (swc14 n) (dcl-swc14 n) p4))))
  (exact (vqk-intro xq xw xs cs2 es2 n2 i1 i2 i3 i4)))

;; an allocation: afterwards every stamp is below the allocator
(a/theorem vqk-up [xq :- (List Nat), xw :- (List Nat), xs :- Bool, cs :- (List CompRow), es :- (List EdgeRow), n :- Nat,
                   cs2 :- (List CompRow), es2 :- (List EdgeRow), n2 :- Nat]
  (=> (cpres cs cs2) (epres es es2) (< n n2) (= (vqk xq xw xs cs es n) true) (= (vqk xq xw true cs2 es2 n2) true))
  (intros hc he hl h)
  (have f := (vqk-frame xq xw xs cs es n cs2 es2 n2 hc he (Nat.le_of_lt hl) h))
  (have p := (vqk-parts xq xw xs cs2 es2 n2 f))
  (have s := (sw-of-iv cs2 n n2 hl (iv14-pres cs cs2 n hc (And.left (vqk-parts xq xw xs cs es n h)))))
  (have i4 (= (Bool.or (Bool.not true) (tbl-all (swc14 n2) cs2)) true)) (simp only [Bool.not_true Bool.false_or]) (exact s)
  (exact (vqk-intro xq xw true cs2 es2 n2 (And.left p) (And.left (And.right p)) (And.left (And.right (And.right p))) i4)))

(a/theorem vrk-frame [xd :- (List Nat), xr :- (List Nat), cs :- (List CompRow), es :- (List EdgeRow), n :- Nat,
                      cs2 :- (List CompRow), es2 :- (List EdgeRow)]
  (=> (cpres cs cs2) (epres es es2) (= (vrk xd xr cs es n) true) (= (vrk xd xr cs2 es2 n) true))
  (intros hc he h)
  (have p := (vrk-parts xd xr cs es n h))
  (have i1 := (iv14-pres cs cs2 n hc (And.left p)))
  (have i2 := (tbl-all-mono EdgeRow (dnb14 xd xr cs) (dnb14 xd xr cs2)
                (fn [e :- EdgeRow, h1 :- (= (dnb14 xd xr cs e) true)] (dnb14-pres xd xr cs cs2 e hc h1)) es2
                (he (dnb14 xd xr cs) (ecl-dnb14 xd xr cs) (And.left (And.right p)))))
  (have i3 := (tbl-all-mono EdgeRow (dne14 xd n cs) (dne14 xd n cs2)
                (fn [e :- EdgeRow, h1 :- (= (dne14 xd n cs e) true)] (dne14-pres xd n cs cs2 e hc h1)) es2
                (he (dne14 xd n cs) (ecl-dne14 xd n cs) (And.left (And.right (And.right p))))))
  (have i4 := (tbl-all-mono EdgeRow (dep-active cs) (dep-active cs2)
                (fn [e :- EdgeRow, h1 :- (= (dep-active cs e) true)] (dep-active-pres cs cs2 e hc h1)) es2
                (he (dep-active cs) (ecl-dep-active cs) (And.right (And.right (And.right p))))))
  (exact (vrk-intro xd xr cs2 es2 n i1 i2 i3 i4)))

(a/theorem vq-rest-frame [xq :- (List Nat), xw :- (List Nat), xs :- Bool, w :- World, w2 :- World]
  (=> (cpres (:comps w) (:comps w2)) (epres (:edges w) (:edges w2)) (<= (:next-id w) (:next-id w2))
      (= (vq-rest xq xw xs w) true) (= (vq-rest xq xw xs w2) true))
  (intros hc he hl h) (exact (vqk-frame xq xw xs _ _ _ _ _ _ hc he hl h)))
(a/theorem vq-rest-up [xq :- (List Nat), xw :- (List Nat), xs :- Bool, w :- World, w2 :- World]
  (=> (cpres (:comps w) (:comps w2)) (epres (:edges w) (:edges w2)) (< (:next-id w) (:next-id w2))
      (= (vq-rest xq xw xs w) true) (= (vq-rest xq xw true w2) true))
  (intros hc he hl h) (exact (vqk-up xq xw xs _ _ _ _ _ _ hc he hl h)))
(a/theorem vr-rest-frame [xd :- (List Nat), xr :- (List Nat), w :- World, w2 :- World]
  (=> (cpres (:comps w) (:comps w2)) (epres (:edges w) (:edges w2)) (= (:next-id w2) (:next-id w))
      (= (vr-rest xd xr w) true) (= (vr-rest xd xr w2) true))
  (intros hc he hn h)
  (simp only [vr-rest] at h) (simp only [vr-rest]) (rw [hn])
  (exact (vrk-frame xd xr _ _ _ _ _ hc he h)))

;; ===========================================================================
;; Part D. The primitive edits: w2 dominated by w with the same allocator (wdom)
;; ===========================================================================

(a/defn wdom [w :- World, w2 :- World] Prop
  (And (cpres (:comps w) (:comps w2)) (And (epres (:edges w) (:edges w2)) (= (:next-id w2) (:next-id w)))))
(a/theorem wdom-refl [w :- World] (wdom w w)
  (exact (And.intro (cpres-refl (:comps w)) (And.intro (epres-refl (:edges w)) (rfl)))))
(a/theorem wdom-trans [w :- World, w2 :- World, w3 :- World] (=> (wdom w w2) (wdom w2 w3) (wdom w w3))
  (intros h1 h2)
  (exact (And.intro (cpres-trans _ _ _ (And.left h1) (And.left h2))
           (And.intro (epres-trans _ _ _ (And.left (And.right h1)) (And.left (And.right h2)))
                      (Eq.trans (And.right (And.right h2)) (And.right (And.right h1)))))))
(a/theorem vq-rest-wd [xq :- (List Nat), xw :- (List Nat), xs :- Bool, w :- World, w2 :- World]
  (=> (wdom w w2) (= (vq-rest xq xw xs w) true) (= (vq-rest xq xw xs w2) true))
  (intros hd h)
  (exact (vq-rest-frame xq xw xs w w2 (And.left hd) (And.left (And.right hd))
           (Nat.le_of_eq (Eq.symm (And.right (And.right hd)))) h)))
(a/theorem vr-rest-wd [xd :- (List Nat), xr :- (List Nat), w :- World, w2 :- World]
  (=> (wdom w w2) (= (vr-rest xd xr w) true) (= (vr-rest xd xr w2) true))
  (intros hd h) (exact (vr-rest-frame xd xr w w2 (And.left hd) (And.left (And.right hd)) (And.right (And.right hd)) h)))

(a/theorem wdom-comp-upd [w :- World, x :- Nat, f :- (=> CompRow CompRow), hd :- (forall [c :- CompRow] (dom14 (f c) c))]
  (wdom w (comp-upd w x f))
  (exact (And.intro (cpres-upd x f hd (:comps w)) (And.intro (epres-refl (:edges w)) (rfl)))))
(a/theorem wdom-comp-key [w :- World, x :- Nat, f :- (=> CompRow CompRow), hk :- (forall [c :- CompRow] (= (ck14 (f c)) (ck14 c)))]
  (wdom w (comp-upd w x f))
  (exact (wdom-comp-upd w x f (fn [c :- CompRow] (dom14-key (f c) c (hk c))))))
(a/theorem wdom-edge-upd [w :- World, x :- Nat, f :- (=> EdgeRow EdgeRow),
                          hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                          hc :- (forall [e :- EdgeRow] (= (:creditor (f e)) (:creditor e))),
                          hd :- (forall [e :- EdgeRow] (= (:debtor (f e)) (:debtor e)))]
  (wdom w (edge-upd w x f))
  (exact (And.intro (cpres-refl (:comps w)) (And.intro (epres-upd x f hk hc hd (:edges w)) (rfl)))))
(a/theorem wdom-edge-del [w :- World, x :- Nat] (wdom w (edge-del w x))
  (exact (And.intro (cpres-refl (:comps w)) (And.intro (epres-del x (:edges w)) (rfl)))))
(a/theorem wdom-comp-del [w :- World, x :- Nat] (wdom w (comp-del w x))
  (exact (And.intro (cpres-del x (:comps w)) (And.intro (epres-refl (:edges w)) (rfl)))))
(a/theorem wdom-filter-world [w :- World, K :- (=> Nat Bool)] (wdom w (filter-world K w))
  (exact (And.intro (cpres-keep K (:comps w)) (And.intro (epres-keep K (:edges w)) (rfl)))))
(a/theorem wdom-drop-edges [w :- World, p :- (=> EdgeRow Bool)] (wdom w (drop-edges w p))
  (exact (And.intro (cpres-resync (tbl-filter p (:edges w)) (:comps w)) (And.intro (epres-filter p (:edges w)) (rfl)))))
(a/theorem wdom-drop-cred [w :- World, a :- Nat] (wdom w (drop-cred-edges w a))
  (exact (And.intro (cpres-upd a (comp-set-pending 0) (fn [c :- CompRow] (dom14-key _ c (Eq.refl (ck14 c)))) (:comps w))
           (And.intro (epres-filter (cred-ne a) (:edges w)) (rfl)))))
(a/theorem wdom-drop-act [w :- World, a :- Nat] (wdom w (drop-act w a)) (exact (wdom-drop-cred w a)))
(a/theorem wdom-mark-edge [w :- World, x :- Nat] (wdom w (mark-edge w x))
  (cases hf (edge-find w x)) (case' [some e]) (case' [none])
  (simp only [mark-edge hf]) (exact (wdom-refl w))
  (cases hm (:marked e))
  (simp only [mark-edge hf hm])
  (exact (wdom-trans w (edge-upd w x (edge-set-marked true)) (comp-upd (edge-upd w x (edge-set-marked true)) (:creditor e) comp-inc-pending)
           (wdom-edge-upd w x (edge-set-marked true) (fn [q :- EdgeRow] (Eq.refl (:kind q))) (fn [q :- EdgeRow] (Eq.refl (:creditor q))) (fn [q :- EdgeRow] (Eq.refl (:debtor q))))
           (wdom-comp-key (edge-upd w x (edge-set-marked true)) (:creditor e) comp-inc-pending (fn [c :- CompRow] (Eq.refl (ck14 c))))))
  (simp only [mark-edge hf hm]) (exact (wdom-refl w)))
(a/theorem wdom-unmark-edge [w :- World, x :- Nat] (wdom w (unmark-edge w x))
  (cases hf (edge-find w x)) (case' [some e]) (case' [none])
  (simp only [unmark-edge hf]) (exact (wdom-refl w))
  (cases hm (:marked e))
  (simp only [unmark-edge hf hm]) (exact (wdom-refl w))
  (simp only [unmark-edge hf hm])
  (exact (wdom-trans w (edge-upd w x (edge-set-marked false)) (comp-upd (edge-upd w x (edge-set-marked false)) (:creditor e) comp-dec-pending)
           (wdom-edge-upd w x (edge-set-marked false) (fn [q :- EdgeRow] (Eq.refl (:kind q))) (fn [q :- EdgeRow] (Eq.refl (:creditor q))) (fn [q :- EdgeRow] (Eq.refl (:debtor q))))
           (wdom-comp-key (edge-upd w x (edge-set-marked false)) (:creditor e) comp-dec-pending (fn [c :- CompRow] (Eq.refl (ck14 c)))))))
(a/theorem wdom-remove-edge [w :- World, x :- Nat] (wdom w (remove-edge w x))
  (cases hf (edge-find w x)) (case' [some e]) (case' [none])
  (simp only [remove-edge hf]) (exact (wdom-refl w))
  (cases hm (:marked e))
  (simp only [remove-edge hf hm]) (exact (wdom-edge-del w x))
  (simp only [remove-edge hf hm])
  (exact (wdom-trans w (edge-del w x) (comp-upd (edge-del w x) (:creditor e) comp-dec-pending) (wdom-edge-del w x)
           (wdom-comp-key (edge-del w x) (:creditor e) comp-dec-pending (fn [c :- CompRow] (Eq.refl (ck14 c)))))))

;; ---- vq: computation edits, insertions
(a/theorem vq-comp-wake [xq :- (List Nat), xw :- (List Nat), xs :- Bool, w :- World, x :- Nat, f :- (=> CompRow CompRow),
                         hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                         hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                         hw :- (forall [c :- CompRow] (dom14 (f c) c))]
  (=> (= (vq xq xw xs w) true) (= (vq xq xw xs (comp-upd w x f)) true))
  (intro h)
  (exact (vq-intro xq xw xs _ (inv-comp-upd w x f hid hp (vq-sample xq xw xs w h))
           (vq-rest-wd xq xw xs w (comp-upd w x f) (wdom-comp-upd w x f hw) (vq-rest-of xq xw xs w h)))))
(a/theorem vq-comp-upd [xq :- (List Nat), xw :- (List Nat), xs :- Bool, w :- World, x :- Nat, f :- (=> CompRow CompRow),
                        hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                        hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                        hk :- (forall [c :- CompRow] (= (ck14 (f c)) (ck14 c)))]
  (=> (= (vq xq xw xs w) true) (= (vq xq xw xs (comp-upd w x f)) true))
  (intro h) (exact (vq-comp-wake xq xw xs w x f hid hp (fn [c :- CompRow] (dom14-key (f c) c (hk c))) h)))

(a/theorem vqk-cons-edge [xq :- (List Nat), xw :- (List Nat), xs :- Bool, cs :- (List CompRow), es :- (List EdgeRow), n :- Nat, e :- EdgeRow]
  (=> (= (dnaq14 xq cs e) true) (= (vqk xq xw xs cs es n) true) (= (vqk xq xw xs cs (List.cons EdgeRow e es) n) true))
  (intros he h)
  (have p := (vqk-parts xq xw xs cs es n h))
  (have d (= (tbl-all (dnaq14 xq cs) (List.cons EdgeRow e es)) true)) (simp only [tbl-all he (And.left (And.right p)) Bool.and_self])
  (exact (vqk-intro xq xw xs cs _ n (And.left p) d (And.left (And.right (And.right p))) (And.right (And.right (And.right p))))))

(a/theorem vq-insert-edge-fresh [xq :- (List Nat), xw :- (List Nat), xs :- Bool, w :- World, e :- EdgeRow,
]
  (=> (= (edge-ok-in w e) true) (= (vq xq xw xs w) true) (= (dnaq14 xq (:comps w) e) true) (= (vq xq xw xs (insert-edge-fresh w e)) true))
  (intros he h hn)
  (have r0 := (vqk-frame xq xw xs (:comps w) (:edges w) (:next-id w) (:comps w) (:edges w) (+ (:next-id w) 1)
                (cpres-refl (:comps w)) (epres-refl (:edges w)) (Nat.le_succ (:next-id w)) (vq-rest-of xq xw xs w h)))
  (have hn2 (= (dnaq14 xq (:comps w) (edge-set-marked false (edge-set-id (:next-id w) e))) true)) (exact hn)
  (have r (= (vq-rest xq xw xs (insert-edge-fresh w e)) true))
  (exact (vqk-cons-edge xq xw xs _ _ _ _ hn2 r0))
  (exact (vq-intro xq xw xs _ (insert-edge-fresh-inv-sample w e he (vq-sample xq xw xs w h)) r)))
(a/theorem vq-insert-edge-checked [xq :- (List Nat), xw :- (List Nat), xs :- Bool, w :- World, e :- EdgeRow,
]
  (=> (= (vq xq xw xs w) true) (= (dnaq14 xq (:comps w) e) true) (= (vq xq xw xs (insert-edge-checked w e)) true))
  (intros h hn)
  (cases hk (edge-ok-in w e))
  (simp only [insert-edge-checked hk]) (exact h)
  (simp only [insert-edge-checked hk]) (exact (vq-insert-edge-fresh xq xw xs w e hk h hn)))

;; a new computation (T3) is not idle
(a/theorem vqk-ins-wake [xq :- (List Nat), xw :- (List Nat), xs :- Bool, cs :- (List CompRow), es :- (List EdgeRow), n :- Nat, r :- CompRow]
  (=> (= (:idle r) false) (= (vqk xq xw xs cs es n) true) (= (vqk xq xw xs (List.cons CompRow r cs) es (+ n 1)) true))
  (intros hi h)
  (have p := (vqk-parts xq xw xs cs es n h))
  (have hr1 (= (ivc14 (List.cons CompRow r cs) (+ n 1) r) true)) (simp only [ivc14 hi Bool.not_false Bool.true_or])
  (have dr (forall [v :- Valid] (=> (= (Nat.ble (:stamp v) n) true) (= (deb14 (+ n 1) v r) true))))
  (intros v hv)
  (simp only [Nat.ble_eq] at hv)
  (have lt (= (Nat.blt (:stamp v) (+ n 1)) true)) (simp only [Nat.blt_eq]) (omega)
  (simp only [deb14 lt hi Bool.true_or Bool.not_false Bool.and_self Bool.or_true])
  (have hcs (= (tbl-all (ivc14 (List.cons CompRow r cs) (+ n 1)) cs) true))
  (apply (tbl-all-mono CompRow (ivc14 cs n) _ _ cs (And.left p)))
  (intros k hk)
  (cases hik (:idle k))
  (case [false] (simp only [ivc14 hik Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [ivc14 hik Bool.not_true Bool.false_or] at hk) (simp only [ivc14 hik Bool.not_true Bool.false_or])
    (apply (tbl-all-mono Valid (ent14 cs n) _ _ (:validity k) hk))
    (intros v hv)
    (simp only [ent14 Bool.and_eq_true] at hv)
    (simp only [ent14 tbl-all (dr v (And.left hv)) Bool.true_and Bool.and_eq_true])
    (apply And.intro)
    (have z := (And.left hv)) (simp only [Nat.ble_eq] at z) (simp only [Nat.ble_eq]) (omega)
    (exact (tbl-all-mono CompRow (deb14 n v) (deb14 (+ n 1) v)
             (fn [q :- CompRow, hq :- (= (deb14 n v q) true)] (deb14-next n (+ n 1) v q (Nat.le_succ n) hq)) cs (And.right hv))))
  (have i1 (= (iv14 (List.cons CompRow r cs) (+ n 1)) true)) (simp only [iv14 tbl-all hr1 hcs Bool.and_self])
  (have nr (forall [d :- Nat] (= (not-idle-if-id d r) true))) (intro d) (simp only [not-idle-if-id hi Bool.not_false Bool.or_true])
  (have aw (forall [d :- Nat] (=> (= (awake cs d) true) (= (awake (List.cons CompRow r cs) d) true))))
  (intros d hd) (simp only [awake tbl-all (nr d) Bool.true_and]) (simp only [awake] at hd) (exact hd)
  (have i2 (= (tbl-all (dnaq14 xq (List.cons CompRow r cs)) es) true))
  (apply (tbl-all-mono EdgeRow (dnaq14 xq cs) (dnaq14 xq (List.cons CompRow r cs)) _ es (And.left (And.right p))))
  (intros e he)
  (cases hk (Nat.beq (:kind e) ek-dep))
  (case [false] (simp only [dnaq14 hk Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [dnaq14 hk Bool.not_true Bool.false_or Bool.or_eq_true] at he) (simp only [dnaq14 hk Bool.not_true Bool.false_or Bool.or_eq_true])
    (cases he) (case [inl a1] (exact (Or.inl a1))) (case [inr a2] (exact (Or.inr (aw (:debtor e) a2)))))
  (have i3 := (tbl-all-mono Nat (awake cs) (awake (List.cons CompRow r cs)) aw xw (And.left (And.right (And.right p)))))
  (have i4 (= (Bool.or (Bool.not xs) (tbl-all (swc14 (+ n 1)) (List.cons CompRow r cs))) true))
  (cases xs)
  (case [false] (simp only [Bool.not_false Bool.true_or]))
  (case [true]
    (have p4 := (And.right (And.right (And.right p)))) (simp only [Bool.not_true Bool.false_or] at p4)
    (have s1 (= (swc14 (+ n 1) r) true)) (simp only [swc14 hi Bool.not_false Bool.true_or])
    (simp only [Bool.not_true Bool.false_or tbl-all s1 Bool.true_and])
    (exact (tbl-all-mono CompRow (swc14 n) (swc14 (+ n 1)) (fn [k :- CompRow, h1 :- (= (swc14 n k) true)] (swc14-next n (+ n 1) k (Nat.le_succ n) h1)) cs p4)))
  (exact (vqk-intro xq xw xs _ es _ i1 i2 i3 i4)))
(a/theorem vq-comp-ins-fresh [xq :- (List Nat), xw :- (List Nat), xs :- Bool, w :- World, r :- CompRow, hni :- (= (:idle r) false)]
  (=> (= (comp-id r) (:next-id w)) (= (:pending r) (marked-in (:id r) (:edges w)))
      (= (vq xq xw xs w) true) (= (vq xq xw xs (bump (comp-ins w r))) true))
  (intros h1 h2 h)
  (have r1 (= (vq-rest xq xw xs (bump (comp-ins w r))) true))
  (exact (vqk-ins-wake xq xw xs _ _ _ r hni (vq-rest-of xq xw xs w h)))
  (exact (vq-intro xq xw xs _ (inv-comp-ins-fresh w r h1 h2 (vq-sample xq xw xs w h)) r1)))

;; waking rows
(a/theorem comp-start-row-dom14 [rid :- Nat, c :- CompRow] (dom14 (comp-start-row rid c) c) (apply dom14-wake) (rfl) (rfl) (rfl))
(a/theorem comp-replace-row-dom14 [i :- (List Nat), b :- Nat, c :- CompRow] (dom14 (comp-replace-row i b c) c) (apply dom14-wake) (rfl) (rfl) (rfl))
(a/theorem comp-demand-row-dom14 [c :- CompRow] (dom14 (comp-demand-row c) c) (apply dom14-wake) (rfl) (rfl) (rfl))
(a/theorem comp-react-row-dom14 [c :- CompRow] (dom14 (comp-react-row c) c) (apply dom14-wake) (rfl) (rfl) (rfl))

;; ===========================================================================
;; Part E. The vq copy (raw part)
;; ===========================================================================

(def VQ (mk-bundle 'vq '[zq9 :- (List Nat), zw9 :- (List Nat), zs9 :- Bool] "vq-"
          {'inv-comp-upd ['(fn [c :- CompRow] (Eq.refl (ck14 c))) 5]
           'insert-edge-fresh-inv-sample ['(Eq.refl true) 4]
           'inv-insert-edge-checked ['(Eq.refl true) 3]
           'inv-comp-ins-fresh ['(Eq.refl false) 2]}))
(swap! (:renames VQ) assoc 'inv-parts 'vq-parts 'inv-comp-upd 'vq-comp-upd 'insert-edge-fresh-inv-sample 'vq-insert-edge-fresh
       'inv-insert-edge-checked 'vq-insert-edge-checked 'inv-comp-ins-fresh 'vq-comp-ins-fresh)
(doseq [o '[inv-scope-upd inv-pub-upd inv-source-upd inv-resource-upd inv-cleanup-upd inv-cleanup-del inv-set-pins
            inv-resource-del inv-scope-del inv-cleanup-ins inv-act-upd inv-task-upd inv-run-upd inv-run-del]]
  (prim! VQ o nil))
(doseq [[o t] '[[inv-source-ins-fresh source-ins] [inv-resource-ins-fresh resource-ins] [inv-scope-ins-fresh scope-ins]
                [inv-act-ins-fresh act-ins] [inv-task-ins-fresh task-ins] [inv-run-ins-fresh run-ins]]]
  (prim! VQ o (list 'vq-rest-frame 'zq9 'zw9 'zs9 'w (list 'bump (list t 'w 'r)) '(cpres-refl (:comps w)) '(epres-refl (:edges w))
                    '(Nat.le_succ (:next-id w)) 'R)))
(prim! VQ 'inv-bump '(vq-rest-frame zq9 zw9 zs9 w (bump w) (cpres-refl (:comps w)) (epres-refl (:edges w)) (Nat.le_succ (:next-id w)) R))
(prim! VQ 'inv-edge-upd '(vq-rest-wd zq9 zw9 zs9 w (edge-upd w x f) (wdom-edge-upd w x f hk hc hd) R))
(prim! VQ 'inv-remove-edge '(vq-rest-wd zq9 zw9 zs9 w (remove-edge w x) (wdom-remove-edge w x) R))
(prim! VQ 'mark-edge-inv-sample '(vq-rest-wd zq9 zw9 zs9 w (mark-edge w x) (wdom-mark-edge w x) R))
(prim! VQ 'unmark-edge-inv-sample '(vq-rest-wd zq9 zw9 zs9 w (unmark-edge w x) (wdom-unmark-edge w x) R))
(prim! VQ 'inv-drop-cred '(vq-rest-wd zq9 zw9 zs9 w (drop-cred-edges w a) (wdom-drop-cred w a) R))
(prim! VQ 'inv-drop-act '(vq-rest-wd zq9 zw9 zs9 w (drop-act w a) (wdom-drop-act w a) R))
(prim! VQ 'inv-drop-edges '(vq-rest-wd zq9 zw9 zs9 w (drop-edges w p) (wdom-drop-edges w p) R))
(prim! VQ 'inv-comp-del-unref '(vq-rest-wd zq9 zw9 zs9 w (comp-del w x) (wdom-comp-del w x) R))
(prim! VQ 'inv-filter-world '(vq-rest-wd zq9 zw9 zs9 w (filter-world K w) (wdom-filter-world w K) R))

;; the source patch: an inv-comp-upd with a waking row goes through vq-comp-wake
(def ^:private wake-rows '#{comp-start-row comp-replace-row comp-demand-row comp-react-row})
(defn- fhead [f] (if (seq? f) (first f) f))
(defn wake-patch [lemma params]
  (fn [form]
    (subst-forms (fn [y] (and (seq? y) (= 'inv-comp-upd (first y)) (>= (count y) 6) (contains? wake-rows (fhead (nth y 3)))))
                 (fn [[_ w x f hid hp & more]]
                   (apply list lemma (concat params [w x f hid hp
                                                     (list 'fn '[c :- CompRow]
                                                           (if (seq? f) (apply list (symbol (str (first f) "-dom14")) (concat (rest f) ['c]))
                                                               (list (symbol (str f "-dom14")) 'c)))]
                                             more)))
                 form)))
(doseq [[n _] @@#'spindel.v2.lit/source-theorems] (patch! VQ n (wake-patch 'vq-comp-wake '[zq9 zw9 zs9])))

;; ===========================================================================
;; Part F. Rank changes in the strict window (the I12 raise of T6 and reactivation)
;; ===========================================================================

(a/defn domr14 [k :- CompRow, c :- CompRow] Prop
  (And (= (:id k) (:id c)) (=> (= (:idle k) true) (And (= (:idle c) true) (= (:validity k) (:validity c))))))
(a/defn dclr14 [P :- (=> CompRow Bool)] Prop
  (forall [k :- CompRow, c :- CompRow] (=> (domr14 k c) (= (P c) true) (= (P k) true))))
(a/defn cpresr [cs :- (List CompRow), cs2 :- (List CompRow)] Prop
  (forall [P :- (=> CompRow Bool)] (=> (dclr14 P) (= (tbl-all P cs) true) (= (tbl-all P cs2) true))))
(a/theorem cpresr-upd [x :- Nat, f :- (=> CompRow CompRow), hd :- (forall [c :- CompRow] (domr14 (f c) c)), cs :- (List CompRow)]
  (cpresr cs (tbl-upd comp-id x f cs))
  (intros P hP h)
  (exact (tbl-all-upd CompRow comp-id x f P P
           (fn [r :- CompRow, h1 :- (= (P r) true), h2 :- (= (Nat.beq (comp-id r) x) true)] (hP (f r) r (hd r) h1))
           (fn [r :- CompRow, h1 :- (= (P r) true), h2 :- (= (Nat.beq (comp-id r) x) false)] h1)
           cs h)))
(a/theorem set-rank-domr [m :- Nat, c :- CompRow] (domr14 (comp-set-rank m c) c)
  (apply And.intro) (rfl) (intro hi) (exact (And.intro hi (rfl))))

;; the strict invariant: every entry below the allocator, no rank condition
(a/defn debs14 [v :- Valid, k :- CompRow] Bool
  (Bool.or (Bool.not (Nat.beq (:id k) (:debtor v))) (Bool.or (Bool.not (:idle k)) (tbl-all (prec14 v) (:validity k)))))
(a/defn ents14 [cs :- (List CompRow), n :- Nat, v :- Valid] Bool (Bool.and (Nat.blt (:stamp v) n) (tbl-all (debs14 v) cs)))
(a/defn ivcs14 [cs :- (List CompRow), n :- Nat, k :- CompRow] Bool (Bool.or (Bool.not (:idle k)) (tbl-all (ents14 cs n) (:validity k))))
(a/defn ivs14 [cs :- (List CompRow), n :- Nat] Bool (tbl-all (ivcs14 cs n) cs))

(a/theorem dclr-debs14 [v :- Valid] (dclr14 (debs14 v))
  (intros k c hd hc)
  (cases hi (:idle k))
  (case [false] (simp only [debs14 hi Bool.not_false Bool.true_or Bool.or_true]))
  (case [true]
    (have q := ((And.right hd) hi))
    (simp only [debs14 (And.left q) Bool.not_true Bool.false_or] at hc)
    (simp only [debs14 hi Bool.not_true Bool.false_or]) (rw [(And.left hd)]) (rw [(And.right q)]) (exact hc)))
(a/theorem dclr-ivcs14 [cs :- (List CompRow), n :- Nat] (dclr14 (ivcs14 cs n))
  (intros k c hd hc)
  (cases hi (:idle k))
  (case [false] (simp only [ivcs14 hi Bool.not_false Bool.true_or]))
  (case [true]
    (have q := ((And.right hd) hi))
    (simp only [ivcs14 (And.left q) Bool.not_true Bool.false_or] at hc)
    (simp only [ivcs14 hi Bool.not_true Bool.false_or]) (rw [(And.right q)]) (exact hc)))
(a/theorem dclr-nii [x :- Nat] (dclr14 (not-idle-if-id x))
  (intros k c hd hc)
  (cases hi (:idle k))
  (case [false] (simp only [not-idle-if-id hi Bool.not_false Bool.or_true]))
  (case [true]
    (have q := ((And.right hd) hi))
    (simp only [not-idle-if-id (And.left q) Bool.not_true Bool.or_false] at hc)
    (simp only [not-idle-if-id hi Bool.not_true Bool.or_false]) (rw [(And.left hd)]) (exact hc)))
(a/theorem dclr-swc14 [n :- Nat] (dclr14 (swc14 n))
  (intros k c hd hc)
  (cases hi (:idle k))
  (case [false] (simp only [swc14 hi Bool.not_false Bool.true_or]))
  (case [true]
    (have q := ((And.right hd) hi))
    (simp only [swc14 (And.left q) Bool.not_true Bool.false_or] at hc)
    (simp only [swc14 hi Bool.not_true Bool.false_or]) (rw [(And.right q)]) (exact hc)))

(a/theorem ivs14-pres [cs :- (List CompRow), cs2 :- (List CompRow), n :- Nat]
  (=> (cpresr cs cs2) (= (ivs14 cs n) true) (= (ivs14 cs2 n) true))
  (intros hp h)
  (simp only [ivs14] at h) (simp only [ivs14])
  (have h1 (= (tbl-all (ivcs14 cs2 n) cs) true))
  (apply (tbl-all-mono CompRow (ivcs14 cs n) (ivcs14 cs2 n) _ cs h))
  (intros k hk)
  (cases hi (:idle k))
  (case [false] (simp only [ivcs14 hi Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [ivcs14 hi Bool.not_true Bool.false_or] at hk) (simp only [ivcs14 hi Bool.not_true Bool.false_or])
    (apply (tbl-all-mono Valid (ents14 cs n) (ents14 cs2 n) _ (:validity k) hk))
    (intros v hv)
    (simp only [ents14 Bool.and_eq_true] at hv) (simp only [ents14 Bool.and_eq_true])
    (exact (And.intro (And.left hv) (hp (debs14 v) (dclr-debs14 v) (And.right hv)))))
  (exact (hp (ivcs14 cs2 n) (dclr-ivcs14 cs2 n) h1)))

(a/theorem ivs-of-iv [cs :- (List CompRow), n :- Nat]
  (=> (= (iv14 cs n) true) (= (tbl-all (swc14 n) cs) true) (= (ivs14 cs n) true))
  (intros h hs)
  (simp only [iv14] at h) (simp only [ivs14])
  (apply (tbl-all-mono2 CompRow (ivc14 cs n) (swc14 n) (ivcs14 cs n) _ cs h hs))
  (intros k h1 h2)
  (cases hi (:idle k))
  (case [false] (simp only [ivcs14 hi Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [ivc14 hi Bool.not_true Bool.false_or] at h1) (simp only [swc14 hi Bool.not_true Bool.false_or] at h2)
    (simp only [ivcs14 hi Bool.not_true Bool.false_or])
    (apply (tbl-all-mono2 Valid (ent14 cs n) (stamp-lt n) (ents14 cs n) _ (:validity k) h1 h2))
    (intros v a1 a2)
    (simp only [ent14 Bool.and_eq_true] at a1) (simp only [stamp-lt] at a2)
    (simp only [ents14 a2 Bool.true_and])
    (apply (tbl-all-mono CompRow (deb14 n v) (debs14 v) _ cs (And.right a1)))
    (intros q hq)
    (cases hb (Nat.beq (:id q) (:debtor v)))
    (case [false] (simp only [debs14 hb Bool.not_false Bool.true_or]))
    (case [true]
      (simp only [deb14 hb Bool.not_true Bool.false_or Bool.and_eq_true] at hq)
      (simp only [debs14 hb Bool.not_true Bool.false_or]) (exact (And.right hq)))))

(a/theorem iv-of-ivs [cs :- (List CompRow), n :- Nat]
  (=> (= (ivs14 cs n) true) (And (= (iv14 cs n) true) (= (tbl-all (swc14 n) cs) true)))
  (intro h)
  (simp only [ivs14] at h)
  (apply And.intro)
  (simp only [iv14])
  (apply (tbl-all-mono CompRow (ivcs14 cs n) (ivc14 cs n) _ cs h))
  (intros k hk)
  (cases hi (:idle k))
  (case [false] (simp only [ivc14 hi Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [ivcs14 hi Bool.not_true Bool.false_or] at hk) (simp only [ivc14 hi Bool.not_true Bool.false_or])
    (apply (tbl-all-mono Valid (ents14 cs n) (ent14 cs n) _ (:validity k) hk))
    (intros v hv)
    (simp only [ents14 Bool.and_eq_true] at hv)
    (have lt := (And.left hv))
    (simp only [ent14 Bool.and_eq_true])
    (apply And.intro)
    (simp only [Nat.blt_eq] at lt) (simp only [Nat.ble_eq]) (omega)
    (apply (tbl-all-mono CompRow (debs14 v) (deb14 n v) _ cs (And.right hv)))
    (intros q hq)
    (cases hb (Nat.beq (:id q) (:debtor v)))
    (case [false] (simp only [deb14 hb Bool.not_false Bool.true_or]))
    (case [true]
      (simp only [debs14 hb Bool.not_true Bool.false_or] at hq)
      (simp only [deb14 hb lt hq Bool.not_true Bool.false_or Bool.true_or Bool.true_and])))
  (apply (tbl-all-mono CompRow (ivcs14 cs n) (swc14 n) _ cs h))
  (intros k hk)
  (cases hi (:idle k))
  (case [false] (simp only [swc14 hi Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [ivcs14 hi Bool.not_true Bool.false_or] at hk) (simp only [swc14 hi Bool.not_true Bool.false_or])
    (apply (tbl-all-mono Valid (ents14 cs n) (stamp-lt n) _ (:validity k) hk))
    (intros v hv) (simp only [ents14 Bool.and_eq_true] at hv) (simp only [stamp-lt]) (exact (And.left hv))))

(a/theorem vqk-r-frame [xq :- (List Nat), xw :- (List Nat), cs :- (List CompRow), es :- (List EdgeRow), n :- Nat, cs2 :- (List CompRow)]
  (=> (cpresr cs cs2) (= (vqk xq xw true cs es n) true) (= (vqk xq xw true cs2 es n) true))
  (intros hc h)
  (have p := (vqk-parts xq xw true cs es n h))
  (have p4 := (And.right (And.right (And.right p)))) (simp only [Bool.not_true Bool.false_or] at p4)
  (have v2 := (iv-of-ivs cs2 n (ivs14-pres cs cs2 n hc (ivs-of-iv cs n (And.left p) p4))))
  (have aw (forall [y :- Nat] (=> (= (awake cs y) true) (= (awake cs2 y) true))))
  (intros y hy) (simp only [awake] at hy) (simp only [awake]) (exact (hc (not-idle-if-id y) (dclr-nii y) hy))
  (have i2 (= (tbl-all (dnaq14 xq cs2) es) true))
  (apply (tbl-all-mono EdgeRow (dnaq14 xq cs) (dnaq14 xq cs2) _ es (And.left (And.right p))))
  (intros e he)
  (cases hk (Nat.beq (:kind e) ek-dep))
  (case [false] (simp only [dnaq14 hk Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [dnaq14 hk Bool.not_true Bool.false_or Bool.or_eq_true] at he) (simp only [dnaq14 hk Bool.not_true Bool.false_or Bool.or_eq_true])
    (cases he) (case [inl a1] (exact (Or.inl a1))) (case [inr a2] (exact (Or.inr (aw (:debtor e) a2)))))
  (have i3 := (tbl-all-mono Nat (awake cs) (awake cs2) aw xw (And.left (And.right (And.right p)))))
  (have i4 (= (Bool.or (Bool.not true) (tbl-all (swc14 n) cs2)) true)) (simp only [Bool.not_true Bool.false_or]) (exact (And.right v2))
  (exact (vqk-intro xq xw true cs2 es n (And.left v2) i2 i3 i4)))

(a/theorem vq-set-rank [xq :- (List Nat), xw :- (List Nat), w :- World, y :- Nat, m :- Nat]
  (=> (= (vq xq xw true w) true) (= (vq xq xw true (comp-upd w y (comp-set-rank m))) true))
  (intro h)
  (have r (= (vq-rest xq xw true (comp-upd w y (comp-set-rank m))) true))
  (exact (vqk-r-frame xq xw (:comps w) (:edges w) (:next-id w) _ (cpresr-upd y (comp-set-rank m) (set-rank-domr m) (:comps w)) (vq-rest-of xq xw true w h)))
  (exact (vq-intro xq xw true _ (inv-comp-upd w y (comp-set-rank m) (comp-set-rank-id m) (comp-set-rank-pending m) (vq-sample xq xw true w h)) r)))

(a/theorem vq-raise-loop [xq :- (List Nat), xw :- (List Nat), fuel :- (List Nat)]
  (forall [d :- Nat, w :- World, todo :- (List RJ)]
    (=> (= (vq xq xw true w) true) (= (vq xq xw true (:world (raise-loop fuel d w todo))) true)))
  (induction fuel)
  (case [nil] (intros d w todo h) (cases todo) (all_goals (simp only [raise-loop])) (all_goals (exact h)))
  (case [cons u f ih]
    (intros d w todo h)
    (cases todo)
    (case [nil] (simp only [raise-loop]) (exact h))
    (case [cons j t]
      (cases hd (Nat.beq (:node j) d))
      (case [true] (simp only [raise-loop hd]) (exact h))
      (case [false]
        (cases hn (Nat.ble (:need j) (comp-rank w (:node j))))
        (case [true] (simp only [raise-loop hd hn]) (exact (ih d w t h)))
        (case [false]
          (simp only [raise-loop hd hn])
          (exact (ih d _ _ (vq-set-rank xq xw w (:node j) (:need j) h))))))))
(a/theorem vq-raise-for [xq :- (List Nat), xw :- (List Nat), w :- World, c :- Nat, d :- Nat]
  (=> (= (vq xq xw true w) true) (= (vq xq xw true (raise-for w c d)) true))
  (intro h)
  (cases hd (comp-has w d))
  (simp only [raise-for raise-run hd]) (exact h)
  (simp only [raise-for raise-run hd]) (exact (vq-raise-loop xq xw (raise-fuel w) d w _ h)))

;; ===========================================================================
;; Part G. vq through the allocating transitions: reactivation, demand, T6, T7, T8, T22
;; ===========================================================================

;; ---- awake facts
(a/theorem awake-not-has [cs :- (List CompRow), x :- Nat] (=> (= (tbl-has comp-id x cs) false) (= (awake cs x) true))
  (induction cs)
  (case [nil] (intro h) (simp only [awake tbl-all]))
  (case [cons hd t ih]
    (intro h)
    (cases hb (Nat.beq (comp-id hd) x))
    (case [true] (simp only [tbl-has hb] at h) (cases h))
    (case [false]
      (simp only [tbl-has hb] at h)
      (have a1 (= (not-idle-if-id x hd) true)) (simp only [not-idle-if-id] ) (have hb2 (= (Nat.beq (:id hd) x) false)) (exact hb) (simp only [hb2 Bool.not_false Bool.true_or])
      (have a2 := (ih h)) (simp only [awake] at a2)
      (simp only [awake tbl-all a1 a2 Bool.and_self]))))
(a/theorem awake-none [w :- World, x :- Nat] (=> (= (comp-find w x) (Option.none CompRow)) (= (awake (:comps w) x) true))
  (intro h) (exact (awake-not-has (:comps w) x (tbl-find-none-has CompRow comp-id x (:comps w) h))))
(a/defn not-idle14 [c :- CompRow] Bool (Bool.not (:idle c)))
(a/theorem awake-same [w :- World, x :- Nat, c :- CompRow]
  (=> (= (inv-sample w) true) (= (comp-find w x) (Option.some CompRow c)) (= (:idle c) false) (= (awake (:comps w) x) true))
  (intros hs hf hi)
  (have mc := (tbl-find-mem CompRow comp-id x c (:comps w) hf))
  (have hid := (tbl-find-id CompRow comp-id x c (:comps w) hf))
  (have q (= (not-idle14 c) true)) (simp only [not-idle14 hi Bool.not_false])
  (have z := (gd-same-id w c not-idle14 hs mc q))
  (have hid2 (= (:id c) x)) (exact hid)
  (rw [hid2] at z)
  (simp only [awake])
  (apply (tbl-all-mono CompRow (same-id-then comp-id x not-idle14) (not-idle-if-id x) _ (:comps w) z))
  (intros k hk) (simp only [same-id-then not-idle14] at hk) (simp only [not-idle-if-id]) (exact hk))
(a/theorem awake-upd-wake [x :- Nat, f :- (=> CompRow CompRow), hw :- (forall [c :- CompRow] (= (:idle (f c)) false)), cs :- (List CompRow)]
  (= (awake (tbl-upd comp-id x f cs) x) true)
  (simp only [awake])
  (induction cs)
  (case [nil] (simp only [tbl-upd tbl-all]))
  (case [cons hd t ih]
    (cases hb (Nat.beq (comp-id hd) x))
    (case [true] (simp only [tbl-upd hb tbl-all ih not-idle-if-id (hw hd) Bool.not_false Bool.or_true Bool.and_self]))
    (case [false]
      (have hb2 (= (Nat.beq (:id hd) x) false)) (exact hb)
      (simp only [tbl-upd hb tbl-all ih not-idle-if-id hb2 Bool.not_false Bool.true_or Bool.and_self]))))
(a/theorem awake-src [w :- World, x :- Nat, s :- SourceRow]
  (=> (= (inv-sample w) true) (= (source-find w x) (Option.some SourceRow s)) (= (awake (:comps w) x) true))
  (intros hs hf)
  (have hx := (tbl-find-has SourceRow source-id x s (:sources w) hf))
  (have hc := (comp-not-source w x (And.right (And.right (inv-parts w hs))) hx))
  (simp only [comp-has] at hc)
  (exact (awake-not-has (:comps w) x hc)))

;; ---- moving the parameters
(a/theorem vq-weaken [xq :- (List Nat), xw :- (List Nat), xs :- Bool, xq2 :- (List Nat), xw2 :- (List Nat), w :- World,
                      hq :- (forall [y :- Nat] (=> (= (reach-mem y xq) true) (= (reach-mem y xq2) true))),
                      hw :- (forall [y :- Nat] (=> (= (reach-mem y xw2) true) (= (reach-mem y xw) true)))]
  (=> (= (vq xq xw xs w) true) (= (vq xq2 xw2 xs w) true))
  (intro h)
  (have p := (vqk-parts xq xw xs _ _ _ (vq-rest-of xq xw xs w h)))
  (have i2 (= (tbl-all (dnaq14 xq2 (:comps w)) (:edges w)) true))
  (apply (tbl-all-mono EdgeRow (dnaq14 xq (:comps w)) (dnaq14 xq2 (:comps w)) _ (:edges w) (And.left (And.right p))))
  (intros e he)
  (cases hk (Nat.beq (:kind e) ek-dep))
  (case [false] (simp only [dnaq14 hk Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [dnaq14 hk Bool.not_true Bool.false_or Bool.or_eq_true] at he) (simp only [dnaq14 hk Bool.not_true Bool.false_or Bool.or_eq_true])
    (cases he) (case [inl a1] (exact (Or.inl (hq (:debtor e) a1)))) (case [inr a2] (exact (Or.inr a2))))
  (have i3 := (all-sub (awake (:comps w)) xw xw2 hw (And.left (And.right (And.right p)))))
  (exact (vq-intro xq2 xw2 xs w (vq-sample xq xw xs w h)
           (vqk-intro xq2 xw2 xs _ _ _ (And.left p) i2 i3 (And.right (And.right (And.right p)))))))
(a/theorem vq-weaken-s [xq :- (List Nat), xw :- (List Nat), xs :- Bool, w :- World]
  (=> (= (vq xq xw true w) true) (= (vq xq xw xs w) true))
  (intro h)
  (have p := (vqk-parts xq xw true _ _ _ (vq-rest-of xq xw true w h)))
  (have i4 (= (Bool.or (Bool.not xs) (tbl-all (swc14 (:next-id w)) (:comps w))) true))
  (have p4 := (And.right (And.right (And.right p)))) (simp only [Bool.not_true Bool.false_or] at p4)
  (simp only [p4 Bool.or_true])
  (exact (vq-intro xq xw xs w (vq-sample xq xw true w h)
           (vqk-intro xq xw xs _ _ _ (And.left p) (And.left (And.right p)) (And.left (And.right (And.right p))) i4))))
(a/theorem vq-drop [xq :- (List Nat), xw :- (List Nat), xs :- Bool, w :- World, x :- Nat]
  (=> (= (awake (:comps w) x) true) (= (vq (List.cons Nat x xq) xw xs w) true) (= (vq xq xw xs w) true))
  (intros ha h)
  (have p := (vqk-parts _ xw xs _ _ _ (vq-rest-of _ xw xs w h)))
  (have i2 (= (tbl-all (dnaq14 xq (:comps w)) (:edges w)) true))
  (apply (tbl-all-mono EdgeRow (dnaq14 (List.cons Nat x xq) (:comps w)) (dnaq14 xq (:comps w)) _ (:edges w) (And.left (And.right p))))
  (intros e he)
  (cases hk (Nat.beq (:kind e) ek-dep))
  (case [false] (simp only [dnaq14 hk Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [dnaq14 hk Bool.not_true Bool.false_or Bool.or_eq_true] at he) (simp only [dnaq14 hk Bool.not_true Bool.false_or Bool.or_eq_true])
    (cases he)
    (case [inr a2] (exact (Or.inr a2)))
    (case [inl a1]
      (cases hb (Nat.beq (:debtor e) x))
      (case [true] (have ex := (Nat.eq_of_beq_eq_true hb)) (rw [ex]) (exact (Or.inr ha)))
      (case [false] (simp only [reach-mem hb] at a1) (exact (Or.inl a1)))))
  (exact (vq-intro xq xw xs w (vq-sample _ xw xs w h)
           (vqk-intro xq xw xs _ _ _ (And.left p) i2 (And.left (And.right (And.right p))) (And.right (And.right (And.right p)))))))
(a/theorem vq-watch [xq :- (List Nat), xw :- (List Nat), xs :- Bool, w :- World, d :- Nat]
  (=> (= (awake (:comps w) d) true) (= (vq xq xw xs w) true) (= (vq xq (List.cons Nat d xw) xs w) true))
  (intros ha h)
  (have p := (vqk-parts xq xw xs _ _ _ (vq-rest-of xq xw xs w h)))
  (have i3 (= (tbl-all (awake (:comps w)) (List.cons Nat d xw)) true)) (simp only [tbl-all ha (And.left (And.right (And.right p))) Bool.and_self])
  (exact (vq-intro xq _ xs w (vq-sample xq xw xs w h)
           (vqk-intro xq _ xs _ _ _ (And.left p) (And.left (And.right p)) i3 (And.right (And.right (And.right p)))))))

;; ---- reactivation: the queue is the exemption list for dep edges on idle computations
(a/theorem rm-cons-r [y :- Nat, h :- Nat, xs :- (List Nat)] (=> (= (reach-mem y xs) true) (= (reach-mem y (List.cons Nat h xs)) true))
  (intro hy) (cases hb (Nat.beq y h)) (case [true] (simp only [reach-mem hb])) (case [false] (simp only [reach-mem hb]) (exact hy)))
(a/defn deb-in [q :- (List Nat), v :- Valid] Bool (reach-mem (:debtor v) q))
(a/theorem deb-in-sub [vs :- (List Valid)]
  (forall [L :- (List Nat)] (=> (forall [y :- Nat] (=> (= (reach-mem y (valid-debtors vs)) true) (= (reach-mem y L) true)))
                                (= (tbl-all (deb-in L) vs) true)))
  (induction vs)
  (case [nil] (intros L h) (simp only [tbl-all]))
  (case [cons v t ih]
    (intros L h)
    (have a1 (= (deb-in L v) true)) (simp only [deb-in]) (apply h) (simp only [valid-debtors reach-mem Nat.beq_refl])
    (have a2 (= (tbl-all (deb-in L) t) true))
    (apply ih) (intros y hy) (apply h) (simp only [valid-debtors]) (exact (rm-cons-r y (:debtor v) (valid-debtors t) hy))
    (simp only [tbl-all a1 a2 Bool.and_self])))

(a/theorem vq-react-add [xq :- (List Nat), xw :- (List Nat), w :- World, c :- Nat, v :- Valid]
  (=> (= (deb-in xq v) true) (= (vq xq xw true w) true) (= (vq xq xw true (react-add w c v)) true))
  (intros hd h)
  (cases hk (react-ok w c v))
  (simp only [react-add hk]) (exact h)
  (have hn (= (dnaq14 xq (:comps w) (valid-edge w c v)) true))
  (simp only [deb-in] at hd)
  (simp only [dnaq14 valid-edge hd Bool.true_or Bool.or_true])
  (simp only [react-add hk])
  (exact (vq-raise-for xq xw _ c (:debtor v) (vq-insert-edge-checked xq xw true w (valid-edge w c v) h hn))))
(a/theorem vq-react-edges [xq :- (List Nat), xw :- (List Nat), vs :- (List Valid)]
  (forall [w :- World, c :- Nat] (=> (= (tbl-all (deb-in xq) vs) true) (= (vq xq xw true w) true) (= (vq xq xw true (react-edges w c vs)) true)))
  (induction vs)
  (case [nil] (intros w c hd h) (simp only [react-edges]) (exact h))
  (case [cons v t ih]
    (intros w c hd h)
    (simp only [tbl-all Bool.and_eq_true] at hd)
    (simp only [react-edges])
    (exact (ih _ c (And.right hd) (vq-react-add xq xw w c v (And.left hd) h)))))

;; one reactivation: the popped computation wakes, the queue gains its validity debtors
(a/theorem vq-react-one [q :- (List Nat), xq0 :- (List Nat), xw :- (List Nat), w :- World, c :- CompRow, t :- (List Nat)]
  (=> (= (vq (List.cons Nat (:id c) (List.append Nat t xq0)) xw true w) true)
      (= (vq (List.append Nat (List.append Nat t (valid-debtors (:validity c))) xq0) (List.cons Nat (:id c) xw) true (react-one w c)) true))
  (intro h)
  (have h1 := (vq-comp-wake _ xw true w (:id c) comp-react-row comp-react-row-id comp-react-row-pending comp-react-row-dom14 h))
  (have aw := (awake-upd-wake (:id c) comp-react-row (fn [k :- CompRow] (Eq.refl false)) (:comps w)))
  (have aw2 (= (awake (:comps (comp-upd w (:id c) comp-react-row)) (:id c)) true)) (exact aw)
  (have h2a := (vq-drop (List.append Nat t xq0) xw true (comp-upd w (:id c) comp-react-row) (:id c) aw2 h1))
  (have h2 := (vq-watch (List.append Nat t xq0) xw true (comp-upd w (:id c) comp-react-row) (:id c) aw2 h2a))
  (have sub (forall [y :- Nat] (=> (= (reach-mem y (List.append Nat t xq0)) true)
                                    (= (reach-mem y (List.append Nat (List.append Nat t (valid-debtors (:validity c))) xq0)) true))))
  (intros y hy)
  (simp only [reach-mem-append Bool.or_eq_true] at hy) (simp only [reach-mem-append Bool.or_eq_true])
  (cases hy) (case [inl a1] (exact (Or.inl (Or.inl a1)))) (case [inr a2] (exact (Or.inr a2)))
  (have h3 := (vq-weaken _ (List.cons Nat (:id c) xw) true _ (List.cons Nat (:id c) xw) (comp-upd w (:id c) comp-react-row) sub
                (fn [y :- Nat, hy :- (= (reach-mem y (List.cons Nat (:id c) xw)) true)] hy) h2))
  (have hd := (deb-in-sub (:validity c) (List.append Nat (List.append Nat t (valid-debtors (:validity c))) xq0)
                (fn [y :- Nat, hy :- (= (reach-mem y (valid-debtors (:validity c))) true)]
                  (Eq.trans (reach-mem-append y (List.append Nat t (valid-debtors (:validity c))) xq0)
                    (Eq.trans (congrArg (fn [b :- Bool] (Bool.or b (reach-mem y xq0)))
                                (Eq.trans (reach-mem-append y t (valid-debtors (:validity c))) (congrArg (fn [b :- Bool] (Bool.or (reach-mem y t) b)) hy)))
                              (Eq.trans (congrArg (fn [b :- Bool] (Bool.or b (reach-mem y xq0))) (Bool.or_true (reach-mem y t))) (Bool.true_or (reach-mem y xq0))))))))
  (simp only [react-one])
  (exact (vq-react-edges _ _ (:validity c) (comp-upd w (:id c) comp-react-row) (:id c) hd h3)))

(a/theorem vq-r8 [xq0 :- (List Nat), xw :- (List Nat), fuel :- (List Nat)]
  (forall [w :- World, q :- (List Nat)]
    (=> (= (vq (List.append Nat q xq0) xw true w) true)
        (= (vq (List.append Nat (:rest (react-run8 fuel w q)) xq0) xw true (:world (react-run8 fuel w q))) true)))
  (induction fuel)
  (case [nil] (intros w q h) (simp only [react-run8]) (exact h))
  (case [cons u f ih]
    (intros w q h)
    (cases q)
    (case [nil] (simp only [react-run8]) (exact h))
    (case [cons x t]
      (cases hc (comp-find w x))
      (case [none]
        (simp only [react-run8 hc])
        (exact (ih w t (vq-drop _ xw true w x (awake-none w x hc) h))))
      (case [some c]
        (have hid := (tbl-find-id CompRow comp-id x c (:comps w) hc))
        (have hid2 (= (:id c) x)) (exact hid)
        (cases hi (:idle c))
        (case [false]
          (simp only [react-run8 hc hi])
          (exact (ih w t (vq-drop _ xw true w x (awake-same w x c (vq-sample _ xw true w h) hc hi) h))))
        (case [true]
          (simp only [react-run8 hc hi])
          (have h0 (= (vq (List.cons Nat (:id c) (List.append Nat t xq0)) xw true w) true)) (rw [hid2]) (exact h)
          (have h1 := (vq-react-one t xq0 xw w c t h0))
          (exact (ih _ _ (vq-weaken _ _ true _ xw (react-one w c) (fn [y :- Nat, hy :- (= (reach-mem y (List.append Nat (List.append Nat t (valid-debtors (:validity c))) xq0)) true)] hy)
                           (fn [y :- Nat, hy :- (= (reach-mem y xw) true)] (rm-cons-r y (:id c) xw hy)) h1))))))))

;; demand on d: afterwards d is awake (watched)
(a/theorem r8-step [u :- Nat, f :- (List Nat), w :- World, d :- Nat, c :- CompRow]
  (=> (= (comp-find w d) (Option.some CompRow c)) (= (:idle c) true)
      (= (react-run8 (List.cons Nat u f) w (List.cons Nat d (List.nil Nat)))
         (react-run8 f (react-one w c) (List.append Nat (List.nil Nat) (valid-debtors (:validity c))))))
  (intros hc hi) (simp only [react-run8 hc hi]))
(a/theorem rest-nil [r :- FinRes] (=> (= (match (:rest r) [nil true] [(cons h t) false]) true) (= (:rest r) (List.nil Nat)))
  (intro h) (cases hr (:rest r)) (case [nil] (rfl)) (case [cons a b] (rw [hr] at h) (cases h)))

(a/theorem vq-demand [xq :- (List Nat), xw :- (List Nat), w :- World, d :- Nat]
  (=> (= (vq xq xw true w) true) (= (vq xq (List.cons Nat d xw) true (demand-reactive w d)) true))
  (intro h)
  (have hs := (vq-sample xq xw true w h))
  (cases hc (comp-find w d)) (case' [some c]) (case' [none])
  (simp only [demand-reactive hc]) (exact (vq-watch xq xw true w d (awake-none w d hc) h))
  (have hid := (tbl-find-id CompRow comp-id d c (:comps w) hc))
  (have hid2 (= (:id c) d)) (exact hid)
  (cases hi (:idle c))
  (simp only [demand-reactive hc hi]) (exact (vq-watch xq xw true w d (awake-same w d c hs hc hi) h))
  (cases hv (valid-idle w c))
  (simp only [demand-reactive hc hi hv])
  (have aw (= (awake (:comps (comp-upd w d comp-demand-row)) d) true))
  (exact (awake-upd-wake d comp-demand-row (fn [k :- CompRow] (Eq.refl false)) (:comps w)))
  (exact (vq-watch xq xw true (comp-upd w d comp-demand-row) d aw
           (vq-comp-wake xq xw true w d comp-demand-row comp-demand-row-id comp-demand-row-pending comp-demand-row-dom14 h)))
  (simp only [demand-reactive hc hi hv])
  (have e1 := (react-run8-world (react-fuel w) w (List.cons Nat d (List.nil Nat))))
  (rw [← e1])
  (have e2 := (r8-step 0 (List.cons Nat 0 (tbl-gather (fn [k :- CompRow] true) (fn [k :- CompRow] (valid-debtors (:validity k))) (:comps w))) w d c hc hi))
  (have dn := (rest-nil (react-run8 (react-fuel w) w (List.cons Nat d (List.nil Nat))) (react-done-ok w d hs)))
  (have h0 (= (vq (List.cons Nat (:id c) (List.append Nat (List.nil Nat) xq)) xw true w) true)) (rw [hid2])
  (exact (vq-weaken xq xw true (List.cons Nat d xq) xw w (fn [y :- Nat, hy :- (= (reach-mem y xq) true)] (rm-cons-r y d xq hy))
           (fn [y :- Nat, hy :- (= (reach-mem y xw) true)] hy) h))
  (have h1 := (vq-react-one (List.nil Nat) xq xw w c (List.nil Nat) h0))
  (have h2 := (vq-r8 xq (List.cons Nat (:id c) xw) (List.cons Nat 0 (tbl-gather (fn [k :- CompRow] true) (fn [k :- CompRow] (valid-debtors (:validity k))) (:comps w)))
                (react-one w c) (List.append Nat (List.nil Nat) (valid-debtors (:validity c))) h1))
  (have e3 (= (react-run8 (react-fuel w) w (List.cons Nat d (List.nil Nat)))
              (react-run8 (List.cons Nat 0 (tbl-gather (fn [k :- CompRow] true) (fn [k :- CompRow] (valid-debtors (:validity k))) (:comps w)))
                          (react-one w c) (List.append Nat (List.nil Nat) (valid-debtors (:validity c))))))
  (exact e2)
  (rw [e3]) (rw [e3] at dn) (rw [dn] at h2)
  (apply (vq-weaken (List.append Nat (List.nil Nat) xq) (List.cons Nat (:id c) xw) true xq (List.cons Nat d xw) _
           (fn [y :- Nat, hy :- (= (reach-mem y (List.append Nat (List.nil Nat) xq)) true)] hy)
           (fn [y :- Nat, hy :- (= (reach-mem y (List.cons Nat d xw)) true)] (Eq.trans (congrArg (fn [z :- Nat] (reach-mem y (List.cons Nat z xw))) hid2) hy))))
  (exact h2))

(a/theorem vq-demand-fold [xq :- (List Nat), ds :- (List Nat)]
  (forall [w :- World, xw :- (List Nat)]
    (=> (= (vq xq xw true w) true) (= (vq xq (List.append Nat ds xw) true (nat-fold demand-reactive w ds)) true)))
  (induction ds)
  (case [nil] (intros w xw h) (simp only [nat-fold]) (exact h))
  (case [cons d t ih]
    (intros w xw h)
    (simp only [nat-fold])
    (have h1 := (ih (demand-reactive w d) (List.cons Nat d xw) (vq-demand xq xw w d h)))
    (apply (vq-weaken xq (List.append Nat t (List.cons Nat d xw)) true xq (List.append Nat (List.cons Nat d t) xw) _
             (fn [y :- Nat, hy :- (= (reach-mem y xq) true)] hy)))
    (intros y hy)
    (simp only [List.append reach-mem-append Bool.or_eq_true] at hy) (simp only [reach-mem-append Bool.or_eq_true])
    (cases hb (Nat.beq y d))
    (case [true] (apply Or.inr) (simp only [reach-mem hb]))
    (case [false]
      (simp only [reach-mem hb] at hy)
      (cases hy) (case [inl a1] (exact (Or.inl a1))) (case [inr a2] (apply Or.inr) (simp only [reach-mem hb]) (exact a2)))
    (exact h1)))

;; an allocation by a fresh edge opens the strict window
(a/theorem vq-insert-edge-fresh-up [xq :- (List Nat), xw :- (List Nat), xs :- Bool, w :- World, e :- EdgeRow]
  (=> (= (edge-ok-in w e) true) (= (vq xq xw xs w) true) (= (dnaq14 xq (:comps w) e) true) (= (vq xq xw true (insert-edge-fresh w e)) true))
  (intros he h hn)
  (have r0 := (vqk-up xq xw xs (:comps w) (:edges w) (:next-id w) (:comps w) (:edges w) (+ (:next-id w) 1)
                (cpres-refl (:comps w)) (epres-refl (:edges w)) (Nat.lt_succ_self (:next-id w)) (vq-rest-of xq xw xs w h)))
  (have hn2 (= (dnaq14 xq (:comps w) (edge-set-marked false (edge-set-id (:next-id w) e))) true)) (exact hn)
  (have r (= (vq-rest xq xw true (insert-edge-fresh w e)) true))
  (exact (vqk-cons-edge xq xw true _ _ _ _ hn2 r0))
  (exact (vq-intro xq xw true _ (insert-edge-fresh-inv-sample w e he (vq-sample xq xw xs w h)) r)))

;; ---- T6
(a/theorem vq-await-pre [xq :- (List Nat), xw :- (List Nat), xs :- Bool, w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (= (vq xq xw xs w) true) (= (vq xq (List.append Nat (nat-distinct ds) xw) true (await-pre w r ds mode k mine)) true))
  (intro h)
  (have h1 := (vq-run-upd xq xw xs w (:id r) run-tick run-tick-run-id h))
  (have he (= (act-id (ActRow.mk (:next-id w) (:id r) mode (List.nil Member) (none-slots ds) (nat-len ds) k mine))
              (:next-id (run-upd w (:id r) run-tick))))
  (rfl)
  (have w1 (= (vq xq xw true (bump (act-ins (run-upd w (:id r) run-tick) (ActRow.mk (:next-id w) (:id r) mode (List.nil Member) (none-slots ds) (nat-len ds) k mine)))) true))
  (exact (vq-intro xq xw true (bump (act-ins (run-upd w (:id r) run-tick) (ActRow.mk (:next-id w) (:id r) mode (List.nil Member) (none-slots ds) (nat-len ds) k mine))) (inv-act-ins-fresh (run-upd w (:id r) run-tick) (ActRow.mk (:next-id w) (:id r) mode (List.nil Member) (none-slots ds) (nat-len ds) k mine) he (vq-sample xq xw xs (run-upd w (:id r) run-tick) h1))
           (vq-rest-up xq xw xs (run-upd w (:id r) run-tick) (bump (act-ins (run-upd w (:id r) run-tick) (ActRow.mk (:next-id w) (:id r) mode (List.nil Member) (none-slots ds) (nat-len ds) k mine))) (cpres-refl (:comps (run-upd w (:id r) run-tick))) (epres-refl (:edges (run-upd w (:id r) run-tick))) (Nat.lt_succ_self (:next-id (run-upd w (:id r) run-tick)))
             (vq-rest-of xq xw xs (run-upd w (:id r) run-tick) h1))))
  (simp only [await-pre])
  (exact (vq-demand-fold xq (nat-distinct ds) _ xw w1)))

(a/defn rm-in [xs :- (List Nat), y :- Nat] Bool (reach-mem y xs))
(a/theorem vq-await-step [xq :- (List Nat), xw :- (List Nat), r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, acc :- AwAcc, d :- Nat]
  (=> (= (reach-mem d xw) true) (= (vq xq xw true (:world acc)) true) (= (vq xq xw true (:world (await-step r a mode k acc d))) true))
  (intros hw h)
  (have aw := (all-reach-mem (awake (:comps (:world acc))) d xw (And.left (And.right (And.right (vqk-parts xq xw true _ _ _ (vq-rest-of xq xw true _ h))))) hw))
  (cases hd (as-dep (:world acc) r d))
  (case [false]
    (have hn (= (dnaq14 xq (:comps (:world acc)) (await-edge (:world acc) r a mode k d)) true))
    (simp [dnaq14 await-edge hd ek-wait ek-dep])
    (simp only [await-step hd])
    (exact (vq-insert-edge-checked xq xw true _ _ h hn)))
  (case [true]
    (cases hs (site-edge (:edges (:world acc)) (:of r) (:effect-index r) d))
    (case [none]
      (have hn (= (dnaq14 xq (:comps (:world acc)) (await-edge (:world acc) r a mode k d)) true))
      (simp only [await-edge hd dnaq14 aw Bool.or_true])
      (simp only [await-step hd hs])
      (simp only [await-new-dep])
      (exact (vq-comp-upd xq xw true _ (:of r) (comp-consume-adopt (:effect-index r) d)
               (comp-consume-adopt-comp-id _ _) (comp-consume-adopt-pending _ _) (fn [c :- CompRow] (Eq.refl (ck14 c)))
               (vq-raise-for xq xw _ (:of r) d (vq-insert-edge-checked xq xw true _ _ h hn)))))
    (case [some e]
      (simp only [await-step hd hs])
      (exact (vq-comp-upd xq xw true _ (:of r) (comp-consume-adopt (:effect-index r) d)
               (comp-consume-adopt-comp-id _ _) (comp-consume-adopt-pending _ _) (fn [c :- CompRow] (Eq.refl (ck14 c)))
               (vq-edge-upd xq xw true _ (:id e) (edge-reawait (await-cont r mode k)) (edge-reawait-edge-id _)
                 (edge-reawait-kind _) (edge-reawait-creditor _) (edge-reawait-debtor _) (edge-reawait-marked _) h))))))
(a/theorem vq-await-wire [xq :- (List Nat), xw :- (List Nat), r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, ds :- (List Nat)]
  (forall [acc :- AwAcc] (=> (= (tbl-all (rm-in xw) ds) true) (= (vq xq xw true (:world acc)) true)
                             (= (vq xq xw true (:world (await-wire r a mode k acc ds))) true)))
  (induction ds)
  (case [nil] (intros acc hd h) (simp only [await-wire]) (exact h))
  (case [cons d t ih]
    (intros acc hd h)
    (simp only [tbl-all Bool.and_eq_true] at hd)
    (have hd1 (= (reach-mem d xw) true)) (exact (And.left hd))
    (simp only [await-wire])
    (exact (ih _ (And.right hd) (vq-await-step xq xw r a mode k acc d hd1 h)))))
(a/theorem rm-in-self [xs :- (List Nat), ys :- (List Nat)] (= (tbl-all (rm-in (List.append Nat xs ys)) xs) true)
  (apply (all-of-mem-r (rm-in (List.append Nat xs ys)) xs))
  (intros y hy) (simp only [rm-in reach-mem-append hy Bool.true_or]))

(a/theorem edge-ok-host-wait [w :- World, d :- Nat] (=> (= (deb-exists w d) true) (= (edge-ok-in w (host-wait-edge d)) true))
  (intro h)
  (simp only [deb-exists comp-has task-has source-has resource-has] at h)
  (simp [edge-ok-in edge-ok cred-ok deb-ok host-wait-edge host-cred ek-wait ek-dep h]))

;; ---- the overrides (generic in the bundle parameters, as the copier calls them)
(override! VQ 'inv-await-raw '[inv-await-post]
  '(a/theorem vq-await-raw [zq9 :- (List Nat), zw9 :- (List Nat), zs9 :- Bool, w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
     (=> (= (vq zq9 zw9 zs9 w) true) (= (vq zq9 zw9 zs9 (await-raw w r ds mode k mine)) true))
     (intro h)
     (have h1 := (vq-await-pre zq9 zw9 zs9 w r ds mode k mine h))
     (have h2 := (vq-await-wire zq9 (List.append Nat (nat-distinct ds) zw9) r (:next-id w) mode k (nat-distinct ds)
                   (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) (rm-in-self (nat-distinct ds) zw9) h1))
     (have h3 := (vq-await-post zq9 (List.append Nat (nat-distinct ds) zw9) true (:next-id w) (:id r) ds (await-acc w r ds mode k mine) h2))
     (have h4 := (vq-weaken zq9 (List.append Nat (nat-distinct ds) zw9) true zq9 zw9 (await-post (:next-id w) (:id r) ds (await-acc w r ds mode k mine))
                   (fn [y :- Nat, hy :- (= (reach-mem y zq9) true)] hy)
                   (fn [y :- Nat, hy :- (= (reach-mem y zw9) true)] (Eq.trans (reach-mem-append y (nat-distinct ds) zw9) (Eq.trans (congrArg (fn [b :- Bool] (Bool.or (reach-mem y (nat-distinct ds)) b)) hy) (Bool.or_true _))))
                   h3))
     (simp only [await-raw])
     (exact (vq-weaken-s zq9 zw9 zs9 _ h4))))

(override! VQ 'inv-track-raw '[inv-track-fin]
  '(a/theorem vq-track-raw [zq9 :- (List Nat), zw9 :- (List Nat), zs9 :- Bool, w :- World, r :- RunRow, x :- Nat, s :- SourceRow, k :- Nat]
     (=> (= (comp-has w (:of r)) true) (= (source-find w x) (Option.some SourceRow s))
         (= (vq zq9 zw9 zs9 w) true) (= (vq zq9 zw9 zs9 (track-raw w r x s k)) true))
     (intros hc hs h)
     (have aw := (awake-src w x s (vq-sample zq9 zw9 zs9 w h) hs))
     (have hn (= (dnaq14 zq9 (:comps w) (track-edge r x s k)) true))
     (simp only [dnaq14 track-edge aw Bool.or_true])
     (have h2 (= (vq zq9 zw9 zs9 (match (site-edge (:edges w) (:of r) (:effect-index r) x)
                                  [none (track-new w r x s k)]
                                  [(some e) (comp-upd (track-fin s (:id e) (edge-upd w (:id e) (edge-reread (track-cont r k) s)))
                                                      (:of r) (comp-consume-adopt (:effect-index r) x))])) true))
     (cases he (site-edge (:edges w) (:of r) (:effect-index r) x)) (case' [some e]) (case' [none])
     (simp only [track-new])
     (exact (vq-comp-upd zq9 zw9 zs9 _ (:of r) (comp-consume-adopt (:effect-index r) x)
              (comp-consume-adopt-comp-id _ _) (comp-consume-adopt-pending _ _) (fn [c :- CompRow] (Eq.refl (ck14 c)))
              (vq-track-fin zq9 zw9 zs9 s (:next-id w) _ (vq-insert-edge-fresh zq9 zw9 zs9 w (track-edge r x s k) (track-edge-ok w r x s k hc hs) h hn))))
     (exact (vq-comp-upd zq9 zw9 zs9 _ (:of r) (comp-consume-adopt (:effect-index r) x)
              (comp-consume-adopt-comp-id _ _) (comp-consume-adopt-pending _ _) (fn [c :- CompRow] (Eq.refl (ck14 c)))
              (vq-track-fin zq9 zw9 zs9 s (:id e) _
                (vq-edge-upd zq9 zw9 zs9 w (:id e) (edge-reread (track-cont r k) s) (edge-reread-edge-id _ _) (edge-reread-kind _ _)
                  (edge-reread-creditor _ _) (edge-reread-debtor _ _) (edge-reread-marked _ _) h))))
     (simp only [track-raw])
     (exact (vq-run-upd zq9 zw9 zs9 _ (:id r) run-tick run-tick-run-id h2))))

(override! VQ 't22-inv '[inv-fire-edge]
  '(a/theorem t22-vq [zq9 :- (List Nat), zw9 :- (List Nat), zs9 :- Bool, w :- World, d :- Nat, fresh :- Nat]
     (=> (= (vq zq9 zw9 zs9 w) true) (= (vq zq9 zw9 zs9 (:world (t22-host-await w d fresh))) true))
     (intro h)
     (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (deb-exists w d)))
     (simp only [t22-host-await hg refuse]) (exact h)
     (have hx (= (deb-exists w d) true)) (simp only [Bool.and_eq_true] at hg) (exact (And.right hg))
     (have ok := (edge-ok-host-wait w d hx))
     (have hn (= (dnaq14 zq9 (:comps w) (host-wait-edge d)) true)) (simp [dnaq14 host-wait-edge ek-wait ek-dep])
     (have h0 := (vq-insert-edge-fresh-up zq9 zw9 zs9 w (host-wait-edge d) ok h hn))
     (have e0 (= (insert-edge-checked w (host-wait-edge d)) (insert-edge-fresh w (host-wait-edge d)))) (simp only [insert-edge-checked ok])
     (have h1 (= (vq zq9 (List.cons Nat d zw9) true (host-await-dem w d)) true))
     (simp only [host-await-dem]) (rw [e0]) (exact (vq-demand zq9 zw9 _ d h0))
     (have h2 (= (vq zq9 (List.cons Nat d zw9) true (host-await-raw w d)) true))
     (cases hr (fast-ready (host-await-dem w d) d))
     (simp only [host-await-raw hr]) (exact h1)
     (simp only [host-await-raw hr]) (exact (vq-fire-edge zq9 (List.cons Nat d zw9) true _ _ (:next-id w) h1))
     (simp only [t22-host-await hg accept])
     (exact (vq-weaken-s zq9 zw9 zs9 _ (vq-weaken zq9 (List.cons Nat d zw9) true zq9 zw9 _ (fn [y :- Nat, hy :- (= (reach-mem y zq9) true)] hy)
                                          (fn [y :- Nat, hy :- (= (reach-mem y zw9) true)] (rm-cons-r y d zw9 hy)) h2)))))

(override! VQ 't8-full-inv '[inv-fire-edge]
  '(a/theorem t8-full-vq [zq9 :- (List Nat), zw9 :- (List Nat), zs9 :- Bool, w :- World, d :- Nat, cb :- Nat, fresh :- Nat]
     (=> (= (vq zq9 zw9 zs9 w) true) (= (vq zq9 zw9 zs9 (:world (t8-full w d cb fresh))) true))
     (intro h)
     (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (edge-ok-in w (observe-edge w d cb))))
     (simp only [t8-full hg refuse]) (exact h)
     (have he (= (edge-ok-in w (observe-edge w d cb)) true))
     (simp only [Bool.and_eq_true] at hg) (exact (And.right hg))
     (have hn (= (dnaq14 zq9 (:comps w) (observe-edge w d cb)) true)) (simp [dnaq14 observe-edge ek-observe ek-dep])
     (have h1 := (vq-demand zq9 zw9 _ d (vq-insert-edge-fresh-up zq9 zw9 zs9 w (observe-edge w d cb) he h hn)))
     (have h2 (= (vq zq9 (List.cons Nat d zw9) true (observe-raw w d cb)) true))
     (simp only [observe-raw])
     (cases hr (deb-ready (demand-reactive (insert-edge-fresh w (observe-edge w d cb)) d) d))
     (simp only [hr]) (exact h1)
     (simp only [hr]) (exact (vq-fire-edge zq9 (List.cons Nat d zw9) true _ _ (:next-id w) h1))
     (simp only [t8-full hg accept])
     (exact (vq-weaken-s zq9 zw9 zs9 _ (vq-weaken zq9 (List.cons Nat d zw9) true zq9 zw9 _ (fn [y :- Nat, hy :- (= (reach-mem y zq9) true)] hy)
                                          (fn [y :- Nat, hy :- (= (reach-mem y zw9) true)] (rm-cons-r y d zw9 hy)) h2)))))

(override! VQ 'inv-take-park '[]
  '(a/theorem vq-take-park [zq9 :- (List Nat), zw9 :- (List Nat), zs9 :- Bool, w :- World, r :- RunRow, x :- Nat, k :- Nat]
     (=> (= (vq zq9 zw9 zs9 w) true) (= (vq zq9 zw9 zs9 (take-park w r x k)) true))
     (intro h)
     (have h1 := (vq-act-ins-fresh zq9 zw9 zs9 w (take-act w r k) (rfl) h))
     (have hn (= (dnaq14 zq9 (:comps (bump (act-ins w (take-act w r k)))) (take-edge r (:next-id w) x)) true))
     (simp [dnaq14 take-edge ek-wait ek-dep])
     (have h2 := (vq-insert-edge-checked zq9 zw9 zs9 (bump (act-ins w (take-act w r k))) (take-edge r (:next-id w) x) h1 hn))
     (simp only [take-park])
     (exact (vq-run-upd zq9 zw9 zs9 _ (:id r) run-tick-park run-tick-park-id h2))))

(lcopy! VQ 'raw-inv)

;; ===========================================================================
;; Part H. The vr copy (Rule R: no allocation, the pass's demotions share the allocator)
;; ===========================================================================

(a/theorem vr-comp-upd [xd :- (List Nat), xr :- (List Nat), w :- World, x :- Nat, f :- (=> CompRow CompRow),
                        hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                        hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                        hk :- (forall [c :- CompRow] (= (ck14 (f c)) (ck14 c)))]
  (=> (= (vr xd xr w) true) (= (vr xd xr (comp-upd w x f)) true))
  (intro h)
  (exact (vr-intro xd xr _ (inv-comp-upd w x f hid hp (vr-sample xd xr w h))
           (vr-rest-wd xd xr w (comp-upd w x f) (wdom-comp-key w x f hk) (vr-rest-of xd xr w h)))))

(def VR (mk-bundle 'vr '[zd9 :- (List Nat), zr9 :- (List Nat)] "vr-"
          {'inv-comp-upd ['(fn [c :- CompRow] (Eq.refl (ck14 c))) 5]}))
(swap! (:renames VR) assoc 'inv-parts 'vr-parts 'inv-comp-upd 'vr-comp-upd)
(doseq [o '[inv-scope-upd inv-pub-upd inv-source-upd inv-resource-upd inv-cleanup-upd inv-cleanup-del inv-set-pins
            inv-resource-del inv-scope-del inv-cleanup-ins inv-act-upd inv-task-upd inv-run-upd inv-run-del]]
  (prim! VR o nil))
(prim! VR 'inv-edge-upd '(vr-rest-wd zd9 zr9 w (edge-upd w x f) (wdom-edge-upd w x f hk hc hd) R))
(prim! VR 'inv-remove-edge '(vr-rest-wd zd9 zr9 w (remove-edge w x) (wdom-remove-edge w x) R))
(prim! VR 'mark-edge-inv-sample '(vr-rest-wd zd9 zr9 w (mark-edge w x) (wdom-mark-edge w x) R))
(prim! VR 'unmark-edge-inv-sample '(vr-rest-wd zd9 zr9 w (unmark-edge w x) (wdom-unmark-edge w x) R))
(prim! VR 'inv-drop-cred '(vr-rest-wd zd9 zr9 w (drop-cred-edges w a) (wdom-drop-cred w a) R))
(prim! VR 'inv-drop-act '(vr-rest-wd zd9 zr9 w (drop-act w a) (wdom-drop-act w a) R))
(prim! VR 'inv-drop-edges '(vr-rest-wd zd9 zr9 w (drop-edges w p) (wdom-drop-edges w p) R))
(prim! VR 'inv-comp-del-unref '(vr-rest-wd zd9 zr9 w (comp-del w x) (wdom-comp-del w x) R))
(prim! VR 'inv-filter-world '(vr-rest-wd zd9 zr9 w (filter-world K w) (wdom-filter-world w K) R))

;; ---- the demotion of x: comp-make-idle with entries at the pass's allocator and x's rank
(a/defn xr14 [x :- Nat, rx :- Nat, k :- CompRow] Bool (Bool.or (Bool.not (Nat.beq (:id k) x)) (Nat.beq (:rank k) rx)))
(a/defn rlt14 [d :- Nat, r :- Nat, q :- CompRow] Bool (Bool.or (Bool.not (Nat.beq (:id q) d)) (Nat.blt (:rank q) r)))
(a/defn ulow14 [n :- Nat, r :- Nat, u :- Valid] Bool (Bool.and (Nat.beq (:stamp u) n) (Nat.blt (:crank u) r)))
(a/defn vdn14 [n :- Nat, d :- Nat, r :- Nat, q :- CompRow] Bool
  (Bool.or (Bool.not (Bool.and (Nat.beq (:id q) d) (:idle q))) (tbl-all (ulow14 n r) (:validity q))))
(a/defn vent14 [n :- Nat, rx :- Nat, cs :- (List CompRow), v :- Valid] Bool
  (Bool.and (Nat.beq (:stamp v) n) (Bool.and (Nat.beq (:crank v) rx)
    (Bool.and (tbl-all (rlt14 (:debtor v) rx) cs) (tbl-all (vdn14 n (:debtor v) rx) cs)))))
(a/defn ncd14 [x :- Nat, e :- EdgeRow] Bool (Bool.or (Bool.not (Nat.beq (:kind e) ek-dep)) (Bool.not (Nat.beq (:creditor e) x))))
(a/defn inx14 [x :- Nat, rx :- Nat, cs :- (List CompRow), e :- EdgeRow] Bool
  (Bool.or (Bool.not (Bool.and (Nat.beq (:kind e) ek-dep) (Nat.beq (:debtor e) x))) (tbl-all (rgt14 (:creditor e) rx) cs)))
(a/defn tri14 [n :- Nat, d :- Nat, rx :- Nat, x :- Nat, q :- CompRow] Bool
  (Bool.and (rlt14 d rx q) (Bool.and (vdn14 n d rx q) (xr14 x rx q))))

(a/theorem vent14-parts [n :- Nat, rx :- Nat, cs :- (List CompRow), v :- Valid]
  (=> (= (vent14 n rx cs v) true)
      (And (= (:stamp v) n) (And (= (:crank v) rx) (And (= (tbl-all (rlt14 (:debtor v) rx) cs) true) (= (tbl-all (vdn14 n (:debtor v) rx) cs) true)))))
  (intro h) (simp only [vent14 Bool.and_eq_true] at h)
  (exact (And.intro (Nat.eq_of_beq_eq_true (And.left h)) (And.intro (Nat.eq_of_beq_eq_true (And.left (And.right h))) (And.right (And.right h))))))

(a/theorem tri14-all [n :- Nat, d :- Nat, rx :- Nat, x :- Nat, cs :- (List CompRow)]
  (=> (= (tbl-all (rlt14 d rx) cs) true) (= (tbl-all (vdn14 n d rx) cs) true) (= (tbl-all (xr14 x rx) cs) true) (= (tbl-all (tri14 n d rx x) cs) true))
  (intros h1 h2 h3)
  (apply (all-of-mem CompRow (tri14 n d rx x) cs))
  (intros q hq)
  (simp only [tri14 (tbl-all-mem CompRow (rlt14 d rx) q cs h1 hq) (tbl-all-mem CompRow (vdn14 n d rx) q cs h2 hq) (tbl-all-mem CompRow (xr14 x rx) q cs h3 hq) Bool.and_self]))

;; prec for the entries of the new idle row
(a/theorem prec-ulow [n :- Nat, rx :- Nat, v :- Valid, us :- (List Valid)]
  (=> (= (:stamp v) n) (= (:crank v) rx) (= (tbl-all (ulow14 n rx) us) true) (= (tbl-all (prec14 v) us) true))
  (intros hs hc h)
  (apply (tbl-all-mono Valid (ulow14 n rx) (prec14 v) _ us h))
  (intros u hu)
  (simp only [ulow14 Bool.and_eq_true] at hu)
  (have e1 := (Nat.eq_of_beq_eq_true (And.left hu)))
  (have b1 (= (Nat.beq (:stamp u) (:stamp v)) true)) (rw [e1, hs]) (exact (Nat.beq_refl n))
  (have b2 (= (Nat.blt (:crank u) (:crank v)) true)) (rw [hc]) (exact (And.right hu))
  (simp only [prec14 b1 b2 Bool.and_self Bool.or_true]))
(a/theorem prec-new [n :- Nat, rx :- Nat, v :- Valid, vs :- (List Valid), cs :- (List CompRow)]
  (=> (= (Nat.ble (:stamp v) n) true) (= (Bool.or (Nat.blt (:stamp v) n) (Nat.blt rx (:crank v))) true)
      (= (tbl-all (vent14 n rx cs) vs) true) (= (tbl-all (prec14 v) vs) true))
  (intros hl ho h)
  (apply (tbl-all-mono Valid (vent14 n rx cs) (prec14 v) _ vs h))
  (intros u hu)
  (have p := (vent14-parts n rx cs u hu))
  (cases hb (Nat.blt (:stamp v) n))
  (case [true]
    (have b1 (= (Nat.blt (:stamp v) (:stamp u)) true)) (rw [(And.left p)]) (exact hb)
    (simp only [prec14 b1 Bool.true_or]))
  (case [false]
    (simp only [hb Bool.false_or] at ho)
    (simp only [Nat.blt_eq Nat.ble_eq] at hb hl)
    (have b1 (= (Nat.beq (:stamp u) (:stamp v)) true)) (rw [(And.left p)]) (simp only [Nat.beq_eq]) (omega)
    (have b2 (= (Nat.blt (:crank u) (:crank v)) true)) (rw [(And.left (And.right p))]) (exact ho)
    (simp only [prec14 b1 b2 Bool.and_self Bool.or_true])))

;; deb14 of an entry towards the rows of the updated list
(a/theorem deb-new-all [n :- Nat, x :- Nat, rx :- Nat, cs :- (List CompRow), vs :- (List Valid), v :- Valid]
  (=> (= (vent14 n rx cs v) true) (= (tbl-all (xr14 x rx) cs) true)
      (= (tbl-all (deb14 n v) (tbl-upd comp-id x (comp-make-idle vs) cs)) true))
  (intros hv hx)
  (have p := (vent14-parts n rx cs v hv))
  (have t3 := (tri14-all n (:debtor v) rx x cs (And.left (And.right (And.right p))) (And.right (And.right (And.right p))) hx))
  (apply (tbl-all-upd CompRow comp-id x (comp-make-idle vs) (tri14 n (:debtor v) rx x) (deb14 n v) _ _ cs t3))
  (intros q hq hqx)
  (simp only [tri14 rlt14 xr14 Bool.and_eq_true Bool.or_eq_true] at hq)
  (have hqx2 (= (Nat.beq (:id q) x) true)) (exact hqx)
  (cases hb (Nat.beq (:id q) (:debtor v)))
  (case [false] (simp only [deb14 comp-make-idle hb Bool.not_false Bool.true_or]))
  (case [true]
    (exfalso)
    (have a1 := (And.left hq)) (simp only [hb Bool.not_true] at a1)
    (have a3 := (And.right (And.right hq))) (simp only [hqx2 Bool.not_true] at a3)
    (cases a1) (case [inl z] (cases z))
    (case [inr z]
      (cases a3) (case [inl y] (cases y))
      (case [inr y] (have e := (Nat.eq_of_beq_eq_true y)) (simp only [Nat.blt_eq] at z) (omega))))
  (intros q hq hqx)
  (simp only [tri14 rlt14 vdn14 Bool.and_eq_true] at hq)
  (cases hb (Nat.beq (:id q) (:debtor v)))
  (case [false] (simp only [deb14 hb Bool.not_false Bool.true_or]))
  (case [true]
    (have a1 := (And.left hq)) (simp only [hb Bool.not_true Bool.false_or] at a1)
    (have a2 := (And.left (And.right hq))) (simp only [hb Bool.true_and] at a2)
    (have c2 (= (Nat.blt (:rank q) (:crank v)) true)) (rw [(And.left (And.right p))]) (exact a1)
    (simp only [deb14 hb c2 Bool.not_true Bool.false_or Bool.or_true Bool.true_and])
    (cases hi (:idle q))
    (case [false] (simp only [Bool.not_false Bool.true_or]))
    (case [true]
      (simp only [hi Bool.not_true Bool.false_or] at a2) (simp only [Bool.not_true Bool.false_or])
      (exact (prec-ulow n rx v (:validity q) (And.left p) (And.left (And.right p)) a2)))))

(a/theorem deb-old-all [n :- Nat, x :- Nat, rx :- Nat, cs :- (List CompRow), vs :- (List Valid), v :- Valid]
  (=> (= (ent14 cs n v) true) (= (tbl-all (xr14 x rx) cs) true) (= (tbl-all (vent14 n rx cs) vs) true)
      (= (tbl-all (deb14 n v) (tbl-upd comp-id x (comp-make-idle vs) cs)) true))
  (intros he hx hvs)
  (simp only [ent14 Bool.and_eq_true] at he)
  (have hb2 := (tbl-all-mono2 CompRow (deb14 n v) (xr14 x rx) (both (deb14 n v) (xr14 x rx))
                 (fn [q :- CompRow, h1 :- (= (deb14 n v q) true), h2 :- (= (xr14 x rx q) true)] (both-of CompRow (deb14 n v) (xr14 x rx) q h1 h2))
                 cs (And.right he) hx))
  (apply (tbl-all-upd CompRow comp-id x (comp-make-idle vs) (both (deb14 n v) (xr14 x rx)) (deb14 n v) _ _ cs hb2))
  (intros q hq hqx)
  (have d1 := (both-left CompRow (deb14 n v) (xr14 x rx) q hq))
  (have x1 := (both-right CompRow (deb14 n v) (xr14 x rx) q hq))
  (have hqx2 (= (Nat.beq (:id q) x) true)) (exact hqx)
  (simp only [xr14 hqx2 Bool.not_true Bool.false_or] at x1)
  (have er := (Nat.eq_of_beq_eq_true x1))
  (cases hb (Nat.beq (:id q) (:debtor v)))
  (case [false] (simp only [deb14 comp-make-idle hb Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [deb14 hb Bool.not_true Bool.false_or Bool.and_eq_true] at d1)
    (have o1 := (And.left d1))
    (have o2 (= (Bool.or (Nat.blt (:stamp v) n) (Nat.blt rx (:crank v))) true)) (rw [← er]) (exact o1)
    (have hq2 (= (tbl-all (prec14 v) vs) true)) (exact (prec-new n rx v vs cs (And.left he) o2 hvs))
    (simp only [deb14 comp-make-idle hb o1 hq2 Bool.not_true Bool.false_or Bool.or_true Bool.and_self]))
  (intros q hq hqx) (exact (both-left CompRow (deb14 n v) (xr14 x rx) q hq)))

(a/theorem iv14-make-idle [n :- Nat, x :- Nat, rx :- Nat, cs :- (List CompRow), vs :- (List Valid)]
  (=> (= (iv14 cs n) true) (= (tbl-all (xr14 x rx) cs) true) (= (tbl-all (vent14 n rx cs) vs) true)
      (= (iv14 (tbl-upd comp-id x (comp-make-idle vs) cs) n) true))
  (intros h hx hvs)
  (simp only [iv14] at h) (simp only [iv14])
  (apply (tbl-all-upd CompRow comp-id x (comp-make-idle vs) (ivc14 cs n) (ivc14 (tbl-upd comp-id x (comp-make-idle vs) cs) n) _ _ cs h))
  (intros k hk hkx)
  (simp only [ivc14 comp-make-idle Bool.not_true Bool.false_or])
  (apply (tbl-all-mono Valid (vent14 n rx cs) _ _ vs hvs))
  (intros v hv)
  (have p := (vent14-parts n rx cs v hv))
  (have b (= (Nat.ble (:stamp v) n) true)) (rw [(And.left p)]) (simp only [Nat.ble_eq]) (omega)
  (simp only [ent14 b (deb-new-all n x rx cs vs v hv hx) Bool.and_self])
  (intros k hk hkx)
  (cases hi (:idle k))
  (case [false] (simp only [ivc14 hi Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [ivc14 hi Bool.not_true Bool.false_or] at hk) (simp only [ivc14 hi Bool.not_true Bool.false_or])
    (apply (tbl-all-mono Valid (ent14 cs n) _ _ (:validity k) hk))
    (intros v hv)
    (have hv2 (= (Bool.and (Nat.ble (:stamp v) n) (tbl-all (deb14 n v) cs)) true)) (exact hv)
    (simp only [Bool.and_eq_true] at hv2) (have b := (And.left hv2))
    (simp only [ent14 b (deb-old-all n x rx cs vs v hv hx hvs) Bool.and_self])))

(a/theorem awake-upd-other [x :- Nat, d :- Nat, f :- (=> CompRow CompRow), hid :- (forall [c :- CompRow] (= (:id (f c)) (:id c))), cs :- (List CompRow)]
  (=> (= (Nat.beq d x) false) (= (awake cs d) true) (= (awake (tbl-upd comp-id x f cs) d) true))
  (intros hne h)
  (simp only [awake] at h) (simp only [awake])
  (apply (tbl-all-upd CompRow comp-id x f (not-idle-if-id d) (not-idle-if-id d) _ _ cs h))
  (intros r hr hrx)
  (have e := (Nat.eq_of_beq_eq_true hrx))
  (have b (= (Nat.beq (:id (f r)) d) false)) (rw [(hid r)]) (have e2 (= (:id r) x)) (exact e) (rw [e2]) (rw [beq-comm]) (exact hne)
  (simp only [not-idle-if-id b Bool.not_false Bool.true_or])
  (intros r hr hrx) (exact hr))
(a/theorem rgt-upd [x :- Nat, y :- Nat, r :- Nat, f :- (=> CompRow CompRow),
                    hid :- (forall [c :- CompRow] (= (:id (f c)) (:id c))), hr :- (forall [c :- CompRow] (= (:rank (f c)) (:rank c))), cs :- (List CompRow)]
  (=> (= (tbl-all (rgt14 y r) cs) true) (= (tbl-all (rgt14 y r) (tbl-upd comp-id x f cs)) true))
  (intro h)
  (apply (tbl-all-upd CompRow comp-id x f (rgt14 y r) (rgt14 y r) _ _ cs h))
  (intros q hq hqx) (simp only [rgt14] at hq) (simp only [rgt14 (hid q) (hr q)]) (exact hq)
  (intros q hq hqx) (exact hq))

(a/theorem vrk-make-idle [S :- (List Nat), R :- (List Nat), cs :- (List CompRow), es :- (List EdgeRow), n :- Nat, x :- Nat, rx :- Nat, vs :- (List Valid)]
  (=> (= (vrk S R cs es n) true) (= (reach-mem x S) true) (= (tbl-all (ncd14 x) es) true) (= (tbl-all (xr14 x rx) cs) true)
      (= (tbl-all (vent14 n rx cs) vs) true) (= (tbl-all (inx14 x rx cs) es) true)
      (= (vrk S R (tbl-upd comp-id x (comp-make-idle vs) cs) es n) true))
  (intros h hx hn hxr hvs hin)
  (have p := (vrk-parts S R cs es n h))
  (have i1 := (iv14-make-idle n x rx cs vs (And.left p) hxr hvs))
  (have hid (forall [c :- CompRow] (= (:id (comp-make-idle vs c)) (:id c)))) (intro c) (rfl)
  (have hrk (forall [c :- CompRow] (= (:rank (comp-make-idle vs c)) (:rank c)))) (intro c) (rfl)
  (have i2 (= (tbl-all (dnb14 S R (tbl-upd comp-id x (comp-make-idle vs) cs)) es) true))
  (apply (tbl-all-mono EdgeRow (dnb14 S R cs) _ _ es (And.left (And.right p))))
  (intros e he)
  (cases hk (Nat.beq (:kind e) ek-dep))
  (case [false] (simp only [dnb14 hk Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [dnb14 hk Bool.not_true Bool.false_or Bool.and_eq_true Bool.or_eq_true] at he)
    (simp only [dnb14 hk Bool.not_true Bool.false_or Bool.and_eq_true Bool.or_eq_true])
    (apply And.intro)
    (have hz := (And.left he))
    (cases hz)
    (case [inl a1] (exact (Or.inl a1)))
    (case [inr a2]
      (cases hdx (Nat.beq (:debtor e) x))
      (case [true] (have ed := (Nat.eq_of_beq_eq_true hdx)) (rw [ed]) (exact (Or.inl hx)))
      (case [false] (exact (Or.inr (awake-upd-other x (:debtor e) (comp-make-idle vs) hid cs hdx a2)))))
    (exact (And.right he)))
  (have i3 (= (tbl-all (dne14 S n (tbl-upd comp-id x (comp-make-idle vs) cs)) es) true))
  (apply (tbl-all-mono2 EdgeRow (dne14 S n cs) (inx14 x rx cs) _ _ es (And.left (And.right (And.right p))) hin))
  (intros e he hie)
  (cases hb (Bool.and (Nat.beq (:kind e) ek-dep) (reach-mem (:debtor e) S)))
  (case [false] (simp only [dne14 hb Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [dne14 hb Bool.not_true Bool.false_or] at he) (simp only [dne14 hb Bool.not_true Bool.false_or])
    (apply (tbl-all-upd CompRow comp-id x (comp-make-idle vs) (dnk14 n cs (:creditor e) (:debtor e)) _ _ _ cs he))
    (intros k hk hkx)
    (cases hdx (Nat.beq x (:debtor e)))
    (case [false]
      (have hkx2 (= (Nat.beq (:id k) x) true)) (exact hkx)
      (have e1 := (Nat.eq_of_beq_eq_true hkx2))
      (have b1 (= (Nat.beq (:id (comp-make-idle vs k)) (:debtor e)) false)) (rw [(hid k)]) (rw [e1]) (exact hdx)
      (simp only [dnk14 b1 Bool.false_and Bool.not_false Bool.true_or]))
    (case [true]
      (have ed := (Nat.eq_of_beq_eq_true hdx))
      (simp only [Bool.and_eq_true] at hb)
      (have hie2 (= (tbl-all (rgt14 (:creditor e) rx) cs) true))
      (have kk (= (Bool.and (Nat.beq (:kind e) ek-dep) (Nat.beq (:debtor e) x)) true)) (rw [← ed]) (simp only [(And.left hb) Nat.beq_refl Bool.and_self])
      (simp only [inx14 kk Bool.not_true Bool.false_or] at hie) (exact hie)
      (have g := (rgt-upd x (:creditor e) rx (comp-make-idle vs) hid hrk cs hie2))
      (simp only [dnk14 comp-make-idle Bool.and_true])
      (cases hkd (Nat.beq (:id k) (:debtor e)))
      (case [false] (simp only [Bool.not_false Bool.true_or]))
      (case [true]
        (simp only [Bool.not_true Bool.false_or])
        (apply (tbl-all-mono Valid (vent14 n rx cs) _ _ vs hvs))
        (intros u hu)
        (have pu := (vent14-parts n rx cs u hu))
        (have s1 (= (Nat.beq (:stamp u) n) true)) (rw [(And.left pu)]) (exact (Nat.beq_refl n))
        (simp only [dnu14 s1 Bool.true_and])
        (rw [(And.left (And.right pu))]) (exact g)))
    (intros k hk hkx)
    (cases hb2 (Bool.and (Nat.beq (:id k) (:debtor e)) (:idle k)))
    (case [false] (simp only [dnk14 hb2 Bool.not_false Bool.true_or]))
    (case [true]
      (simp only [dnk14 hb2 Bool.not_true Bool.false_or] at hk) (simp only [dnk14 hb2 Bool.not_true Bool.false_or])
      (apply (tbl-all-mono Valid (dnu14 n cs (:creditor e)) _ _ (:validity k) hk))
      (intros u hu)
      (simp only [dnu14 Bool.and_eq_true] at hu)
      (simp only [dnu14 (And.left hu) (rgt-upd x (:creditor e) (:crank u) (comp-make-idle vs) hid hrk cs (And.right hu)) Bool.and_self])))
  (have i4 (= (tbl-all (dep-active (tbl-upd comp-id x (comp-make-idle vs) cs)) es) true))
  (apply (tbl-all-mono2 EdgeRow (dep-active cs) (ncd14 x) _ _ es (And.right (And.right (And.right p))) hn))
  (intros e he hne)
  (cases hk (Nat.beq (:kind e) ek-dep))
  (case [false] (simp only [dep-active hk Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [dep-active hk Bool.not_true Bool.false_or] at he) (simp only [dep-active hk Bool.not_true Bool.false_or])
    (simp only [ncd14 hk Bool.not_true Bool.false_or] at hne)
    (have hne2 := (bnot-true _ hne))
    (have a := (awake-upd-other x (:creditor e) (comp-make-idle vs) hid cs hne2 he)) (simp only [awake] at a) (exact a))
  (exact (vrk-intro S R _ es n i1 i2 i3 i4)))

;; ---- rows with a given id (unique ids)
(a/theorem not-has-all [x :- Nat, P :- (=> CompRow Bool), cs :- (List CompRow)]
  (=> (= (tbl-has comp-id x cs) false) (= (tbl-all (same-id-then comp-id x P) cs) true))
  (induction cs)
  (case [nil] (intro h) (simp only [tbl-all]))
  (case [cons hd t ih]
    (intro h)
    (cases hb (Nat.beq (comp-id hd) x))
    (case [true] (simp only [tbl-has hb] at h) (cases h))
    (case [false] (simp only [tbl-has hb] at h) (simp only [tbl-all same-id-then hb (ih h) Bool.not_false Bool.true_or Bool.and_self]))))
(a/theorem same-all [w :- World, x :- Nat, c :- CompRow, P :- (=> CompRow Bool)]
  (=> (= (inv-sample w) true) (= (comp-find w x) (Option.some CompRow c)) (= (P c) true) (= (tbl-all (same-id-then comp-id x P) (:comps w)) true))
  (intros hs hf hp)
  (have mc := (tbl-find-mem CompRow comp-id x c (:comps w) hf))
  (have hid := (tbl-find-id CompRow comp-id x c (:comps w) hf))
  (have z := (uniq-all CompRow comp-id P c (:comps w) (comps-nodup w hs) mc hp))
  (rw [hid] at z) (exact z))
(a/theorem crank-comp-rank [w :- World, x :- Nat] (= (crank-of w x) (comp-rank w x)) (rfl))
(a/defn rk-is [r :- Nat, k :- CompRow] Bool (Nat.beq (:rank k) r))
(a/defn rlt-q [r :- Nat, k :- CompRow] Bool (Nat.blt (:rank k) r))
(a/defn rgt-q [r :- Nat, k :- CompRow] Bool (Nat.blt r (:rank k)))
(a/defn false-q [k :- CompRow] Bool false)

(a/theorem xr-of [w :- World, x :- Nat] (=> (= (inv-sample w) true) (= (tbl-all (xr14 x (comp-rank w x)) (:comps w)) true))
  (intro hs)
  (cases hf (comp-find w x)) (case' [some c]) (case' [none])
  (have z := (not-has-all x (rk-is 0) (:comps w) (tbl-find-none-has CompRow comp-id x (:comps w) hf)))
  (apply (tbl-all-mono CompRow _ _ _ (:comps w) z))
  (intros k hk) (simp only [same-id-then rk-is comp-id] at hk) (simp only [xr14 comp-rank hf]) (exact hk)
  (have z := (same-all w x c (rk-is (:rank c)) hs hf (Nat.beq_refl (:rank c))))
  (apply (tbl-all-mono CompRow _ _ _ (:comps w) z))
  (intros k hk) (simp only [same-id-then rk-is comp-id] at hk) (simp only [xr14 comp-rank hf]) (exact hk))
(a/theorem rlt-of [w :- World, d :- Nat, r :- Nat]
  (=> (= (inv-sample w) true) (= (Bool.or (Bool.not (comp-has w d)) (Nat.blt (comp-rank w d) r)) true) (= (tbl-all (rlt14 d r) (:comps w)) true))
  (intros hs h)
  (cases hf (comp-find w d)) (case' [some c]) (case' [none])
  (have z := (not-has-all d false-q (:comps w) (tbl-find-none-has CompRow comp-id d (:comps w) hf)))
  (apply (tbl-all-mono CompRow _ _ _ (:comps w) z))
  (intros k hk)
  (cases hb (Nat.beq (:id k) d)) (case [false] (simp only [rlt14 hb Bool.not_false Bool.true_or])) (case [true] (simp only [same-id-then false-q comp-id hb Bool.not_true Bool.false_or] at hk) (cases hk))
  (have hc (= (comp-has w d) true)) (simp only [comp-has]) (exact (tbl-find-has CompRow comp-id d c (:comps w) hf))
  (simp only [hc comp-rank hf Bool.not_true Bool.false_or] at h)
  (have z := (same-all w d c (rlt-q r) hs hf h))
  (apply (tbl-all-mono CompRow _ _ _ (:comps w) z))
  (intros k hk) (simp only [same-id-then rlt-q comp-id] at hk) (simp only [rlt14]) (exact hk))
(a/theorem rgt-of [w :- World, y :- Nat, r :- Nat]
  (=> (= (inv-sample w) true) (= (Bool.or (Bool.not (comp-has w y)) (Nat.blt r (comp-rank w y))) true) (= (tbl-all (rgt14 y r) (:comps w)) true))
  (intros hs h)
  (cases hf (comp-find w y)) (case' [some c]) (case' [none])
  (have z := (not-has-all y false-q (:comps w) (tbl-find-none-has CompRow comp-id y (:comps w) hf)))
  (apply (tbl-all-mono CompRow _ _ _ (:comps w) z))
  (intros k hk)
  (cases hb (Nat.beq (:id k) y)) (case [false] (simp only [rgt14 hb Bool.not_false Bool.true_or])) (case [true] (simp only [same-id-then false-q comp-id hb Bool.not_true Bool.false_or] at hk) (cases hk))
  (have hc (= (comp-has w y) true)) (simp only [comp-has]) (exact (tbl-find-has CompRow comp-id y c (:comps w) hf))
  (simp only [hc comp-rank hf Bool.not_true Bool.false_or] at h)
  (have z := (same-all w y c (rgt-q r) hs hf h))
  (apply (tbl-all-mono CompRow _ _ _ (:comps w) z))
  (intros k hk) (simp only [same-id-then rgt-q comp-id] at hk) (simp only [rgt14]) (exact hk))
(a/theorem zero-rlt [w :- World, r :- Nat] (=> (= (inv-sample w) true) (= (tbl-all (rlt14 0 r) (:comps w)) true))
  (intro hs)
  (apply (rlt-of w 0 r hs))
  (have z := (comp-has-zero w hs)) (simp only [comp-has] ) (simp only [z Bool.not_false Bool.true_or]))
(a/theorem zero-vdn [w :- World, n :- Nat, r :- Nat] (=> (= (inv-sample w) true) (= (tbl-all (vdn14 n 0 r) (:comps w)) true))
  (intro hs)
  (have z := (not-has-all 0 false-q (:comps w) (comp-has-zero w hs)))
  (apply (tbl-all-mono CompRow _ _ _ (:comps w) z))
  (intros k hk)
  (cases hb (Nat.beq (:id k) 0)) (case [false] (simp only [vdn14 hb Bool.false_and Bool.not_false Bool.true_or])) (case [true] (simp only [same-id-then false-q comp-id hb Bool.not_true Bool.false_or] at hk) (cases hk)))

(a/theorem dcl-xr14 [x :- Nat, r :- Nat] (dcl14 (xr14 x r))
  (intros k c hd hc) (simp only [xr14]) (rw [(And.left hd)]) (rw [(And.left (And.right hd))]) (exact hc))
(a/theorem dcl-rlt14 [d :- Nat, r :- Nat] (dcl14 (rlt14 d r))
  (intros k c hd hc) (simp only [rlt14]) (rw [(And.left hd)]) (rw [(And.left (And.right hd))]) (exact hc))
(a/theorem dcl-vdn14 [n :- Nat, d :- Nat, r :- Nat] (dcl14 (vdn14 n d r))
  (intros k c hd hc)
  (cases hi (:idle k))
  (case [false] (simp only [vdn14 hi Bool.and_false Bool.not_false Bool.true_or]))
  (case [true]
    (have q := (dom14-idle k c hd hi))
    (simp only [vdn14 (And.left q) Bool.and_true] at hc)
    (simp only [vdn14 hi Bool.and_true]) (rw [(And.left hd)]) (rw [(And.right q)]) (exact hc)))
(a/theorem vent-pres [n :- Nat, rx :- Nat, cs :- (List CompRow), cs2 :- (List CompRow), v :- Valid]
  (=> (cpres cs cs2) (= (vent14 n rx cs v) true) (= (vent14 n rx cs2 v) true))
  (intros hp h)
  (simp only [vent14 Bool.and_eq_true] at h) (simp only [vent14 Bool.and_eq_true])
  (exact (And.intro (And.left h) (And.intro (And.left (And.right h))
           (And.intro (hp (rlt14 (:debtor v) rx) (dcl-rlt14 (:debtor v) rx) (And.left (And.right (And.right h))))
                      (hp (vdn14 n (:debtor v) rx) (dcl-vdn14 n (:debtor v) rx) (And.right (And.right (And.right h)))))))))

;; ---- membership in filters and validity lists
(a/theorem mem-filter14 [A :- Type, p :- (=> A Bool), x :- A, xs :- (List A)]
  (=> (List.Mem x (tbl-filter p xs)) (And (List.Mem x xs) (= (p x) true)))
  (induction xs)
  (case [nil] (intro h) (simp only [tbl-filter] at h) (cases h))
  (case [cons hd t ih]
    (intro h)
    (cases hq (p hd))
    (case [false] (simp only [tbl-filter hq] at h) (have z := (ih h)) (exact (And.intro (List.Mem.tail hd (And.left z)) (And.right z))))
    (case [true]
      (simp only [tbl-filter hq] at h)
      (cases h)
      (case [head] (exact (And.intro (List.Mem.head t) hq)))
      (case [tail b] (have z := (ih b)) (exact (And.intro (List.Mem.tail hd (And.left z)) (And.right z)))))))
(a/theorem valid-list-all [w :- World, Q :- (=> Valid Bool), es :- (List EdgeRow)]
  (=> (forall [e :- EdgeRow] (=> (List.Mem e es) (= (Q (edge-valid w e)) true))) (= (tbl-all Q (valid-list w es)) true))
  (induction es)
  (case [nil] (intro h) (simp only [valid-list tbl-all]))
  (case [cons hd t ih]
    (intro h)
    (have a1 := (h hd (List.Mem.head t)))
    (have a2 := (ih (fn [e :- EdgeRow, m :- (List.Mem e t)] (h e (List.Mem.tail hd m)))))
    (simp only [valid-list tbl-all a1 a2 Bool.and_self])))

;; ---- the entries recorded at the demotion of x
(a/theorem edge-ok-mem [w :- World, e :- EdgeRow]
  (=> (= (inv-sample w) true) (List.Mem e (:edges w)) (= (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w) e) true))
  (intros hs hm)
  (exact (tbl-all-mem EdgeRow (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w)) e (:edges w)
           (And.left (And.right (inv-parts w hs))) hm)))
(a/theorem dep-cred-has [w :- World, e :- EdgeRow]
  (=> (= (inv-sample w) true) (List.Mem e (:edges w)) (= (Nat.beq (:kind e) ek-dep) true) (= (comp-has w (:creditor e)) true))
  (intros hs hm hk)
  (have ho := (edge-ok-mem w e hs hm))
  (simp only [edge-ok cred-ok hk Bool.and_eq_true] at ho)
  (simp only [comp-has]) (exact (And.left ho)))

(a/theorem vent-edge [S :- (List Nat), R :- (List Nat), w :- World, x :- Nat, e :- EdgeRow]
  (=> (= (vr S (List.cons Nat x R) w) true) (= (ranks-ok w) true) (List.Mem e (:edges w)) (= (dep-of x e) true)
      (= (vent14 (:next-id w) (comp-rank w x) (:comps w) (edge-valid w e)) true))
  (intros h hr hm hd)
  (have hs := (vr-sample _ _ w h))
  (have p := (vrk-parts _ _ _ _ _ (vr-rest-of _ _ w h)))
  (simp only [dep-of Bool.and_eq_true] at hd)
  (have hk := (And.left hd))
  (have ec := (Nat.eq_of_beq_eq_true (And.right hd)))
  (have hcx0 := (dep-cred-has w e hs hm hk))
  (have hcx (= (comp-has w x) true)) (rw [← ec]) (exact hcx0)
  (have cr (= (crank-of w (:creditor e)) (comp-rank w x))) (exact (Eq.trans (congrArg (fn [z :- Nat] (crank-of w z)) ec) (crank-comp-rank w x)))
  (cases hsn (:has-seen e))
  (case [false]
    (simp only [edge-valid hsn vent14 Nat.beq_refl Bool.true_and])
    (rw [cr]) (simp only [Nat.beq_refl Bool.true_and (zero-rlt w (comp-rank w x) hs) (zero-vdn w (:next-id w) (comp-rank w x) hs) Bool.and_self]))
  (case [true]
    (simp only [edge-valid hsn vent14 Nat.beq_refl Bool.true_and])
    (rw [cr])
    (simp only [Nat.beq_refl Bool.true_and])
    (have ro := (tbl-all-mem EdgeRow (rank-edge-ok w) e (:edges w) hr hm))
    (simp only [rank-edge-ok hk Bool.not_true Bool.false_or] at ro)
    (rw [ec] at ro) (simp only [hcx Bool.not_true Bool.false_or] at ro)
    (have r1 (= (Bool.or (Bool.not (comp-has w (:debtor e))) (Nat.blt (comp-rank w (:debtor e)) (comp-rank w x))) true))
    (cases hd2 (comp-has w (:debtor e)))
    (case [false] (simp only [Bool.not_false Bool.true_or]))
    (case [true] (simp only [hd2 Bool.or_false Bool.not_true Bool.false_or] at ro) (simp only [Bool.not_true Bool.false_or]) (exact ro))
    (have a1 := (rlt-of w (:debtor e) (comp-rank w x) hs r1))
    (have db := (tbl-all-mem EdgeRow (dnb14 S (List.cons Nat x R) (:comps w)) e (:edges w) (And.left (And.right p)) hm))
    (simp only [dnb14 hk Bool.not_true Bool.false_or Bool.and_eq_true Bool.or_eq_true] at db)
    (have a2 (= (tbl-all (vdn14 (:next-id w) (:debtor e) (comp-rank w x)) (:comps w)) true))
    (have dz := (And.left db))
    (cases dz)
    (case [inr aw]
      (simp only [awake] at aw)
      (apply (tbl-all-mono CompRow (not-idle-if-id (:debtor e)) _ _ (:comps w) aw))
      (intros q hq)
      (cases hb (Nat.beq (:id q) (:debtor e)))
      (case [false] (simp only [vdn14 hb Bool.false_and Bool.not_false Bool.true_or]))
      (case [true] (simp only [not-idle-if-id hb Bool.not_true Bool.false_or] at hq) (have hq2 := (bnot-true _ hq))
        (simp only [vdn14 hb hq2 Bool.and_false Bool.not_false Bool.true_or])))
    (case [inl ins]
      (have dn := (tbl-all-mem EdgeRow (dne14 S (:next-id w) (:comps w)) e (:edges w) (And.left (And.right (And.right p))) hm))
      (have kk (= (Bool.and (Nat.beq (:kind e) ek-dep) (reach-mem (:debtor e) S)) true)) (simp only [hk ins Bool.and_self])
      (simp only [dne14 kk Bool.not_true Bool.false_or] at dn)
      (rw [ec] at dn)
      (cases hf (comp-find w x)) (case' [some cx]) (case' [none])
      (simp only [comp-has] at hcx) (have z := (tbl-find-none-has CompRow comp-id x (:comps w) hf)) (rw [z] at hcx) (cases hcx)
      (have mx := (tbl-find-mem CompRow comp-id x cx (:comps w) hf))
      (have ix := (tbl-find-id CompRow comp-id x cx (:comps w) hf))
      (have rx (= (comp-rank w x) (:rank cx))) (simp only [comp-rank hf])
      (rw [rx])
      (apply (tbl-all-mono CompRow (dnk14 (:next-id w) (:comps w) x (:debtor e)) _ _ (:comps w) dn))
      (intros q hq)
      (cases hb (Bool.and (Nat.beq (:id q) (:debtor e)) (:idle q)))
      (case [false] (simp only [vdn14 hb Bool.not_false Bool.true_or]))
      (case [true]
        (simp only [dnk14 hb Bool.not_true Bool.false_or] at hq) (simp only [vdn14 hb Bool.not_true Bool.false_or])
        (apply (tbl-all-mono Valid (dnu14 (:next-id w) (:comps w) x) _ _ (:validity q) hq))
        (intros u hu)
        (simp only [dnu14 Bool.and_eq_true] at hu)
        (have g := (tbl-all-mem CompRow (rgt14 x (:crank u)) cx (:comps w) (And.right hu) mx))
        (have ix2 (= (Nat.beq (:id cx) x) true)) (simp only [Nat.beq_eq]) (exact ix)
        (simp only [rgt14 ix2 Bool.not_true Bool.false_or] at g)
        (simp only [ulow14 (And.left hu) g Bool.and_self])))
    (simp only [a1 a2 Bool.and_self])))

(a/theorem vent-all [S :- (List Nat), R :- (List Nat), w :- World, x :- Nat]
  (=> (= (vr S (List.cons Nat x R) w) true) (= (ranks-ok w) true)
      (= (tbl-all (vent14 (:next-id w) (comp-rank w x) (:comps w)) (validity-of w x)) true))
  (intros h hr)
  (simp only [validity-of])
  (apply (valid-list-all w (vent14 (:next-id w) (comp-rank w x) (:comps w)) (tbl-filter (dep-of x) (:edges w))))
  (intros e hm)
  (have z := (mem-filter14 EdgeRow (dep-of x) e (:edges w) hm))
  (exact (vent-edge S R w x e h hr (And.left z) (And.right z))))

;; ---- no dep edge of x (x missing, idle, or its dep edges dropped)
(a/theorem vr-drop-r [S :- (List Nat), R :- (List Nat), w :- World, x :- Nat]
  (=> (= (tbl-all (ncd14 x) (:edges w)) true) (= (vr S (List.cons Nat x R) w) true) (= (vr S R w) true))
  (intros hn h)
  (have p := (vrk-parts _ _ _ _ _ (vr-rest-of _ _ w h)))
  (have i2 (= (tbl-all (dnb14 S R (:comps w)) (:edges w)) true))
  (apply (tbl-all-mono2 EdgeRow (dnb14 S (List.cons Nat x R) (:comps w)) (ncd14 x) _ _ (:edges w) (And.left (And.right p)) hn))
  (intros e he hne)
  (cases hk (Nat.beq (:kind e) ek-dep))
  (case [false] (simp only [dnb14 hk Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [dnb14 hk Bool.not_true Bool.false_or Bool.and_eq_true] at he) (simp only [dnb14 hk Bool.not_true Bool.false_or Bool.and_eq_true])
    (simp only [ncd14 hk Bool.not_true Bool.false_or] at hne)
    (have hne2 := (bnot-true _ hne))
    (have r2 := (And.right he)) (simp only [reach-mem hne2] at r2)
    (exact (And.intro (And.left he) r2)))
  (exact (vr-intro S R w (vr-sample _ _ w h) (vrk-intro S R _ _ _ (And.left p) i2 (And.left (And.right (And.right p))) (And.right (And.right (And.right p)))))))
(a/theorem ncd-none [w :- World, x :- Nat]
  (=> (= (inv-sample w) true) (= (comp-find w x) (Option.none CompRow)) (= (tbl-all (ncd14 x) (:edges w)) true))
  (intros hs hf)
  (have z := (tbl-find-none-has CompRow comp-id x (:comps w) hf))
  (apply (all-of-mem EdgeRow (ncd14 x) (:edges w)))
  (intros e hm)
  (cases hk (Nat.beq (:kind e) ek-dep))
  (case [false] (simp only [ncd14 hk Bool.not_false Bool.true_or]))
  (case [true]
    (have hc := (dep-cred-has w e hs hm hk))
    (cases hb (Nat.beq (:creditor e) x))
    (case [false] (simp only [ncd14 hb Bool.not_false Bool.or_true]))
    (case [true] (have eb := (Nat.eq_of_beq_eq_true hb)) (simp only [comp-has] at hc) (rw [eb] at hc) (rw [z] at hc) (cases hc))))
(a/theorem ncd-idle [S :- (List Nat), R :- (List Nat), w :- World, x :- Nat, c :- CompRow]
  (=> (= (vr S R w) true) (= (comp-find w x) (Option.some CompRow c)) (= (:idle c) true) (= (tbl-all (ncd14 x) (:edges w)) true))
  (intros h hf hi)
  (have p := (vrk-parts _ _ _ _ _ (vr-rest-of _ _ w h)))
  (have mc := (tbl-find-mem CompRow comp-id x c (:comps w) hf))
  (have ic := (tbl-find-id CompRow comp-id x c (:comps w) hf))
  (apply (tbl-all-mono EdgeRow (dep-active (:comps w)) (ncd14 x) _ (:edges w) (And.right (And.right (And.right p)))))
  (intros e he)
  (cases hk (Nat.beq (:kind e) ek-dep))
  (case [false] (simp only [ncd14 hk Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [dep-active hk Bool.not_true Bool.false_or] at he)
    (cases hb (Nat.beq (:creditor e) x))
    (case [false] (simp only [ncd14 hb Bool.not_false Bool.or_true]))
    (case [true]
      (have eb := (Nat.eq_of_beq_eq_true hb)) (rw [eb] at he)
      (have z := (tbl-all-mem CompRow (not-idle-if-id x) c (:comps w) he mc))
      (have ic2 (= (Nat.beq (:id c) x) true)) (simp only [Nat.beq_eq]) (exact ic)
      (simp only [not-idle-if-id ic2 hi Bool.not_true Bool.false_or] at z) (cases z))))
(a/theorem ncd-drop [w :- World, x :- Nat] (= (tbl-all (ncd14 x) (:edges (drop-edges w (not-dep-of x)))) true)
  (simp only [drop-edges set-comps set-edges])
  (apply (tbl-all-mono EdgeRow (not-dep-of x) (ncd14 x) _ _ (tbl-all-filter-self EdgeRow (not-dep-of x) (:edges w))))
  (intros e he)
  (cases hk (Nat.beq (:kind e) ek-dep))
  (case [false] (simp only [ncd14 hk Bool.not_false Bool.true_or]))
  (case [true] (simp only [not-dep-of dep-of hk Bool.true_and] at he) (simp only [ncd14 hk he Bool.not_true Bool.false_or])))

;; edges on x: their creditors rank above x
(a/theorem inx-of [w :- World, x :- Nat, rx :- Nat, c :- CompRow]
  (=> (= (inv-sample w) true) (= (ranks-ok w) true) (= (comp-find w x) (Option.some CompRow c)) (= (:rank c) rx)
      (= (tbl-all (inx14 x rx (:comps w)) (:edges w)) true))
  (intros hs hr hf hrx)
  (have hcx (= (comp-has w x) true)) (simp only [comp-has]) (exact (tbl-find-has CompRow comp-id x c (:comps w) hf))
  (have crx (= (comp-rank w x) rx)) (simp only [comp-rank hf]) (exact hrx)
  (apply (tbl-all-mono EdgeRow (rank-edge-ok w) (inx14 x rx (:comps w)) _ (:edges w) hr))
  (intros e he)
  (cases hb (Bool.and (Nat.beq (:kind e) ek-dep) (Nat.beq (:debtor e) x)))
  (case [false] (simp only [inx14 hb Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [inx14 hb Bool.not_true Bool.false_or])
    (simp only [Bool.and_eq_true] at hb)
    (have ed := (Nat.eq_of_beq_eq_true (And.right hb)))
    (simp only [rank-edge-ok (And.left hb) Bool.not_true Bool.false_or] at he)
    (rw [ed] at he) (simp only [hcx crx Bool.not_true Bool.false_or] at he)
    (apply (rgt-of w (:creditor e) rx hs))
    (cases hy (comp-has w (:creditor e)))
    (case [false] (simp only [Bool.not_false Bool.true_or]))
    (case [true] (simp only [hy Bool.not_true Bool.false_or] at he) (simp only [Bool.not_true Bool.false_or]) (exact he))))

(lcopy! VR 'inv-run-cascade)
(lcopy! VR 'inv-demote-epoch)
(lcopy! VR 'inv-detach)

;; the demotion's last part on the epoch-stepped world W2 (W3 = W2 without x's dep edges)
(a/theorem vr-demote-tail [S :- (List Nat), R :- (List Nat), W2 :- World, x :- Nat]
  (=> (= (reach-mem x S) true) (= (vr S (List.cons Nat x R) W2) true) (= (inv-rank W2) true)
      (= (vr S R (drop-edges W2 (not-dep-of x))) true) (= (inv-rank (drop-edges W2 (not-dep-of x))) true)
      (= (vr S R (demote-finish (drop-edges W2 (not-dep-of x)) x (validity-of W2 x))) true))
  (intros hx h2 k2 h3 k3)
  (have hs2 := (rk-sample W2 k2))
  (have hs3 := (rk-sample _ k3))
  (cases hf3 (comp-find (drop-edges W2 (not-dep-of x)) x)) (case' [some c3]) (case' [none])
  (simp only [demote-finish hf3]) (exact h3)
  (cases hkp (demote-keep (drop-edges W2 (not-dep-of x)) c3))
  (simp only [demote-finish hf3 hkp])
  (exact (vr-comp-del-unref S R _ x (drop-edges-avoids (drop-edges W2 (not-dep-of x)) x)
           (vr-drop-edges S R (drop-edges W2 (not-dep-of x)) (edge-avoids x) h3)))
  (simp only [demote-finish hf3 hkp])
  (have hxr := (cpres-resync (tbl-filter (not-dep-of x) (:edges W2)) (:comps W2) (xr14 x (comp-rank W2 x)) (dcl-xr14 x (comp-rank W2 x)) (xr-of W2 x hs2)))
  (have hvs0 := (vent-all S R W2 x h2 (rk-ranks W2 k2)))
  (have hvs := (tbl-all-mono Valid (vent14 (:next-id W2) (comp-rank W2 x) (:comps W2)) (vent14 (:next-id W2) (comp-rank W2 x) (comps-resync (tbl-filter (not-dep-of x) (:edges W2)) (:comps W2)))
                 (fn [v :- Valid, hv :- (= (vent14 (:next-id W2) (comp-rank W2 x) (:comps W2) v) true)]
                   (vent-pres (:next-id W2) (comp-rank W2 x) (:comps W2) _ v (cpres-resync (tbl-filter (not-dep-of x) (:edges W2)) (:comps W2)) hv))
                 (validity-of W2 x) hvs0))
  (have mc3 := (tbl-find-mem CompRow comp-id x c3 _ hf3))
  (have ic3 := (tbl-find-id CompRow comp-id x c3 _ hf3))
  (have xc3 := (tbl-all-mem CompRow (xr14 x (comp-rank W2 x)) c3 _ hxr mc3))
  (have ic32 (= (Nat.beq (:id c3) x) true)) (simp only [Nat.beq_eq]) (exact ic3)
  (simp only [xr14 ic32 Bool.not_true Bool.false_or] at xc3)
  (have rc3 := (Nat.eq_of_beq_eq_true xc3))
  (have hin := (inx-of (drop-edges W2 (not-dep-of x)) x (comp-rank W2 x) c3 hs3 (rk-ranks _ k3) hf3 rc3))
  (have r (= (vr-rest S R (comp-upd (drop-edges W2 (not-dep-of x)) x (comp-make-idle (validity-of W2 x)))) true))
  (exact (vrk-make-idle S R _ _ _ x (comp-rank W2 x) (validity-of W2 x) (vr-rest-of S R _ h3) hx (ncd-drop W2 x) hxr hvs hin))
  (exact (vr-intro S R _ (inv-comp-upd _ x (comp-make-idle (validity-of W2 x)) (comp-make-idle-id (validity-of W2 x)) (comp-make-idle-pending (validity-of W2 x)) hs3) r)))

;; Theorem (one demotion of a stray x of the pass): x leaves the creditors to come
(a/theorem vr-demote [S :- (List Nat), R :- (List Nat), w :- World, x :- Nat]
  (=> (= (reach-mem x S) true) (= (inv-rank w) true) (= (vr S (List.cons Nat x R) w) true) (= (vr S R (demote w x)) true))
  (intros hx hk h)
  (have hs := (vr-sample _ _ w h))
  (cases hf (comp-find w x)) (case' [some c]) (case' [none])
  (simp only [demote hf]) (exact (vr-drop-r S R w x (ncd-none w x hs hf) h))
  (cases hi (:idle c))
  (case' [true])
  (simp only [demote hf hi]) (exact (vr-drop-r S R w x (ncd-idle S (List.cons Nat x R) w x c h hf hi) h))
  (simp only [demote hf hi demote-edges])
  (have h1 := (vr-run-cascade S (List.cons Nat x R) w (cancel-jobs (demote-cancels w c)) h))
  (have k1 := (rk-run-cascade w (cancel-jobs (demote-cancels w c)) hk))
  (have h2 := (vr-demote-epoch S (List.cons Nat x R) (run-cascade w (cancel-jobs (demote-cancels w c))) x (demote-cur w c) h1))
  (have k2 := (rk-demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) x (demote-cur w c) k1))
  (have h3a := (vr-drop-edges S (List.cons Nat x R) (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) x (demote-cur w c)) (not-dep-of x) h2))
  (have h3 := (vr-drop-r S R (drop-edges (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) x (demote-cur w c)) (not-dep-of x)) x
                (ncd-drop (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) x (demote-cur w c)) x) h3a))
  (have k3 := (rk-drop-edges (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) x (demote-cur w c)) (not-dep-of x) k2))
  (exact (vr-demote-tail S R (demote-epoch (run-cascade w (cancel-jobs (demote-cancels w c))) x (demote-cur w c)) x hx h2 k2 h3 k3)))

;; ---- a normalization round: the strays of the round are the exemption list
(a/theorem vr-pass-start [w :- World]
  (=> (= (vr (List.nil Nat) (List.nil Nat) w) true)
      (= (vr (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) w) true))
  (intro h)
  (have hs := (vr-sample _ _ w h))
  (have p := (vrk-parts _ _ _ _ _ (vr-rest-of _ _ w h)))
  (have i2 (= (tbl-all (dnb14 (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (:comps w)) (:edges w)) true))
  (apply (all-of-mem EdgeRow _ (:edges w)))
  (intros e hm)
  (have d0 := (tbl-all-mem EdgeRow (dnb14 (List.nil Nat) (List.nil Nat) (:comps w)) e (:edges w) (And.left (And.right p)) hm))
  (have da := (tbl-all-mem EdgeRow (dep-active (:comps w)) e (:edges w) (And.right (And.right (And.right p))) hm))
  (cases hk (Nat.beq (:kind e) ek-dep))
  (case [false] (simp only [dnb14 hk Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [dnb14 hk reach-mem Bool.not_true Bool.false_or Bool.not_false Bool.true_or Bool.and_true] at d0)
    (simp only [dep-active hk Bool.not_true Bool.false_or] at da)
    (simp only [dnb14 hk d0 Bool.not_true Bool.false_or Bool.or_true Bool.true_and])
    (cases hd (reach-mem (:debtor e) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w))))
    (case [false] (simp only [Bool.not_false Bool.true_or]))
    (case [true]
      (simp only [Bool.not_true Bool.false_or])
      (have sf := (scan-mem-find CompRow comp-id (comp-stray (live-list w)) (:debtor e) (:comps w) hd (comps-nodup w hs)))
      (cases hfd (comp-find w (:debtor e))) (case' [some cd]) (case' [none])
      (simp only [comp-find] at hfd) (rw [hfd] at sf) (simp only [opt-test] at sf) (cases sf)
      (simp only [comp-find] at hfd) (rw [hfd] at sf) (simp only [opt-test comp-stray] at sf)
      (have z0 := (bnot-true _ sf)) (simp only [comp-norm] at z0)
      (have icd := (tbl-find-id CompRow comp-id (:debtor e) cd (:comps w) hfd))
      (have icd2 (= (:id cd) (:debtor e))) (exact icd)
      (have ld (= (reach-mem (:debtor e) (live-list w)) false))
      (cases hz (reach-mem (:debtor e) (live-list w)))
      (case [false] (rfl))
      (case [true] (rw [← icd2] at hz) (simp only [hz Bool.or_true] at z0) (cases z0))
      (have hcy := (dep-cred-has w e hs hm hk))
      (cases hfy (comp-find w (:creditor e))) (case' [some cy]) (case' [none])
      (simp only [comp-has comp-find] at hcy hfy) (rw [(tbl-find-none-has CompRow comp-id (:creditor e) (:comps w) hfy)] at hcy) (cases hcy)
      (have my := (tbl-find-mem CompRow comp-id (:creditor e) cy (:comps w) hfy))
      (have iy := (tbl-find-id CompRow comp-id (:creditor e) cy (:comps w) hfy))
      (have iy2 (= (:id cy) (:creditor e))) (exact iy)
      (have yi := (tbl-all-mem CompRow (not-idle-if-id (:creditor e)) cy (:comps w) da my))
      (have iy3 (= (Nat.beq (:id cy) (:creditor e)) true)) (simp only [Nat.beq_eq]) (exact iy2)
      (simp only [not-idle-if-id iy3 Bool.not_true Bool.false_or] at yi)
      (have yi2 := (bnot-true _ yi))
      (have ly (= (reach-mem (:creditor e) (live-list w)) false))
      (cases hl (reach-mem (:creditor e) (live-list w)))
      (case [false] (rfl))
      (case [true]
        (exfalso)
        (have dep (= (dep-of (:id cy) e) true)) (simp only [dep-of hk Bool.true_and]) (rw [beq-comm]) (exact iy3)
        (have hl2 (= (in-live w (:id cy)) true)) (simp only [in-live]) (rw [iy2]) (exact hl)
        (have el := (live-close w (:id cy) (:id e) hl2 (succ-dep w cy e my yi2 hm dep)))
        (have dl := (live-close w (:id e) (:debtor e) el (succ-edge w e hm (deb-nz w e hs hm))))
        (simp only [in-live] at dl) (rw [ld] at dl) (cases dl))
      (have st (= (comp-stray (live-list w) cy) true)) (simp only [comp-stray comp-norm yi2 Bool.false_or]) (rw [iy2]) (rw [ly])
      (have sc := (scan-mem CompRow comp-id (comp-stray (live-list w)) cy (:comps w) my st))
      (have iy4 (= (comp-id cy) (:creditor e))) (exact iy2)
      (rw [iy4] at sc) (exact sc)))
  (have i3 (= (tbl-all (dne14 (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (:next-id w) (:comps w)) (:edges w)) true))
  (apply (tbl-all-mono EdgeRow (dnb14 (List.nil Nat) (List.nil Nat) (:comps w)) _ _ (:edges w) (And.left (And.right p))))
  (intros e he)
  (cases hk (Nat.beq (:kind e) ek-dep))
  (case [false] (simp only [dne14 hk Bool.false_and Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [dnb14 hk reach-mem Bool.not_true Bool.false_or Bool.not_false Bool.true_or Bool.and_true] at he)
    (simp only [awake] at he)
    (cases hb (Bool.and (Nat.beq (:kind e) ek-dep) (reach-mem (:debtor e) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)))))
    (case [false] (simp only [dne14 hb Bool.not_false Bool.true_or]))
    (case [true]
      (simp only [dne14 hb Bool.not_true Bool.false_or])
      (apply (tbl-all-mono CompRow (not-idle-if-id (:debtor e)) _ _ (:comps w) he))
      (intros k hk2)
      (cases hb2 (Bool.and (Nat.beq (:id k) (:debtor e)) (:idle k)))
      (case [false] (simp only [dnk14 hb2 Bool.not_false Bool.true_or]))
      (case [true]
        (simp only [Bool.and_eq_true] at hb2)
        (simp only [not-idle-if-id (And.left hb2) (And.right hb2) Bool.not_true Bool.false_or] at hk2) (cases hk2))))
  (exact (vr-intro _ _ w hs (vrk-intro _ _ _ _ _ (And.left p) i2 i3 (And.right (And.right (And.right p)))))))

(a/theorem vr-pass-end [S :- (List Nat), w :- World] (=> (= (vr S (List.nil Nat) w) true) (= (vr (List.nil Nat) (List.nil Nat) w) true))
  (intro h)
  (have p := (vrk-parts _ _ _ _ _ (vr-rest-of _ _ w h)))
  (have i2 (= (tbl-all (dnb14 (List.nil Nat) (List.nil Nat) (:comps w)) (:edges w)) true))
  (apply (tbl-all-mono EdgeRow (dnb14 S (List.nil Nat) (:comps w)) _ _ (:edges w) (And.left (And.right p))))
  (intros e he)
  (cases hk (Nat.beq (:kind e) ek-dep))
  (case [false] (simp only [dnb14 hk Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [dnb14 hk reach-mem Bool.not_true Bool.false_or Bool.or_false Bool.and_eq_true] at he)
    (simp only [dnb14 hk reach-mem Bool.not_true Bool.false_or Bool.not_false Bool.true_or Bool.and_true])
    (have a2 := (And.right he))
    (have nd := (bnot-true _ a2))
    (have a1 := (And.left he)) (simp only [nd Bool.false_or] at a1) (exact a1))
  (have i3 (= (tbl-all (dne14 (List.nil Nat) (:next-id w) (:comps w)) (:edges w)) true))
  (apply (all-of-mem EdgeRow _ (:edges w)))
  (intros e hm) (simp only [dne14 reach-mem Bool.and_false Bool.not_false Bool.true_or])
  (exact (vr-intro _ _ w (vr-sample _ _ w h) (vrk-intro _ _ _ _ _ (And.left p) i2 i3 (And.right (And.right (And.right p)))))))

(a/theorem vr-fold [S :- (List Nat), L :- (List Nat)]
  (forall [w :- World] (=> (= (tbl-all (rm-in S) L) true) (= (inv-rank w) true) (= (vr S L w) true)
                           (And (= (vr S (List.nil Nat) (nat-fold demote w L)) true) (= (inv-rank (nat-fold demote w L)) true))))
  (induction L)
  (case [nil] (intros w hl hk h) (simp only [nat-fold]) (exact (And.intro h hk)))
  (case [cons x t ih]
    (intros w hl hk h)
    (simp only [tbl-all Bool.and_eq_true] at hl)
    (have hx (= (reach-mem x S) true)) (exact (And.left hl))
    (simp only [nat-fold])
    (exact (ih (demote w x) (And.right hl) (rk-demote w x hk) (vr-demote S t w x hx hk h)))))

(a/theorem rm-in-scan [A :- Type, idf :- (=> A Nat), p :- (=> A Bool), xs :- (List A)] (= (tbl-all (rm-in (tbl-scan idf p xs)) (tbl-scan idf p xs)) true)
  (apply (all-of-mem-r (rm-in (tbl-scan idf p xs)) (tbl-scan idf p xs))) (intros y hy) (simp only [rm-in]) (exact hy))

;; Theorem (a normalization round keeps vr): the strays of the round demote among themselves
(a/theorem vr-norm-round [w :- World]
  (=> (= (inv-rank w) true) (= (vr (List.nil Nat) (List.nil Nat) w) true) (= (vr (List.nil Nat) (List.nil Nat) (norm-round w)) true))
  (intros hk h)
  (have h0 := (vr-pass-start w h))
  (have h1 := (vr-run-cascade _ _ w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w))) h0))
  (have k1 := (rk-run-cascade w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w))) hk))
  (have f := (vr-fold (tbl-scan comp-id (comp-stray (live-list w)) (:comps w)) (tbl-scan comp-id (comp-stray (live-list w)) (:comps w))
               (run-cascade w (cancel-jobs (tbl-scan run-id (run-stray (live-list w)) (:runs w)))) (rm-in-scan CompRow comp-id (comp-stray (live-list w)) (:comps w)) k1 h1))
  (simp only [norm-round norm-round-lv])
  (exact (vr-detach (List.nil Nat) (List.nil Nat) _ (vr-pass-end _ _ (And.left f)))))

(a/theorem vr-norm-loop [fuel :- (List Nat)]
  (forall [w :- World] (=> (= (inv-rank w) true) (= (vr (List.nil Nat) (List.nil Nat) w) true) (= (vr (List.nil Nat) (List.nil Nat) (norm-loop fuel w)) true)))
  (induction fuel)
  (case [nil] (intros w hk h) (simp only [norm-loop]) (exact h))
  (case [cons u f ih]
    (intros w hk h)
    (cases hn (normalized w))
    (case [false] (simp only [norm-loop hn]) (exact (ih (norm-round w) (rk-norm-round w hk) (vr-norm-round w hk h))))
    (case [true] (simp only [norm-loop hn]) (exact h))))
(a/theorem vr-normalize [w :- World]
  (=> (= (inv-rank w) true) (= (vr (List.nil Nat) (List.nil Nat) w) true) (= (vr (List.nil Nat) (List.nil Nat) (normalize w)) true))
  (intros hk h)
  (simp only [normalize])
  (exact (vr-norm-loop (norm-fuel (detach w)) (detach w) (rk-detach w hk) (vr-detach (List.nil Nat) (List.nil Nat) w h))))
(a/theorem vr-rule-r-round [w :- World]
  (=> (= (inv-rank w) true) (= (vr (List.nil Nat) (List.nil Nat) w) true) (= (filter-safe (normalize w)) true)
      (= (vr (List.nil Nat) (List.nil Nat) (rule-r-round w)) true))
  (intros hk h hf)
  (simp only [rule-r-round]) (rw [rule-r-filter-eq])
  (exact (vr-filter-world (List.nil Nat) (List.nil Nat) _ (keep-fn (normalize w)) (vr-normalize w hk h) hf)))
(a/theorem vr-rr-loop [fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (inv-rank w0) true) (= (vr (List.nil Nat) (List.nil Nat) w0) true) (= (rr-safe fuel w0) true)
                            (= (vr (List.nil Nat) (List.nil Nat) (rr-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 hk h hs) (simp only [rr-safe] at hs) (simp only [rr-loop]) (exact (vr-rule-r-round w0 hk h hs)))
  (case [cons x f ih]
    (intros w0 hk h hs)
    (simp only [rr-safe Bool.and_eq_true] at hs)
    (have h1 := (vr-rule-r-round w0 hk h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false] (simp only [ho] at hs) (simp only [rr-loop ho]) (exact (ih (rule-r-round w0) (rk-rule-r-round w0 hk (And.left hs)) h1 (And.right hs))))
    (case [true] (simp only [rr-loop ho]) (exact h1))))
(a/theorem vr-rule-r [w :- World]
  (=> (= (inv-rank w) true) (= (vr (List.nil Nat) (List.nil Nat) w) true) (= (rule-r-safe w) true) (= (vr (List.nil Nat) (List.nil Nat) (rule-r w)) true))
  (intros hk h hs) (simp only [rule-r-safe] at hs) (simp only [rule-r]) (exact (vr-rr-loop (rr-fuel w) w hk h hs)))

;; ===========================================================================
;; Part I. The step, the combined bundle, I14 as a theorem
;; ===========================================================================

(a/theorem dep-active-of-g7 [w :- World] (=> (= (g7 w) true) (= (tbl-all (dep-active (:comps w)) (:edges w)) true))
  (intro h)
  (have p := (g7k-parts _ _ _ (g7-rest-of w h)))
  (apply (tbl-all-mono EdgeRow (dm-one (:comps w)) (dep-active (:comps w)) _ (:edges w) (And.left (And.right p))))
  (intros e he)
  (cases hk (Nat.beq (:kind e) ek-dep))
  (case [false] (simp only [dep-active hk Bool.not_false Bool.true_or]))
  (case [true] (simp only [dm-one hk Bool.true_or Bool.not_true Bool.false_or] at he) (simp only [dep-active hk Bool.not_true Bool.false_or]) (exact he)))
(a/theorem vr-of-vq [xw :- (List Nat), xs :- Bool, w :- World]
  (=> (= (vq (List.nil Nat) xw xs w) true) (= (tbl-all (dep-active (:comps w)) (:edges w)) true) (= (vr (List.nil Nat) (List.nil Nat) w) true))
  (intros h hd)
  (have p := (vqk-parts _ _ _ _ _ _ (vq-rest-of _ _ _ w h)))
  (have i2 (= (tbl-all (dnb14 (List.nil Nat) (List.nil Nat) (:comps w)) (:edges w)) true))
  (apply (tbl-all-mono EdgeRow (dnaq14 (List.nil Nat) (:comps w)) _ _ (:edges w) (And.left (And.right p))))
  (intros e he)
  (cases hk (Nat.beq (:kind e) ek-dep))
  (case [false] (simp only [dnb14 hk Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [dnaq14 hk reach-mem Bool.not_true Bool.false_or] at he)
    (simp only [dnb14 hk reach-mem he Bool.not_true Bool.false_or Bool.not_false Bool.true_or Bool.and_self]))
  (have i3 (= (tbl-all (dne14 (List.nil Nat) (:next-id w) (:comps w)) (:edges w)) true))
  (apply (all-of-mem EdgeRow _ (:edges w)))
  (intros e hm) (simp only [dne14 reach-mem Bool.and_false Bool.not_false Bool.true_or])
  (exact (vr-intro _ _ w (vq-sample _ _ _ w h) (vrk-intro _ _ _ _ _ (And.left p) i2 i3 hd))))
(a/theorem vq-of-vr [w :- World] (=> (= (vr (List.nil Nat) (List.nil Nat) w) true) (= (vq (List.nil Nat) (List.nil Nat) false w) true))
  (intro h)
  (have p := (vrk-parts _ _ _ _ _ (vr-rest-of _ _ w h)))
  (have i2 (= (tbl-all (dnaq14 (List.nil Nat) (:comps w)) (:edges w)) true))
  (apply (tbl-all-mono EdgeRow (dnb14 (List.nil Nat) (List.nil Nat) (:comps w)) _ _ (:edges w) (And.left (And.right p))))
  (intros e he)
  (cases hk (Nat.beq (:kind e) ek-dep))
  (case [false] (simp only [dnaq14 hk Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [dnb14 hk reach-mem Bool.not_true Bool.false_or Bool.not_false Bool.true_or Bool.and_true] at he)
    (simp only [dnaq14 hk reach-mem he Bool.not_true Bool.false_or]))
  (have i3 (= (tbl-all (awake (:comps w)) (List.nil Nat)) true)) (simp only [tbl-all])
  (have i4 (= (Bool.or (Bool.not false) (tbl-all (swc14 (:next-id w)) (:comps w))) true)) (simp only [Bool.not_false Bool.true_or])
  (exact (vq-intro _ _ _ w (vr-sample _ _ w h) (vqk-intro _ _ _ _ _ _ (And.left p) i2 i3 i4))))

;; the step invariant
(a/defn v14 [w :- World] Bool (vq (List.nil Nat) (List.nil Nat) false w))
(a/theorem step-v14 [w :- World, it :- Item]
  (=> (= (v14 w) true) (= (g7 w) true) (= (inv-rank w) true) (= (rule-r-safe (:world (raw w it))) true)
      (= (v14 (:world (world-step w it))) true))
  (intros h hg hk hs)
  (simp only [v14] at h) (simp only [v14])
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true]
    (have e2 := (step-accepted w it ha)) (rw [e2])
    (have r0 := (raw-vq (List.nil Nat) (List.nil Nat) false w it h))
    (exact (vq-of-vr _ (vr-rule-r _ (raw-rk w it hk) (vr-of-vq (List.nil Nat) false _ r0 (dep-active-of-g7 _ (raw-g7 w it hg))) hs)))))
(a/theorem v14-empty [] (= (v14 empty-world) true) (rfl))

;; the combined bundle: p3k = p3j && v14 (no honest hypothesis)
(a/defn p3k [w :- World] Bool (Bool.and (p3j w) (v14 w)))
(a/theorem p3k-parts [w :- World] (=> (= (p3k w) true) (And (= (p3j w) true) (= (v14 w) true)))
  (intro h) (simp only [p3k Bool.and_eq_true] at h) (exact h))
(a/theorem p3k-empty [] (= (p3k empty-world) true) (rfl))
(a/theorem step-p3k [w :- World, it :- Item] (=> (= (p3k w) true) (= (p3k (:world (world-step w it))) true))
  (intro h)
  (have p := (p3k-parts w h))
  (have pi := (And.left (p3j-parts w (And.left p))))
  (have pb := (And.left (p3i-ctx w pi)))
  (have hk := (And.left (And.right (p3b-parts w pb))))
  (have a1 := (step-p3j w it (And.left p)))
  (have a2 := (step-v14 w it (And.right p) (p3i-g7 w pi) hk (step-rule-r-safe w it pb)))
  (simp only [p3k a1 a2 Bool.and_self]))

;; ---- I14: the validity graph over idle computations has no cycle
(a/defn idle-row [w :- World, d :- Nat] Bool (match (comp-find w d) [none false] [(some c) (:idle c)]))
(a/defn vrow [w :- World, d :- Nat] (List Valid) (match (comp-find w d) [none (List.nil Valid)] [(some c) (:validity c)]))
;; the validity graph: an idle computation's successors are its idle computation debtors
(a/defn vsucc14 [w :- World, x :- Nat] (List Nat)
  (match (comp-find w x)
    [none (List.nil Nat)]
    [(some c) (if (:idle c) (tbl-filter (idle-row w) (valid-debtors (:validity c))) (List.nil Nat))]))
(a/defn above-all [us :- (List Valid), v :- Valid] Bool (tbl-all (prec14 v) us))

(a/theorem prec-trans [v :- Valid, u :- Valid, t :- Valid]
  (=> (= (prec14 v u) true) (= (prec14 u t) true) (= (prec14 v t) true))
  (intros h1 h2)
  (simp only [prec14 Bool.or_eq_true Bool.and_eq_true Nat.blt_eq Nat.beq_eq] at h1 h2)
  (simp only [prec14 Bool.or_eq_true Bool.and_eq_true Nat.blt_eq Nat.beq_eq])
  (cases h1)
  (case [inl a1] (cases h2) (case [inl b1] (exact (Or.inl (Nat.lt_trans a1 b1))))
    (case [inr b2] (have b21 := (And.left b2)) (apply Or.inl) (omega)))
  (case [inr a2] (have a21 := (And.left a2)) (have a22 := (And.right a2))
    (cases h2) (case [inl b1] (apply Or.inl) (omega))
    (case [inr b2] (have b21 := (And.left b2)) (have b22 := (And.right b2)) (apply Or.inr) (exact (And.intro (Eq.trans b21 a21) (Nat.lt_trans b22 a22))))))
(a/theorem prec-irrefl [v :- Valid] (= (prec14 v v) false)
  (cases h (prec14 v v)) (case [false] (rfl))
  (case [true] (simp only [prec14 Bool.or_eq_true Bool.and_eq_true Nat.blt_eq Nat.beq_eq] at h) (cases h) (case [inl a] (omega)) (case [inr b] (have b2 := (And.right b)) (omega))))

(a/theorem above-step-c [n :- Nat, cs :- (List CompRow), cz :- CompRow, z :- Nat, v2 :- Valid, vs :- (List Valid)]
  (=> (List.Mem cz cs) (= (:id cz) z) (= (:idle cz) true) (= (tbl-all (ent14 cs n) vs) true) (= (reach-mem z (valid-debtors vs)) true)
      (= (tbl-all (prec14 v2) vs) true) (= (tbl-all (prec14 v2) (:validity cz)) true))
  (intros hm hid hi)
  (induction vs)
  (case [nil] (intros he hr hp) (simp only [valid-debtors reach-mem] at hr) (cases hr))
  (case [cons u t ih]
    (intros he hr hp)
    (simp only [tbl-all Bool.and_eq_true] at he hp)
    (cases hb (Nat.beq z (:debtor u)))
    (case [false] (simp only [valid-debtors reach-mem hb] at hr) (exact (ih (And.right he) hr (And.right hp))))
    (case [true]
      (have e1 := (And.left he)) (simp only [ent14 Bool.and_eq_true] at e1)
      (have d := (tbl-all-mem CompRow (deb14 n u) cz cs (And.right e1) hm))
      (have ib (= (Nat.beq (:id cz) (:debtor u)) true)) (rw [hid]) (exact hb)
      (simp only [deb14 ib hi Bool.not_true Bool.false_or Bool.and_eq_true] at d)
      (exact (tbl-all-mono Valid (prec14 u) (prec14 v2)
               (fn [t2 :- Valid, ht :- (= (prec14 u t2) true)] (prec-trans v2 u t2 (And.left hp) ht)) (:validity cz) (And.right d))))))
(a/theorem root-any-c [n :- Nat, cs :- (List CompRow), cz :- CompRow, z :- Nat, vs :- (List Valid)]
  (=> (List.Mem cz cs) (= (:id cz) z) (= (:idle cz) true) (= (tbl-all (ent14 cs n) vs) true) (= (reach-mem z (valid-debtors vs)) true)
      (= (tbl-any (above-all (:validity cz)) vs) true))
  (intros hm hid hi)
  (induction vs)
  (case [nil] (intros he hr) (simp only [valid-debtors reach-mem] at hr) (cases hr))
  (case [cons u t ih]
    (intros he hr)
    (simp only [tbl-all Bool.and_eq_true] at he)
    (cases hb (Nat.beq z (:debtor u)))
    (case [false] (simp only [valid-debtors reach-mem hb] at hr) (simp only [tbl-any (ih (And.right he) hr) Bool.or_true]))
    (case [true]
      (have e1 := (And.left he)) (simp only [ent14 Bool.and_eq_true] at e1)
      (have d := (tbl-all-mem CompRow (deb14 n u) cz cs (And.right e1) hm))
      (have ib (= (Nat.beq (:id cz) (:debtor u)) true)) (rw [hid]) (exact hb)
      (simp only [deb14 ib hi Bool.not_true Bool.false_or Bool.and_eq_true] at d)
      (have a1 (= (above-all (:validity cz) u) true)) (simp only [above-all]) (exact (And.right d))
      (simp only [tbl-any a1 Bool.true_or]))))

(a/theorem iv-ent [w :- World, x :- Nat, c :- CompRow]
  (=> (= (iv14 (:comps w) (:next-id w)) true) (= (comp-find w x) (Option.some CompRow c)) (= (:idle c) true)
      (= (tbl-all (ent14 (:comps w) (:next-id w)) (:validity c)) true))
  (intros h hf hi)
  (have z := (tbl-all-mem CompRow (ivc14 (:comps w) (:next-id w)) c (:comps w) h (tbl-find-mem CompRow comp-id x c (:comps w) hf)))
  (simp only [ivc14 hi Bool.not_true Bool.false_or] at z) (exact z))

(a/theorem vsucc-mem [w :- World, p :- Nat, q :- Nat]
  (=> (List.Mem q (vsucc14 w p))
      (Exists (fn [cp :- CompRow] (And (= (comp-find w p) (Option.some CompRow cp)) (And (= (:idle cp) true)
        (And (= (reach-mem q (valid-debtors (:validity cp))) true) (= (idle-row w q) true)))))))
  (intro h)
  (cases hf (comp-find w p)) (case' [some cp]) (case' [none])
  (simp only [vsucc14 hf] at h) (cases h)
  (cases hi (:idle cp))
  (case' [true])
  (simp only [vsucc14 hf hi] at h)
  (have z := (mem-filter14 Nat (idle-row w) q (valid-debtors (:validity cp)) h))
  (apply (Exists.intro cp)) (exact (And.intro (Eq.refl (Option.some CompRow cp)) (And.intro hi (And.intro (Iff.mpr (reach-mem-iff q (valid-debtors (:validity cp))) (And.left z)) (And.right z)))))
  (simp only [vsucc14 hf hi] at h) (cases h))

(a/theorem idle-row-c [w :- World, q :- Nat]
  (=> (= (idle-row w q) true)
      (Exists (fn [cq :- CompRow] (And (= (comp-find w q) (Option.some CompRow cq)) (= (:idle cq) true)))))
  (intro h)
  (cases hf (comp-find w q)) (case' [some cq]) (case' [none])
  (simp only [idle-row hf] at h) (cases h)
  (simp only [idle-row hf] at h) (apply (Exists.intro cq)) (exact (And.intro (Eq.refl (Option.some CompRow cq)) h)))

(a/theorem reach-above [w :- World, x :- Nat, c :- CompRow]
  (=> (= (iv14 (:comps w) (:next-id w)) true) (= (comp-find w x) (Option.some CompRow c)) (= (:idle c) true)
      (forall [y :- Nat] (=> (Reach (vsucc14 w) (vsucc14 w x) y)
                              (And (= (idle-row w y) true) (= (tbl-any (above-all (vrow w y)) (:validity c)) true)))))
  (intros h hf hi y hr)
  (induction hr)
  (case [root r hm]
    (have z := (vsucc-mem w x r hm))
    (cases z)
    (case [intro cp pz]
      (have e := (Eq.trans (Eq.symm (And.left pz)) hf))
      (have ec (= cp c)) (cases e) (rfl)
      (rw [ec] at pz)
      (have q := (idle-row-c w r (And.right (And.right (And.right pz)))))
      (cases q)
      (case [intro cq pq]
        (have mq := (tbl-find-mem CompRow comp-id r cq (:comps w) (And.left pq)))
        (have iq := (tbl-find-id CompRow comp-id r cq (:comps w) (And.left pq)))
        (have vr0 (= (vrow w r) (:validity cq))) (simp only [vrow (And.left pq)])
        (rw [vr0])
        (exact (And.intro (And.right (And.right (And.right pz)))
                 (root-any-c (:next-id w) (:comps w) cq r (:validity c) mq iq (And.right pq) (iv-ent w x c h hf hi) (And.left (And.right (And.right pz)))))))))
  (case [step p q hp ihp hq]
    (have z := (vsucc-mem w p q hq))
    (cases z)
    (case [intro cp pz]
      (have q2 := (idle-row-c w q (And.right (And.right (And.right pz)))))
      (cases q2)
      (case [intro cq pq]
        (have mq := (tbl-find-mem CompRow comp-id q cq (:comps w) (And.left pq)))
        (have iq := (tbl-find-id CompRow comp-id q cq (:comps w) (And.left pq)))
        (have vrq (= (vrow w q) (:validity cq))) (simp only [vrow (And.left pq)])
        (have vrp (= (vrow w p) (:validity cp))) (simp only [vrow (And.left pz)])
        (have a0 := (And.right ihp)) (rw [vrp] at a0)
        (rw [vrq])
        (apply And.intro) (exact (And.right (And.right (And.right pz))))
        (apply (tbl-any-mono Valid (above-all (:validity cp)) (above-all (:validity cq)) _ (:validity c) a0))
        (intros v2 hv) (simp only [above-all] at hv) (simp only [above-all])
        (exact (above-step-c (:next-id w) (:comps w) cq q v2 (:validity cp) mq iq (And.right pq)
                 (iv-ent w p cp h (And.left pz) (And.left (And.right pz))) (And.left (And.right (And.right pz))) hv))))))

(a/theorem any-above-self [vs :- (List Valid)]
  (forall [xs :- (List Valid)] (=> (forall [v :- Valid] (=> (List.Mem v xs) (List.Mem v vs))) (= (tbl-any (above-all vs) xs) true) False))
  (intro xs)
  (induction xs)
  (case [nil] (intros hs h) (simp only [tbl-any] at h) (cases h))
  (case [cons v t ih]
    (intros hs h)
    (simp only [tbl-any Bool.or_eq_true] at h)
    (cases h)
    (case [inl a]
      (simp only [above-all] at a)
      (have z := (tbl-all-mem Valid (prec14 v) v vs a (hs v (List.Mem.head t))))
      (rw [(prec-irrefl v)] at z) (cases z))
    (case [inr b] (exact (ih (fn [u :- Valid, m :- (List.Mem u t)] (hs u (List.Mem.tail v m))) b)))))

(a/theorem reach-nil [succ :- (=> Nat (List Nat)), y :- Nat] (=> (Reach succ (List.nil Nat) y) False)
  (intro hr)
  (induction hr)
  (case [root r hm] (cases hm))
  (case [step p q hp ihp hq] (exact ihp)))

;; Theorem (I14): in a v14 world no idle computation reaches itself through the validity graph
(a/theorem i14-acyclic [w :- World, x :- Nat]
  (=> (= (v14 w) true) (Not (Reach (vsucc14 w) (vsucc14 w x) x)))
  (intros h hr)
  (have p := (vqk-parts _ _ _ _ _ _ (vq-rest-of _ _ _ w h)))
  (cases hf (comp-find w x)) (case' [some c]) (case' [none])
  (simp only [vsucc14 hf] at hr) (exact (reach-nil (vsucc14 w) x hr))
  (cases hi (:idle c))
  (case' [true])
  (have z := (reach-above w x c (And.left p) hf hi x hr))
  (have vx (= (vrow w x) (:validity c))) (simp only [vrow hf])
  (have a := (And.right z)) (rw [vx] at a)
  (exact (any-above-self (:validity c) (:validity c) (fn [v :- Valid, m :- (List.Mem v (:validity c))] m) a))
  (simp only [vsucc14 hf hi] at hr) (exact (reach-nil (vsucc14 w) x hr)))

;; Theorem: after every step from a p3k world, I14 holds (no honest hypothesis)
(a/theorem step-i14-total [w :- World, it :- Item, x :- Nat]
  (=> (= (p3k w) true) (Not (Reach (vsucc14 (:world (world-step w it))) (vsucc14 (:world (world-step w it)) x) x)))
  (intro h) (exact (i14-acyclic _ x (And.right (p3k-parts _ (step-p3k w it h))))))

;; ===========================================================================
;; Part J. P10 (i8's raw0 guard `cur-closed` / `body-shut`) reduced to the run scope: an alive normal task
;; run's CURRENT scope is open as soon as its RUN scope is open (the current scope is the run scope or
;; an open explicit scope reached from it through open explicit children)
;; ===========================================================================

(a/theorem nat-max-cases [xs :- (List Nat)]
  (forall [m :- Nat] (Or (= (nat-max m xs) m) (= (reach-mem (nat-max m xs) xs) true)))
  (induction xs)
  (case [nil] (intro m) (apply Or.inl) (simp only [nat-max]))
  (case [cons h t ih]
    (intro m)
    (simp only [nat-max])
    (cases hb (Nat.blt m h))
    (case [false]
      (simp only [hb])
      (have z := (ih m))
      (cases z)
      (case [inl a1] (exact (Or.inl a1)))
      (case [inr a2] (apply Or.inr) (exact (rm-cons-r _ h t a2))))
    (case [true]
      (simp only [hb])
      (have z := (ih h))
      (apply Or.inr)
      (cases z)
      (case [inl a1] (rw [a1]) (simp only [reach-mem Nat.beq_refl]))
      (case [inr a2] (exact (rm-cons-r _ h t a2))))))

(a/theorem mem-scan-row [A :- Type, idf :- (=> A Nat), p :- (=> A Bool), v :- Nat, xs :- (List A)]
  (=> (List.Mem v (tbl-scan idf p xs))
      (Exists (fn [r :- A] (And (List.Mem r xs) (And (= (idf r) v) (= (p r) true))))))
  (induction xs)
  (case [nil] (intro h) (simp only [tbl-scan] at h) (cases h))
  (case [cons hd t ih]
    (intro h)
    (cases hp (p hd))
    (case [false]
      (simp only [tbl-scan hp] at h)
      (have z := (ih h)) (cases z)
      (case [intro r pr] (apply (Exists.intro r)) (exact (And.intro (List.Mem.tail hd (And.left pr)) (And.right pr)))))
    (case [true]
      (simp only [tbl-scan hp] at h)
      (cases h)
      (case [head] (apply (Exists.intro hd)) (exact (And.intro (List.Mem.head t) (And.intro (Eq.refl (idf hd)) hp))))
      (case [tail b]
        (have z := (ih b)) (cases z)
        (case [intro r pr] (apply (Exists.intro r)) (exact (And.intro (List.Mem.tail hd (And.left pr)) (And.right pr))))))))

(a/defn sopen-q [s :- ScopeRow] Bool (:open s))
(a/theorem oec-reach [w :- World, s0 :- Nat, v :- Nat]
  (=> (Reach (open-explicit-children w) (List.cons Nat s0 (List.nil Nat)) v)
      (Or (= v s0) (Exists (fn [s :- ScopeRow] (And (List.Mem s (:scopes w)) (And (= (scope-id s) v) (= (sopen-q s) true)))))))
  (intro hr)
  (induction hr)
  (case [root r hm]
    (cases hm) (case [head] (apply Or.inl) (rfl)) (case [tail b] (cases b)))
  (case [step p q hp ihp hq]
    (apply Or.inr)
    (have z := (mem-scan-row ScopeRow scope-id (open-explicit-child p) q (:scopes w) hq))
    (cases z)
    (case [intro s ps]
      (apply (Exists.intro s))
      (have o := (And.right (And.right ps)))
      (simp only [open-explicit-child Bool.and_eq_true] at o)
      (have o2 (= (sopen-q s) true)) (simp only [sopen-q]) (exact (And.right (And.right o)))
      (exact (And.intro (And.left ps) (And.intro (And.left (And.right ps)) o2))))))

(a/theorem scope-open-of-row [w :- World, s :- ScopeRow, v :- Nat]
  (=> (= (inv-sample w) true) (List.Mem s (:scopes w)) (= (scope-id s) v) (= (sopen-q s) true) (= (scope-open-at w v) true))
  (intros hs hm hid ho)
  (have u := (uniq-all ScopeRow scope-id sopen-q s (:scopes w) (scopes-nodup8 w hs) hm ho))
  (rw [hid] at u)
  (cases hf (scope-find w v)) (case' [some sf]) (case' [none])
  (have hh := (tbl-find-none-has ScopeRow scope-id v (:scopes w) hf))
  (have hh2 := (mem-ids-has ScopeRow scope-id s (:scopes w) hm)) (rw [hid] at hh2) (rw [nat-mem-ids] at hh2)
  (rw [hh] at hh2) (cases hh2)
  (have mf := (tbl-find-mem ScopeRow scope-id v sf (:scopes w) hf))
  (have idf := (tbl-find-id ScopeRow scope-id v sf (:scopes w) hf))
  (have z := (tbl-all-mem ScopeRow (same-id-then scope-id v sopen-q) sf (:scopes w) u mf))
  (have idf2 (= (Nat.beq (scope-id sf) v) true)) (simp only [Nat.beq_eq]) (exact idf)
  (simp only [same-id-then idf2 Bool.not_true Bool.false_or sopen-q] at z)
  (simp only [scope-open-at hf]) (exact z))

;; Theorem (P10 reduced): a run whose run scope is open does not trip the guard
(a/theorem cur-open-of-run-scope [w :- World, r :- RunRow]
  (=> (= (inv-sample w) true) (= (scope-open-at w (:scope r)) true) (= (run-cur-closed w r) false))
  (intros hs ho)
  (have co (= (scope-open-at w (cur-scope w r)) true))
  (simp only [cur-scope])
  (have z := (nat-max-cases (:visited (reach-run-l (List.cons Nat 0 (List.cons Nat 0 (tbl-ids scope-id (:scopes w))))
                                                    (open-explicit-children w) (List.cons Nat (:scope r) (List.nil Nat)))) (:scope r)))
  (cases z)
  (case [inl a1] (rw [a1]) (exact ho))
  (case [inr a2]
    (rw [(reach-run-l-eq (List.cons Nat 0 (List.cons Nat 0 (tbl-ids scope-id (:scopes w)))) (open-explicit-children w) (List.cons Nat (:scope r) (List.nil Nat)))] at a2)
    (have rr := (reach-run-sound _ (open-explicit-children w) (List.cons Nat (:scope r) (List.nil Nat)) _ a2))
    (have q := (oec-reach w (:scope r) _ rr))
    (cases q)
    (case [inl b1] (rw [(reach-run-l-eq (List.cons Nat 0 (List.cons Nat 0 (tbl-ids scope-id (:scopes w)))) (open-explicit-children w) (List.cons Nat (:scope r) (List.nil Nat)))]) (rw [b1]) (exact ho))
    (case [inr b2]
      (cases b2)
      (case [intro s ps]
        (rw [(reach-run-l-eq (List.cons Nat 0 (List.cons Nat 0 (tbl-ids scope-id (:scopes w)))) (open-explicit-children w) (List.cons Nat (:scope r) (List.nil Nat)))])
        (exact (scope-open-of-row w s _ hs (And.left ps) (And.left (And.right ps)) (And.right (And.right ps)))))))
  (simp only [run-cur-closed co Bool.not_true Bool.and_false]))

;; the open run-scope fact (obligation P10' = (a) of the plan) and its consequence cur-open-ok
(a/defn rso [w :- World, r :- RunRow] Bool
  (Bool.or (Bool.not (Bool.and (run-alive r) (Nat.beq (:mode r) mode-normal)))
           (Bool.or (in-comp w r) (scope-open-at w (:scope r)))))
(a/theorem cur-open-of-rso [w :- World]
  (=> (= (inv-sample w) true) (= (tbl-all (rso w) (:runs w)) true) (= (cur-open-ok w) true))
  (intros hs h)
  (simp only [cur-open-ok])
  (apply (tbl-all-mono RunRow (rso w) (run-cur-ok w) _ (:runs w) h))
  (intros r hr)
  (cases ha (Bool.and (run-alive r) (Nat.beq (:mode r) mode-normal)))
  (case [false] (simp only [run-cur-ok ha Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [rso ha Bool.not_true Bool.false_or Bool.or_eq_true] at hr)
    (cases hr)
    (case [inl c1] (simp only [run-cur-ok run-cur-closed c1 ha Bool.not_true Bool.false_and Bool.not_false Bool.or_true]))
    (case [inr c2] (simp only [run-cur-ok ha (cur-open-of-run-scope w r hs c2) Bool.not_false Bool.or_true]))))
