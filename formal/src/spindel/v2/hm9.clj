(ns spindel.v2.hm9
  "Bounded await wiring certificate before member installation.
   Guarded structural outputs remain separate from general H3 transport."
  (:require [ansatz.core :as a]
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
            [spindel.v2.hm :refer :all]
            [spindel.v2.i10 :refer :all]
            [spindel.v2.ar :refer :all]
            [spindel.v2.hmk2 :refer :all]
            [spindel.v2.hmk :refer :all]
            [spindel.v2.hm3 :refer :all]
            [spindel.v2.hm5 :refer :all]
            [spindel.v2.hm6 :refer :all]
            [spindel.v2.hm6-base :refer :all]
            [spindel.v2.hm7 :refer :all]
            [spindel.v2.hm8 :refer :all]
            [spindel.v2.i5 :refer :all]
            [spindel.v2.i8 :refer :all]
            [spindel.v2.i1r :refer :all]))

;; Exact transparent helper meanings from the independently frozen annex.
(a/defn h9-entry [xm :- (List Nat), w :- World, r :- RunRow,
                  ds :- (List Nat), mode :- Nat, st :- Nat, fresh :- Nat] Prop
  (And (= (p3la w) true)
   (And (= (h3 xm w) true)
    (And (= (tok-run w st) (Option.some RunRow r))
         (= (await-ok w r ds mode fresh) true)))))

(a/defn h9-act [w :- World, r :- RunRow, ds :- (List Nat),
                mode :- Nat, k :- Nat, mine :- (List Nat)] ActRow
  (ActRow.mk (:next-id w) (:id r) mode (List.nil Member)
             (none-slots ds) (nat-len ds) k mine))

(a/defn h9-prefix [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat,
                   k :- Nat, mine :- (List Nat), pre :- (List Nat)] AwAcc
  (await-wire r (:next-id w) mode k
    (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) pre))

(a/defn h9-debtors [ps :- (List DE)] (List Nat)
  (match ps [nil (List.nil Nat)]
    [(cons p t) (List.cons Nat (:deb p) (h9-debtors t))]))

(a/defn h9-pairs [pre :- (List Nat), tail :- (List Nat), ps :- (List DE)] Prop
  (And (forall [d :- Nat]
         (Iff (= (de-has d ps) true) (= (nat-mem d pre) true)))
   (And (= (nat-len (h9-debtors ps)) (nat-len pre))
    (And (= (nat-nodup (h9-debtors ps)) true)
     (And (forall [d :- Nat]
            (=> (= (nat-mem d tail) true) (= (de-has d ps) false)))
          (forall [p :- DE, q :- DE]
            (=> (List.Mem p ps) (List.Mem q ps) (= (:edge p) (:edge q))
                (= (:deb p) (:deb q)))))))))

(a/defn h9-edge-fields [P :- World, r :- RunRow, a :- Nat, mode :- Nat,
                       k :- Nat, d :- Nat, e :- EdgeRow] Prop
  (And (= (:debtor e) d)
   (And (= (:at e) (:effect-index r))
    (And (= (:phase e) ph-armed)
     (And (= (:kind e) (if (as-dep P r d) ek-dep ek-wait))
      (And (= (:creditor e) (if (as-dep P r d) (:of r) a))
           (= (:cont e) (if (as-dep P r d) (await-cont r mode k) cont-restart))))))))

(a/defn h9-support [xm :- (List Nat), W :- World, r :- RunRow, a :- Nat] Prop
  (And (= (h3 xm W) true)
   (And (= (g7 W) true)
    (And (= (aha W) true)
     (And (= (gd W) true)
      (And (= (ar W) true)
       (And (= (hmk (List.nil Nat) W) true)
        (And (= (ekb W) true)
         (And (= (gl W) true)
          (And (= (ka (:id r) W) true)
           (And (= (awo (:of r) (:id r) W) true)
                (= (gx (Ex.mk (:id r) a) W) true))))))))))))

(a/defn h9-shape [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat,
                  k :- Nat, mine :- (List Nat), W :- World] Prop
  (And (= (:acts W) (List.cons ActRow (h9-act w r ds mode k mine) (:acts w)))
   (And (= (:runs W) (:runs (run-upd w (:id r) run-tick)))
    (And (= (:tasks W) (:tasks w))
     (And (= (:sources W) (:sources w))
      (And (= (:res W) (:res w))
           (forall [x :- Nat] (= (comp-has W x) (comp-has w x)))))))))

;; Both copier families must materialize their actual dependency closures.
(lcopy! H3 'inv-await-step)
(lcopy! H3 'inv-await-wire)
(doseq [B [G7 AHA GD AR HMK EKB GL AWO KA]]
  (lcopy! B 'inv-await-pre)
  (lcopy! B 'inv-await-wire))
(spindel.v2.acts/copy! GX 'nat-fold-inv)
(spindel.v2.acts/copy! GX 'inv-demand-reactive)
(spindel.v2.acts/copy! GX 'inv-await-wire)

(a/theorem h3-await-step [xm :- (List Nat), r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, acc :- AwAcc, d :- Nat]
  (=> (= (h3 xm (:world acc)) true) (= (h3 xm (:world (await-step r a mode k acc d))) true))
  (intro h) (exact (hm3-await-step xm r a mode k acc d h)))

(a/theorem h3-await-wire [xm :- (List Nat), r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, ds :- (List Nat), acc :- AwAcc]
  (=> (= (h3 xm (:world acc)) true) (= (h3 xm (:world (await-wire r a mode k acc ds))) true))
  (intro h) (exact (hm3-await-wire xm r a mode k ds acc h)))

(a/theorem h3-await-acc-p3la [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (= (p3la w) true) (= (h3 xm w) true) (List.Mem r (:runs w)) (= (run-alive r) true)
      (= (h3 xm (:world (await-acc w r ds mode k mine))) true))
  (intros hp h mr al)
  (exact (h3-await-wire xm r (:next-id w) mode k (nat-distinct ds)
           (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true)
           (h3-await-pre-p3la xm w r ds mode k mine hp h mr al))))

(a/theorem h9-awo-of-run [w :- World, r :- RunRow]
  (=> (= (g7 w) true) (List.Mem r (:runs w)) (= (run-alive r) true)
      (= (awo (:of r) (:id r) w) true))
  (intros h mr al)
  (have q := (g7k-parts _ _ _ (g7-rest-of w h)))
  (have aw := (tbl-all-mem RunRow (a7-one (:comps w)) r (:runs w) (And.left q) mr))
  (simp only [a7-one al Bool.not_true Bool.false_or] at aw)
  (have of (= (tbl-all (run-of-at (:id r) (:of r)) (:runs w)) true))
  (exact (uniq-all RunRow run-id (fn [b :- RunRow] (Nat.beq (:of b) (:of r))) r (:runs w)
           (lit-runs-nodup w (g7-sample w h)) mr (Nat.beq_refl (:of r))))
  (exact (awo-intro (:of r) (:id r) w (g7-sample w h) (awo-rest-mk (:of r) (:id r) w aw of))))

(a/theorem h9-p3la-gl [w :- World] (=> (= (p3la w) true) (= (gl w) true))
  (intro h) (have p := (p3b-parts w (p3la-p3b w h)))
  (exact (And.left (And.right (And.right p)))))

(a/theorem h9-gx-pre [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (List.Mem r (:runs w)) (= (:slice r) true) (= (ga w) true)
      (= (gx (Ex.mk (:id r) (:next-id w)) (await-pre w r ds mode k mine)) true))
  (intros mr sl h)
  (have hn := (no-act-bad w r h mr (slice-not-good r sl)))
  (have hlt := (run-below w r (ga-sample w h) mr))
  (have h1 := (ga-run-upd w (:id r) run-tick run-tick-run-id (fn [q :- RunRow] (Eq.refl (good-row q))) h))
  (have h2 := (gx-act-ins (run-upd w (:id r) run-tick) (h9-act w r ds mode k mine) (rfl) hlt hn h1))
  (simp only [await-pre h9-act])
  (exact (nat-fold-gx (Ex.mk (:id r) (:next-id w)) demand-reactive (gx-demand-reactive (Ex.mk (:id r) (:next-id w)))
           (nat-distinct ds) _ h2)))

(a/theorem h9-prefix-support [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, pre :- (List Nat), tail :- (List Nat)]
  (=> (h9-entry xm w r ds mode st fresh) (= (List.append Nat pre tail) (nat-distinct ds))
      (h9-support xm (:world (h9-prefix w r ds mode k mine pre)) r (:next-id w)))
  (intros ent split)
  (simp only [h9-entry] at ent)
  (have hp := (And.left ent))
  (have h := (And.left (And.right ent)))
  (have ht := (And.left (And.right (And.right ent))))
  (have hok := (And.right (And.right (And.right ent))))
  (have tf := (tok-facts w st r ht))
  (have mr := (And.left tf))
  (have sl := (And.right tf))
  (simp only [await-ok Bool.and_eq_true] at hok)
  (have al := (normal-alive r (And.left (And.right hok))))
  (have a0 := (h9-awo-of-run w r (p3la-g7 w hp) mr al))
  (have a1 := (awo-await-pre (:of r) (:id r) w r ds mode k mine a0))
  (have a2 := (awo-await-wire (:of r) (:id r) r (:next-id w) mode k pre (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) a1))
  (have k0 := (ka-intro (:id r) w (g7-sample w (p3la-g7 w hp)) (run-ok-of-mem w r (g7-sample w (p3la-g7 w hp)) mr al)))
  (have k1 := (ka-await-pre (:id r) w r ds mode k mine k0))
  (have k2 := (ka-await-wire (:id r) r (:next-id w) mode k pre (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) k1))
  (have x0 := (h9-gx-pre w r ds mode k mine mr sl (p3la-ga w hp)))
  (have x2 := (gx-await-wire (Ex.mk (:id r) (:next-id w)) r (:next-id w) mode k pre (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) x0))
  (simp only [h9-support h9-prefix])
  (apply And.intro)
  (exact (h3-await-wire xm r (:next-id w) mode k pre (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) (h3-await-pre-p3la xm w r ds mode k mine hp h mr al)))
  (apply And.intro)
  (exact (g7-await-wire r (:next-id w) mode k pre (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) a1 (g7-await-pre-p3la w r ds mode k mine hp mr al)))
  (apply And.intro)
  (exact (aha-await-wire r (:next-id w) mode k pre (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) (aha-await-pre-p3la w r ds mode k mine hp mr al)))
  (apply And.intro)
  (exact (gd-await-wire r (:next-id w) mode k pre (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) (gd-await-pre-p3la w r ds mode k mine hp mr al)))
  (apply And.intro)
  (exact (ar-await-wire r (:next-id w) mode k pre (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) (ar-await-pre-p3la w r ds mode k mine hp mr al)))
  (apply And.intro)
  (exact (hmk-await-wire (List.nil Nat) r (:next-id w) mode k pre (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) (hmk-await-pre-p3la w r ds mode k mine hp mr al)))
  (apply And.intro)
  (exact (ekb-await-wire r (:next-id w) mode k pre (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) (ekb-await-pre-p3la w r ds mode k mine hp mr al)))
  (apply And.intro)
  (exact (gl-await-wire r (:next-id w) mode k pre (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) (gl-await-pre w r ds mode k mine (h9-p3la-gl w hp))))
  (exact (And.intro k2 (And.intro a2 x2))))

(a/theorem h9-step-ok-false [r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, acc :- AwAcc, d :- Nat]
  (=> (= (:ok acc) false) (= (:ok (await-step r a mode k acc d)) false))
  (intro h)
  (cases hd (as-dep (:world acc) r d))
  (case [false] (simp only [await-step hd]) (exact h))
  (case [true]
    (cases hs (site-edge (:edges (:world acc)) (:of r) (:effect-index r) d))
    (case [none] (simp only [await-step hd hs h Bool.false_and]))
    (case [some e] (simp only [await-step hd hs]) (exact h))))

(a/theorem h9-wire-ok-false [r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, acc :- AwAcc, ds :- (List Nat)]
  (=> (= (:ok acc) false) (= (:ok (await-wire r a mode k acc ds)) false))
  (have gen (forall [xs :- (List Nat), B :- AwAcc]
              (=> (= (:ok B) false) (= (:ok (await-wire r a mode k B xs)) false))))
  (intro xs) (induction xs)
  (case [nil] (intros B h) (simp only [await-wire]) (exact h))
  (case [cons d t ih] (intros B h) (simp only [await-wire]) (exact (ih _ (h9-step-ok-false r a mode k B d h))))
  (exact (gen ds acc)))

(a/theorem h9-acc-rank [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat]
  (=> (h9-entry xm w r ds mode st fresh) (= (:ok (await-acc w r ds mode k mine)) true)
      (= (inv-rank (:world (await-acc w r ds mode k mine))) true))
  (intros ent ok)
  (simp only [h9-entry] at ent)
  (have pb := (p3b-parts w (p3la-p3b w (And.left ent))))
  (have h1 := (rk-await-pre w r ds mode k mine (And.left (And.right pb))))
  (have hs := (inv-await-wire r (:next-id w) mode k (nat-distinct ds)
                (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) (rk-sample _ h1)))
  (have hr := (await-wire-ranks r (:next-id w) mode k (nat-distinct ds)
                (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true)
                (fn [h :- (= true true)] (rk-ranks _ h1)) ok))
  (exact (rk-intro _ hs hr)))

(a/theorem h9-members-split [ps :- (List DE), i :- Nat, left :- (List Nat), d :- Nat, right :- (List Nat)]
  (= (mk-members ps i (List.append Nat left (List.cons Nat d right)))
     (List.append Member (mk-members ps i left)
       (List.cons Member (Member.mk (pair-edge d ps) (+ i (nat-len left)))
         (mk-members ps (+ (+ i (nat-len left)) 1) right))))
  (have gen (forall [xs :- (List Nat), n :- Nat]
              (= (mk-members ps n (List.append Nat xs (List.cons Nat d right)))
                 (List.append Member (mk-members ps n xs)
                   (List.cons Member (Member.mk (pair-edge d ps) (+ n (nat-len xs)))
                     (mk-members ps (+ (+ n (nat-len xs)) 1) right))))))
  (intro xs) (induction xs)
  (case [nil] (intro n) (simp only [List.append mk-members nat-len Nat.add_zero]))
  (case [cons x t ih]
    (intro n)
    (have e (= (+ (+ n 1) (nat-len t)) (+ n (+ (nat-len t) 1)))) (omega)
    (simp only [List.append mk-members nat-len (ih (+ n 1)) e]))
  (exact (gen left i)))

(a/theorem h9-member-count [ps :- (List DE), i :- Nat, ds :- (List Nat)]
  (= (nat-len (member-edges (mk-members ps i ds))) (nat-len ds))
  (have gen (forall [xs :- (List Nat), n :- Nat]
              (= (nat-len (member-edges (mk-members ps n xs))) (nat-len xs))))
  (intro xs) (induction xs)
  (case [nil] (intro n) (simp only [mk-members member-edges nat-len]))
  (case [cons d t ih] (intro n) (simp only [mk-members member-edges nat-len (ih (+ n 1))]))
  (exact (gen ds i)))

(a/theorem h9-mem-app-right [A :- Type, x :- A, xs :- (List A), ys :- (List A)]
  (=> (List.Mem x ys) (List.Mem x (List.append A xs ys)))
  (induction xs)
  (case [nil] (intro h) (simp only [List.append]) (exact h))
  (case [cons y t ih] (intro h) (simp only [List.append]) (exact (List.Mem.tail y (ih h)))))

(a/theorem h9-member-at [ps :- (List DE), i :- Nat, left :- (List Nat), d :- Nat, right :- (List Nat)]
  (List.Mem (Member.mk (pair-edge d ps) (+ i (nat-len left)))
    (mk-members ps i (List.append Nat left (List.cons Nat d right))))
  (rw [h9-members-split])
  (apply h9-mem-app-right)
  (exact (List.Mem.head _)))

(a/theorem h9-duplicate-slots [ps :- (List DE), i :- Nat, left :- (List Nat), d :- Nat, middle :- (List Nat), right :- (List Nat)]
  (let [ds (List.append Nat left (List.cons Nat d (List.append Nat middle (List.cons Nat d right))))
        j (+ i (nat-len left)), l (+ (+ j 1) (nat-len middle))
        m1 (Member.mk (pair-edge d ps) j), m2 (Member.mk (pair-edge d ps) l)]
    (And (List.Mem m1 (mk-members ps i ds))
     (And (List.Mem m2 (mk-members ps i ds))
      (And (= (:edge m1) (:edge m2)) (= (Nat.blt (:idx m1) (:idx m2)) true)))))
  (apply And.intro)
  (exact (h9-member-at ps i left d (List.append Nat middle (List.cons Nat d right))))
  (apply And.intro)
  (rw [h9-members-split])
  (apply h9-mem-app-right)
  (apply List.Mem.tail)
  (exact (h9-member-at ps (+ (+ i (nat-len left)) 1) middle d right))
  (apply And.intro) (rfl)
  (apply gd-blt-of)
  (change (< (+ i (nat-len left)) (+ (+ (+ i (nat-len left)) 1) (nat-len middle))))
  (omega))

(a/theorem h9-shape-comp [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), W :- World, x :- Nat, f :- (=> CompRow CompRow), hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c)))]
  (=> (h9-shape w r ds mode k mine W) (h9-shape w r ds mode k mine (comp-upd W x f)))
  (intro h) (simp only [h9-shape] at h) (simp only [h9-shape])
  (apply And.intro) (exact (And.left h))
  (apply And.intro) (exact (And.left (And.right h)))
  (apply And.intro) (exact (And.left (And.right (And.right h))))
  (apply And.intro) (exact (And.left (And.right (And.right (And.right h)))))
  (apply And.intro) (exact (And.left (And.right (And.right (And.right (And.right h))))))
  (intro y)
  (have ch (= (comp-has (comp-upd W x f) y) (comp-has W y)))
  (simp only [comp-has comp-upd set-comps])
  (exact (tbl-has-upd CompRow comp-id x y f hid (:comps W)))
  (exact (Eq.trans ch ((And.right (And.right (And.right (And.right (And.right h))))) y))))

(a/theorem h9-shape-insert [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), W :- World, e :- EdgeRow]
  (=> (h9-shape w r ds mode k mine W) (h9-shape w r ds mode k mine (insert-edge-checked W e)))
  (intro h) (cases he (edge-ok-in W e))
  (case [false] (simp only [insert-edge-checked he]) (exact h))
  (case [true] (simp only [insert-edge-checked he]) (exact h)))

(a/theorem h9-shape-raise [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), fuel :- (List Nat)]
  (forall [d :- Nat, W :- World, todo :- (List RJ)]
    (=> (h9-shape w r ds mode k mine W) (h9-shape w r ds mode k mine (:world (raise-loop fuel d W todo)))))
  (induction fuel)
  (case [nil] (intros d W todo h) (cases todo) (all_goals (simp only [raise-loop])) (all_goals (exact h)))
  (case [cons z f ih]
    (intros d W todo h) (cases todo)
    (case [nil] (simp only [raise-loop]) (exact h))
    (case [cons j t]
      (cases hd (Nat.beq (:node j) d))
      (case [true] (simp only [raise-loop hd]) (exact h))
      (case [false]
        (cases hn (Nat.ble (:need j) (comp-rank W (:node j))))
        (case [true] (simp only [raise-loop hd hn]) (exact (ih d W t h)))
        (case [false] (simp only [raise-loop hd hn])
          (exact (ih d _ _ (h9-shape-comp w r ds mode k mine W (:node j) (comp-set-rank (:need j)) (comp-set-rank-id (:need j)) h))))))))

(a/theorem h9-shape-raise-run [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), W :- World, c :- Nat, d :- Nat]
  (=> (h9-shape w r ds mode k mine W) (h9-shape w r ds mode k mine (:world (raise-run W c d))))
  (intro h) (cases hd (comp-has W d))
  (case [false] (simp only [raise-run hd]) (exact h))
  (case [true] (simp only [raise-run hd]) (exact (h9-shape-raise w r ds mode k mine (raise-fuel W) d W _ h))))

(a/theorem h9-shape-react-add [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), W :- World, c :- Nat, v :- Valid]
  (=> (h9-shape w r ds mode k mine W) (h9-shape w r ds mode k mine (react-add W c v)))
  (intro h) (cases ho (react-ok W c v))
  (case [false] (simp only [react-add ho]) (exact h))
  (case [true] (simp only [react-add ho])
    (exact (h9-shape-raise-run w r ds mode k mine _ c (:debtor v) (h9-shape-insert w r ds mode k mine W _ h)))))

(a/theorem h9-shape-react-edges [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), vs :- (List Valid)]
  (forall [W :- World, c :- Nat] (=> (h9-shape w r ds mode k mine W) (h9-shape w r ds mode k mine (react-edges W c vs))))
  (induction vs)
  (case [nil] (intros W c h) (simp only [react-edges]) (exact h))
  (case [cons v t ih] (intros W c h) (simp only [react-edges]) (exact (ih _ c (h9-shape-react-add w r ds mode k mine W c v h)))))

(a/theorem h9-shape-react-one [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), W :- World, c :- CompRow]
  (=> (h9-shape w r ds mode k mine W) (h9-shape w r ds mode k mine (react-one W c)))
  (intro h) (simp only [react-one])
  (exact (h9-shape-react-edges w r ds mode k mine (:validity c) _ (:id c)
           (h9-shape-comp w r ds mode k mine W (:id c) comp-react-row comp-react-row-id h))))

(a/theorem h9-shape-react-loop [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), fuel :- (List Nat)]
  (forall [W :- World, q :- (List Nat)] (=> (h9-shape w r ds mode k mine W) (h9-shape w r ds mode k mine (react-loop fuel W q))))
  (induction fuel)
  (case [nil] (intros W q h) (simp only [react-loop]) (exact h))
  (case [cons z f ih]
    (intros W q h) (cases q)
    (case [nil] (simp only [react-loop]) (exact h))
    (case [cons x t]
      (cases hf (comp-find W x))
      (case [none] (simp only [react-loop hf]) (exact (ih W t h)))
      (case [some c]
        (cases hi (:idle c))
        (case [false] (simp only [react-loop hf hi]) (exact (ih W t h)))
        (case [true] (simp only [react-loop hf hi]) (exact (ih _ _ (h9-shape-react-one w r ds mode k mine W c h))))))))

(a/theorem h9-shape-demand [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), W :- World, d :- Nat]
  (=> (h9-shape w r ds mode k mine W) (h9-shape w r ds mode k mine (demand-reactive W d)))
  (intro h) (cases hf (comp-find W d))
  (case [none] (simp only [demand-reactive hf]) (exact h))
  (case [some c]
    (cases hi (:idle c))
    (case [false] (simp only [demand-reactive hf hi]) (exact h))
    (case [true]
      (cases hv (valid-idle W c))
      (case [false] (simp only [demand-reactive hf hi hv]) (exact (h9-shape-comp w r ds mode k mine W d comp-demand-row comp-demand-row-id h)))
      (case [true] (simp only [demand-reactive hf hi hv]) (exact (h9-shape-react-loop w r ds mode k mine (react-fuel W) W _ h))))))

(a/theorem h9-shape-demand-fold [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), xs :- (List Nat)]
  (forall [W :- World] (=> (h9-shape w r ds mode k mine W) (h9-shape w r ds mode k mine (nat-fold demand-reactive W xs))))
  (induction xs)
  (case [nil] (intros W h) (simp only [nat-fold]) (exact h))
  (case [cons d t ih] (intros W h) (simp only [nat-fold]) (exact (ih _ (h9-shape-demand w r ds mode k mine W d h)))))

(a/theorem h9-shape-pre [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (h9-shape w r ds mode k mine (await-pre w r ds mode k mine))
  (have base (h9-shape w r ds mode k mine (bump (act-ins (run-upd w (:id r) run-tick) (h9-act w r ds mode k mine)))))
  (apply And.intro) (rfl)
  (apply And.intro) (rfl)
  (apply And.intro) (rfl)
  (apply And.intro) (rfl)
  (apply And.intro) (rfl)
  (intro x) (rfl)
  (exact (h9-shape-demand-fold w r ds mode k mine (nat-distinct ds) _ base)))

(a/theorem h9-shape-step [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), a :- Nat, acc :- AwAcc, d :- Nat]
  (=> (h9-shape w r ds mode k mine (:world acc)) (h9-shape w r ds mode k mine (:world (await-step r a mode k acc d))))
  (intro h) (cases hd (as-dep (:world acc) r d))
  (case [false] (simp only [await-step hd]) (exact (h9-shape-insert w r ds mode k mine (:world acc) _ h)))
  (case [true]
    (cases hs (site-edge (:edges (:world acc)) (:of r) (:effect-index r) d))
    (case [none] (simp only [await-step hd hs await-new-dep])
      (exact (h9-shape-comp w r ds mode k mine _ (:of r) (comp-consume-adopt (:effect-index r) d) (comp-consume-adopt-comp-id _ _)
               (h9-shape-raise-run w r ds mode k mine _ (:of r) d (h9-shape-insert w r ds mode k mine (:world acc) _ h)))))
    (case [some e] (simp only [await-step hd hs])
      (exact (h9-shape-comp w r ds mode k mine _ (:of r) (comp-consume-adopt (:effect-index r) d) (comp-consume-adopt-comp-id _ _) h)))))

(a/theorem h9-shape-wire [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), pre :- (List Nat)]
  (forall [a :- Nat, acc :- AwAcc]
    (=> (h9-shape w r ds mode k mine (:world acc)) (h9-shape w r ds mode k mine (:world (await-wire r a mode k acc pre)))))
  (induction pre)
  (case [nil] (intros a acc h) (simp only [await-wire]) (exact h))
  (case [cons d t ih] (intros a acc h) (simp only [await-wire]) (exact (ih a _ (h9-shape-step w r ds mode k mine a acc d h)))))

(a/theorem h9-prefix-shape [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, pre :- (List Nat), tail :- (List Nat)]
  (=> (h9-entry xm w r ds mode st fresh) (= (List.append Nat pre tail) (nat-distinct ds))
      (h9-shape w r ds mode k mine (:world (h9-prefix w r ds mode k mine pre))))
  (intros ent split)
  (exact (h9-shape-wire w r ds mode k mine pre (:next-id w)
           (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) (h9-shape-pre w r ds mode k mine))))

(a/theorem h9-distinct-acc-source [xs :- (List Nat)]
  (forall [seen :- (List Nat), d :- Nat]
    (=> (= (nat-mem d (nat-distinct-acc seen xs)) true) (= (nat-mem d xs) true)))
  (induction xs)
  (case [nil] (intros seen d h) (simp only [nat-distinct-acc nat-mem] at h) (cases h))
  (case [cons x t ih]
    (intros seen d h)
    (cases hx (nat-mem x seen))
    (case [true]
      (simp only [nat-distinct-acc hx] at h)
      (have q := (ih seen d h))
      (cases eq (Nat.beq x d))
      (case [true] (simp only [nat-mem eq]))
      (case [false] (simp only [nat-mem eq]) (exact q)))
    (case [false]
      (cases eq (Nat.beq x d))
      (case [true] (simp only [nat-mem eq]))
      (case [false]
        (simp only [nat-distinct-acc hx nat-mem eq] at h)
        (simp only [nat-mem eq]) (exact (ih (List.cons Nat x seen) d h))))))

(a/theorem h9-distinct-source [xs :- (List Nat), d :- Nat]
  (=> (= (nat-mem d (nat-distinct xs)) true) (= (nat-mem d xs) true))
  (intro h) (exact (h9-distinct-acc-source xs (List.nil Nat) d h)))

(a/theorem h9-deb-shape [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), W :- World, d :- Nat]
  (=> (h9-shape w r ds mode k mine W) (= (deb-exists w d) true) (= (deb-exists W d) true))
  (intros shape h) (simp only [h9-shape] at shape)
  (have ts := (And.left (And.right (And.right shape))))
  (have ss := (And.left (And.right (And.right (And.right shape)))))
  (have rs := (And.left (And.right (And.right (And.right (And.right shape))))))
  (have cs := (And.right (And.right (And.right (And.right (And.right shape))))))
  (simp only [deb-exists task-has source-has resource-has ts ss rs (cs d)])
  (simp only [deb-exists task-has source-has resource-has] at h) (exact h))

(a/theorem h9-as-dep-shape [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), W :- World, d :- Nat]
  (=> (h9-shape w r ds mode k mine W) (= (as-dep W r d) (as-dep w r d)))
  (intro shape) (simp only [h9-shape] at shape)
  (have rs := (And.left (And.right (And.right (And.right (And.right shape))))))
  (have cs := (And.right (And.right (And.right (And.right (And.right shape))))))
  (simp only [as-dep in-comp resource-has rs (cs (:of r))]))

(a/theorem h9-edge-ok-from-fields [W :- World, r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, d :- Nat]
  (=> (= (deb-exists W d) true) (= (act-has W a) true)
      (= (edge-ok-in W (await-edge W r a mode k d)) true))
  (intros hd ha)
  (cases ad (as-dep W r d))
  (case [false]
    (have cr (= (cred-ok (:comps W) (:acts W) (await-edge W r a mode k d)) true))
    (cases hz (Nat.beq a 0))
    (case [true] (simp only [await-edge ad cred-ok host-cred hz]))
    (case [false] (simp only [await-edge ad cred-ok host-cred hz]) (exact ha))
    (have db (= (deb-ok (:comps W) (:tasks W) (:sources W) (:res W) (await-edge W r a mode k d)) true))
    (simp only [await-edge ad deb-ok Nat.beq_refl Bool.true_and]) (exact hd)
    (simp only [edge-ok-in edge-ok cr db Bool.and_self]))
  (case [true]
    (have ad2 := ad) (simp only [as-dep Bool.and_eq_true] at ad2)
    (have ch := (And.left ad2))
    (have rh := (bnot-true _ (And.right ad2)))
    (have cr (= (cred-ok (:comps W) (:acts W) (await-edge W r a mode k d)) true))
    (simp only [await-edge ad cred-ok Nat.beq_refl]) (exact ch)
    (have db (= (deb-ok (:comps W) (:tasks W) (:sources W) (:res W) (await-edge W r a mode k d)) true))
    (simp only [deb-exists rh Bool.or_false] at hd)
    (simp only [resource-has] at rh)
    (simp only [await-edge ad deb-ok rh Bool.and_false Bool.or_false]) (exact hd)
    (simp only [edge-ok-in edge-ok cr db Bool.and_self])))

(a/theorem h9-next-edge-ok [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, pre :- (List Nat), tail :- (List Nat), d :- Nat]
  (=> (h9-entry xm w r ds mode st fresh) (= (List.append Nat pre (List.cons Nat d tail)) (nat-distinct ds))
      (let [W (:world (h9-prefix w r ds mode k mine pre))]
        (= (edge-ok-in W (await-edge W r (:next-id w) mode k d)) true)))
  (intros ent split)
  (have shape := (h9-prefix-shape xm w r ds mode k mine st fresh pre (List.cons Nat d tail) ent split))
  (have md (= (nat-mem d (nat-distinct ds)) true))
  (rw [← split ← reach-mem-nat-mem reach-mem-append reach-mem-cons Nat.beq_refl Bool.true_or Bool.or_true])
  (have orig := (h9-distinct-source ds d md))
  (have me := (Iff.mp (reach-mem-iff d ds) (Eq.trans (reach-mem-nat-mem d ds) orig)))
  (have ent2 := ent) (simp only [h9-entry] at ent2)
  (have hok := (And.right (And.right (And.right ent2))))
  (simp only [await-ok Bool.and_eq_true] at hok)
  (have ex := (tbl-all-mem Nat (deb-exists w) d ds (And.left (And.right (And.right (And.right hok)))) me))
  (have ac (= (act-has (:world (h9-prefix w r ds mode k mine pre)) (:next-id w)) true))
  (have sh := shape) (simp only [h9-shape] at sh)
  (simp only [act-has (And.left sh) tbl-has h9-act act-id Nat.beq_refl])
  (exact (h9-edge-ok-from-fields _ r (:next-id w) mode k d (h9-deb-shape w r ds mode k mine _ d shape ex) ac)))

(a/theorem h9-raise-view [fuel :- (List Nat)]
  (forall [d :- Nat, W :- World, todo :- (List RJ)]
    (And (= (:next-id (:world (raise-loop fuel d W todo))) (:next-id W))
         (= (:edges (:world (raise-loop fuel d W todo))) (:edges W))))
  (induction fuel)
  (case [nil] (intros d W todo) (cases todo) (all_goals (exact (And.intro (Eq.refl (:next-id W)) (Eq.refl (:edges W))))))
  (case [cons z f ih]
    (intros d W todo) (cases todo)
    (case [nil] (exact (And.intro (rfl) (rfl))))
    (case [cons j t]
      (cases hd (Nat.beq (:node j) d))
      (case [true] (simp only [raise-loop hd]) (exact (And.intro True.intro True.intro)))
      (case [false]
        (cases hn (Nat.ble (:need j) (comp-rank W (:node j))))
        (case [true] (simp only [raise-loop hd hn]) (exact (ih d W t)))
        (case [false] (simp only [raise-loop hd hn]) (exact (ih d _ _)))))))

(a/theorem h9-raise-run-view [W :- World, c :- Nat, d :- Nat]
  (And (= (:next-id (:world (raise-run W c d))) (:next-id W))
       (= (:edges (:world (raise-run W c d))) (:edges W)))
  (cases hd (comp-has W d))
  (case [false] (simp only [raise-run hd]) (exact (And.intro True.intro True.intro)))
  (case [true] (simp only [raise-run hd]) (exact (h9-raise-view (raise-fuel W) d W _))))

(a/theorem h9-fresh-find [W :- World, e :- EdgeRow]
  (=> (= (edge-ok-in W e) true)
      (= (edge-find (insert-edge-checked W e) (:next-id W))
         (Option.some EdgeRow (edge-set-marked false (edge-set-id (:next-id W) e)))))
  (intro hk)
  (simp only [insert-edge-checked hk insert-edge-fresh insert-edge edge-ins bump set-next-id set-edges tbl-ins
              edge-find tbl-find edge-id edge-set-marked edge-set-id Nat.beq_refl]))

(a/theorem h9-step-reuse-frame [r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, acc :- AwAcc, d :- Nat, e :- EdgeRow]
  (=> (= (inv-sample (:world acc)) true) (= (as-dep (:world acc) r d) true)
      (= (site-edge (:edges (:world acc)) (:of r) (:effect-index r) d) (Option.some EdgeRow e))
      (let [B (await-step r a mode k acc d)]
        (And (= (:next-id (:world B)) (:next-id (:world acc)))
         (And (= (:pairs B) (List.cons DE (DE.mk d (:id e)) (:pairs acc)))
          (And (= (:ok B) (:ok acc))
               (= (edge-find (:world B) (:id e))
                  (Option.some EdgeRow (edge-reawait (await-cont r mode k) e))))))))
  (intros hs hd hf)
  (have sm := (site-edge-mem (:edges (:world acc)) (:of r) (:effect-index r) d e hf))
  (have found := (find-self EdgeRow edge-id e (:edges (:world acc)) (edges-nodup (:world acc) hs) (And.left sm)))
  (have upd := (tbl-find-upd-same EdgeRow edge-id (:id e) (edge-reawait (await-cont r mode k))
                 (edge-reawait-edge-id _) (:edges (:world acc)) e found))
  (simp only [await-step hd hf])
  (exact (And.intro True.intro (And.intro True.intro (And.intro True.intro upd))))

)

(a/theorem h9-step-fresh-frame [r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, acc :- AwAcc, d :- Nat]
  (=> (= (inv-sample (:world acc)) true)
      (= (edge-ok-in (:world acc) (await-edge (:world acc) r a mode k d)) true)
      (Or (= (as-dep (:world acc) r d) false)
          (= (site-edge (:edges (:world acc)) (:of r) (:effect-index r) d) (Option.none EdgeRow)))
      (let [B (await-step r a mode k acc d), n (:next-id (:world acc)),
            e (edge-set-marked false (edge-set-id n (await-edge (:world acc) r a mode k d)))]
        (And (= (:next-id (:world B)) (+ n 1))
         (And (= (:pairs B) (List.cons DE (DE.mk d n) (:pairs acc)))
          (And (= (edge-find (:world B) n) (Option.some EdgeRow e))
               (= (:ok B)
                  (if (as-dep (:world acc) r d)
                    (Bool.and (:ok acc) (:ok (await-new-dep (:world acc) r a mode k d)))
                    (:ok acc))))))))
  (intros hs hk branch)
  (have fresh := (h9-fresh-find (:world acc) (await-edge (:world acc) r a mode k d) hk))
  (have alloc (= (:next-id (insert-edge-checked (:world acc) (await-edge (:world acc) r a mode k d))) (+ (:next-id (:world acc)) 1)))
  (simp only [insert-edge-checked hk insert-edge-fresh bump set-next-id])
  (cases hd (as-dep (:world acc) r d))
  (case [false]
    (have ni (= (:next-id (insert-edge-checked (:world acc) (await-edge (:world acc) r a mode k d))) (+ (:next-id (:world acc)) 1)))
    (simp only [insert-edge-checked hk insert-edge-fresh bump set-next-id])
    (simp only [await-step hd])
    (exact (And.intro ni (And.intro True.intro (And.intro fresh True.intro)))))
  (case [true]
    (have site (= (site-edge (:edges (:world acc)) (:of r) (:effect-index r) d) (Option.none EdgeRow)))
    (cases branch)
    (case [inl q] (rw [hd] at q) (cases q))
    (case [inr q] (exact q))
    (have view := (h9-raise-run-view (insert-edge-checked (:world acc) (await-edge (:world acc) r a mode k d)) (:of r) d))
    (have ni (= (:next-id (:world (await-new-dep (:world acc) r a mode k d))) (+ (:next-id (:world acc)) 1)))
    (exact (Eq.trans (And.left view) alloc))
    (have ei (= (edge-find (:world (await-new-dep (:world acc) r a mode k d)) (:next-id (:world acc)))
                (Option.some EdgeRow (edge-set-marked false (edge-set-id (:next-id (:world acc)) (await-edge (:world acc) r a mode k d))))))
    (simp only [edge-find await-new-dep (And.right view)]) (exact fresh)
    (simp only [await-step hd site])
    (exact (And.intro ni (And.intro True.intro (And.intro ei True.intro)))))

)

(a/theorem h9-rank-update-find [W :- World, x :- Nat, n :- Nat, k :- Nat, c :- CompRow]
  (=> (= (comp-find W x) (Option.some CompRow c)) (Exists (fn [c2 :- CompRow] (And (= (comp-find (comp-upd W n (comp-set-rank k)) x) (Option.some CompRow c2)) (And (= (:adopt-baselines c2) (:adopt-baselines c)) (And (= (:adopt-basis c2) (:adopt-basis c)) (= (:basis c2) (:basis c))))))))
  (intro hf)
  (cases hx (Nat.beq x n))
  (case [false]
    (apply (Exists.intro c)) (apply And.intro)
    (exact (Eq.trans (tbl-find-upd-ne CompRow comp-id n x (comp-set-rank k) (comp-set-rank-id k) (:comps W) hx) hf))
    (exact (And.intro (rfl) (And.intro (rfl) (rfl)))))
  (case [true]
    (have eq (= x n)) (exact (Nat.eq_of_beq_eq_true hx))
    (rw [← eq])
    (apply (Exists.intro (comp-set-rank k c))) (apply And.intro)
    (exact (hk-find-upd CompRow comp-id x (comp-set-rank k) (comp-set-rank-id k) (:comps W) c hf))
    (exact (And.intro (rfl) (And.intro (rfl) (rfl))))))

(a/theorem h9-raise-find [fuel :- (List Nat)]
  (forall [d :- Nat, W :- World, todo :- (List RJ), x :- Nat, c :- CompRow]
    (=> (= (comp-find W x) (Option.some CompRow c)) (Exists (fn [c2 :- CompRow] (And (= (comp-find (:world (raise-loop fuel d W todo)) x) (Option.some CompRow c2)) (And (= (:adopt-baselines c2) (:adopt-baselines c)) (And (= (:adopt-basis c2) (:adopt-basis c)) (= (:basis c2) (:basis c)))))))))
  (induction fuel)
  (case [nil]
    (intros d W todo x c hf) (cases todo)
    (all_goals (apply (Exists.intro c)))
    (all_goals (exact (And.intro hf (And.intro (rfl) (And.intro (rfl) (rfl)))))))
  (case [cons z f ih]
    (intros d W todo x c hf) (cases todo)
    (case [nil] (apply (Exists.intro c)) (exact (And.intro hf (And.intro (rfl) (And.intro (rfl) (rfl))))))
    (case [cons j t]
      (cases hd (Nat.beq (:node j) d))
      (case [true]
        (simp only [raise-loop hd])
        (apply (Exists.intro c)) (exact (And.intro hf (And.intro (rfl) (And.intro (rfl) (rfl))))))
      (case [false]
        (cases hn (Nat.ble (:need j) (comp-rank W (:node j))))
        (case [true] (simp only [raise-loop hd hn]) (exact (ih d W t x c hf)))
        (case [false]
          (have update := (h9-rank-update-find W x (:node j) (:need j) c hf))
          (cases update)
          (case [intro c2 h2]
            (have next := (ih d (comp-upd W (:node j) (comp-set-rank (:need j)))
                           (List.append RJ t (rjobs (+ (:need j) 1) (dep-creditors (:edges W) (:node j))))
                           x c2 (And.left h2)))
            (cases next)
            (case [intro c3 h3]
              (simp only [raise-loop hd hn])
              (apply (Exists.intro c3)) (apply And.intro) (exact (And.left h3))
              (exact (And.intro (Eq.trans (And.left (And.right h3)) (And.left (And.right h2)))
                       (And.intro (Eq.trans (And.left (And.right (And.right h3))) (And.left (And.right (And.right h2))))
                                  (Eq.trans (And.right (And.right (And.right h3))) (And.right (And.right (And.right h2))))))))))))))

(a/theorem h9-raise-run-find [W :- World, c :- Nat, d :- Nat, x :- Nat, row :- CompRow]
  (=> (= (comp-find W x) (Option.some CompRow row)) (Exists (fn [c2 :- CompRow] (And (= (comp-find (:world (raise-run W c d)) x) (Option.some CompRow c2)) (And (= (:adopt-baselines c2) (:adopt-baselines row)) (And (= (:adopt-basis c2) (:adopt-basis row)) (= (:basis c2) (:basis row))))))))
  (intro hf) (cases hd (comp-has W d))
  (case [false] (simp only [raise-run hd])
    (apply (Exists.intro row)) (exact (And.intro hf (And.intro (rfl) (And.intro (rfl) (rfl))))))
  (case [true] (simp only [raise-run hd]) (exact (h9-raise-find (raise-fuel W) d W _ x row hf))))

(a/theorem h9-consume-find [W :- World, site :- Nat, d :- Nat, x :- Nat, c :- CompRow, original :- CompRow]
  (=> (= (comp-find W x) (Option.some CompRow c)) (And (= (:adopt-baselines c) (:adopt-baselines original)) (And (= (:adopt-basis c) (:adopt-basis original)) (= (:basis c) (:basis original))))
      (Exists (fn [c2 :- CompRow]
        (And (= (comp-find (comp-upd W x (comp-consume-adopt site d)) x) (Option.some CompRow c2))
         (And (= (:adopt-baselines c2) (tbl-filter (adopt-other site d) (:adopt-baselines original)))
          (And (= (:adopt-basis c2) (:adopt-basis original)) (= (:basis c2) (:basis original))))))))
  (intros hf fields)
  (apply (Exists.intro (comp-consume-adopt site d c)))
  (apply And.intro)
  (exact (hk-find-upd CompRow comp-id x (comp-consume-adopt site d) (comp-consume-adopt-comp-id site d) (:comps W) c hf))
  (apply And.intro)
  (exact (congrArg (fn [bs :- (List AdoptBase)] (tbl-filter (adopt-other site d) bs)) (And.left fields)))
  (exact (And.right fields)))

(a/theorem h9-step-adoption [r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, acc :- AwAcc, d :- Nat, c :- CompRow]
  (=> (= (inv-sample (:world acc)) true) (= (as-dep (:world acc) r d) true)
      (= (comp-find (:world acc) (:of r)) (Option.some CompRow c))
      (Exists (fn [c2 :- CompRow]
        (And (= (comp-find (:world (await-step r a mode k acc d)) (:of r)) (Option.some CompRow c2))
         (And (= (:adopt-baselines c2)
                 (tbl-filter (adopt-other (:effect-index r) d) (:adopt-baselines c)))
          (And (= (:adopt-basis c2) (:adopt-basis c)) (= (:basis c2) (:basis c))))))))
  (intros hs hd hf)
  (cases site (site-edge (:edges (:world acc)) (:of r) (:effect-index r) d))
  (case [some e]
    (simp only [await-step hd site])
    (exact (h9-consume-find (edge-upd (:world acc) (:id e) (edge-reawait (await-cont r mode k)))
             (:effect-index r) d (:of r) c c hf (And.intro (rfl) (And.intro (rfl) (rfl))))))
  (case [none]
    (have inserted (= (comp-find (insert-edge-checked (:world acc) (await-edge (:world acc) r a mode k d)) (:of r)) (Option.some CompRow c)))
    (cases ok (edge-ok-in (:world acc) (await-edge (:world acc) r a mode k d)))
    (case [false] (simp only [insert-edge-checked ok]) (exact hf))
    (case [true] (simp only [insert-edge-checked ok]) (exact hf))
    (have raised := (h9-raise-run-find (insert-edge-checked (:world acc) (await-edge (:world acc) r a mode k d)) (:of r) d (:of r) c inserted))
    (cases raised)
    (case [intro c1 fields]
      (simp only [await-step hd site])
      (exact (h9-consume-find (:world (await-new-dep (:world acc) r a mode k d)) (:effect-index r) d (:of r) c1 c (And.left fields) (And.right fields)))))

)

(a/theorem h9-row-uniq [A :- Type, idf :- (=> A Nat), a :- A, b :- A, xs :- (List A)]
  (=> (= (nat-nodup (tbl-ids idf xs)) true) (List.Mem a xs) (List.Mem b xs) (= (idf a) (idf b)) (= a b))
  (intros nd ma mb eq)
  (have fa := (find-self A idf a xs nd ma))
  (have fb := (find-self A idf b xs nd mb))
  (rw [eq fb] at fa) (exact (Eq.symm (Option.some.inj fa))))

(a/theorem h9-aha-run [W :- World, a :- ActRow, q :- RunRow]
  (=> (= (aha W) true) (List.Mem a (:acts W)) (List.Mem q (:runs W)) (= (:id q) (:run a)) (= (run-alive q) true))
  (intros ha ma mq eq)
  (have al := (aha-acts-alive W ha)) (simp only [acts-alive] at al)
  (have row := (tbl-all-mem RunRow _ q _ (tbl-all-mem ActRow _ a _ al ma) mq))
  (simp only [run-ok-for eq Nat.beq_refl Bool.not_true Bool.false_or] at row) (exact row))

(a/theorem h9-free-creditor [xm :- (List Nat), W :- World, r :- RunRow, b :- ActRow, e :- EdgeRow]
  (=> (= (h3 xm W) true) (= (aha W) true) (= (ar W) true)
      (= (gx (Ex.mk (:id r) (:id b)) W) true)
      (List.Mem b (:acts W)) (= (:members b) (List.nil Member))
      (List.Mem r (:runs W)) (= (run-alive r) true) (List.Mem e (:edges W))
      (Or (And (= (Nat.beq (:kind e) ek-dep) true) (= (:creditor e) (:of r)))
          (And (= (Nat.beq (:kind e) ek-dep) false) (= (:creditor e) (:id b))))
      (= (h3-free xm W (:id e)) true))
  (intros h ha har hx mb empty mr al me cred)
  (have hs := (h3-sample xm W h))
  (apply h3-free-by)
  (intros a q ma mq runeq exempt current member mex)
  (have ob := (h3-ob-use xm W a q (:id e) e (h3-rest-of xm W h) ma mq runeq exempt current member mex me (rfl)))
  (have st := (And.left ob)) (simp only [h3-s Bool.and_eq_true] at st)
  (have aid (= (:id a) (:id b)))
  (cases cred)
  (case [inl dep]
    (have qc := (And.left (And.right st)))
    (simp only [(And.left dep) Bool.not_true Bool.false_or] at qc)
    (have ofq (= (:of q) (:of r)))
    (have ce := (Nat.eq_of_beq_eq_true qc)) (try (simp only [rk3] at ce))
    (rw [← ce]) (exact (And.right dep))
    (apply (any-elim CompRow (h3-cur (rk3 q)) _ (:comps W) current))
    (intros c mc cp)
    (simp only [h3-cur Bool.and_eq_true] at cp)
    (have cq (= (:id c) (:of q))) (exact (Nat.eq_of_beq_eq_true (And.left cp)))
    (have cr (= (:id c) (:of r))) (exact (Eq.trans cq ofq))
    (have aq := (h9-aha-run W a q ha ma mq runeq))
    (have qr := (h3-ar-run W q c har mq aq mc cq))
    (have rr := (h3-ar-run W r c har mr al mc cr))
    (have arun (= (:run a) (:id r))) (rw [← runeq ← qr]) (exact rr)
    (have gxparts := (gr-parts (act-rows-good-x (Ex.mk (:id r) (:id b))) W (gx-rest-of _ W hx)))
    (have good := (tbl-all-mem ActRow _ a _ (And.left (And.right gxparts)) ma))
    (simp only [act-rows-good-x arun Nat.beq_refl] at good)
    (exact (Nat.eq_of_beq_eq_true good)))
  (case [inr wait]
    (have ac := (And.left (And.right (And.right st))))
    (simp only [(And.left wait) Bool.false_or] at ac)
    (have eq := (Nat.eq_of_beq_eq_true ac))
    (exact (Eq.trans (Eq.symm eq) (And.right wait))))
  (have same := (h9-row-uniq ActRow act-id a b (:acts W) (h3-acts-nodup W hs) ma mb aid))
  (rw [same] at member)
  (simp only [act-contrib empty member-edges reach-mem] at member)
  (cases member))

(a/theorem h9-prefix-free-edge [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, pre :- (List Nat), tail :- (List Nat), e :- EdgeRow]
  (=> (h9-entry xm w r ds mode st fresh) (= (List.append Nat pre tail) (nat-distinct ds))
      (List.Mem e (:edges (:world (h9-prefix w r ds mode k mine pre))))
      (Or (And (= (Nat.beq (:kind e) ek-dep) true) (= (:creditor e) (:of r)))
          (And (= (Nat.beq (:kind e) ek-dep) false) (= (:creditor e) (:next-id w))))
      (= (h3-free xm (:world (h9-prefix w r ds mode k mine pre)) (:id e)) true))
  (intros ent split me cred)
  (have shape := (h9-prefix-shape xm w r ds mode k mine st fresh pre tail ent split))
  (have support := (h9-prefix-support xm w r ds mode k mine st fresh pre tail ent split))
  (simp only [h9-shape] at shape) (simp only [h9-support] at support)
  (have ent2 := ent) (simp only [h9-entry] at ent2)
  (have ht := (And.left (And.right (And.right ent2))))
  (have mr := (And.left (tok-facts w st r ht)))
  (have hok := (And.right (And.right (And.right ent2))))
  (simp only [await-ok Bool.and_eq_true] at hok)
  (have al := (normal-alive r (And.left (And.right hok))))
  (have before := (find-self RunRow run-id r (:runs w) (lit-runs-nodup w (h3-sample xm w (And.left (And.right ent2)))) mr))
  (have after := (hk-find-upd RunRow run-id (:id r) run-tick run-tick-run-id (:runs w) r before))
  (have stored (List.Mem (run-tick r) (:runs (:world (h9-prefix w r ds mode k mine pre)))))
  (rw [(And.left (And.right shape))])
  (exact (tbl-find-mem RunRow run-id (:id r) (run-tick r) (:runs (run-upd w (:id r) run-tick)) after))
  (have head (List.Mem (h9-act w r ds mode k mine) (:acts (:world (h9-prefix w r ds mode k mine pre)))))
  (rw [(And.left shape)]) (exact (List.Mem.head _))
  (exact (h9-free-creditor xm _ (run-tick r) (h9-act w r ds mode k mine) e
           (And.left support) (And.left (And.right (And.right support))) (And.left (And.right (And.right (And.right (And.right support))))) (And.right (And.right (And.right (And.right (And.right (And.right (And.right (And.right (And.right (And.right support))))))))))
           head (rfl) stored al me cred)))

(a/theorem h9-prefix-reuse-free [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, pre :- (List Nat), tail :- (List Nat), d :- Nat, e :- EdgeRow]
  (=> (h9-entry xm w r ds mode st fresh) (= (List.append Nat pre (List.cons Nat d tail)) (nat-distinct ds))
      (= (as-dep (:world (h9-prefix w r ds mode k mine pre)) r d) true)
      (= (site-edge (:edges (:world (h9-prefix w r ds mode k mine pre))) (:of r) (:effect-index r) d)
         (Option.some EdgeRow e))
      (= (h3-free xm (:world (h9-prefix w r ds mode k mine pre)) (:id e)) true))
  (intros ent split dep site)
  (have sm := (site-edge-mem (:edges (:world (h9-prefix w r ds mode k mine pre))) (:of r) (:effect-index r) d e site))
  (have sp := (h3-site-p _ (:of r) (:effect-index r) d e site))
  (simp only [site-edge-p Bool.and_eq_true] at sp)
  (exact (h9-prefix-free-edge xm w r ds mode k mine st fresh pre (List.cons Nat d tail) e ent split (And.left sm)
           (Or.inl (And.intro (And.left sp) (Nat.eq_of_beq_eq_true (And.left (And.right sp)))))))

)

(a/theorem h9-old-insert-find [W :- World, new :- EdgeRow, x :- Nat, e :- EdgeRow]
  (=> (= (inv-sample W) true) (= (edge-find W x) (Option.some EdgeRow e))
      (= (edge-find (insert-edge-checked W new) x) (Option.some EdgeRow e)))
  (intros hs hf)
  (have me := (tbl-find-mem EdgeRow edge-id x e (:edges W) hf))
  (have ix := (find-id W x e hf))
  (have lt := (gd-lt-of _ _ (run-ref-ok-edge W e hs me)))
  (have ne (= (Nat.beq (:next-id W) x) false))
  (cases eq (Nat.beq (:next-id W) x))
  (case [false] (rfl))
  (case [true] (have same := (Nat.eq_of_beq_eq_true eq)) (omega))
  (cases hk (edge-ok-in W new))
  (case [false] (simp only [insert-edge-checked hk]) (exact hf))
  (case [true]
    (simp only [insert-edge-checked hk insert-edge-fresh insert-edge edge-ins bump set-next-id set-edges tbl-ins
                edge-find tbl-find edge-id edge-set-marked edge-set-id ne])
    (exact hf)))

(a/theorem h9-old-step-find [r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, acc :- AwAcc, d :- Nat, x :- Nat, e :- EdgeRow]
  (=> (= (inv-sample (:world acc)) true) (= (edge-find (:world acc) x) (Option.some EdgeRow e))
      (= (Nat.beq (:debtor e) d) false)
      (= (edge-find (:world (await-step r a mode k acc d)) x) (Option.some EdgeRow e)))
  (intros hs hf ne)
  (cases hd (as-dep (:world acc) r d))
  (case [false] (simp only [await-step hd]) (exact (h9-old-insert-find (:world acc) _ x e hs hf)))
  (case [true]
    (cases site (site-edge (:edges (:world acc)) (:of r) (:effect-index r) d))
    (case [none]
      (have view := (h9-raise-run-view (insert-edge-checked (:world acc) (await-edge (:world acc) r a mode k d)) (:of r) d))
      (simp only [await-step hd site comp-upd set-comps edge-find await-new-dep (And.right view)])
      (exact (h9-old-insert-find (:world acc) _ x e hs hf)))
    (case [some picked]
      (have sm := (site-edge-mem (:edges (:world acc)) (:of r) (:effect-index r) d picked site))
      (have pf (= (edge-find (:world acc) (:id picked)) (Option.some EdgeRow picked)))
      (exact (find-self EdgeRow edge-id picked (:edges (:world acc)) (edges-nodup (:world acc) hs) (And.left sm)))
      (have off (= (Nat.beq x (:id picked)) false))
      (cases eq (Nat.beq x (:id picked)))
      (case [false] (rfl))
      (case [true]
        (have id := (Nat.eq_of_beq_eq_true eq))
        (have ef := hf) (rw [id pf] at ef)
        (have same := (Option.some.inj ef))
        (rw [← same (And.right sm)] at ne) (cases ne))
      (have lookup := (tbl-find-upd-ne EdgeRow edge-id (:id picked) x (edge-reawait (await-cont r mode k)) (edge-reawait-edge-id _) (:edges (:world acc)) off))
      (simp only [await-step hd site])
      (exact (Eq.trans lookup hf)))))

(a/theorem h9-fresh-fields [P :- World, W :- World, r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, d :- Nat, n :- Nat]
  (=> (= (as-dep W r d) (as-dep P r d))
      (h9-edge-fields P r a mode k d (edge-set-marked false (edge-set-id n (await-edge W r a mode k d)))))
  (intro same) (cases dep (as-dep W r d))
  (all_goals (simp only [h9-edge-fields (Eq.symm same) await-edge dep edge-set-marked edge-set-id]))
  (all_goals (exact (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro (And.intro True.intro True.intro))))))))

(a/theorem h9-reuse-fields [P :- World, r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, d :- Nat, e :- EdgeRow]
  (=> (= (as-dep P r d) true) (= (site-edge-p (:of r) (:effect-index r) d e) true)
      (h9-edge-fields P r a mode k d (edge-reawait (await-cont r mode k) e)))
  (intros dep sp) (simp only [site-edge-p Bool.and_eq_true] at sp)
  (simp only [h9-edge-fields dep edge-reawait])
  (exact (And.intro (Nat.eq_of_beq_eq_true (And.right (And.right (And.right sp))))
           (And.intro (Nat.eq_of_beq_eq_true (And.left (And.right (And.right sp))))
            (And.intro True.intro (And.intro (Nat.eq_of_beq_eq_true (And.left sp))
             (And.intro (Nat.eq_of_beq_eq_true (And.left (And.right sp))) True.intro)))))))

(a/theorem h9-dehas-debtors [ps :- (List DE), d :- Nat]
  (= (nat-mem d (h9-debtors ps)) (de-has d ps))
  (induction ps)
  (case [nil] (simp only [h9-debtors nat-mem de-has tbl-any]))
  (case [cons p t ih]
    (cases eq (Nat.beq (:deb p) d))
    (all_goals (simp only [h9-debtors nat-mem de-has tbl-any eq ih Bool.false_or Bool.true_or]))))

(a/theorem h9-step-debtors [r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, acc :- AwAcc, d :- Nat]
  (= (h9-debtors (:pairs (await-step r a mode k acc d))) (List.cons Nat d (h9-debtors (:pairs acc))))
  (cases dep (as-dep (:world acc) r d))
  (case [false] (simp only [await-step dep h9-debtors]))
  (case [true]
    (cases site (site-edge (:edges (:world acc)) (:of r) (:effect-index r) d))
    (all_goals (simp only [await-step dep site h9-debtors]))))

(a/theorem h9-wire-dehas [r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, xs :- (List Nat)]
  (forall [acc :- AwAcc, d :- Nat]
    (= (de-has d (:pairs (await-wire r a mode k acc xs))) (Bool.or (nat-mem d xs) (de-has d (:pairs acc)))))
  (induction xs)
  (case [nil] (intros acc d) (simp only [await-wire nat-mem Bool.false_or]))
  (case [cons x t ih]
    (intros acc d) (cases eq (Nat.beq x d))
    (all_goals (simp only [await-wire (ih (await-step r a mode k acc x) d) dehas-step nat-mem eq Bool.false_or Bool.true_or Bool.or_true]))))

(a/theorem h9-wire-count [r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, xs :- (List Nat)]
  (forall [acc :- AwAcc]
    (= (nat-len (h9-debtors (:pairs (await-wire r a mode k acc xs)))) (+ (nat-len xs) (nat-len (h9-debtors (:pairs acc))))))
  (induction xs)
  (case [nil] (intro acc) (simp only [await-wire nat-len Nat.zero_add]))
  (case [cons x t ih]
    (intro acc)
    (simp only [await-wire (ih (await-step r a mode k acc x)) h9-step-debtors nat-len]) (omega)))

(a/theorem h9-mem-append [d :- Nat, xs :- (List Nat), ys :- (List Nat)]
  (= (nat-mem d (List.append Nat xs ys)) (Bool.or (nat-mem d xs) (nat-mem d ys)))
  (induction xs)
  (case [nil] (simp only [List.append nat-mem Bool.false_or]))
  (case [cons x t ih] (cases eq (Nat.beq x d))
    (all_goals (simp only [List.append nat-mem eq ih Bool.true_or]))))

(a/theorem h9-nodup-append [xs :- (List Nat), ys :- (List Nat)]
  (=> (= (nat-nodup (List.append Nat xs ys)) true)
      (And (= (nat-nodup xs) true)
       (And (= (nat-nodup ys) true)
            (forall [d :- Nat] (=> (= (nat-mem d ys) true) (= (nat-mem d xs) false))))))
  (induction xs)
  (case [nil]
    (intro h) (simp only [List.append] at h)
    (apply And.intro) (rfl)
    (apply And.intro) (exact h)
    (intros d md) (rfl))
  (case [cons x t ih]
    (intro h) (simp only [List.append nat-nodup Bool.and_eq_true] at h)
    (have none := (bnot-true _ (And.left h)))
    (have nt (= (nat-mem x t) false))
    (cases q (nat-mem x t))
    (case [false] (rfl))
    (case [true] (rw [h9-mem-append q Bool.true_or] at none) (cases none))
    (have ny (= (nat-mem x ys) false))
    (cases q (nat-mem x ys))
    (case [false] (rfl))
    (case [true] (rw [h9-mem-append q Bool.or_true] at none) (cases none))
    (have tail := (ih (And.right h)))
    (apply And.intro)
    (simp only [nat-nodup nt Bool.not_false Bool.true_and]) (exact (And.left tail))
    (apply And.intro) (exact (And.left (And.right tail)))
    (intros d md)
    (have old := ((And.right (And.right tail)) d md))
    (have ne (= (Nat.beq x d) false))
    (cases eq (Nat.beq x d))
    (case [false] (rfl))
    (case [true] (have same := (Nat.eq_of_beq_eq_true eq)) (rw [← same] at md) (rw [ny] at md) (cases md))
    (simp only [nat-mem ne]) (exact old)))

(a/theorem h9-wire-nodup [r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, xs :- (List Nat)]
  (forall [acc :- AwAcc]
    (=> (= (nat-nodup xs) true) (= (nat-nodup (h9-debtors (:pairs acc))) true)
        (forall [d :- Nat] (=> (= (nat-mem d xs) true) (= (de-has d (:pairs acc)) false)))
        (= (nat-nodup (h9-debtors (:pairs (await-wire r a mode k acc xs)))) true)))
  (induction xs)
  (case [nil] (intros acc nd old off) (simp only [await-wire]) (exact old))
  (case [cons d t ih]
    (intros acc nd old off)
    (simp only [nat-nodup Bool.and_eq_true] at nd)
    (have no := (bnot-true _ (And.left nd)))
    (have md (= (nat-mem d (List.cons Nat d t)) true))
    (simp only [nat-mem Nat.beq_refl])
    (have first := (off d md))
    (have next (= (nat-nodup (h9-debtors (:pairs (await-step r a mode k acc d)))) true))
    (simp only [h9-step-debtors nat-nodup h9-dehas-debtors first old Bool.not_false Bool.and_self])
    (have later (forall [y :- Nat] (=> (= (nat-mem y t) true) (= (de-has y (:pairs (await-step r a mode k acc d))) false))))
    (intros y my)
    (have ne (= (Nat.beq d y) false))
    (cases eq (Nat.beq d y))
    (case [false] (rfl))
    (case [true] (have same := (Nat.eq_of_beq_eq_true eq)) (rw [← same] at my) (rw [no] at my) (cases my))
    (have before := (off y (Eq.trans (congrArg (fn [b :- Bool] (if b true (nat-mem y t))) ne) my)))
    (simp only [dehas-step ne before Bool.false_or])
    (simp only [await-wire]) (exact (ih _ (And.right nd) next later))))

(a/theorem h9-fields-cons [P :- World, r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, W :- World, ps :- (List DE), d :- Nat, n :- Nat, new :- EdgeRow]
  (=> (= (edge-find W n) (Option.some EdgeRow new)) (= (:id new) n) (h9-edge-fields P r a mode k d new)
      (forall [p :- DE] (=> (List.Mem p ps) (Exists (fn [e :- EdgeRow] (And (= (edge-find W (:edge p)) (Option.some EdgeRow e)) (And (= (:id e) (:edge p)) (h9-edge-fields P r a mode k (:deb p) e))))))) (forall [p :- DE] (=> (List.Mem p (List.cons DE (DE.mk d n) ps)) (Exists (fn [e :- EdgeRow] (And (= (edge-find W (:edge p)) (Option.some EdgeRow e)) (And (= (:id e) (:edge p)) (h9-edge-fields P r a mode k (:deb p) e))))))))
  (intros lookup id fields old p mp)
  (cases mp)
  (case [head] (apply (Exists.intro new)) (exact (And.intro lookup (And.intro id fields))))
  (case [tail tail] (exact (old p tail))))

(a/theorem h9-fields-step [P :- World, r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, acc :- AwAcc, d :- Nat]
  (=> (= (inv-sample (:world acc)) true) (= (edge-ok-in (:world acc) (await-edge (:world acc) r a mode k d)) true)
      (= (as-dep (:world acc) r d) (as-dep P r d))
      (forall [p :- DE] (=> (List.Mem p (:pairs acc)) (= (Nat.beq (:deb p) d) false)))
      (forall [p :- DE] (=> (List.Mem p (:pairs acc)) (Exists (fn [e :- EdgeRow] (And (= (edge-find (:world acc) (:edge p)) (Option.some EdgeRow e)) (And (= (:id e) (:edge p)) (h9-edge-fields P r a mode k (:deb p) e))))))) (forall [p :- DE] (=> (List.Mem p (:pairs (await-step r a mode k acc d))) (Exists (fn [e :- EdgeRow] (And (= (edge-find (:world (await-step r a mode k acc d)) (:edge p)) (Option.some EdgeRow e)) (And (= (:id e) (:edge p)) (h9-edge-fields P r a mode k (:deb p) e))))))))
  (intros hs hk stable off old)
  (have keep (forall [p :- DE] (=> (List.Mem p (:pairs acc)) (Exists (fn [e :- EdgeRow] (And (= (edge-find (:world (await-step r a mode k acc d)) (:edge p)) (Option.some EdgeRow e)) (And (= (:id e) (:edge p)) (h9-edge-fields P r a mode k (:deb p) e))))))))
  (intros p mp)
  (have row := (old p mp)) (cases row)
  (case [intro e found]
    (have deb := (And.left (And.right (And.right found))))
    (have ne (= (Nat.beq (:debtor e) d) false)) (rw [deb]) (exact (off p mp))
    (apply (Exists.intro e))
    (exact (And.intro (h9-old-step-find r a mode k acc d (:edge p) e hs (And.left found) ne) (And.right found))))
  (cases dep (as-dep (:world acc) r d))
  (case [false]
    (have frame := (h9-step-fresh-frame r a mode k acc d hs hk (Or.inl dep)))
    (rw [(And.left (And.right frame))])
    (exact (h9-fields-cons P r a mode k (:world (await-step r a mode k acc d)) (:pairs acc) d (:next-id (:world acc))
             (edge-set-marked false (edge-set-id (:next-id (:world acc)) (await-edge (:world acc) r a mode k d)))
             (And.left (And.right (And.right frame))) (rfl) (h9-fresh-fields P (:world acc) r a mode k d (:next-id (:world acc)) stable) keep)))
  (case [true]
    (cases site (site-edge (:edges (:world acc)) (:of r) (:effect-index r) d))
    (case [none]
      (have frame := (h9-step-fresh-frame r a mode k acc d hs hk (Or.inr site)))
      (rw [(And.left (And.right frame))])
      (exact (h9-fields-cons P r a mode k (:world (await-step r a mode k acc d)) (:pairs acc) d (:next-id (:world acc))
               (edge-set-marked false (edge-set-id (:next-id (:world acc)) (await-edge (:world acc) r a mode k d)))
               (And.left (And.right (And.right frame))) (rfl) (h9-fresh-fields P (:world acc) r a mode k d (:next-id (:world acc)) stable) keep)))
    (case [some picked]
      (have frame := (h9-step-reuse-frame r a mode k acc d picked hs dep site))
      (have dp (= (as-dep P r d) true)) (exact (Eq.trans (Eq.symm stable) dep))
      (rw [(And.left (And.right frame))])
      (exact (h9-fields-cons P r a mode k (:world (await-step r a mode k acc d)) (:pairs acc) d (:id picked)
               (edge-reawait (await-cont r mode k) picked)
               (And.right (And.right (And.right frame))) (rfl)
               (h9-reuse-fields P r a mode k d picked dp (h3-site-p _ (:of r) (:effect-index r) d picked site)) keep)))))

(a/theorem h9-app-nil [xs :- (List Nat)] (= (List.append Nat xs (List.nil Nat)) xs)
  (induction xs)
  (case [nil] (rfl))
  (case [cons x t ih] (simp only [List.append ih])))

(a/theorem h9-app-assoc [xs :- (List Nat), ys :- (List Nat), zs :- (List Nat)]
  (= (List.append Nat (List.append Nat xs ys) zs) (List.append Nat xs (List.append Nat ys zs)))
  (induction xs)
  (case [nil] (rfl))
  (case [cons x t ih] (simp only [List.append ih])))

(a/theorem h9-wire-append [r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, xs :- (List Nat)]
  (forall [ys :- (List Nat), acc :- AwAcc]
    (= (await-wire r a mode k acc (List.append Nat xs ys)) (await-wire r a mode k (await-wire r a mode k acc xs) ys)))
  (induction xs)
  (case [nil] (intros ys acc) (rfl))
  (case [cons d t ih] (intros ys acc) (simp only [List.append await-wire]) (exact (ih ys (await-step r a mode k acc d)))))

(a/theorem h9-prefix-snoc [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), pre :- (List Nat), d :- Nat]
  (= (h9-prefix w r ds mode k mine (List.append Nat pre (List.cons Nat d (List.nil Nat))))
     (await-step r (:next-id w) mode k (h9-prefix w r ds mode k mine pre) d))
  (exact (h9-wire-append r (:next-id w) mode k pre (List.cons Nat d (List.nil Nat)) (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true))))

(a/theorem h9-prefix-has [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), pre :- (List Nat), d :- Nat]
  (= (de-has d (:pairs (h9-prefix w r ds mode k mine pre))) (nat-mem d pre))
  (have h := (h9-wire-dehas r (:next-id w) mode k pre (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) d))
  (simp only [de-has tbl-any Bool.or_false] at h) (exact h))

(a/theorem h9-prefix-process [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, xs :- (List Nat)]
  (forall [pre :- (List Nat), tail :- (List Nat)]
    (=> (h9-entry xm w r ds mode st fresh) (= (List.append Nat pre (List.append Nat xs tail)) (nat-distinct ds))
        (forall [p :- DE] (=> (List.Mem p (:pairs (h9-prefix w r ds mode k mine pre))) (Exists (fn [e :- EdgeRow] (And (= (edge-find (:world (h9-prefix w r ds mode k mine pre)) (:edge p)) (Option.some EdgeRow e)) (And (= (:id e) (:edge p)) (h9-edge-fields (await-pre w r ds mode k mine) r (:next-id w) mode k (:deb p) e))))))) (forall [p :- DE] (=> (List.Mem p (:pairs (h9-prefix w r ds mode k mine (List.append Nat pre xs)))) (Exists (fn [e :- EdgeRow] (And (= (edge-find (:world (h9-prefix w r ds mode k mine (List.append Nat pre xs))) (:edge p)) (Option.some EdgeRow e)) (And (= (:id e) (:edge p)) (h9-edge-fields (await-pre w r ds mode k mine) r (:next-id w) mode k (:deb p) e)))))))))
  (induction xs)
  (case [nil] (intros pre tail ent split old) (rw [h9-app-nil]) (exact old))
  (case [cons d t ih]
    (intros pre tail ent split old)
    (have sup := (h9-prefix-support xm w r ds mode k mine st fresh pre (List.cons Nat d (List.append Nat t tail)) ent split))
    (have shape := (h9-prefix-shape xm w r ds mode k mine st fresh pre (List.cons Nat d (List.append Nat t tail)) ent split))
    (have guard := (h9-next-edge-ok xm w r ds mode k mine st fresh pre (List.append Nat t tail) d ent split))
    (have inv := (h3-sample xm _ (And.left sup)))
    (have stable := (Eq.trans (h9-as-dep-shape w r ds mode k mine _ d shape)
                      (Eq.symm (h9-as-dep-shape w r ds mode k mine _ d (h9-shape-pre w r ds mode k mine)))))
    (have nd (= (nat-nodup (List.append Nat pre (List.cons Nat d (List.append Nat t tail)))) true))
    (rw [split]) (exact (distinct-nodup ds))
    (have parts := (h9-nodup-append pre (List.cons Nat d (List.append Nat t tail)) nd))
    (have dm (= (nat-mem d (List.cons Nat d (List.append Nat t tail))) true)) (simp only [nat-mem Nat.beq_refl])
    (have absent := ((And.right (And.right parts)) d dm))
    (have offd := (Eq.trans (h9-prefix-has w r ds mode k mine pre d) absent))
    (have off (forall [p :- DE] (=> (List.Mem p (:pairs (h9-prefix w r ds mode k mine pre))) (= (Nat.beq (:deb p) d) false))))
    (intros p mp)
    (have all := (any-false-all DE (fn [p :- DE] (Nat.beq (:deb p) d)) (:pairs (h9-prefix w r ds mode k mine pre)) offd))
    (have q := (tbl-all-mem DE _ p _ all mp)) (exact (bnot-true _ q))
    (have next := (h9-fields-step (await-pre w r ds mode k mine) r (:next-id w) mode k (h9-prefix w r ds mode k mine pre) d inv guard stable off old))
    (have extended (forall [p :- DE] (=> (List.Mem p (:pairs (h9-prefix w r ds mode k mine (List.append Nat pre (List.cons Nat d (List.nil Nat)))))) (Exists (fn [e :- EdgeRow] (And (= (edge-find (:world (h9-prefix w r ds mode k mine (List.append Nat pre (List.cons Nat d (List.nil Nat))))) (:edge p)) (Option.some EdgeRow e)) (And (= (:id e) (:edge p)) (h9-edge-fields (await-pre w r ds mode k mine) r (:next-id w) mode k (:deb p) e))))))))
    (rw [h9-prefix-snoc]) (exact next)
    (have split2 (= (List.append Nat (List.append Nat pre (List.cons Nat d (List.nil Nat))) (List.append Nat t tail)) (nat-distinct ds)))
    (rw [h9-app-assoc]) (exact split)
    (have final := (ih (List.append Nat pre (List.cons Nat d (List.nil Nat))) tail ent split2 extended))
    (rw [h9-app-assoc] at final) (exact final)))

(a/theorem h9-prefix-fields [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, pre :- (List Nat), tail :- (List Nat)]
  (=> (h9-entry xm w r ds mode st fresh) (= (List.append Nat pre tail) (nat-distinct ds)) (forall [p :- DE] (=> (List.Mem p (:pairs (h9-prefix w r ds mode k mine pre))) (Exists (fn [e :- EdgeRow] (And (= (edge-find (:world (h9-prefix w r ds mode k mine pre)) (:edge p)) (Option.some EdgeRow e)) (And (= (:id e) (:edge p)) (h9-edge-fields (await-pre w r ds mode k mine) r (:next-id w) mode k (:deb p) e))))))))
  (intros ent split)
  (have base (forall [p :- DE] (=> (List.Mem p (:pairs (h9-prefix w r ds mode k mine (List.nil Nat)))) (Exists (fn [e :- EdgeRow] (And (= (edge-find (:world (h9-prefix w r ds mode k mine (List.nil Nat))) (:edge p)) (Option.some EdgeRow e)) (And (= (:id e) (:edge p)) (h9-edge-fields (await-pre w r ds mode k mine) r (:next-id w) mode k (:deb p) e))))))))
  (intros p mp) (cases mp)
  (exact (h9-prefix-process xm w r ds mode k mine st fresh pre (List.nil Nat) tail ent split base)))

(a/theorem h9-prefix-pairs [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, pre :- (List Nat), tail :- (List Nat)]
  (=> (h9-entry xm w r ds mode st fresh) (= (List.append Nat pre tail) (nat-distinct ds))
      (h9-pairs pre tail (:pairs (h9-prefix w r ds mode k mine pre))))
  (intros ent split)
  (have nd (= (nat-nodup (List.append Nat pre tail)) true)) (rw [split]) (exact (distinct-nodup ds))
  (have parts := (h9-nodup-append pre tail nd))
  (have fields := (h9-prefix-fields xm w r ds mode k mine st fresh pre tail ent split))
  (simp only [h9-pairs])
  (apply And.intro)
  (intro d) (rw [h9-prefix-has])
  (apply Iff.intro) (intro q) (exact q) (intro q) (exact q)
  (apply And.intro)
  (have count := (h9-wire-count r (:next-id w) mode k pre (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true)))
  (simp only [h9-debtors nat-len Nat.add_zero] at count) (exact count)
  (apply And.intro)
  (exact (h9-wire-nodup r (:next-id w) mode k pre (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true)
           (And.left parts) (rfl) (fn [d :- Nat, md :- (= (nat-mem d pre) true)] (Eq.refl false))))
  (apply And.intro)
  (intros d md) (exact (Eq.trans (h9-prefix-has w r ds mode k mine pre d) ((And.right (And.right parts)) d md)))
  (intros p q mp mq same)
  (have fp := (fields p mp)) (cases fp)
  (case [intro ep fp]
    (have fq := (fields q mq)) (cases fq)
    (case [intro eq fq]
      (have lookup := (And.left fp)) (rw [same (And.left fq)] at lookup)
      (have rows := (Option.some.inj lookup))
      (have pd := (And.left (And.right (And.right fp))))
      (have qd := (And.left (And.right (And.right fq))))
      (rw [rows] at qd)
      (exact (Eq.trans (Eq.symm pd) qd))))

)

(a/theorem h9-pair-picked [ps :- (List DE), d :- Nat]
  (=> (= (de-has d ps) true)
      (Exists (fn [p :- DE] (And (List.Mem p ps) (And (= (:deb p) d) (= (:edge p) (pair-edge d ps)))))))
  (induction ps)
  (case [nil] (intro h) (simp only [de-has tbl-any] at h) (cases h))
  (case [cons p t ih]
    (intro h) (cases eq (Nat.beq (:deb p) d))
    (case [true]
      (apply (Exists.intro p)) (apply And.intro) (exact (List.Mem.head t))
      (apply And.intro) (exact (Nat.eq_of_beq_eq_true eq))
      (simp only [pair-edge eq]))
    (case [false]
      (simp only [de-has tbl-any eq Bool.false_or] at h)
      (have row := (ih h)) (cases row)
      (case [intro q proof]
        (apply (Exists.intro q)) (apply And.intro) (exact (List.Mem.tail p (And.left proof)))
        (simp only [pair-edge eq]) (exact (And.right proof))))))

(a/theorem h9-prefix-pair-edge [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, pre :- (List Nat), tail :- (List Nat), d :- Nat]
  (=> (h9-entry xm w r ds mode st fresh) (= (List.append Nat pre tail) (nat-distinct ds)) (= (nat-mem d pre) true)
      (let [C (h9-prefix w r ds mode k mine pre), W (:world C), x (pair-edge d (:pairs C))]
        (Exists (fn [e :- EdgeRow]
          (And (= (edge-find W x) (Option.some EdgeRow e))
           (And (= (:id e) x)
            (And (h9-edge-fields (await-pre w r ds mode k mine) r (:next-id w) mode k d e)
                 (forall [q :- EdgeRow]
                   (=> (List.Mem q (:edges W)) (= (:id q) x) (= q e))))))))))
  (intros ent split md)
  (have has := (Eq.trans (h9-prefix-has w r ds mode k mine pre d) md))
  (have picked := (h9-pair-picked (:pairs (h9-prefix w r ds mode k mine pre)) d has))
  (cases picked)
  (case [intro p picked]
    (have rows := (h9-prefix-fields xm w r ds mode k mine st fresh pre tail ent split p (And.left picked)))
    (cases rows)
    (case [intro e rows]
      (have edge := (And.right (And.right picked)))
      (have deb := (And.left (And.right picked)))
      (have lookup := (And.left rows)) (rw [edge] at lookup)
      (have id := (And.left (And.right rows))) (rw [edge] at id)
      (have fields := (And.right (And.right rows))) (rw [deb] at fields)
      (apply (Exists.intro e))
      (apply And.intro) (exact lookup)
      (apply And.intro) (exact id)
      (apply And.intro) (exact fields)
      (have support := (h9-prefix-support xm w r ds mode k mine st fresh pre tail ent split))
      (have hs := (h3-sample xm _ (And.left support)))
      (have me := (tbl-find-mem EdgeRow edge-id _ e (:edges (:world (h9-prefix w r ds mode k mine pre))) lookup))
      (intros q mq iq)
      (exact (h9-row-uniq EdgeRow edge-id q e (:edges (:world (h9-prefix w r ds mode k mine pre)))
               (edges-nodup _ hs) mq me (Eq.trans iq (Eq.symm id))))))

)

(a/theorem h9-prefix-pair-free [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, pre :- (List Nat), tail :- (List Nat), p :- DE]
  (=> (h9-entry xm w r ds mode st fresh) (= (List.append Nat pre tail) (nat-distinct ds)) (List.Mem p (:pairs (h9-prefix w r ds mode k mine pre)))
      (= (h3-free xm (:world (h9-prefix w r ds mode k mine pre)) (:edge p)) true))
  (intros ent split mp)
  (have rows := (h9-prefix-fields xm w r ds mode k mine st fresh pre tail ent split p mp))
  (cases rows)
  (case [intro e rows]
    (have me := (tbl-find-mem EdgeRow edge-id (:edge p) e (:edges (:world (h9-prefix w r ds mode k mine pre))) (And.left rows)))
    (have id := (And.left (And.right rows)))
    (have fields := (And.right (And.right rows)))
    (simp only [h9-edge-fields] at fields)
    (have kind := (And.left (And.right (And.right (And.right fields)))))
    (have cred := (And.left (And.right (And.right (And.right (And.right fields))))))
    (have facts (Or (And (= (Nat.beq (:kind e) ek-dep) true) (= (:creditor e) (:of r)))
                   (And (= (Nat.beq (:kind e) ek-dep) false) (= (:creditor e) (:next-id w)))))
    (cases dep (as-dep (await-pre w r ds mode k mine) r (:deb p)))
    (case [true]
      (simp only [dep] at kind cred)
      (have bk := (Eq.trans (congrArg (fn [n :- Nat] (Nat.beq n ek-dep)) kind) (Nat.beq_refl ek-dep)))
      (exact (Or.inl (And.intro bk cred))))
    (case [false]
      (simp only [dep] at kind cred)
      (have neq (= (Nat.beq ek-wait ek-dep) false)) (rfl)
      (have bk := (Eq.trans (congrArg (fn [n :- Nat] (Nat.beq n ek-dep)) kind) neq))
      (exact (Or.inr (And.intro bk cred))))
    (rw [← id])
    (exact (h9-prefix-free-edge xm w r ds mode k mine st fresh pre tail e ent split me facts)))

)

(a/theorem h9-distinct-acc-complete [xs :- (List Nat)]
  (forall [seen :- (List Nat), d :- Nat]
    (=> (= (nat-mem d xs) true) (= (nat-mem d seen) false)
        (= (nat-mem d (nat-distinct-acc seen xs)) true)))
  (induction xs)
  (case [nil] (intros seen d md no) (simp only [nat-mem] at md) (cases md))
  (case [cons x t ih]
    (intros seen d md no)
    (cases eq (Nat.beq x d))
    (case [true]
      (have same := (Nat.eq_of_beq_eq_true eq))
      (have nx (= (nat-mem x seen) false)) (rw [same]) (exact no)
      (simp only [nat-distinct-acc nx nat-mem eq]))
    (case [false]
      (simp only [nat-mem eq] at md)
      (cases nx (nat-mem x seen))
      (case [true] (simp only [nat-distinct-acc nx]) (exact (ih seen d md no)))
      (case [false]
        (have extra (= (nat-mem d (List.cons Nat x seen)) false)) (simp only [nat-mem eq]) (exact no)
        (simp only [nat-distinct-acc nx nat-mem eq]) (exact (ih (List.cons Nat x seen) d md extra))))))

(a/theorem h9-distinct-complete [xs :- (List Nat), d :- Nat]
  (=> (= (nat-mem d xs) true) (= (nat-mem d (nat-distinct xs)) true))
  (intro h) (exact (h9-distinct-acc-complete xs (List.nil Nat) d h (rfl))))

(a/theorem h9-members-has [ps :- (List DE), ds :- (List Nat)]
  (forall [i :- Nat, d :- Nat]
    (=> (= (nat-mem d ds) true) (= (mem-has (pair-edge d ps) (mk-members ps i ds)) true)))
  (induction ds)
  (case [nil] (intros i d h) (simp only [nat-mem] at h) (cases h))
  (case [cons x t ih]
    (intros i d h) (cases eq (Nat.beq x d))
    (case [true]
      (have same := (Nat.eq_of_beq_eq_true eq)) (rw [same])
      (simp only [mk-members mem-has Nat.beq_refl Bool.true_or]))
    (case [false]
      (simp only [nat-mem eq] at h)
      (have rest := (ih (+ i 1) d h))
      (simp only [mk-members mem-has rest Bool.or_true]))))

(a/theorem h9-update-head [b :- ActRow, tail :- (List ActRow), f :- (=> ActRow ActRow)]
  (=> (= (nat-nodup (tbl-ids act-id (List.cons ActRow b tail))) true)
      (= (tbl-upd act-id (:id b) f (List.cons ActRow b tail)) (List.cons ActRow (f b) tail)))
  (intro nd)
  (simp only [tbl-ids nat-nodup Bool.and_eq_true] at nd)
  (have absent := (bnot-true _ (And.left nd)))
  (have ah (= (tbl-has act-id (:id b) tail) false))
  (exact (Eq.trans (Eq.symm (nat-mem-ids ActRow act-id (:id b) tail)) absent))
  (simp only [tbl-upd act-id Nat.beq_refl (tbl-upd-absent ActRow act-id (:id b) f tail ah)]))

(a/theorem h9-s-from-fields [P :- World, r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, d :- Nat, e :- EdgeRow, acts :- (List ActRow), b :- ActRow]
  (=> (h9-edge-fields P r a mode k d e) (= (:id b) a)
      (= (act-with-member (:id e) acts) (Option.some ActRow b))
      (= (h3-s acts b (rk3 r) e) true))
  (intros fields bid first)
  (simp only [h9-edge-fields] at fields)
  (have phase := (And.left (And.right (And.right fields))))
  (have kind := (And.left (And.right (And.right (And.right fields)))))
  (have cred := (And.left (And.right (And.right (And.right (And.right fields))))))
  (cases dep (as-dep P r d))
  (case [true]
    (simp only [dep] at kind cred)
    (simp only [h3-s phase kind cred first opt-test h3-first rk3 Nat.beq_refl Bool.not_true Bool.false_or Bool.true_or Bool.or_true Bool.and_self]))
  (case [false]
    (simp only [dep] at kind cred)
    (simp only [h3-s phase kind cred first opt-test h3-first rk3 bid Nat.beq_refl Bool.not_false Bool.true_or Bool.or_true Bool.and_self])))

(a/theorem h9-installed-first-holder [xm :- (List Nat), w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat), st :- Nat, fresh :- Nat, d :- Nat]
  (=> (h9-entry xm w r ds mode st fresh) (= (nat-mem d ds) true)
      (let [C (await-acc w r ds mode k mine), W (:world C), ps (:pairs C),
            M (mk-members ps 0 ds), b2 (act-set-members M (h9-act w r ds mode k mine)),
            I (act-upd W (:next-id w) (act-set-members M)), x (pair-edge d ps)]
        (Exists (fn [e :- EdgeRow]
          (And (= (edge-find W x) (Option.some EdgeRow e))
           (And (= (edge-find I x) (Option.some EdgeRow e))
            (And (= (act-with-member x (:acts I)) (Option.some ActRow b2))
                 (= (h3-s (:acts I) b2 (rk3 r) e) true))))))))
  (intros ent md)
  (have split := (h9-app-nil (nat-distinct ds)))
  (have member := (h9-distinct-complete ds d md))
  (have found := (h9-prefix-pair-edge xm w r ds mode k mine st fresh (nat-distinct ds) (List.nil Nat) d ent split member))
  (cases found)
  (case [intro e found]
    (have shape := (h9-prefix-shape xm w r ds mode k mine st fresh (nat-distinct ds) (List.nil Nat) ent split))
    (have support := (h9-prefix-support xm w r ds mode k mine st fresh (nat-distinct ds) (List.nil Nat) ent split))
    (have hs := (h3-sample xm _ (And.left support)))
    (have id (= (:id e) (pair-edge d (:pairs (await-acc w r ds mode k mine)))))
    (exact (And.left (And.right found)))
    (have fields := (And.left (And.right (And.right found))))
    (have nd := (h3-acts-nodup (:world (await-acc w r ds mode k mine)) hs))
    (have acts (= (:acts (:world (await-acc w r ds mode k mine)))
                   (List.cons ActRow (h9-act w r ds mode k mine) (:acts w))))
    (exact (And.left shape))
    (rw [acts] at nd)
    (have changed (= (:acts (act-upd (:world (await-acc w r ds mode k mine)) (:next-id w)
                              (act-set-members (mk-members (:pairs (await-acc w r ds mode k mine)) 0 ds))))
                    (List.cons ActRow (act-set-members (mk-members (:pairs (await-acc w r ds mode k mine)) 0 ds)
                                         (h9-act w r ds mode k mine)) (:acts w))))
    (simp only [act-upd set-acts acts])
    (exact (h9-update-head (h9-act w r ds mode k mine) (:acts w)
             (act-set-members (mk-members (:pairs (await-acc w r ds mode k mine)) 0 ds)) nd))
    (have first (= (act-with-member (:id e)
                     (:acts (act-upd (:world (await-acc w r ds mode k mine)) (:next-id w)
                              (act-set-members (mk-members (:pairs (await-acc w r ds mode k mine)) 0 ds)))))
                   (Option.some ActRow (act-set-members (mk-members (:pairs (await-acc w r ds mode k mine)) 0 ds)
                                         (h9-act w r ds mode k mine)))))
    (rw [changed id])
    (simp only [act-with-member act-set-members (h9-members-has (:pairs (await-acc w r ds mode k mine)) ds 0 d md)])
    (have structural := (h9-s-from-fields (await-pre w r ds mode k mine) r (:next-id w) mode k d e
                          (:acts (act-upd (:world (await-acc w r ds mode k mine)) (:next-id w)
                                   (act-set-members (mk-members (:pairs (await-acc w r ds mode k mine)) 0 ds))))
                          (act-set-members (mk-members (:pairs (await-acc w r ds mode k mine)) 0 ds) (h9-act w r ds mode k mine))
                          fields (rfl) first))
    (rw [id] at first)
    (apply (Exists.intro e))
    (exact (And.intro (And.left found) (And.intro (And.left found) (And.intro first structural)))))

)
