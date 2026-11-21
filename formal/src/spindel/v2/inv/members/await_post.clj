(ns spindel.v2.inv.members.await-post
  "Compose accepted fast-fill/park support with finalization to actual await-post H3."
  (:require [ansatz.core :as a]
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
            [spindel.v2.pres.part :refer :all]
            [spindel.v2.inv.copier :refer :all]
            [spindel.v2.inv.idle :refer :all]
            [spindel.v2.inv.base :refer :all]
            [spindel.v2.inv.comp-facts :refer :all]
            [spindel.v2.inv.i10 :refer :all]
            [spindel.v2.inv.alive-runs :refer :all]
            [spindel.v2.inv.marks-step :refer :all]
            [spindel.v2.inv.marks :refer :all]
            [spindel.v2.inv.members.bundle :refer :all]
            [spindel.v2.inv.members.track-take :refer :all]
            [spindel.v2.inv.members.cascade :refer :all]
            [spindel.v2.inv.members.base :refer :all]
            [spindel.v2.inv.members.react :refer :all]
            [spindel.v2.inv.members.await-prep :refer :all]
            [spindel.v2.inv.i5 :refer :all]
            [spindel.v2.inv.i8 :refer :all]
            [spindel.v2.inv.i1-runs :refer :all]
            [spindel.v2.inv.members.fires :refer :all]
            [spindel.v2.inv.members.await-wire :refer :all]
            [spindel.v2.progress.l5 :refer :all]
            [spindel.v2.inv.members.await-fill :refer :all]))

(a/defn h11-parked [a :- Nat, rid :- Nat, ds :- (List Nat),
                    acc :- AwAcc] World
  (park-if (h10-fill-prefix a ds acc (nat-distinct ds)) a rid))

(a/defn h11-final-prefix [a :- Nat, rid :- Nat, ds :- (List Nat),
                         acc :- AwAcc, pre :- (List Nat)] World
  (nat-fold fin-if-final (h11-parked a rid ds acc) pre))


(a/theorem h11-park-hmk [xm :- (List Nat), w :- World, r :- RunRow,
         ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat),
         st :- Nat, fresh :- Nat]
  (=> (h9-entry xm w r ds mode st fresh)
      (= (hmk (List.nil Nat)
           (h11-parked (:next-id w) (:id r) ds
             (await-acc w r ds mode k mine))) true))
  (intro ent)
  (have support := (h9-prefix-support xm w r ds mode k mine st fresh
                     (nat-distinct ds) (List.nil Nat) ent (h9-app-nil _)))
  (have hk := (And.left (And.right (And.right (And.right (And.right (And.right support)))))))
  (have installed := (hmk-act-upd (List.nil Nat) (:world (await-acc w r ds mode k mine)) (:next-id w)
                        (act-set-members (mk-members (:pairs (await-acc w r ds mode k mine)) 0 ds))
                        (act-set-members-id _) hk))
  (have filled := (nat-fold-hmk (List.nil Nat) (fast-fill (:pairs (await-acc w r ds mode k mine)))
                     (hmk-fast-fill (List.nil Nat) (:pairs (await-acc w r ds mode k mine)))
                     (nat-distinct ds) (h10-install (:next-id w) ds (await-acc w r ds mode k mine)) installed))
  (exact (hmk-park-if (List.nil Nat)
           (h10-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) (nat-distinct ds))
           (:next-id w) (:id r) filled)))

;; Generalize the current world in the induction; xm and hx stay independent.
(a/theorem h11-fin-fold-general [xm :- (List Nat), hx :- (List Nat), ds :- (List Nat)]
  (forall [w :- World]
    (=> (= (hmk hx w) true) (= (h3 xm w) true)
        (And (= (hmk hx (nat-fold fin-if-final w ds)) true)
             (= (h3 xm (nat-fold fin-if-final w ds)) true))))
  (induction ds)
  (case [nil] (intros w hk h) (simp only [nat-fold]) (exact (And.intro hk h)))
  (case [cons d tail ih]
    (intros w hk h)
    (simp only [nat-fold])
    (exact (ih (fin-if-final w d) (hmk-fin-if-final hx w d hk) (h3-fin-if-final xm hx w d hk h)))))

(a/theorem h11-fin-fold [xm :- (List Nat), hx :- (List Nat), w :- World,
         ds :- (List Nat)]
  (=> (= (hmk hx w) true)
      (= (h3 xm w) true)
      (And (= (hmk hx (nat-fold fin-if-final w ds)) true)
           (= (h3 xm (nat-fold fin-if-final w ds)) true)))
  (intros hk h)
  (exact (h11-fin-fold-general xm hx ds w hk h)))

(a/theorem h11-final-prefix-invariants [xm :- (List Nat), w :- World, r :- RunRow,
         ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat),
         st :- Nat, fresh :- Nat, pre :- (List Nat), tail :- (List Nat)]
  (=> (h9-entry xm w r ds mode st fresh)
      (= (List.append Nat pre tail) (nat-distinct ds))
      (let [W (h11-final-prefix (:next-id w) (:id r) ds
                (await-acc w r ds mode k mine) pre)]
        (And (= (hmk (List.nil Nat) W) true)
             (= (h3 xm W) true))))
  (intros ent split)
  (exact (h11-fin-fold xm (List.nil Nat)
           (h11-parked (:next-id w) (:id r) ds (await-acc w r ds mode k mine)) pre
           (h11-park-hmk xm w r ds mode k mine st fresh ent)
           (h10-park-h3 xm w r ds mode k mine st fresh ent))))

(a/theorem h11-await-post-h3 [xm :- (List Nat), w :- World, r :- RunRow,
         ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat),
         st :- Nat, fresh :- Nat]
  (=> (h9-entry xm w r ds mode st fresh)
      (= (h3 xm
           (await-post (:next-id w) (:id r) ds
             (await-acc w r ds mode k mine))) true))
  (intro ent)
  (have final := (h11-final-prefix-invariants xm w r ds mode k mine st fresh
                   (nat-distinct ds) (List.nil Nat) ent (h9-app-nil _)))
  (exact (And.right final)))
