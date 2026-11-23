(ns ^:ansatz/lean spindel.v2.inv.members.await-post
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

(a/defn current-members-parked [a :- Nat, rid :- Nat, ds :- (List Nat),
                    acc :- AwAcc] World
  (park-if (current-members-fill-prefix a ds acc (nat-distinct ds)) a rid))

(a/defn current-members-final-prefix [a :- Nat, rid :- Nat, ds :- (List Nat),
                         acc :- AwAcc, pre :- (List Nat)] World
  (nat-fold finalize-if-final (current-members-parked a rid ds acc) pre))


(a/theorem current-members-park-marks-waiting [xm :- (List Nat), w :- World, r :- RunRow,
         ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat),
         st :- Nat, fresh :- Nat]
  (=> (current-members-entry xm w r ds mode st fresh)
      (= (marks-waiting (List.nil Nat)
           (current-members-parked (:next-id w) (:id r) ds
             (await-acc w r ds mode k mine))) true))
  (intro ent)
  (have support := (current-members-prefix-support xm w r ds mode k mine st fresh
                     (nat-distinct ds) (List.nil Nat) ent (current-members-app-nil _)))
  (have hk := (And.left (And.right (And.right (And.right (And.right (And.right support)))))))
  (have installed := (marks-waiting-act-upd (List.nil Nat) (:world (await-acc w r ds mode k mine)) (:next-id w)
                        (act-set-members (mk-members (:pairs (await-acc w r ds mode k mine)) 0 ds))
                        (act-set-members-id _) hk))
  (have filled := (marks-waiting-nat-fold (List.nil Nat) (fast-fill (:pairs (await-acc w r ds mode k mine)))
                     (marks-waiting-fast-fill (List.nil Nat) (:pairs (await-acc w r ds mode k mine)))
                     (nat-distinct ds) (current-members-install (:next-id w) ds (await-acc w r ds mode k mine)) installed))
  (exact (marks-waiting-park-if (List.nil Nat)
           (current-members-fill-prefix (:next-id w) ds (await-acc w r ds mode k mine) (nat-distinct ds))
           (:next-id w) (:id r) filled)))

;; Generalize the current world in the induction; xm and hx stay independent.
(a/theorem current-members-fin-fold-general [xm :- (List Nat), hx :- (List Nat), ds :- (List Nat)]
  (forall [w :- World]
    (=> (= (marks-waiting hx w) true) (= (current-members xm w) true)
        (And (= (marks-waiting hx (nat-fold finalize-if-final w ds)) true)
             (= (current-members xm (nat-fold finalize-if-final w ds)) true))))
  (induction ds)
  (case [nil] (intros w hk h) (simp only [nat-fold]) (exact (And.intro hk h)))
  (case [cons d tail ih]
    (intros w hk h)
    (simp only [nat-fold])
    (exact (ih (finalize-if-final w d) (marks-waiting-finalize-if-final hx w d hk) (current-members-finalize-if-final xm hx w d hk h)))))

(a/theorem current-members-fin-fold [xm :- (List Nat), hx :- (List Nat), w :- World,
         ds :- (List Nat)]
  (=> (= (marks-waiting hx w) true)
      (= (current-members xm w) true)
      (And (= (marks-waiting hx (nat-fold finalize-if-final w ds)) true)
           (= (current-members xm (nat-fold finalize-if-final w ds)) true)))
  (intros hk h)
  (exact (current-members-fin-fold-general xm hx ds w hk h)))

(a/theorem current-members-final-prefix-invariants [xm :- (List Nat), w :- World, r :- RunRow,
         ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat),
         st :- Nat, fresh :- Nat, pre :- (List Nat), tail :- (List Nat)]
  (=> (current-members-entry xm w r ds mode st fresh)
      (= (List.append Nat pre tail) (nat-distinct ds))
      (let [W (current-members-final-prefix (:next-id w) (:id r) ds
                (await-acc w r ds mode k mine) pre)]
        (And (= (marks-waiting (List.nil Nat) W) true)
             (= (current-members xm W) true))))
  (intros ent split)
  (exact (current-members-fin-fold xm (List.nil Nat)
           (current-members-parked (:next-id w) (:id r) ds (await-acc w r ds mode k mine)) pre
           (current-members-park-marks-waiting xm w r ds mode k mine st fresh ent)
           (current-members-park xm w r ds mode k mine st fresh ent))))

(a/theorem current-members-await-post [xm :- (List Nat), w :- World, r :- RunRow,
         ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat),
         st :- Nat, fresh :- Nat]
  (=> (current-members-entry xm w r ds mode st fresh)
      (= (current-members xm
           (await-post (:next-id w) (:id r) ds
             (await-acc w r ds mode k mine))) true))
  (intro ent)
  (have final := (current-members-final-prefix-invariants xm w r ds mode k mine st fresh
                   (nat-distinct ds) (List.nil Nat) ent (current-members-app-nil _)))
  (exact (And.right final)))
