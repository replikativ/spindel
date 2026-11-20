(ns spindel.v2.inv.i9-res
  "The part g9, I9 resource part (spec §6 I9), through the step on the generic tree
  (spindel.v2.pres.tree; formal/notes/proof-layout.md §5c), kernel-checked (Init only).

  Theorems:
    step-g9            g9 w, rule-r-safe raw -> g9 (world-step w it)
    step-lit-i9-res    ... -> lit-i9-res (world-step w it)      (literal I9, resources)

  The part's predicate, cells and content lemmas are in spindel.v2.inv.copier (Part D); this
  namespace is its table in the tree and its step."
  (:require [ansatz.core :as a]
            [spindel.v2.state :refer :all]
            [spindel.v2.edits :refer :all]
            [spindel.v2.step :refer :all]
            [spindel.v2.rule :refer :all]
            [spindel.v2.engine :refer :all]
            [spindel.v2.inv :refer :all]
            [spindel.v2.inv.copier :refer :all]
            [spindel.v2.pres.tree :as tree]))

;; ---------------------------------------------------------------------------
;; The part g9: I9, resource part
;;
;; 1. In words: every resource's owner is below the allocator and its phase is valid (armed, fired
;;    or cancelling); every run row with the owner's id lists the resource in `resources`; and
;;    `lit-i9-res`: an unwinding run's resources are cancelling or fired (quiet). `g9-rest`
;;    (copier, Part D).
;; 2. View: next-id, res, runs (`defpart G9` in the copier). Finer, column level: the run key `rk9`
;;    (id, mode, resources).
;; 3. Exempt form: none; g9 holds after every edit.
;; 4. Cells: a run update that keeps `rk9` (the bundle's extra argument: `rfl` at every site), run
;;    and resource deletes, inserts and `bump` (the allocator only grows), Rule R's filter (`g9-filter`);
;;    frames from the view. Sites, below: the two resource updates (`g9-res-upd-q`: id and owner
;;    kept, the phase stays valid, a quiet resource stays quiet).
;; 5. Content (:over below): T14's local part (the run unwinds and every resource it lists is
;;    cancelled: `g9-cancel-mid`), T15's ack (the resource goes and leaves its owner's list:
;;    `g9-ack-raw-o`), T17's arm (a new armed resource of a run that is not unwinding, Z#40:
;;    `g9-arm-o`). The facts these take from the path (:ctx, :own, :pass below): the run is a row;
;;    the arming run is not unwinding, from raw0's guard `fin-shut`.
;; 6. Companions: none.

(tree/part! G9
  :sites '{[inv-resource-upd res-cancel-row]          (g9-res-upd-q w x res-cancel-row hf          ; T14: cancel a resource
                                                        cancel-row-owner cancel-row-phase cancel-row-quiet h0)
           [inv-resource-upd (res-set-phase rp-fired)] (g9-res-upd-q w x (res-set-phase rp-fired) hf ; T18: fire it
                                                        (fn [q :- ResRow] (Eq.refl (:owner q)))
                                                        (fn [q :- ResRow, hq :- (= (phase-ok q) true)] (Eq.refl true))
                                                        (fn [q :- ResRow, hq :- (= (res-quiet q) true)] (Eq.refl true)) h0)}
  :over '{inv-cancel-run-local g9-cancel-run-local     ; T14 local: cancel-mid, then the generic debtor side
          inv-ack-raw          g9-ack-raw-o            ; T15: the resource leaves its owner's list
          inv-arm-park         g9-arm-park}            ; T17: arm (g9-arm-o), then the generic park
  :ctx '{inv-cancel-run-local [(List.Mem r (:runs w))]                         ; the cancelled run is a row
         inv-arm-park         [(List.Mem r (:runs w)) (= (run-unwinding r) false)]}  ; the arming run: a row, not unwinding
  :own '{t17-inv [hc (= (fin-shut w st) false)]}                               ; raw0's guard: not in a cleanup slice
  :pass '{inv-job-apply {inv-cancel-run-local [(tbl-find-mem RunRow run-id rid r (:runs w) hf)]}     ; run-find found it
          raw0-inv      {t17-inv [hc]}                                                               ; the guard
          t17-inv       {inv-arm-park [(And.left (tok-facts w st r ht))                              ; the token's run,
                                       (cleanup-not-unw w st r (fin-shut-cleanup w st hc) ht)]}})    ;   not unwinding

;; ---- T14's local part: the run unwinds, its resources are cancelled; then the debtor side

(tree/restate! G9 '[inv-cancel-debtor])

(a/theorem g9-cancel-run-local [w :- World, r :- RunRow, rep :- Bool]
  (=> (List.Mem r (:runs w)) (= (g9 w) true) (= (g9 (cancel-run-local w r rep)) true))
  (intros hm h)
  (have e (= (cancel-run-local w r rep) (cancel-debtor rep (cancel-mid w r) r))) (rfl)
  (rw [e])
  (exact (g9-cancel-debtor rep _ r (g9-cancel-mid w r hm h))))

;; ---- T17's arm: a new armed resource, then the run parks

(tree/restate! G9 '[inv-take-park])

(a/theorem g9-arm-park [w :- World, r :- RunRow, kind :- Nat, k :- Nat]
  (=> (List.Mem r (:runs w)) (= (run-unwinding r) false) (= (g9 w) true) (= (g9 (arm-park w r kind k)) true))
  (intros hm hu h)
  (simp only [arm-park])
  (exact (g9-take-park _ (run-arm (:next-id w) r) (:next-id w) k (g9-arm-o w r kind hm hu h))))

;; ---- the step (Rule R included: its filter is the cell g9-filter)

(tree/restate! G9 '[step-inv])

(a/theorem g9-empty [] (= (g9 empty-world) true) (rfl))

;; Theorem: literal I9, resources (an unwinding run's resources are cancelling or fired),
;; through every step
(a/theorem step-lit-i9-res [w :- World, it :- Item]
  (=> (= (g9 w) true) (= (rule-r-safe (:world (raw w it))) true) (= (lit-i9-res (:world (world-step w it))) true))
  (intros h hs)
  (have h2 := (g9-rest-of _ (step-g9 w it h hs)))
  (simp only [g9-rest Bool.and_eq_true] at h2)
  (exact (And.right (And.right h2))))
