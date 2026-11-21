(ns spindel.v2.inv.i9-res
  "The part i9-res, I9 resource part (spec §6 I9), through the step on the generic tree
  (spindel.v2.pres.tree; formal/notes/proof-layout.md §5c), kernel-checked (Init only).

  Theorems:
    step-i9-res            i9-res w, rule-r-safe raw -> i9-res (world-step w it)
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
            [spindel.v2.pres.part :refer :all]
            [spindel.v2.inv.copier :refer :all]
            [spindel.v2.pres.tree :as tree]))

;; ---------------------------------------------------------------------------
;; The part i9-res: I9, resource part
;;
;; 1. In words: every resource's owner is below the allocator and its phase is valid (armed, fired
;;    or cancelling); every run row with the owner's id lists the resource in `resources`; and
;;    `lit-i9-res`: an unwinding run's resources are cancelling or fired (quiet). `i9-res-rest`
;;    (copier, Part D).
;; 2. View: next-id, res, runs (`defpart G9` in the copier). Finer, column level: the run key `i9-res-run-key`
;;    (id, mode, resources).
;; 3. Exempt form: none; i9-res holds after every edit.
;; 4. Cells: a run update that keeps `i9-res-run-key` (the bundle's extra argument: `rfl` at every site), run
;;    and resource deletes, inserts and `bump` (the allocator only grows), Rule R's filter (`i9-res-filter`);
;;    frames from the view. Sites, below: the two resource updates (`i9-res-res-upd-q`: id and owner
;;    kept, the phase stays valid, a quiet resource stays quiet).
;; 5. Content (:over below): T14's local part (the run unwinds and every resource it lists is
;;    cancelled: `i9-res-cancel-mid`), T15's ack (the resource goes and leaves its owner's list:
;;    `i9-res-ack-raw-hand`), T17's arm (a new armed resource of a run that is not unwinding, Z#40:
;;    `i9-res-arm-hand`). The facts these take from the path (:ctx, :own, :pass below): the run is a row;
;;    the arming run is not unwinding, from transition's guard `arm-refused`.
;; 6. Companions: none.

(tree/part! G9
  :sites '{[well-formed-resource-upd res-cancel-row]          (i9-res-res-upd-q w x res-cancel-row hf          ; T14: cancel a resource
                                                        cancel-row-owner cancel-row-phase cancel-row-quiet h0)
           [well-formed-resource-upd (res-set-phase rp-fired)] (i9-res-res-upd-q w x (res-set-phase rp-fired) hf ; T18: fire it
                                                        (fn [q :- ResRow] (Eq.refl (:owner q)))
                                                        (fn [q :- ResRow, hq :- (= (phase-ok q) true)] (Eq.refl true))
                                                        (fn [q :- ResRow, hq :- (= (res-quiet q) true)] (Eq.refl true)) h0)}
  :over '{well-formed-cancel-run-local i9-res-cancel-run-local     ; T14 local: cancel-mid, then the generic debtor side
          well-formed-ack-raw          i9-res-ack-raw-hand            ; T15: the resource leaves its owner's list
          well-formed-arm-park         i9-res-arm-park}            ; T17: arm (i9-res-arm-hand), then the generic park
  :ctx '{well-formed-cancel-run-local [(List.Mem r (:runs w))]                         ; the cancelled run is a row
         well-formed-arm-park         [(List.Mem r (:runs w)) (= (run-unwinding r) false)]}  ; the arming run: a row, not unwinding
  :own '{well-formed-t17-arm [hc (= (arm-refused w st) false)]}                               ; transition's guard: not in a cleanup slice
  :pass '{well-formed-job-apply {well-formed-cancel-run-local [(tbl-find-mem RunRow run-id rid r (:runs w) hf)]}     ; run-find found it
          well-formed-transition-arm  {well-formed-t17-arm [hc]}                                                               ; the guard
          well-formed-t17-arm       {well-formed-arm-park [(And.left (tok-facts w st r ht))                              ; the token's run,
                                       (cleanup-not-unw w st r (arm-refused-cleanup w st hc) ht)]}})    ;   not unwinding

;; ---- T14's local part: the run unwinds, its resources are cancelled; then the debtor side

(tree/restate! G9 '[well-formed-cancel-debtor])

(a/theorem i9-res-cancel-run-local [w :- World, r :- RunRow, rep :- Bool]
  (=> (List.Mem r (:runs w)) (= (i9-res w) true) (= (i9-res (cancel-run-local w r rep)) true))
  (intros hm h)
  (have e (= (cancel-run-local w r rep) (cancel-debtor rep (cancel-mid w r) r))) (rfl)
  (rw [e])
  (exact (i9-res-cancel-debtor rep _ r (i9-res-cancel-mid w r hm h))))

;; ---- T17's arm: a new armed resource, then the run parks

(tree/restate! G9 '[well-formed-take-park])

(a/theorem i9-res-arm-park [w :- World, r :- RunRow, kind :- Nat, k :- Nat]
  (=> (List.Mem r (:runs w)) (= (run-unwinding r) false) (= (i9-res w) true) (= (i9-res (arm-park w r kind k)) true))
  (intros hm hu h)
  (simp only [arm-park])
  (exact (i9-res-take-park _ (run-arm (:next-id w) r) (:next-id w) k (i9-res-arm-hand w r kind hm hu h))))

;; ---- the step (Rule R included: its filter is the cell i9-res-filter)

(tree/restate! G9 '[step-well-formed])

(a/theorem i9-res-empty [] (= (i9-res empty-world) true) (rfl))

;; Theorem: literal I9, resources (an unwinding run's resources are cancelling or fired),
;; through every step
(a/theorem step-lit-i9-res [w :- World, it :- Item]
  (=> (= (i9-res w) true) (= (rule-r-safe (:world (raw w it))) true) (= (lit-i9-res (:world (world-step w it))) true))
  (intros h hs)
  (have h2 := (i9-res-rest-of _ (step-i9-res w it h hs)))
  (simp only [i9-res-rest Bool.and_eq_true] at h2)
  (exact (And.right (And.right h2))))
