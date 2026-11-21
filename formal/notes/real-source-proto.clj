;; Prototype for notes/proof-layout.md §5c: the generic composite as checked-in source, for one
;; transition, T14's local part `cancel-run-local` (overridden by 8 bundles under the copier).
;;
;; Not part of the model (nothing loads it). To reproduce, from formal/ in a REPL (clojure -M:repl):
;;   (require 'spindel.v2.pres.tree)                ; about 2 minutes
;;   (load-file "notes/real-source-proto.clj")
;;
;; Today rule.clj states well-formed-cancel-run-local over well-formed, and spindel.v2.pres.tree generates
;; pres-cancel-run-local from its source text. Here the generic lemma is the source (`src-cancel-run-
;; local`, written by hand over an abstract part Q, its callees as hypotheses) and the base lemma is
;; derived from it: Q := the trivial part, every hypothesis the base lemma of that callee.

(in-ns 'spindel.v2.pres.tree)

;; ---- the generic composite, written by hand: T14 on run r, local part
(a/theorem src-cancel-run-local
  [Q :- (=> World Bool), w :- World, r :- RunRow, rep :- Bool,
   kill :- (forall [w :- World, x :- Nat, hf :- (forall [r :- RunRow] (= (run-id (run-cancel-row r)) (run-id r)))]
             (=> (= (gp Q w) true) (= (gp Q (run-upd w x run-cancel-row)) true))),
   acts :- (forall [w :- World, rid :- Nat] (=> (= (gp Q w) true) (= (gp Q (cancel-acts w rid)) true))),
   res :- (forall [w :- World, r :- RunRow] (=> (= (gp Q w) true) (= (gp Q (cancel-res w r)) true))),
   cleanup :- (forall [w :- World, rid :- Nat, rows :- (List Nat)] (=> (= (gp Q w) true) (= (gp Q (cleanup-set w rid rows)) true))),
   debtor :- (forall [rep :- Bool, w :- World, r :- RunRow] (=> (= (gp Q w) true) (= (gp Q (cancel-debtor rep w r)) true)))]
  (=> (= (gp Q w) true) (= (gp Q (cancel-run-local w r rep)) true))
  (intro h)
  (simp only [cancel-run-local])
  (exact (debtor rep _ r (cleanup _ (:id r) (cleanup-rows-of w r) (res _ r (acts _ (:id r) (kill w (:id r) run-cancel-row-id h)))))))

;; ---- the base lemma, derived. well-formed is the trivial part: gp (fun _ => true) w = well-formed w && true,
;; which is not well-formed w by definition (Bool.and is stuck on its first argument), so every callee's base
;; lemma is lifted (`up`) and the result is brought back (`down`).
(a/defn triv [w :- World] Bool true)
(a/theorem triv-down [w :- World] (=> (= (gp triv w) true) (= (well-formed w) true)) (intro h) (exact (gp-well-formed triv w h)))
(a/theorem triv-up [w :- World] (=> (= (well-formed w) true) (= (gp triv w) true)) (intro h) (simp only [gp triv h Bool.and_self]))

(a/theorem inv-cancel-run-local-derived [w :- World, r :- RunRow, rep :- Bool]
  (=> (= (well-formed w) true) (= (well-formed (cancel-run-local w r rep)) true))
  (intro h)
  (exact (triv-down _
           (src-cancel-run-local triv w r rep
             (fn [w :- World, x :- Nat, hf :- (forall [r :- RunRow] (= (run-id (run-cancel-row r)) (run-id r))), h :- (= (gp triv w) true)]
               (triv-up _ (well-formed-run-upd w x run-cancel-row hf (triv-down w h))))
             (fn [w :- World, rid :- Nat, h :- (= (gp triv w) true)] (triv-up _ (well-formed-cancel-acts w rid (triv-down w h))))
             (fn [w :- World, r :- RunRow, h :- (= (gp triv w) true)] (triv-up _ (well-formed-cancel-res w r (triv-down w h))))
             (fn [w :- World, rid :- Nat, rows :- (List Nat), h :- (= (gp triv w) true)]
               (triv-up _ (well-formed-cleanup-set w rid rows (triv-down w h))))
             (fn [rep :- Bool, w :- World, r :- RunRow, h :- (= (gp triv w) true)] (triv-up _ (well-formed-cancel-debtor rep w r (triv-down w h))))
             (triv-up w h)))))

;; ---- gl's lemma from the hand-written source: unchanged, it is gl's override (content)
;; ---- g9's (no override needed with the context): the generic lemma with g9's lemmas for the callees
