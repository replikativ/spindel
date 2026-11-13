(ns spindel.v2.edits
  "Primitive table edits and their first invariant lemmas (spec v1.5).

  - Exact pending (§2, X#1): `C.pending = #{existing e | e.creditor = C ∧ e.marked}`.
    `pending-exact` checks it over all computations. The edge edits `mark-edge`,
    `unmark-edge`, `remove-edge` and `insert-edge` adjust the creditor's `pending` in the
    same edit and preserve `pending-exact` given unique edge ids. Every other table edit
    preserves it by a frame lemma (it reads only `comps`' ids/pending and `edges`'
    creditor/marked).
  - I2 sample (§6): `edges-ref-ok` — every edge's creditor and debtor exist; a `dep`
    edge's creditor is a computation, a `wait`/`savepoint` edge's an activation, an
    `observe` edge's the host, and a `wait` edge with creditor 0 is a host wait (T22,
    Z#27). The debtor is a computation, task or source, or, for a wait edge only, a resource
    (Z#6); so resource edits are no longer frames: `resource-upd-edges-ref-ok` (ids kept),
    `resource-ins-edges-ref-ok`, and `resource-del-edges-ref-ok` / `inv-resource-del` need
    `tbl-all (no-debtor z) edges` (the T15 token).
  - Id uniqueness over the global id space: `ids-unique` (no id twice in `all-ids`) and
    `ids-below` (every id is in 1 .. next-id-1, next-id >= 1). Inserting a row whose id is
    `next-id` and bumping the allocator preserves both."
  (:require [ansatz.core :as a]
            [spindel.v2.state :refer :all]))

;; ---------------------------------------------------------------------------
;; Row updates

(a/defn edge-set-marked [b :- Bool, e :- EdgeRow] EdgeRow
  (EdgeRow.mk (:id e) (:kind e) (:creditor e) (:debtor e) (:cont e) (:at e) (:phase e)
              b (:has-seen e) (:seen e) (:has-base e) (:base-value e) (:base-version e)))

(a/defn edge-set-id [i :- Nat, e :- EdgeRow] EdgeRow
  (EdgeRow.mk i (:kind e) (:creditor e) (:debtor e) (:cont e) (:at e) (:phase e)
              (:marked e) (:has-seen e) (:seen e) (:has-base e) (:base-value e) (:base-version e)))

(a/defn comp-set-pending [n :- Nat, c :- CompRow] CompRow
  (CompRow.mk (:id c) (:owner c) (:inputs c) (:body c) (:run c) (:epoch c) (:done-epoch c)
              n (:rank c) (:version c) (:result c) (:idle c) (:validity c) (:basis c)
              (:adopt-basis c) (:adopt-baselines c) (:handles c)))

(a/defn comp-inc-pending [c :- CompRow] CompRow (comp-set-pending (+ (:pending c) 1) c))
(a/defn comp-dec-pending [c :- CompRow] CompRow (comp-set-pending (- (:pending c) 1) c))

;; ---------------------------------------------------------------------------
;; Exact pending

;; edge e is a marked in-edge of c
(a/defn marks [c :- Nat, e :- EdgeRow] Bool (Bool.and (Nat.beq (:creditor e) c) (:marked e)))
(a/defn marked-in [c :- Nat, es :- (List EdgeRow)] Nat (tbl-count (marks c) es))
(a/defn comp-exact [es :- (List EdgeRow), c :- CompRow] Bool
  (Nat.beq (:pending c) (marked-in (:id c) es)))
(a/defn pending-exact-in [cs :- (List CompRow), es :- (List EdgeRow)] Bool
  (tbl-all (comp-exact es) cs))
(a/defn pending-exact [w :- World] Bool (pending-exact-in (:comps w) (:edges w)))

(a/defn edge-ids-nodup [w :- World] Bool (nat-nodup (tbl-ids edge-id (:edges w))))

;; Primitive edge edits. Each adjusts the creditor's pending in the same edit.
(a/defn mark-edge [w :- World, x :- Nat] World
  (match (edge-find w x)
    [none w]
    [(some e) (if (:marked e) w
                  (comp-upd (edge-upd w x (edge-set-marked true)) (:creditor e) comp-inc-pending))]))

(a/defn unmark-edge [w :- World, x :- Nat] World
  (match (edge-find w x)
    [none w]
    [(some e) (if (:marked e)
                  (comp-upd (edge-upd w x (edge-set-marked false)) (:creditor e) comp-dec-pending)
                  w)]))

(a/defn remove-edge [w :- World, x :- Nat] World
  (match (edge-find w x)
    [none w]
    [(some e) (if (:marked e)
                  (comp-upd (edge-del w x) (:creditor e) comp-dec-pending)
                  (edge-del w x))]))

;; inserted unmarked
(a/defn insert-edge [w :- World, e :- EdgeRow] World
  (edge-ins w (edge-set-marked false e)))

;; with a fresh id from the allocator
(a/defn insert-edge-fresh [w :- World, e :- EdgeRow] World
  (bump (insert-edge w (edge-set-id (:next-id w) e))))

;; ---------------------------------------------------------------------------
;; Exact pending: the edge edits

(a/theorem marked-in-mark [c :- Nat, x :- Nat, e :- EdgeRow, es :- (List EdgeRow)]
  (=> (= (tbl-find edge-id x es) (Option.some EdgeRow e))
      (= (nat-nodup (tbl-ids edge-id es)) true)
      (= (:marked e) false)
      (= (marked-in c (tbl-upd edge-id x (edge-set-marked true) es))
         (+ (marked-in c es) (b2n (Nat.beq (:creditor e) c)))))
  (intros hf hn hm)
  (have h (= (+ (tbl-count (marks c) (tbl-upd edge-id x (edge-set-marked true) es)) (b2n (marks c e)))
             (+ (tbl-count (marks c) es) (b2n (marks c (edge-set-marked true e))))))
  (exact (tbl-count-upd EdgeRow edge-id x (edge-set-marked true) (marks c) e es hf hn))
  (simp only [marks hm edge-set-marked Bool.and_false Bool.and_true] at h)
  (simp only [marked-in])
  (simp only [b2n] at h)
  (omega))

(a/theorem pe-mark-core [cs :- (List CompRow), es :- (List EdgeRow), x :- Nat, e :- EdgeRow]
  (=> (= (tbl-find edge-id x es) (Option.some EdgeRow e))
      (= (nat-nodup (tbl-ids edge-id es)) true)
      (= (:marked e) false)
      (= (pending-exact-in cs es) true)
      (= (pending-exact-in (tbl-upd comp-id (:creditor e) comp-inc-pending cs)
                           (tbl-upd edge-id x (edge-set-marked true) es)) true))
  (intros hf hn hm hpe)
  (have hin (forall [r :- CompRow]
              (=> (= (comp-exact es r) true) (= (Nat.beq (comp-id r) (:creditor e)) true)
                  (= (comp-exact (tbl-upd edge-id x (edge-set-marked true) es) (comp-inc-pending r)) true))))
  (intros r hp hid)
  (simp only [comp-exact Nat.beq_eq] at hp)
  (have hid2 (= (:id r) (:creditor e))) (exact (Nat.eq_of_beq_eq_true hid))
  (simp only [comp-exact Nat.beq_eq comp-inc-pending comp-set-pending])
  (rw [(marked-in-mark (:id r) x e es hf hn hm)])
  (rw [hid2])
  (rw [hid2] at hp)
  (simp [b2n])
  (omega)
  (have hout (forall [r :- CompRow]
              (=> (= (comp-exact es r) true) (= (Nat.beq (comp-id r) (:creditor e)) false)
                  (= (comp-exact (tbl-upd edge-id x (edge-set-marked true) es) r) true))))
  (intros r hp hid)
  (simp only [comp-exact Nat.beq_eq] at hp)
  (simp only [comp-exact Nat.beq_eq])
  (rw [(marked-in-mark (:id r) x e es hf hn hm)])
  (simp only [comp-id] at hid)
  (rw [(beq-comm (:creditor e) (:id r)) hid])
  (simp [b2n])
  (exact hp)
  (exact (tbl-all-upd CompRow comp-id (:creditor e) comp-inc-pending (comp-exact es)
           (comp-exact (tbl-upd edge-id x (edge-set-marked true) es)) hin hout cs hpe)))

;; Three shapes of a change to the marked in-edge counts, and what the comps need.
(a/theorem pe-same [cs :- (List CompRow), es :- (List EdgeRow), es2 :- (List EdgeRow),
                    h :- (forall [c :- Nat] (= (marked-in c es2) (marked-in c es)))]
  (=> (= (pending-exact-in cs es) true) (= (pending-exact-in cs es2) true))
  (intro hpe)
  (have hpq (forall [r :- CompRow] (=> (= (comp-exact es r) true) (= (comp-exact es2 r) true))))
  (intros r hp)
  (simp only [comp-exact Nat.beq_eq] at hp)
  (simp only [comp-exact Nat.beq_eq (h (:id r))])
  (exact hp)
  (exact (tbl-all-mono CompRow (comp-exact es) (comp-exact es2) hpq cs hpe)))

(a/theorem pe-down [cs :- (List CompRow), es :- (List EdgeRow), es2 :- (List EdgeRow), y :- Nat,
                    h :- (forall [c :- Nat] (= (+ (marked-in c es2) (b2n (Nat.beq y c))) (marked-in c es)))]
  (=> (= (pending-exact-in cs es) true)
      (= (pending-exact-in (tbl-upd comp-id y comp-dec-pending cs) es2) true))
  (intro hpe)
  (have hin (forall [r :- CompRow]
              (=> (= (comp-exact es r) true) (= (Nat.beq (comp-id r) y) true)
                  (= (comp-exact es2 (comp-dec-pending r)) true))))
  (intros r hp hid)
  (simp only [comp-exact Nat.beq_eq] at hp)
  (have hid2 (= (:id r) y)) (exact (Nat.eq_of_beq_eq_true hid))
  (simp only [comp-exact Nat.beq_eq comp-dec-pending comp-set-pending])
  (have hc (= (+ (marked-in (:id r) es2) (b2n (Nat.beq y (:id r)))) (marked-in (:id r) es)))
  (exact (h (:id r)))
  (rw [hid2] at hc) (rw [hid2] at hp) (rw [hid2])
  (simp [b2n] at hc)
  (omega)
  (have hout (forall [r :- CompRow]
              (=> (= (comp-exact es r) true) (= (Nat.beq (comp-id r) y) false)
                  (= (comp-exact es2 r) true))))
  (intros r hp hid)
  (simp only [comp-exact Nat.beq_eq] at hp)
  (simp only [comp-exact Nat.beq_eq])
  (have hc (= (+ (marked-in (:id r) es2) (b2n (Nat.beq y (:id r)))) (marked-in (:id r) es)))
  (exact (h (:id r)))
  (simp only [comp-id] at hid)
  (rw [(beq-comm y (:id r)) hid] at hc)
  (simp [b2n] at hc)
  (omega)
  (exact (tbl-all-upd CompRow comp-id y comp-dec-pending (comp-exact es) (comp-exact es2) hin hout cs hpe)))

(a/theorem marked-in-unmark [c :- Nat, x :- Nat, e :- EdgeRow, es :- (List EdgeRow)]
  (=> (= (tbl-find edge-id x es) (Option.some EdgeRow e))
      (= (nat-nodup (tbl-ids edge-id es)) true)
      (= (:marked e) true)
      (= (+ (marked-in c (tbl-upd edge-id x (edge-set-marked false) es)) (b2n (Nat.beq (:creditor e) c)))
         (marked-in c es)))
  (intros hf hn hm)
  (have h (= (+ (tbl-count (marks c) (tbl-upd edge-id x (edge-set-marked false) es)) (b2n (marks c e)))
             (+ (tbl-count (marks c) es) (b2n (marks c (edge-set-marked false e))))))
  (exact (tbl-count-upd EdgeRow edge-id x (edge-set-marked false) (marks c) e es hf hn))
  (simp only [marks hm edge-set-marked Bool.and_false Bool.and_true] at h)
  (simp only [marked-in])
  (simp only [b2n] at h)
  (simp only [b2n])
  (omega))

(a/theorem marked-in-del [c :- Nat, x :- Nat, e :- EdgeRow, es :- (List EdgeRow)]
  (=> (= (tbl-find edge-id x es) (Option.some EdgeRow e))
      (= (nat-nodup (tbl-ids edge-id es)) true)
      (= (+ (marked-in c (tbl-del edge-id x es)) (b2n (marks c e))) (marked-in c es)))
  (intros hf hn)
  (exact (tbl-count-del EdgeRow edge-id x (marks c) e es hf hn)))

(a/theorem marked-in-ins-unmarked [c :- Nat, e :- EdgeRow, es :- (List EdgeRow)]
  (= (marked-in c (tbl-ins (edge-set-marked false e) es)) (marked-in c es))
  (simp [marked-in tbl-ins tbl-count-cons marks edge-set-marked b2n]))

(a/theorem pe-unmark-core [cs :- (List CompRow), es :- (List EdgeRow), x :- Nat, e :- EdgeRow]
  (=> (= (tbl-find edge-id x es) (Option.some EdgeRow e))
      (= (nat-nodup (tbl-ids edge-id es)) true)
      (= (:marked e) true)
      (= (pending-exact-in cs es) true)
      (= (pending-exact-in (tbl-upd comp-id (:creditor e) comp-dec-pending cs)
                           (tbl-upd edge-id x (edge-set-marked false) es)) true))
  (intros hf hn hm hpe)
  (exact (pe-down cs es (tbl-upd edge-id x (edge-set-marked false) es) (:creditor e)
           (fn [c :- Nat] (marked-in-unmark c x e es hf hn hm)) hpe)))

(a/theorem pe-remove-marked-core [cs :- (List CompRow), es :- (List EdgeRow), x :- Nat, e :- EdgeRow]
  (=> (= (tbl-find edge-id x es) (Option.some EdgeRow e))
      (= (nat-nodup (tbl-ids edge-id es)) true)
      (= (:marked e) true)
      (= (pending-exact-in cs es) true)
      (= (pending-exact-in (tbl-upd comp-id (:creditor e) comp-dec-pending cs) (tbl-del edge-id x es)) true))
  (intros hf hn hm hpe)
  (have h (forall [c :- Nat] (= (+ (marked-in c (tbl-del edge-id x es)) (b2n (Nat.beq (:creditor e) c)))
                                (marked-in c es))))
  (intro c)
  (have h1 (= (+ (marked-in c (tbl-del edge-id x es)) (b2n (marks c e))) (marked-in c es)))
  (exact (marked-in-del c x e es hf hn))
  (simp only [marks hm Bool.and_true] at h1)
  (exact h1)
  (exact (pe-down cs es (tbl-del edge-id x es) (:creditor e) h hpe)))

(a/theorem pe-remove-unmarked-core [cs :- (List CompRow), es :- (List EdgeRow), x :- Nat, e :- EdgeRow]
  (=> (= (tbl-find edge-id x es) (Option.some EdgeRow e))
      (= (nat-nodup (tbl-ids edge-id es)) true)
      (= (:marked e) false)
      (= (pending-exact-in cs es) true)
      (= (pending-exact-in cs (tbl-del edge-id x es)) true))
  (intros hf hn hm hpe)
  (have h (forall [c :- Nat] (= (marked-in c (tbl-del edge-id x es)) (marked-in c es))))
  (intro c)
  (have h1 (= (+ (marked-in c (tbl-del edge-id x es)) (b2n (marks c e))) (marked-in c es)))
  (exact (marked-in-del c x e es hf hn))
  (simp only [marks hm Bool.and_false b2n] at h1)
  (omega)
  (exact (pe-same cs es (tbl-del edge-id x es) h hpe)))

;; ---- World-level: the four edge edits preserve pending-exact

(a/theorem mark-edge-pending-exact [w :- World, x :- Nat]
  (=> (= (edge-ids-nodup w) true) (= (pending-exact w) true) (= (pending-exact (mark-edge w x)) true))
  (intros hn hpe)
  (cases hf (edge-find w x)) (case' [some e]) (case' [none])
  (simp only [mark-edge hf])
  (exact hpe)
  (cases hm (:marked e))
  (simp only [mark-edge hf hm])
  (exact (pe-mark-core (:comps w) (:edges w) x e hf hn hm hpe))
  (simp only [mark-edge hf hm])
  (exact hpe))

(a/theorem unmark-edge-pending-exact [w :- World, x :- Nat]
  (=> (= (edge-ids-nodup w) true) (= (pending-exact w) true) (= (pending-exact (unmark-edge w x)) true))
  (intros hn hpe)
  (cases hf (edge-find w x)) (case' [some e]) (case' [none])
  (simp only [unmark-edge hf])
  (exact hpe)
  (cases hm (:marked e))
  (simp only [unmark-edge hf hm])
  (exact hpe)
  (simp only [unmark-edge hf hm])
  (exact (pe-unmark-core (:comps w) (:edges w) x e hf hn hm hpe)))

(a/theorem remove-edge-pending-exact [w :- World, x :- Nat]
  (=> (= (edge-ids-nodup w) true) (= (pending-exact w) true) (= (pending-exact (remove-edge w x)) true))
  (intros hn hpe)
  (cases hf (edge-find w x)) (case' [some e]) (case' [none])
  (simp only [remove-edge hf])
  (exact hpe)
  (cases hm (:marked e))
  (simp only [remove-edge hf hm])
  (exact (pe-remove-unmarked-core (:comps w) (:edges w) x e hf hn hm hpe))
  (simp only [remove-edge hf hm])
  (exact (pe-remove-marked-core (:comps w) (:edges w) x e hf hn hm hpe)))

(a/theorem insert-edge-pending-exact [w :- World, e :- EdgeRow]
  (=> (= (pending-exact w) true) (= (pending-exact (insert-edge w e)) true))
  (intro hpe)
  (exact (pe-same (:comps w) (:edges w) (tbl-ins (edge-set-marked false e) (:edges w))
           (fn [c :- Nat] (marked-in-ins-unmarked c e (:edges w))) hpe)))


;; ---- pending-exact frames: it reads only comps' id/pending and edges' creditor/marked

(a/theorem pending-exact-frame [w1 :- World, w2 :- World]
  (=> (= (:comps w2) (:comps w1)) (= (:edges w2) (:edges w1))
      (= (pending-exact w2) (pending-exact w1)))
  (intros h1 h2)
  (simp only [pending-exact h1 h2]))

(defmacro ^:private defframes
  "One rfl frame lemma per (predicate, World edit) pair: (= (pred edit-applied) (pred w))."
  [pred & edits]
  `(do ~@(for [[nm params app] (partition 3 edits)]
           `(a/theorem ~(symbol (str pred "-" nm)) [~'w :- ~'World ~@params]
              (~'= (~pred ~app) (~pred ~'w)) (~'rfl)))))

(defmacro ^:private table-edits
  "The ins/del/upd World edits of the given per-table prefixes, as defframes triples."
  [& specs]
  (vec (mapcat (fn [[prefix row]]
                 [(symbol (str prefix "-ins")) ['r :- row] (list (symbol (str prefix "-ins")) 'w 'r)
                  (symbol (str prefix "-del")) ['x :- 'Nat] (list (symbol (str prefix "-del")) 'w 'x)
                  (symbol (str prefix "-upd")) ['x :- 'Nat 'f :- (list '=> row row)]
                  (list (symbol (str prefix "-upd")) 'w 'x 'f)])
               (partition 2 specs))))

(defmacro ^:private defframes-tables [pred & specs]
  `(defframes ~pred ~@(macroexpand `(table-edits ~@specs))))

(defframes-tables pending-exact
  scope ScopeRow task TaskRow run RunRow source SourceRow act ActRow resource ResRow
  cleanup CleanupRow pub PubRow fork ForkRow)
(defframes pending-exact
  set-pins [v :- (List Nat)] (set-pins w v)
  set-pending-act [v :- Nat] (set-pending-act w v)
  set-released [v :- Bool] (set-released w v)
  bump [] (bump w))

;; comp edits that keep ids and pending
(a/theorem pending-exact-comp-upd [w :- World, x :- Nat, f :- (=> CompRow CompRow),
                                   hid :- (forall [c :- CompRow] (= (:id (f c)) (:id c))),
                                   hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c)))]
  (=> (= (pending-exact w) true) (= (pending-exact (comp-upd w x f)) true))
  (intro hpe)
  (have hin (forall [r :- CompRow]
              (=> (= (comp-exact (:edges w) r) true) (= (Nat.beq (comp-id r) x) true)
                  (= (comp-exact (:edges w) (f r)) true))))
  (intros r h1 h2)
  (simp only [comp-exact hid hp])
  (exact h1)
  (have hout (forall [r :- CompRow]
              (=> (= (comp-exact (:edges w) r) true) (= (Nat.beq (comp-id r) x) false)
                  (= (comp-exact (:edges w) r) true))))
  (intros r h1 h2) (exact h1)
  (exact (tbl-all-upd CompRow comp-id x f (comp-exact (:edges w)) (comp-exact (:edges w)) hin hout (:comps w) hpe)))

(a/theorem pending-exact-comp-del [w :- World, x :- Nat]
  (=> (= (pending-exact w) true) (= (pending-exact (comp-del w x)) true))
  (intro hpe)
  (have hout (forall [r :- CompRow]
              (=> (= (comp-exact (:edges w) r) true) (= (Nat.beq (comp-id r) x) false)
                  (= (comp-exact (:edges w) r) true))))
  (intros r h1 h2) (exact h1)
  (exact (tbl-all-del CompRow comp-id x (comp-exact (:edges w)) (comp-exact (:edges w)) hout (:comps w) hpe)))

;; a new comp must arrive with its exact pending (0 for a fresh id: no edge names it yet)
(a/theorem pending-exact-comp-ins [w :- World, c :- CompRow]
  (=> (= (:pending c) (marked-in (:id c) (:edges w)))
      (= (pending-exact w) true) (= (pending-exact (comp-ins w c)) true))
  (intros hc hpe)
  (simp only [pending-exact comp-ins set-comps pending-exact-in tbl-ins tbl-all comp-exact
              Bool.and_eq_true Nat.beq_eq])
  (exact (And.intro hc hpe)))

;; edge edits that keep creditor and marked
(a/theorem pending-exact-edge-upd [w :- World, x :- Nat, f :- (=> EdgeRow EdgeRow),
                                   hc :- (forall [e :- EdgeRow] (= (:creditor (f e)) (:creditor e))),
                                   hm :- (forall [e :- EdgeRow] (= (:marked (f e)) (:marked e)))]
  (=> (= (pending-exact w) true) (= (pending-exact (edge-upd w x f)) true))
  (intro hpe)
  (have h (forall [c :- Nat] (= (marked-in c (tbl-upd edge-id x f (:edges w))) (marked-in c (:edges w)))))
  (intro c)
  (have hp (forall [e :- EdgeRow] (= (marks c (f e)) (marks c e))))
  (intro e) (simp only [marks hc hm])
  (exact (tbl-count-upd-same EdgeRow edge-id x f (marks c) hp (:edges w)))
  (exact (pe-same (:comps w) (:edges w) (tbl-upd edge-id x f (:edges w)) h hpe)))


;; ---------------------------------------------------------------------------
;; I2 sample: edge referential integrity

;; creditor: dep -> computation, observe -> host (no row), wait/savepoint -> activation;
;; a wait edge with creditor 0 is a host wait (T22, Z#27)
(a/defn cred-ok [cs :- (List CompRow), as :- (List ActRow), e :- EdgeRow] Bool
  (if (Nat.beq (:kind e) ek-dep) (tbl-has comp-id (:creditor e) cs)
      (if (host-cred e) true (tbl-has act-id (:creditor e) as))))
;; debtor: C | K | X, or Z for a wait edge (Z#6)
(a/defn deb-ok [cs :- (List CompRow), ts :- (List TaskRow), xs :- (List SourceRow), rs :- (List ResRow), e :- EdgeRow] Bool
  (Bool.or (tbl-has comp-id (:debtor e) cs)
           (Bool.or (tbl-has task-id (:debtor e) ts)
                    (Bool.or (tbl-has source-id (:debtor e) xs)
                             (Bool.and (Nat.beq (:kind e) ek-wait) (tbl-has resource-id (:debtor e) rs))))))
(a/defn edge-ok [cs :- (List CompRow), ts :- (List TaskRow), xs :- (List SourceRow),
                 as :- (List ActRow), rs :- (List ResRow), e :- EdgeRow] Bool
  (Bool.and (cred-ok cs as e) (deb-ok cs ts xs rs e)))
(a/defn edges-ref-ok-in [cs :- (List CompRow), ts :- (List TaskRow), xs :- (List SourceRow),
                         as :- (List ActRow), rs :- (List ResRow), es :- (List EdgeRow)] Bool
  (tbl-all (edge-ok cs ts xs as rs) es))
(a/defn edges-ref-ok [w :- World] Bool
  (edges-ref-ok-in (:comps w) (:tasks w) (:sources w) (:acts w) (:res w) (:edges w)))
;; the precondition for inserting e into w
(a/defn edge-ok-in [w :- World, e :- EdgeRow] Bool
  (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w) e))
;; no edge names id x as creditor or debtor
(a/defn edge-avoids [x :- Nat, e :- EdgeRow] Bool
  (Bool.and (Bool.not (Nat.beq (:creditor e) x)) (Bool.not (Nat.beq (:debtor e) x))))
(a/defn unreferenced [w :- World, x :- Nat] Bool (tbl-all (edge-avoids x) (:edges w)))

(a/theorem edges-ref-ok-frame [w1 :- World, w2 :- World]
  (=> (= (:comps w2) (:comps w1)) (= (:tasks w2) (:tasks w1)) (= (:sources w2) (:sources w1))
      (= (:acts w2) (:acts w1)) (= (:edges w2) (:edges w1)) (= (:res w2) (:res w1))
      (= (edges-ref-ok w2) (edges-ref-ok w1)))
  (intros h1 h2 h3 h4 h5 h6)
  (simp only [edges-ref-ok h1 h2 h3 h4 h5 h6]))

(defframes-tables edges-ref-ok
  scope ScopeRow run RunRow cleanup CleanupRow pub PubRow fork ForkRow)
(defframes edges-ref-ok
  set-pins [v :- (List Nat)] (set-pins w v)
  set-pending-act [v :- Nat] (set-pending-act w v)
  set-released [v :- Bool] (set-released w v)
  bump [] (bump w))

(a/theorem edge-ok-set-marked [cs :- (List CompRow), ts :- (List TaskRow), xs :- (List SourceRow),
                               as :- (List ActRow), rs :- (List ResRow), b :- Bool, e :- EdgeRow]
  (= (edge-ok cs ts xs as rs (edge-set-marked b e)) (edge-ok cs ts xs as rs e))
  (rfl))

;; comp edits that keep ids keep every edge's verdict
(a/theorem edge-ok-comps-upd [cs :- (List CompRow), ts :- (List TaskRow), xs :- (List SourceRow),
                              as :- (List ActRow), rs :- (List ResRow), y :- Nat, f :- (=> CompRow CompRow),
                              hf :- (forall [r :- CompRow] (= (comp-id (f r)) (comp-id r))), e :- EdgeRow]
  (= (edge-ok (tbl-upd comp-id y f cs) ts xs as rs e) (edge-ok cs ts xs as rs e))
  (simp only [edge-ok cred-ok deb-ok (tbl-has-upd CompRow comp-id y (:creditor e) f hf cs)
              (tbl-has-upd CompRow comp-id y (:debtor e) f hf cs)]))

(a/theorem edges-ref-ok-comps-upd [cs :- (List CompRow), ts :- (List TaskRow), xs :- (List SourceRow),
                                   as :- (List ActRow), rs :- (List ResRow), es :- (List EdgeRow), y :- Nat, f :- (=> CompRow CompRow),
                                   hf :- (forall [r :- CompRow] (= (comp-id (f r)) (comp-id r)))]
  (= (edges-ref-ok-in (tbl-upd comp-id y f cs) ts xs as rs es) (edges-ref-ok-in cs ts xs as rs es))
  (simp only [edges-ref-ok-in])
  (exact (tbl-all-congr EdgeRow (edge-ok (tbl-upd comp-id y f cs) ts xs as rs) (edge-ok cs ts xs as rs)
           (edge-ok-comps-upd cs ts xs as rs y f hf) es)))

(a/theorem edges-ref-ok-set-marked [cs :- (List CompRow), ts :- (List TaskRow), xs :- (List SourceRow),
                                    as :- (List ActRow), rs :- (List ResRow), es :- (List EdgeRow), x :- Nat, b :- Bool]
  (=> (= (edges-ref-ok-in cs ts xs as rs es) true)
      (= (edges-ref-ok-in cs ts xs as rs (tbl-upd edge-id x (edge-set-marked b) es)) true))
  (intro h)
  (have hin (forall [r :- EdgeRow] (=> (= (edge-ok cs ts xs as rs r) true) (= (Nat.beq (edge-id r) x) true)
                                       (= (edge-ok cs ts xs as rs (edge-set-marked b r)) true))))
  (intros r h1 h2) (rw [(edge-ok-set-marked cs ts xs as rs b r)]) (exact h1)
  (have hout (forall [r :- EdgeRow] (=> (= (edge-ok cs ts xs as rs r) true) (= (Nat.beq (edge-id r) x) false)
                                        (= (edge-ok cs ts xs as rs r) true))))
  (intros r h1 h2) (exact h1)
  (exact (tbl-all-upd EdgeRow edge-id x (edge-set-marked b) (edge-ok cs ts xs as rs) (edge-ok cs ts xs as rs)
           hin hout es h)))

(a/theorem edges-ref-ok-del [cs :- (List CompRow), ts :- (List TaskRow), xs :- (List SourceRow),
                             as :- (List ActRow), rs :- (List ResRow), es :- (List EdgeRow), x :- Nat]
  (=> (= (edges-ref-ok-in cs ts xs as rs es) true)
      (= (edges-ref-ok-in cs ts xs as rs (tbl-del edge-id x es)) true))
  (intro h)
  (have hout (forall [r :- EdgeRow] (=> (= (edge-ok cs ts xs as rs r) true) (= (Nat.beq (edge-id r) x) false)
                                        (= (edge-ok cs ts xs as rs r) true))))
  (intros r h1 h2) (exact h1)
  (exact (tbl-all-del EdgeRow edge-id x (edge-ok cs ts xs as rs) (edge-ok cs ts xs as rs) hout es h)))

(a/theorem comp-inc-pending-id [r :- CompRow] (= (comp-id (comp-inc-pending r)) (comp-id r)) (rfl))
(a/theorem comp-dec-pending-id [r :- CompRow] (= (comp-id (comp-dec-pending r)) (comp-id r)) (rfl))

;; ---- World-level: edge edits preserve edges-ref-ok

(a/theorem insert-edge-edges-ref-ok [w :- World, e :- EdgeRow]
  (=> (= (edge-ok-in w e) true) (= (edges-ref-ok w) true) (= (edges-ref-ok (insert-edge w e)) true))
  (intros he h)
  (simp only [edges-ref-ok insert-edge edge-ins set-edges edges-ref-ok-in tbl-ins tbl-all
              edge-ok-set-marked Bool.and_eq_true])
  (exact (And.intro he h)))

(a/theorem mark-edge-edges-ref-ok [w :- World, x :- Nat]
  (=> (= (edges-ref-ok w) true) (= (edges-ref-ok (mark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x)) (case' [some e]) (case' [none])
  (simp only [mark-edge hf]) (exact h)
  (cases hm (:marked e))
  (simp only [mark-edge hf hm edges-ref-ok comp-upd edge-upd set-comps set-edges
              (edges-ref-ok-comps-upd (:comps w) (:tasks w) (:sources w) (:acts w) (:res w)
                (tbl-upd edge-id x (edge-set-marked true) (:edges w)) (:creditor e) comp-inc-pending
                comp-inc-pending-id)])
  (exact (edges-ref-ok-set-marked (:comps w) (:tasks w) (:sources w) (:acts w) (:res w) (:edges w) x true h))
  (simp only [mark-edge hf hm]) (exact h))

(a/theorem unmark-edge-edges-ref-ok [w :- World, x :- Nat]
  (=> (= (edges-ref-ok w) true) (= (edges-ref-ok (unmark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x)) (case' [some e]) (case' [none])
  (simp only [unmark-edge hf]) (exact h)
  (cases hm (:marked e))
  (simp only [unmark-edge hf hm]) (exact h)
  (simp only [unmark-edge hf hm edges-ref-ok comp-upd edge-upd set-comps set-edges
              (edges-ref-ok-comps-upd (:comps w) (:tasks w) (:sources w) (:acts w) (:res w)
                (tbl-upd edge-id x (edge-set-marked false) (:edges w)) (:creditor e) comp-dec-pending
                comp-dec-pending-id)])
  (exact (edges-ref-ok-set-marked (:comps w) (:tasks w) (:sources w) (:acts w) (:res w) (:edges w) x false h)))

(a/theorem remove-edge-edges-ref-ok [w :- World, x :- Nat]
  (=> (= (edges-ref-ok w) true) (= (edges-ref-ok (remove-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x)) (case' [some e]) (case' [none])
  (simp only [remove-edge hf]) (exact h)
  (cases hm (:marked e))
  (simp only [remove-edge hf hm edges-ref-ok edge-del set-edges])
  (exact (edges-ref-ok-del (:comps w) (:tasks w) (:sources w) (:acts w) (:res w) (:edges w) x h))
  (simp only [remove-edge hf hm edges-ref-ok comp-upd edge-del set-comps set-edges
              (edges-ref-ok-comps-upd (:comps w) (:tasks w) (:sources w) (:acts w) (:res w)
                (tbl-del edge-id x (:edges w)) (:creditor e) comp-dec-pending comp-dec-pending-id)])
  (exact (edges-ref-ok-del (:comps w) (:tasks w) (:sources w) (:acts w) (:res w) (:edges w) x h)))

;; removing a computation that no edge references keeps every edge's endpoints
(a/theorem edge-ok-comp-del [cs :- (List CompRow), ts :- (List TaskRow), xs :- (List SourceRow),
                             as :- (List ActRow), rs :- (List ResRow), x :- Nat, e :- EdgeRow]
  (=> (= (edge-avoids x e) true)
      (= (edge-ok (tbl-del comp-id x cs) ts xs as rs e) (edge-ok cs ts xs as rs e)))
  (intro ha)
  (simp only [edge-avoids Bool.and_eq_true] at ha)
  (have hc (= (Nat.beq x (:creditor e)) false))
  (rw [(beq-comm x (:creditor e))]) (exact (bnot-true (Nat.beq (:creditor e) x) (And.left ha)))
  (have hd (= (Nat.beq x (:debtor e)) false))
  (rw [(beq-comm x (:debtor e))]) (exact (bnot-true (Nat.beq (:debtor e) x) (And.right ha)))
  (simp only [edge-ok cred-ok deb-ok (tbl-has-del-ne CompRow comp-id x (:creditor e) cs hc)
              (tbl-has-del-ne CompRow comp-id x (:debtor e) cs hd)]))

(a/theorem comp-del-edges-ref-ok [w :- World, x :- Nat]
  (=> (= (unreferenced w x) true) (= (edges-ref-ok w) true) (= (edges-ref-ok (comp-del w x)) true))
  (intros hu h)
  (have hpq (forall [r :- EdgeRow]
              (=> (= (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w) r) true)
                  (= (edge-avoids x r) true)
                  (= (edge-ok (tbl-del comp-id x (:comps w)) (:tasks w) (:sources w) (:acts w) (:res w) r) true))))
  (intros r h1 h2)
  (rw [(edge-ok-comp-del (:comps w) (:tasks w) (:sources w) (:acts w) (:res w) x r h2)])
  (exact h1)
  (exact (tbl-all-mono2 EdgeRow (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w)) (edge-avoids x)
           (edge-ok (tbl-del comp-id x (:comps w)) (:tasks w) (:sources w) (:acts w) (:res w)) hpq (:edges w) h hu)))

;; comp edits that keep ids
(a/theorem comp-upd-edges-ref-ok [w :- World, x :- Nat, f :- (=> CompRow CompRow),
                                  hf :- (forall [r :- CompRow] (= (comp-id (f r)) (comp-id r)))]
  (= (edges-ref-ok (comp-upd w x f)) (edges-ref-ok w))
  (simp only [edges-ref-ok comp-upd set-comps
              (edges-ref-ok-comps-upd (:comps w) (:tasks w) (:sources w) (:acts w) (:res w) (:edges w) x f hf)]))


;; ---------------------------------------------------------------------------
;; Id uniqueness over the global id space

(a/defn ids-unique [w :- World] Bool (nat-nodup (all-ids w)))
;; allocator >= 1 and every id in 1 .. next-id - 1
(a/defn ids-below [w :- World] Bool
  (Bool.and (Nat.blt 0 (:next-id w)) (tbl-all (id-in-range (:next-id w)) (all-ids w))))
(a/defn ids-ok [w :- World] Bool (Bool.and (ids-unique w) (ids-below w)))

(a/theorem ids-ok-empty [] (= (ids-ok empty-world) true) (rfl))

(a/theorem ids-unique-edges [w :- World]
  (=> (= (ids-unique w) true) (= (edge-ids-nodup w) true))
  (intro h)
  (simp only [ids-unique all-ids] at h)
  (simp only [edge-ids-nodup])
  (exact (nat-nodup-app-left _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _
           (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ (nat-nodup-app-right _ _ h))))))))


(def ^:private id-tables
  "all-ids order: [prefix field row]"
  '[[scope scopes ScopeRow] [comp comps CompRow] [task tasks TaskRow] [run runs RunRow]
    [source sources SourceRow] [edge edges EdgeRow] [act acts ActRow] [resource res ResRow]
    [pub pubs PubRow] [fork forks ForkRow]])

(defn- ids-of [[prefix field _]] (list 'tbl-ids (symbol (str prefix "-id")) (list (keyword field) 'w)))
(defn- app-chain [xs] (reduce (fn [acc x] (list 'nat-app x acc)) (reverse xs)))

(defmacro ^:private deffresh
  "For each id table: inserting a row whose id is next-id, then bumping, preserves ids-ok."
  []
  `(do
     ~@(for [k (range (count id-tables))
             :let [[prefix _ row :as t] (nth id-tables k)
                   pre (map ids-of (take k id-tables))
                   P (if (seq pre) (app-chain pre) '(List.nil Nat))
                   rest (drop (inc k) id-tables)
                   Q' (when (seq rest) (app-chain (map ids-of rest)))
                   ins (symbol (str prefix "-ins"))
                   idf (symbol (str prefix "-id"))
                   tail (if Q' (list 'nat-app (ids-of t) Q') (ids-of t))]]
         `(a/theorem ~(symbol (str prefix "-ins-fresh-ids-ok")) [~'w :- ~'World, ~'r :- ~row]
            (~'=> (~'= (~idf ~'r) (:next-id ~'w)) (~'= (~'ids-ok ~'w) true)
                  (~'= (~'ids-ok (~'bump (~ins ~'w ~'r))) true))
            (~'intros ~'hr ~'h)
            (~'simp ~'only [~'ids-ok ~'ids-unique ~'ids-below ~'Bool.and_eq_true] ~'at ~'h)
            (~'have ~'hold (~'= (~'all-ids ~'w) (~'nat-app ~P ~tail)))
            (~'simp ~'only [~'all-ids ~'nat-app-assoc ~'nat-app])
            (~'have ~'hnew (~'= (~'all-ids (~'bump (~ins ~'w ~'r)))
                               (~'nat-app ~P (~'List.cons ~'Nat (:next-id ~'w) ~tail))))
            (~'simp ~'only [~'all-ids ~'bump ~ins ~(symbol (str "set-" (second t))) ~'set-next-id
                            ~'tbl-ins ~'tbl-ids ~'hr ~'nat-app-assoc ~'nat-app])
            (~'rw [~'hold] ~'at ~'h)
            (~'have ~'hf (~'And (~'= (~'nat-nodup (~'nat-app ~P (~'List.cons ~'Nat (:next-id ~'w) ~tail))) true)
                                (~'= (~'tbl-all (~'id-in-range (~'+ (:next-id ~'w) 1))
                                       (~'nat-app ~P (~'List.cons ~'Nat (:next-id ~'w) ~tail))) true)))
            (~'exact (~'ids-fresh-insert (:next-id ~'w) ~P ~tail (~'And.left ~'h) (~'And.left (~'And.right ~'h))
                       (~'And.right (~'And.right ~'h))))
            (~'simp ~'only [~'ids-ok ~'ids-unique ~'ids-below ~'Bool.and_eq_true ~'hnew ~'bump ~'set-next-id
                            ~'Nat.blt_eq])
            (~'exact (~'And.intro (~'And.left ~'hf) (~'And.intro ~'True.intro (~'And.right ~'hf))))))))

(deffresh)

(a/theorem insert-edge-fresh-ids-ok [w :- World, e :- EdgeRow]
  (=> (= (ids-ok w) true) (= (ids-ok (insert-edge-fresh w e)) true))
  (intro h)
  (exact (edge-ins-fresh-ids-ok w (edge-set-marked false (edge-set-id (:next-id w) e)) (rfl) h)))


;; ---------------------------------------------------------------------------
;; Corollaries over the bundle

(a/theorem ids-ok-edges [w :- World]
  (=> (= (ids-ok w) true) (= (edge-ids-nodup w) true))
  (intro h)
  (simp only [ids-ok Bool.and_eq_true] at h)
  (exact (ids-unique-edges w (And.left h))))

(a/theorem edge-set-marked-id [b :- Bool, e :- EdgeRow] (= (edge-id (edge-set-marked b e)) (edge-id e)) (rfl))

(a/theorem mark-edge-all-ids [w :- World, x :- Nat]
  (And (= (all-ids (mark-edge w x)) (all-ids w)) (= (:next-id (mark-edge w x)) (:next-id w)))
  (cases hf (edge-find w x)) (case' [some e]) (case' [none])
  (simp only [mark-edge hf]) (simp)
  (cases hm (:marked e))
  (simp only [mark-edge hf hm all-ids comp-upd edge-upd set-comps set-edges
              (tbl-ids-upd CompRow comp-id (:creditor e) comp-inc-pending comp-inc-pending-id (:comps w))
              (tbl-ids-upd EdgeRow edge-id x (edge-set-marked true) (edge-set-marked-id true) (:edges w))])
  (simp)
  (simp only [mark-edge hf hm]) (simp))

(a/theorem unmark-edge-all-ids [w :- World, x :- Nat]
  (And (= (all-ids (unmark-edge w x)) (all-ids w)) (= (:next-id (unmark-edge w x)) (:next-id w)))
  (cases hf (edge-find w x)) (case' [some e]) (case' [none])
  (simp only [unmark-edge hf]) (simp)
  (cases hm (:marked e))
  (simp only [unmark-edge hf hm]) (simp)
  (simp only [unmark-edge hf hm all-ids comp-upd edge-upd set-comps set-edges
              (tbl-ids-upd CompRow comp-id (:creditor e) comp-dec-pending comp-dec-pending-id (:comps w))
              (tbl-ids-upd EdgeRow edge-id x (edge-set-marked false) (edge-set-marked-id false) (:edges w))])
  (simp))

(a/theorem mark-edge-ids-ok [w :- World, x :- Nat]
  (= (ids-ok (mark-edge w x)) (ids-ok w))
  (simp only [ids-ok ids-unique ids-below (And.left (mark-edge-all-ids w x)) (And.right (mark-edge-all-ids w x))]))

(a/theorem unmark-edge-ids-ok [w :- World, x :- Nat]
  (= (ids-ok (unmark-edge w x)) (ids-ok w))
  (simp only [ids-ok ids-unique ids-below (And.left (unmark-edge-all-ids w x)) (And.right (unmark-edge-all-ids w x))]))

(a/theorem insert-edge-fresh-pending-exact [w :- World, e :- EdgeRow]
  (=> (= (pending-exact w) true) (= (pending-exact (insert-edge-fresh w e)) true))
  (intro h)
  (exact (insert-edge-pending-exact w (edge-set-id (:next-id w) e) h)))

(a/theorem insert-edge-fresh-edges-ref-ok [w :- World, e :- EdgeRow]
  (=> (= (edge-ok-in w e) true) (= (edges-ref-ok w) true) (= (edges-ref-ok (insert-edge-fresh w e)) true))
  (intros he h)
  (exact (insert-edge-edges-ref-ok w (edge-set-id (:next-id w) e) he h)))

;; The sample bundle and the edge edits.
(a/defn inv-sample [w :- World] Bool
  (Bool.and (pending-exact w) (Bool.and (edges-ref-ok w) (ids-ok w))))

(a/theorem inv-sample-empty [] (= (inv-sample empty-world) true) (rfl))

(a/theorem mark-edge-inv-sample [w :- World, x :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (mark-edge w x)) true))
  (intro h)
  (simp only [inv-sample Bool.and_eq_true] at h)
  (simp only [inv-sample Bool.and_eq_true (mark-edge-ids-ok w x)])
  (exact (And.intro (mark-edge-pending-exact w x (ids-ok-edges w (And.right (And.right h))) (And.left h))
           (And.intro (mark-edge-edges-ref-ok w x (And.left (And.right h))) (And.right (And.right h))))))

(a/theorem unmark-edge-inv-sample [w :- World, x :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (unmark-edge w x)) true))
  (intro h)
  (simp only [inv-sample Bool.and_eq_true] at h)
  (simp only [inv-sample Bool.and_eq_true (unmark-edge-ids-ok w x)])
  (exact (And.intro (unmark-edge-pending-exact w x (ids-ok-edges w (And.right (And.right h))) (And.left h))
           (And.intro (unmark-edge-edges-ref-ok w x (And.left (And.right h))) (And.right (And.right h))))))

(a/theorem insert-edge-fresh-inv-sample [w :- World, e :- EdgeRow]
  (=> (= (edge-ok-in w e) true) (= (inv-sample w) true) (= (inv-sample (insert-edge-fresh w e)) true))
  (intros he h)
  (simp only [inv-sample Bool.and_eq_true] at h)
  (simp only [inv-sample Bool.and_eq_true])
  (exact (And.intro (insert-edge-fresh-pending-exact w e (And.left h))
           (And.intro (insert-edge-fresh-edges-ref-ok w e he (And.left (And.right h)))
                      (insert-edge-fresh-ids-ok w e (And.right (And.right h)))))))


;; ===========================================================================
;; Appended for spindel.v2.step: more primitive edits and their lemmas
;;
;; - `tbl-filter` (filter rows), `nat-del`; `tbl-del` is a `tbl-filter` (`tbl-del-filter`).
;; - ids-ok: keeping a subset of / deleting rows of one id table (`<p>-filter-ids-ok`,
;;   `<p>-del-ids-ok`, all tables but forks), id-preserving updates (`<p>-upd-ids-ok`),
;;   rfl frames for cleanup and pins, `remove-edge-ids-ok`.
;; - edges-ref-ok: id-preserving updates of sources/tasks/acts, `source-ins` (monotone).
;; - `drop-cred-edges w a` removes every edge whose creditor is a (and zeroes a's pending);
;;   `drop-act w a` then removes activation a.
;; - inv-sample (pending-exact ∧ edges-ref-ok ∧ ids-ok), one lemma per edit: `inv-<p>-upd`,
;;   `inv-edge-upd` (keeps id/kind/creditor/debtor/marked), `inv-comp-upd` (keeps id/pending),
;;   `inv-run-del`, `inv-resource-del`, `inv-cleanup-*`, `inv-set-pins`, `inv-source-ins-fresh`,
;;   `inv-resource-ins-fresh`, `inv-remove-edge`, `inv-drop-cred`, `inv-drop-act`.
;; - `nat-fold f w ids` (an edit over a list of ids) and `nat-fold-inv`; `tbl-find-has`.
;; ===========================================================================

(a/defn tbl-filter [A :- Type :implicit, p :- (=> A Bool), xs :- (List A)] (List A)
  (match xs [nil (List.nil A)]
         [(cons h t) (if (p h) (List.cons A h (tbl-filter p t)) (tbl-filter p t))]))

(a/defn nat-del [x :- Nat, xs :- (List Nat)] (List Nat)
  (match xs [nil (List.nil Nat)]
         [(cons h t) (if (Nat.beq h x) (nat-del x t) (List.cons Nat h (nat-del x t)))]))

(a/defn id-ne [A :- Type :implicit, idf :- (=> A Nat), x :- Nat, r :- A] Bool
  (Bool.not (Nat.beq (idf r) x)))

(a/theorem tbl-del-filter [A :- Type, idf :- (=> A Nat), x :- Nat, xs :- (List A)]
  (= (tbl-del idf x xs) (tbl-filter (id-ne idf x) xs))
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (simp [tbl-del tbl-filter])
  (cases hx (Nat.beq (idf h) x))
  (all_goals (simp [tbl-del tbl-filter id-ne hx ih])))

(a/theorem tbl-all-filter [A :- Type, P :- (=> A Bool), q :- (=> A Bool), xs :- (List A)]
  (=> (= (tbl-all P xs) true) (= (tbl-all P (tbl-filter q xs)) true))
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (intro hp) (simp [tbl-filter tbl-all])
  (intro hp)
  (simp only [tbl-all Bool.and_eq_true] at hp)
  (cases hq (q h))
  (simp only [tbl-filter hq]) (exact (ih (And.right hp)))
  (simp only [tbl-filter hq tbl-all Bool.and_eq_true])
  (exact (And.intro (And.left hp) (ih (And.right hp)))))

(a/theorem tbl-all-filter-self [A :- Type, q :- (=> A Bool), xs :- (List A)]
  (= (tbl-all q (tbl-filter q xs)) true)
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (simp [tbl-filter tbl-all])
  (cases hq (q h))
  (simp only [tbl-filter hq]) (exact ih)
  (simp [tbl-filter hq tbl-all ih]))

(a/theorem filter-ids-not-mem [A :- Type, idf :- (=> A Nat), p :- (=> A Bool), y :- Nat, xs :- (List A)]
  (=> (= (nat-mem y (tbl-ids idf xs)) false) (= (nat-mem y (tbl-ids idf (tbl-filter p xs))) false))
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (intro hm) (simp [tbl-filter tbl-ids nat-mem])
  (intro hm)
  (cases hy (Nat.beq (idf h) y))
  (simp only [tbl-ids nat-mem hy] at hm)
  (cases hp (p h))
  (simp only [tbl-filter hp]) (exact (ih hm))
  (simp only [tbl-filter hp tbl-ids nat-mem hy]) (exact (ih hm))
  (simp [tbl-ids nat-mem hy] at hm))

(a/theorem filter-ids-range [A :- Type, idf :- (=> A Nat), p :- (=> A Bool), q :- (=> Nat Bool), xs :- (List A)]
  (=> (= (tbl-all q (tbl-ids idf xs)) true) (= (tbl-all q (tbl-ids idf (tbl-filter p xs))) true))
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (intro hr) (simp [tbl-filter tbl-ids tbl-all])
  (intro hr)
  (simp only [tbl-ids tbl-all Bool.and_eq_true] at hr)
  (cases hp (p h))
  (simp only [tbl-filter hp]) (exact (ih (And.right hr)))
  (simp only [tbl-filter hp tbl-ids tbl-all Bool.and_eq_true])
  (exact (And.intro (And.left hr) (ih (And.right hr)))))

(a/theorem filter-ids-nodup-app [A :- Type, idf :- (=> A Nat), p :- (=> A Bool), R :- (List Nat), xs :- (List A)]
  (=> (= (nat-nodup (nat-app (tbl-ids idf xs) R)) true)
      (= (nat-nodup (nat-app (tbl-ids idf (tbl-filter p xs)) R)) true))
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (intro hn) (simp only [tbl-filter tbl-ids nat-app] at hn) (simp only [tbl-filter tbl-ids nat-app]) (exact hn)
  (intro hn)
  (simp only [tbl-ids nat-app nat-nodup Bool.and_eq_true] at hn)
  (have hm (= (nat-mem (idf h) (nat-app (tbl-ids idf t) R)) false))
  (exact (bnot-true _ (And.left hn)))
  (simp only [nat-mem-app Bool.or_eq_false_iff] at hm)
  (cases hp (p h))
  (simp only [tbl-filter hp]) (exact (ih (And.right hn)))
  (simp only [tbl-filter hp tbl-ids nat-app nat-nodup Bool.and_eq_true])
  (apply And.intro)
  (simp [nat-mem-app (filter-ids-not-mem A idf p (idf h) t (And.left hm)) (And.right hm)])
  (exact (ih (And.right hn))))

(a/theorem filter-ids-nodup-mid [A :- Type, idf :- (=> A Nat), p :- (=> A Bool), xs :- (List A), R :- (List Nat),
                               P :- (List Nat)]
  (=> (= (nat-nodup (nat-app P (nat-app (tbl-ids idf xs) R))) true)
      (= (nat-nodup (nat-app P (nat-app (tbl-ids idf (tbl-filter p xs)) R))) true))
  (induction P)
  (case' [cons h t ih])
  (case' [nil])
  (intro hn) (simp only [nat-app] at hn) (simp only [nat-app]) (exact (filter-ids-nodup-app A idf p R xs hn))
  (intro hn)
  (simp only [nat-app nat-nodup Bool.and_eq_true] at hn)
  (have hm (= (nat-mem h (nat-app t (nat-app (tbl-ids idf xs) R))) false))
  (exact (bnot-true _ (And.left hn)))
  (simp only [nat-mem-app Bool.or_eq_false_iff] at hm)
  (simp only [nat-app nat-nodup Bool.and_eq_true])
  (apply And.intro)
  (simp [nat-mem-app (And.left hm) (filter-ids-not-mem A idf p h xs (And.left (And.right hm)))
         (And.right (And.right hm))])
  (exact (ih (And.right hn))))

(a/theorem filter-ids-range-mid [A :- Type, idf :- (=> A Nat), p :- (=> A Bool), q :- (=> Nat Bool),
                               xs :- (List A), R :- (List Nat), P :- (List Nat)]
  (=> (= (tbl-all q (nat-app P (nat-app (tbl-ids idf xs) R))) true)
      (= (tbl-all q (nat-app P (nat-app (tbl-ids idf (tbl-filter p xs)) R))) true))
  (intro h)
  (simp only [tbl-all-nat-app Bool.and_eq_true] at h)
  (simp only [tbl-all-nat-app Bool.and_eq_true])
  (exact (And.intro (And.left h) (And.intro (filter-ids-range A idf p q xs (And.left (And.right h)))
                                            (And.right (And.right h))))))

;; ---- ids-ok under filtering / deleting rows of one id table, and under id-preserving updates

(defmacro ^:private deffilter
  "For each id table except the last: keeping a subset of its rows preserves ids-ok
  (<p>-filter-ids-ok), hence so does deleting a row (<p>-del-ids-ok)."
  []
  `(do
     ~@(for [k (range (dec (count id-tables)))
             :let [[prefix field row :as t] (nth id-tables k)
                   pre (map ids-of (take k id-tables))
                   P (if (seq pre) (app-chain pre) '(List.nil Nat))
                   R (app-chain (map ids-of (drop (inc k) id-tables)))
                   idf (symbol (str prefix "-id"))
                   setter (symbol (str "set-" field))
                   kept (list 'tbl-filter 'q (list (keyword field) 'w))]]
         `(do
            (a/theorem ~(symbol (str prefix "-filter-ids-ok")) [~'w :- ~'World, ~'q :- (~'=> ~row ~'Bool)]
              (~'=> (~'= (~'ids-ok ~'w) true) (~'= (~'ids-ok (~setter ~'w ~kept)) true))
              (~'intro ~'h)
              (~'simp ~'only [~'ids-ok ~'ids-unique ~'ids-below ~'Bool.and_eq_true] ~'at ~'h)
              (~'have ~'hold (~'= (~'all-ids ~'w) (~'nat-app ~P (~'nat-app ~(ids-of t) ~R))))
              (~'simp ~'only [~'all-ids ~'nat-app-assoc ~'nat-app])
              (~'have ~'hnew (~'= (~'all-ids (~setter ~'w ~kept))
                                 (~'nat-app ~P (~'nat-app (~'tbl-ids ~idf ~kept) ~R))))
              (~'simp ~'only [~'all-ids ~setter ~'nat-app-assoc ~'nat-app])
              (~'have ~'hnx (~'= (:next-id (~setter ~'w ~kept)) (:next-id ~'w)))
              (~'rfl)
              (~'rw [~'hold] ~'at ~'h)
              (~'simp ~'only [~'ids-ok ~'ids-unique ~'ids-below ~'Bool.and_eq_true ~'hnew ~'hnx])
              (~'exact (~'And.intro
                        (~'filter-ids-nodup-mid ~row ~idf ~'q ~(list (keyword field) 'w) ~R ~P (~'And.left ~'h))
                        (~'And.intro (~'And.left (~'And.right ~'h))
                         (~'filter-ids-range-mid ~row ~idf ~'q (~'id-in-range (:next-id ~'w))
                          ~(list (keyword field) 'w) ~R ~P (~'And.right (~'And.right ~'h)))))))
            (a/theorem ~(symbol (str prefix "-del-ids-ok")) [~'w :- ~'World, ~'x :- ~'Nat]
              (~'=> (~'= (~'ids-ok ~'w) true) (~'= (~'ids-ok (~(symbol (str prefix "-del")) ~'w ~'x)) true))
              (~'intro ~'h)
              (~'simp ~'only [~(symbol (str prefix "-del")) (~'tbl-del-filter ~row ~idf ~'x ~(list (keyword field) 'w))])
              (~'exact (~(symbol (str prefix "-filter-ids-ok")) ~'w (~'id-ne ~idf ~'x) ~'h)))))))

(deffilter)

(defmacro ^:private defupd-ids
  "For each id table: an update that keeps row ids keeps ids-ok (<p>-upd-ids-ok)."
  []
  `(do
     ~@(for [[prefix field row] id-tables
             :let [idf (symbol (str prefix "-id"))
                   upd (symbol (str prefix "-upd"))]]
         `(a/theorem ~(symbol (str prefix "-upd-ids-ok"))
            [~'w :- ~'World, ~'x :- ~'Nat, ~'f :- (~'=> ~row ~row),
             ~'hf :- (~'forall [~'r :- ~row] (~'= (~idf (~'f ~'r)) (~idf ~'r)))]
            (~'= (~'ids-ok (~upd ~'w ~'x ~'f)) (~'ids-ok ~'w))
            (~'simp ~'only [~'ids-ok ~'ids-unique ~'ids-below ~'all-ids ~upd ~(symbol (str "set-" field))
                            (~'tbl-ids-upd ~row ~idf ~'x ~'f ~'hf ~(list (keyword field) 'w))])))))

(defupd-ids)

;; ids-ok does not read cleanup, pins, pending-act or released
(a/theorem ids-ok-cleanup-del [w :- World, x :- Nat] (= (ids-ok (cleanup-del w x)) (ids-ok w)) (rfl))
(a/theorem ids-ok-cleanup-upd [w :- World, x :- Nat, f :- (=> CleanupRow CleanupRow)]
  (= (ids-ok (cleanup-upd w x f)) (ids-ok w)) (rfl))
(a/theorem ids-ok-set-pins [w :- World, v :- (List Nat)] (= (ids-ok (set-pins w v)) (ids-ok w)) (rfl))

;; ---- edges-ref-ok under id-preserving updates of the tables it reads, and under source-ins

(a/theorem edge-ok-sources-upd [cs :- (List CompRow), ts :- (List TaskRow), xs :- (List SourceRow),
                                as :- (List ActRow), rs :- (List ResRow), y :- Nat, f :- (=> SourceRow SourceRow),
                                hf :- (forall [r :- SourceRow] (= (source-id (f r)) (source-id r))), e :- EdgeRow]
  (= (edge-ok cs ts (tbl-upd source-id y f xs) as rs e) (edge-ok cs ts xs as rs e))
  (simp only [edge-ok cred-ok deb-ok (tbl-has-upd SourceRow source-id y (:debtor e) f hf xs)]))

(a/theorem edge-ok-tasks-upd [cs :- (List CompRow), ts :- (List TaskRow), xs :- (List SourceRow),
                              as :- (List ActRow), rs :- (List ResRow), y :- Nat, f :- (=> TaskRow TaskRow),
                              hf :- (forall [r :- TaskRow] (= (task-id (f r)) (task-id r))), e :- EdgeRow]
  (= (edge-ok cs (tbl-upd task-id y f ts) xs as rs e) (edge-ok cs ts xs as rs e))
  (simp only [edge-ok cred-ok deb-ok (tbl-has-upd TaskRow task-id y (:debtor e) f hf ts)]))

(a/theorem edge-ok-acts-upd [cs :- (List CompRow), ts :- (List TaskRow), xs :- (List SourceRow),
                             as :- (List ActRow), rs :- (List ResRow), y :- Nat, f :- (=> ActRow ActRow),
                             hf :- (forall [r :- ActRow] (= (act-id (f r)) (act-id r))), e :- EdgeRow]
  (= (edge-ok cs ts xs (tbl-upd act-id y f as) rs e) (edge-ok cs ts xs as rs e))
  (simp only [edge-ok cred-ok deb-ok (tbl-has-upd ActRow act-id y (:creditor e) f hf as)]))

(a/theorem source-upd-edges-ref-ok [w :- World, x :- Nat, f :- (=> SourceRow SourceRow),
                                    hf :- (forall [r :- SourceRow] (= (source-id (f r)) (source-id r)))]
  (= (edges-ref-ok (source-upd w x f)) (edges-ref-ok w))
  (simp only [edges-ref-ok source-upd set-sources edges-ref-ok-in])
  (exact (tbl-all-congr EdgeRow (edge-ok (:comps w) (:tasks w) (tbl-upd source-id x f (:sources w)) (:acts w) (:res w))
           (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w))
           (edge-ok-sources-upd (:comps w) (:tasks w) (:sources w) (:acts w) (:res w) x f hf) (:edges w))))

(a/theorem task-upd-edges-ref-ok [w :- World, x :- Nat, f :- (=> TaskRow TaskRow),
                                  hf :- (forall [r :- TaskRow] (= (task-id (f r)) (task-id r)))]
  (= (edges-ref-ok (task-upd w x f)) (edges-ref-ok w))
  (simp only [edges-ref-ok task-upd set-tasks edges-ref-ok-in])
  (exact (tbl-all-congr EdgeRow (edge-ok (:comps w) (tbl-upd task-id x f (:tasks w)) (:sources w) (:acts w) (:res w))
           (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w))
           (edge-ok-tasks-upd (:comps w) (:tasks w) (:sources w) (:acts w) (:res w) x f hf) (:edges w))))

(a/theorem act-upd-edges-ref-ok [w :- World, x :- Nat, f :- (=> ActRow ActRow),
                                 hf :- (forall [r :- ActRow] (= (act-id (f r)) (act-id r)))]
  (= (edges-ref-ok (act-upd w x f)) (edges-ref-ok w))
  (simp only [edges-ref-ok act-upd set-acts edges-ref-ok-in])
  (exact (tbl-all-congr EdgeRow (edge-ok (:comps w) (:tasks w) (:sources w) (tbl-upd act-id x f (:acts w)) (:res w))
           (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w))
           (edge-ok-acts-upd (:comps w) (:tasks w) (:sources w) (:acts w) (:res w) x f hf) (:edges w))))

(a/theorem tbl-has-ins [A :- Type, idf :- (=> A Nat), y :- Nat, r :- A, xs :- (List A)]
  (= (tbl-has idf y (tbl-ins r xs)) (Bool.or (Nat.beq (idf r) y) (tbl-has idf y xs)))
  (cases hb (Nat.beq (idf r) y))
  (all_goals (simp [tbl-ins tbl-has hb])))

(a/theorem deb-ok-sources-ins [cs :- (List CompRow), ts :- (List TaskRow), xs :- (List SourceRow),
                               rs :- (List ResRow), r :- SourceRow, e :- EdgeRow]
  (= (deb-ok cs ts (tbl-ins r xs) rs e) (Bool.or (deb-ok cs ts xs rs e) (Nat.beq (source-id r) (:debtor e))))
  (cases hb (Nat.beq (source-id r) (:debtor e)))
  (all_goals (simp [deb-ok tbl-has-ins hb])))

(a/theorem source-ins-edges-ref-ok [w :- World, r :- SourceRow]
  (=> (= (edges-ref-ok w) true) (= (edges-ref-ok (source-ins w r)) true))
  (intro h)
  (have hpq (forall [e :- EdgeRow]
              (=> (= (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w) e) true)
                  (= (edge-ok (:comps w) (:tasks w) (tbl-ins r (:sources w)) (:acts w) (:res w) e) true))))
  (intros e he)
  (simp only [edge-ok Bool.and_eq_true] at he)
  (simp only [edge-ok Bool.and_eq_true deb-ok-sources-ins Bool.or_eq_true])
  (exact (And.intro (And.left he) (Or.inl (And.right he))))
  (simp only [edges-ref-ok source-ins set-sources edges-ref-ok-in])
  (exact (tbl-all-mono EdgeRow (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w))
           (edge-ok (:comps w) (:tasks w) (tbl-ins r (:sources w)) (:acts w) (:res w)) hpq (:edges w) h)))

;; ---- resources as wait debtors (Z#6): id-preserving updates, insertion, deletion of an
;; unreferenced resource

(a/theorem edge-ok-res-upd [cs :- (List CompRow), ts :- (List TaskRow), xs :- (List SourceRow),
                            as :- (List ActRow), rs :- (List ResRow), y :- Nat, f :- (=> ResRow ResRow),
                            hf :- (forall [r :- ResRow] (= (resource-id (f r)) (resource-id r))), e :- EdgeRow]
  (= (edge-ok cs ts xs as (tbl-upd resource-id y f rs) e) (edge-ok cs ts xs as rs e))
  (simp only [edge-ok cred-ok deb-ok (tbl-has-upd ResRow resource-id y (:debtor e) f hf rs)]))

(a/theorem resource-upd-edges-ref-ok [w :- World, x :- Nat, f :- (=> ResRow ResRow),
                                      hf :- (forall [r :- ResRow] (= (resource-id (f r)) (resource-id r)))]
  (= (edges-ref-ok (resource-upd w x f)) (edges-ref-ok w))
  (simp only [edges-ref-ok resource-upd set-res edges-ref-ok-in])
  (exact (tbl-all-congr EdgeRow (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (tbl-upd resource-id x f (:res w)))
           (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w))
           (edge-ok-res-upd (:comps w) (:tasks w) (:sources w) (:acts w) (:res w) x f hf) (:edges w))))

(a/theorem deb-ok-res-ins [cs :- (List CompRow), ts :- (List TaskRow), xs :- (List SourceRow),
                           rs :- (List ResRow), r :- ResRow, e :- EdgeRow]
  (=> (= (deb-ok cs ts xs rs e) true) (= (deb-ok cs ts xs (tbl-ins r rs) e) true))
  (intro h)
  (have hm (=> (= (tbl-has resource-id (:debtor e) rs) true) (= (tbl-has resource-id (:debtor e) (tbl-ins r rs)) true)))
  (intro hh) (simp [tbl-has-ins hh])
  (simp only [deb-ok Bool.or_eq_true Bool.and_eq_true] at h)
  (simp only [deb-ok Bool.or_eq_true Bool.and_eq_true])
  (cases h)
  (rename_i h1) (exact (Or.inl h1))
  (rename_i h1) (cases h1)
  (rename_i h2) (exact (Or.inr (Or.inl h2)))
  (rename_i h2) (cases h2)
  (rename_i h3) (exact (Or.inr (Or.inr (Or.inl h3))))
  (rename_i h3) (exact (Or.inr (Or.inr (Or.inr (And.intro (And.left h3) (hm (And.right h3))))))))

(a/theorem resource-ins-edges-ref-ok [w :- World, r :- ResRow]
  (=> (= (edges-ref-ok w) true) (= (edges-ref-ok (resource-ins w r)) true))
  (intro h)
  (have hpq (forall [e :- EdgeRow]
              (=> (= (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w) e) true)
                  (= (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (tbl-ins r (:res w)) e) true))))
  (intros e he)
  (simp only [edge-ok Bool.and_eq_true] at he)
  (simp only [edge-ok Bool.and_eq_true])
  (exact (And.intro (And.left he) (deb-ok-res-ins (:comps w) (:tasks w) (:sources w) (:res w) r e (And.right he))))
  (simp only [edges-ref-ok resource-ins set-res edges-ref-ok-in])
  (exact (tbl-all-mono EdgeRow (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w))
           (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (tbl-ins r (:res w))) hpq (:edges w) h)))

;; no edge has z as its debtor (the Z#6 acknowledgement precondition)
(a/defn no-debtor [z :- Nat, e :- EdgeRow] Bool (Bool.not (Nat.beq (:debtor e) z)))

(a/theorem edge-ok-res-del [cs :- (List CompRow), ts :- (List TaskRow), xs :- (List SourceRow),
                            as :- (List ActRow), rs :- (List ResRow), z :- Nat, e :- EdgeRow]
  (=> (= (no-debtor z e) true) (= (edge-ok cs ts xs as (tbl-del resource-id z rs) e) (edge-ok cs ts xs as rs e)))
  (intro hc)
  (simp only [no-debtor] at hc)
  (have hne (= (Nat.beq z (:debtor e)) false))
  (rw [(beq-comm z (:debtor e))]) (exact (bnot-true _ hc))
  (simp only [edge-ok cred-ok deb-ok (tbl-has-del-ne ResRow resource-id z (:debtor e) rs hne)]))

(a/theorem resource-del-edges-ref-ok [w :- World, z :- Nat]
  (=> (= (tbl-all (no-debtor z) (:edges w)) true) (= (edges-ref-ok w) true)
      (= (edges-ref-ok (resource-del w z)) true))
  (intros hu h)
  (have hpq (forall [r :- EdgeRow]
              (=> (= (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w) r) true)
                  (= (no-debtor z r) true)
                  (= (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (tbl-del resource-id z (:res w)) r) true))))
  (intros r h1 h2)
  (rw [(edge-ok-res-del (:comps w) (:tasks w) (:sources w) (:acts w) (:res w) z r h2)])
  (exact h1)
  (simp only [edges-ref-ok resource-del set-res edges-ref-ok-in])
  (exact (tbl-all-mono2 EdgeRow (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w)) (no-debtor z)
           (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (tbl-del resource-id z (:res w))) hpq (:edges w) h hu)))

;; ---- remove-edge keeps ids-ok

(a/theorem remove-edge-ids-ok [w :- World, x :- Nat]
  (=> (= (ids-ok w) true) (= (ids-ok (remove-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x)) (case' [some e]) (case' [none])
  (simp only [remove-edge hf]) (exact h)
  (cases hm (:marked e))
  (simp only [remove-edge hf hm]) (exact (edge-del-ids-ok w x h))
  (simp only [remove-edge hf hm (comp-upd-ids-ok (edge-del w x) (:creditor e) comp-dec-pending comp-dec-pending-id)])
  (exact (edge-del-ids-ok w x h)))

;; ---- drop-cred-edges: remove every edge whose creditor is a, and zero a's pending
;; (a is an activation in every use, so no computation has that id; zeroing keeps the edit
;; exact without that fact).

(a/defn cred-ne [a :- Nat, e :- EdgeRow] Bool (Bool.not (Nat.beq (:creditor e) a)))

(a/theorem bnot-false [b :- Bool] (=> (= (Bool.not b) false) (= b true))
  (cases b) (all_goals (simp)))

(a/defn drop-cred-edges [w :- World, a :- Nat] World
  (comp-upd (set-edges w (tbl-filter (cred-ne a) (:edges w))) a (comp-set-pending 0)))

(a/theorem marked-in-filter-ne [c :- Nat, a :- Nat, es :- (List EdgeRow)]
  (=> (= (Nat.beq a c) false) (= (marked-in c (tbl-filter (cred-ne a) es)) (marked-in c es)))
  (intro hne)
  (induction es)
  (case' [cons h t ih])
  (case' [nil])
  (simp [marked-in tbl-filter tbl-count])
  (simp only [marked-in] at ih)
  (simp only [marked-in])
  (cases hk (cred-ne a h))
  (have hc (= (:creditor h) a))
  (simp only [cred-ne] at hk)
  (exact (Nat.eq_of_beq_eq_true (bnot-false _ hk)))
  (simp only [tbl-filter hk tbl-count-cons marks hc hne Bool.false_and b2n ih])
  (simp only [tbl-filter hk tbl-count-cons ih]))

(a/theorem marked-in-filter-eq [a :- Nat, es :- (List EdgeRow)]
  (= (marked-in a (tbl-filter (cred-ne a) es)) 0)
  (induction es)
  (case' [cons h t ih])
  (case' [nil])
  (simp [marked-in tbl-filter tbl-count])
  (simp only [marked-in] at ih)
  (simp only [marked-in])
  (cases hk (cred-ne a h))
  (simp only [tbl-filter hk]) (exact ih)
  (have hc (= (Nat.beq (:creditor h) a) false))
  (simp only [cred-ne] at hk) (exact (bnot-true _ hk))
  (simp only [tbl-filter hk tbl-count-cons marks hc Bool.false_and b2n ih]))

(a/theorem drop-cred-edges-edges [w :- World, a :- Nat]
  (= (:edges (drop-cred-edges w a)) (tbl-filter (cred-ne a) (:edges w)))
  (rfl))

(a/theorem comp-set-pending-id [n :- Nat, r :- CompRow] (= (comp-id (comp-set-pending n r)) (comp-id r)) (rfl))

(a/theorem drop-cred-pending-exact [w :- World, a :- Nat]
  (=> (= (pending-exact w) true) (= (pending-exact (drop-cred-edges w a)) true))
  (intro hpe)
  (have hin (forall [r :- CompRow]
              (=> (= (comp-exact (:edges w) r) true) (= (Nat.beq (comp-id r) a) true)
                  (= (comp-exact (tbl-filter (cred-ne a) (:edges w)) (comp-set-pending 0 r)) true))))
  (intros r hp hid)
  (have hid2 (= (:id r) a)) (exact (Nat.eq_of_beq_eq_true hid))
  (simp only [comp-exact comp-set-pending hid2 (marked-in-filter-eq a (:edges w))])
  (simp)
  (have hout (forall [r :- CompRow]
               (=> (= (comp-exact (:edges w) r) true) (= (Nat.beq (comp-id r) a) false)
                   (= (comp-exact (tbl-filter (cred-ne a) (:edges w)) r) true))))
  (intros r hp hid)
  (simp only [comp-id] at hid)
  (simp only [comp-exact (marked-in-filter-ne (:id r) a (:edges w) (Eq.trans (beq-comm a (:id r)) hid))])
  (exact hp)
  (exact (tbl-all-upd CompRow comp-id a (comp-set-pending 0) (comp-exact (:edges w))
           (comp-exact (tbl-filter (cred-ne a) (:edges w))) hin hout (:comps w) hpe)))

(a/theorem drop-cred-edges-ref-ok [w :- World, a :- Nat]
  (=> (= (edges-ref-ok w) true) (= (edges-ref-ok (drop-cred-edges w a)) true))
  (intro h)
  (simp only [drop-cred-edges (comp-upd-edges-ref-ok (set-edges w (tbl-filter (cred-ne a) (:edges w))) a
                                (comp-set-pending 0) (comp-set-pending-id 0))])
  (simp only [edges-ref-ok set-edges edges-ref-ok-in])
  (simp only [edges-ref-ok edges-ref-ok-in] at h)
  (exact (tbl-all-filter EdgeRow (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w)) (cred-ne a) (:edges w) h)))

(a/theorem drop-cred-ids-ok [w :- World, a :- Nat]
  (=> (= (ids-ok w) true) (= (ids-ok (drop-cred-edges w a)) true))
  (intro h)
  (simp only [drop-cred-edges (comp-upd-ids-ok (set-edges w (tbl-filter (cred-ne a) (:edges w))) a
                                (comp-set-pending 0) (comp-set-pending-id 0))])
  (exact (edge-filter-ids-ok w (cred-ne a) h)))

;; ---- act-del when no edge names the activation as creditor

(a/theorem edge-ok-act-del [cs :- (List CompRow), ts :- (List TaskRow), xs :- (List SourceRow),
                            as :- (List ActRow), rs :- (List ResRow), a :- Nat, e :- EdgeRow]
  (=> (= (cred-ne a e) true) (= (edge-ok cs ts xs (tbl-del act-id a as) rs e) (edge-ok cs ts xs as rs e)))
  (intro hc)
  (simp only [cred-ne] at hc)
  (have hne (= (Nat.beq a (:creditor e)) false))
  (rw [(beq-comm a (:creditor e))]) (exact (bnot-true _ hc))
  (simp only [edge-ok cred-ok (tbl-has-del-ne ActRow act-id a (:creditor e) as hne)]))

(a/theorem act-del-edges-ref-ok [w :- World, a :- Nat]
  (=> (= (tbl-all (cred-ne a) (:edges w)) true) (= (edges-ref-ok w) true) (= (edges-ref-ok (act-del w a)) true))
  (intros hu h)
  (have hpq (forall [r :- EdgeRow]
              (=> (= (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w) r) true)
                  (= (cred-ne a r) true)
                  (= (edge-ok (:comps w) (:tasks w) (:sources w) (tbl-del act-id a (:acts w)) (:res w) r) true))))
  (intros r h1 h2)
  (rw [(edge-ok-act-del (:comps w) (:tasks w) (:sources w) (:acts w) (:res w) a r h2)])
  (exact h1)
  (simp only [edges-ref-ok act-del set-acts edges-ref-ok-in])
  (exact (tbl-all-mono2 EdgeRow (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w)) (cred-ne a)
           (edge-ok (:comps w) (:tasks w) (:sources w) (tbl-del act-id a (:acts w)) (:res w)) hpq (:edges w) h hu)))

;; ---------------------------------------------------------------------------
;; inv-sample, one lemma per primitive edit

(a/theorem inv-parts [w :- World]
  (=> (= (inv-sample w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (simp only [inv-sample Bool.and_eq_true] at h) (exact h))

(a/theorem inv-intro [w :- World]
  (=> (= (pending-exact w) true) (= (edges-ref-ok w) true) (= (ids-ok w) true) (= (inv-sample w) true))
  (intros h1 h2 h3) (simp only [inv-sample Bool.and_eq_true]) (exact (And.intro h1 (And.intro h2 h3))))

(defmacro ^:private definv-frame-upd
  "inv-<p>-upd for tables whose pending-exact and edges-ref-ok frames are rfl lemmas."
  [& specs]
  `(do
     ~@(for [[prefix row] (partition 2 specs)
             :let [idf (symbol (str prefix "-id")) upd (symbol (str prefix "-upd"))]]
         `(a/theorem ~(symbol (str "inv-" prefix "-upd"))
            [~'w :- ~'World, ~'x :- ~'Nat, ~'f :- (~'=> ~row ~row),
             ~'hf :- (~'forall [~'r :- ~row] (~'= (~idf (~'f ~'r)) (~idf ~'r)))]
            (~'=> (~'= (~'inv-sample ~'w) true) (~'= (~'inv-sample (~upd ~'w ~'x ~'f)) true))
            (~'intro ~'h)
            (~'simp ~'only [~'inv-sample ~(symbol (str "pending-exact-" prefix "-upd"))
                            ~(symbol (str "edges-ref-ok-" prefix "-upd"))
                            (~(symbol (str prefix "-upd-ids-ok")) ~'w ~'x ~'f ~'hf)])
            (~'simp ~'only [~'inv-sample] ~'at ~'h)
            (~'exact ~'h)))))

(definv-frame-upd run RunRow scope ScopeRow pub PubRow)

(defmacro ^:private definv-ref-upd
  "inv-<p>-upd for tables edges-ref-ok reads by id (sources, tasks, acts)."
  [& specs]
  `(do
     ~@(for [[prefix row] (partition 2 specs)
             :let [idf (symbol (str prefix "-id")) upd (symbol (str prefix "-upd"))]]
         `(a/theorem ~(symbol (str "inv-" prefix "-upd"))
            [~'w :- ~'World, ~'x :- ~'Nat, ~'f :- (~'=> ~row ~row),
             ~'hf :- (~'forall [~'r :- ~row] (~'= (~idf (~'f ~'r)) (~idf ~'r)))]
            (~'=> (~'= (~'inv-sample ~'w) true) (~'= (~'inv-sample (~upd ~'w ~'x ~'f)) true))
            (~'intro ~'h)
            (~'simp ~'only [~'inv-sample ~(symbol (str "pending-exact-" prefix "-upd"))
                            (~(symbol (str prefix "-upd-edges-ref-ok")) ~'w ~'x ~'f ~'hf)
                            (~(symbol (str prefix "-upd-ids-ok")) ~'w ~'x ~'f ~'hf)])
            (~'simp ~'only [~'inv-sample] ~'at ~'h)
            (~'exact ~'h)))))

(definv-ref-upd source SourceRow task TaskRow act ActRow resource ResRow)

(a/theorem inv-comp-upd [w :- World, x :- Nat, f :- (=> CompRow CompRow),
                         hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                         hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c)))]
  (=> (= (inv-sample w) true) (= (inv-sample (comp-upd w x f)) true))
  (intro h)
  (have hs (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (exact (inv-parts w h))
  (exact (inv-intro (comp-upd w x f) (pending-exact-comp-upd w x f hid hp (And.left hs))
           (Eq.trans (comp-upd-edges-ref-ok w x f hid) (And.left (And.right hs)))
           (Eq.trans (comp-upd-ids-ok w x f hid) (And.right (And.right hs))))))

(a/theorem edge-ok-row-congr [cs :- (List CompRow), ts :- (List TaskRow), xs :- (List SourceRow),
                              as :- (List ActRow), rs :- (List ResRow), e1 :- EdgeRow, e2 :- EdgeRow]
  (=> (= (:kind e1) (:kind e2)) (= (:creditor e1) (:creditor e2)) (= (:debtor e1) (:debtor e2))
      (= (edge-ok cs ts xs as rs e1) (edge-ok cs ts xs as rs e2)))
  (intros h1 h2 h3) (simp only [edge-ok cred-ok host-cred deb-ok h1 h2 h3]))

;; edge updates that keep id, kind, creditor, debtor and marked
(a/theorem inv-edge-upd [w :- World, x :- Nat, f :- (=> EdgeRow EdgeRow),
                         hid :- (forall [e :- EdgeRow] (= (edge-id (f e)) (edge-id e))),
                         hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                         hc :- (forall [e :- EdgeRow] (= (:creditor (f e)) (:creditor e))),
                         hd :- (forall [e :- EdgeRow] (= (:debtor (f e)) (:debtor e))),
                         hm :- (forall [e :- EdgeRow] (= (:marked (f e)) (:marked e)))]
  (=> (= (inv-sample w) true) (= (inv-sample (edge-upd w x f)) true))
  (intro h)
  (have hs (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (exact (inv-parts w h))
  (have hin (forall [r :- EdgeRow]
              (=> (= (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w) r) true) (= (Nat.beq (edge-id r) x) true)
                  (= (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w) (f r)) true))))
  (intros r h1 h2)
  (rw [(edge-ok-row-congr (:comps w) (:tasks w) (:sources w) (:acts w) (:res w) (f r) r (hk r) (hc r) (hd r))])
  (exact h1)
  (have hout (forall [r :- EdgeRow]
               (=> (= (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w) r) true) (= (Nat.beq (edge-id r) x) false)
                   (= (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w) r) true))))
  (intros r h1 h2) (exact h1)
  (have hr (= (edges-ref-ok (edge-upd w x f)) true))
  (simp only [edges-ref-ok edge-upd set-edges edges-ref-ok-in])
  (have h2 (= (edges-ref-ok-in (:comps w) (:tasks w) (:sources w) (:acts w) (:res w) (:edges w)) true))
  (exact (And.left (And.right hs)))
  (simp only [edges-ref-ok-in] at h2)
  (exact (tbl-all-upd EdgeRow edge-id x f (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w))
           (edge-ok (:comps w) (:tasks w) (:sources w) (:acts w) (:res w)) hin hout (:edges w) h2))
  (exact (inv-intro (edge-upd w x f) (pending-exact-edge-upd w x f hc hm (And.left hs)) hr
           (Eq.trans (edge-upd-ids-ok w x f hid) (And.right (And.right hs))))))

(a/theorem inv-cleanup-upd [w :- World, x :- Nat, f :- (=> CleanupRow CleanupRow)]
  (=> (= (inv-sample w) true) (= (inv-sample (cleanup-upd w x f)) true))
  (intro h) (simp only [inv-sample pending-exact-cleanup-upd edges-ref-ok-cleanup-upd ids-ok-cleanup-upd])
  (simp only [inv-sample] at h) (exact h))

(a/theorem inv-cleanup-del [w :- World, x :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (cleanup-del w x)) true))
  (intro h) (simp only [inv-sample pending-exact-cleanup-del edges-ref-ok-cleanup-del ids-ok-cleanup-del])
  (simp only [inv-sample] at h) (exact h))

(a/theorem inv-set-pins [w :- World, v :- (List Nat)]
  (=> (= (inv-sample w) true) (= (inv-sample (set-pins w v)) true))
  (intro h) (simp only [inv-sample pending-exact-set-pins edges-ref-ok-set-pins ids-ok-set-pins])
  (simp only [inv-sample] at h) (exact h))

(a/theorem inv-run-del [w :- World, x :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (run-del w x)) true))
  (intro h)
  (have hs (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (exact (inv-parts w h))
  (exact (inv-intro (run-del w x) (Eq.trans (pending-exact-run-del w x) (And.left hs))
           (Eq.trans (edges-ref-ok-run-del w x) (And.left (And.right hs)))
           (run-del-ids-ok w x (And.right (And.right hs))))))

(a/theorem inv-resource-del [w :- World, x :- Nat]
  (=> (= (tbl-all (no-debtor x) (:edges w)) true) (= (inv-sample w) true) (= (inv-sample (resource-del w x)) true))
  (intros hu h)
  (have hs (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (exact (inv-parts w h))
  (exact (inv-intro (resource-del w x) (Eq.trans (pending-exact-resource-del w x) (And.left hs))
           (resource-del-edges-ref-ok w x hu (And.left (And.right hs)))
           (resource-del-ids-ok w x (And.right (And.right hs))))))

(a/theorem inv-source-ins-fresh [w :- World, r :- SourceRow]
  (=> (= (source-id r) (:next-id w)) (= (inv-sample w) true) (= (inv-sample (bump (source-ins w r))) true))
  (intros hr h)
  (have hs (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (exact (inv-parts w h))
  (exact (inv-intro (bump (source-ins w r))
           (Eq.trans (pending-exact-bump (source-ins w r)) (Eq.trans (pending-exact-source-ins w r) (And.left hs)))
           (Eq.trans (edges-ref-ok-bump (source-ins w r)) (source-ins-edges-ref-ok w r (And.left (And.right hs))))
           (source-ins-fresh-ids-ok w r hr (And.right (And.right hs))))))

(a/theorem inv-resource-ins-fresh [w :- World, r :- ResRow]
  (=> (= (resource-id r) (:next-id w)) (= (inv-sample w) true) (= (inv-sample (bump (resource-ins w r))) true))
  (intros hr h)
  (have hs (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (exact (inv-parts w h))
  (exact (inv-intro (bump (resource-ins w r))
           (Eq.trans (pending-exact-bump (resource-ins w r)) (Eq.trans (pending-exact-resource-ins w r) (And.left hs)))
           (Eq.trans (edges-ref-ok-bump (resource-ins w r)) (resource-ins-edges-ref-ok w r (And.left (And.right hs))))
           (resource-ins-fresh-ids-ok w r hr (And.right (And.right hs))))))

(a/theorem inv-remove-edge [w :- World, x :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (remove-edge w x)) true))
  (intro h)
  (have hs (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (exact (inv-parts w h))
  (exact (inv-intro (remove-edge w x)
           (remove-edge-pending-exact w x (ids-ok-edges w (And.right (And.right hs))) (And.left hs))
           (remove-edge-edges-ref-ok w x (And.left (And.right hs)))
           (remove-edge-ids-ok w x (And.right (And.right hs))))))

(a/theorem inv-drop-cred [w :- World, a :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (drop-cred-edges w a)) true))
  (intro h)
  (have hs (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (exact (inv-parts w h))
  (exact (inv-intro (drop-cred-edges w a) (drop-cred-pending-exact w a (And.left hs))
           (drop-cred-edges-ref-ok w a (And.left (And.right hs)))
           (drop-cred-ids-ok w a (And.right (And.right hs))))))

;; removing an activation together with every edge it is the creditor of
(a/defn drop-act [w :- World, a :- Nat] World (act-del (drop-cred-edges w a) a))

(a/theorem inv-drop-act [w :- World, a :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (drop-act w a)) true))
  (intro h)
  (have hs (And (= (pending-exact (drop-cred-edges w a)) true)
                (And (= (edges-ref-ok (drop-cred-edges w a)) true) (= (ids-ok (drop-cred-edges w a)) true))))
  (exact (inv-parts (drop-cred-edges w a) (inv-drop-cred w a h)))
  (have hu (= (tbl-all (cred-ne a) (:edges (drop-cred-edges w a))) true))
  (rw [drop-cred-edges-edges]) (exact (tbl-all-filter-self EdgeRow (cred-ne a) (:edges w)))
  (exact (inv-intro (drop-act w a)
           (Eq.trans (pending-exact-act-del (drop-cred-edges w a) a) (And.left hs))
           (act-del-edges-ref-ok (drop-cred-edges w a) a hu (And.left (And.right hs)))
           (act-del-ids-ok (drop-cred-edges w a) a (And.right (And.right hs))))))

;; ---- folds of an edit over a list of ids

(a/defn nat-fold [f :- (=> World Nat World), w :- World, xs :- (List Nat)] World
  (match xs [nil w] [(cons h t) (nat-fold f (f w h) t)]))

(a/theorem nat-fold-inv [f :- (=> World Nat World),
                         hf :- (forall [w :- World, x :- Nat] (=> (= (inv-sample w) true) (= (inv-sample (f w x)) true))),
                         xs :- (List Nat)]
  (forall [w :- World] (=> (= (inv-sample w) true) (= (inv-sample (nat-fold f w xs)) true)))
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (intros w hw) (simp only [nat-fold]) (exact hw)
  (intros w hw) (simp only [nat-fold]) (exact (ih (f w h) (hf w h hw))))

(a/theorem tbl-find-has [A :- Type, idf :- (=> A Nat), x :- Nat, e :- A, xs :- (List A)]
  (=> (= (tbl-find idf x xs) (Option.some A e)) (= (tbl-has idf x xs) true))
  (induction xs)
  (case' [cons h t ih])
  (case' [nil])
  (intro hf) (simp [tbl-find] at hf)
  (intro hf)
  (cases hx (Nat.beq (idf h) x))
  (all_goals (simp_all [tbl-find tbl-has])))
