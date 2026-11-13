(ns spindel.v2.step
  "Raw transitions of spindel engine v2 (spec v1.5.1 §5.1): the effect of each modelled
  host/slice operation BEFORE Rule R, and the Item type. `dispatch : World -> Item -> Outcome`
  here is the raw part for T1, T2, T7-T9, T15 (shallow T13), T18-T20; it refuses the items
  added for the engine (and `arm`, Z#55: T17's park is engine's). The model's step is spindel.v2.engine/world-step = Rule R (rule.clj)
  of engine's `raw`, which routes EVERY item (with T8, T13, T15 replaced by their full forms).

  Items: the payload order of every constructor (the engine emits exactly this order; the
  runtime form is [tag field ...], tag = the constructor index). `st` = the acting run's
  stamp (= run id), `fresh` = the FIRST id the item allocates (refused unless = next-id;
  multi-row items allocate consecutively in the listed order), `tag val` = a result
  (none 0 / ok 1 / err 2), `k` = an opaque continuation, `ds`/`mine` = lists of ids.
    tag item                                   transition   allocates (in order)
     0  create-source st kind v fresh          T1 in a run  source
     1  create-source-top scope kind v fresh   T1 top level source
     2  write x v                              T2           -
     3  track st x k fresh                     T7           dep edge (none on a task run, or when
                                                            the site's edge is reused)
     4  observe d cb fresh                     T8           observe edge, then the reactivation
                                                            edges of a valid idle d (engine)
     5  unobserve e                            T8           -
     6  fire e tag val                         T9           -
     7  resource-ack z                         T15 (+T13)   -
     8  arm st kind k fresh                    T17 + T6     resource, then its `one` activation (cont k),
                                                            then the activation's wait edge on the
                                                            resource (Z#55: ONE body effect; kind
                                                            timer 0 | offload 2; the run parks;
                                                            effect-index advances once; spindel.v2.engine)
     9  resource-fire z tag val                T18 (+T9)    -
    10  handle-drop x                          T19          -
    11  pin x                                  T20          -
    12  unpin x                                T20          -
    13  create-comp st c inputs body           T3 in a run  the computation when c is absent (c
                                                            must then be next-id); inputs = a
                                                            list of interned Nats
    14  create-comp-top scope c inputs body    T3 top level same
    15  spawn st body fresh inputs             T4 in a run  task, run, run scope; nothing when fresh
                                                            names a task of the computation's
                                                            basis/adoption basis (re-spawn, §5.2;
                                                            inputs must equal the task's)
    16  spawn-top scope body fresh inputs      T4 top level task, run, run scope
    17  start c fresh                          T5           run, run scope
    18  await st ds mode k fresh mine          T6           activation (always, Z#28), then the
                                                            reactivation edges of valid idle
                                                            debtors (in a computation), then one
                                                            member edge per distinct debtor in
                                                            debtor-list order (none when reused)
    19  dispatch-comp c fresh                  T11          run, run scope
    20  complete st tag val                    T12          -
    21  schedule r                             D0 scheduling choice (slice to run r)  -
    22  host-await d fresh                     T22          host-wait edge
    23  host-unawait e                         T22          -
    24  handle-new x                           Z#29         -
    25  deliver x v                            §4.3 deferred (fires, T10)  -
    26  post x v                               §4.3 mailbox -
    27  take st x k fresh                      §4.3 take (mailbox) / acquire (semaphore)
                                                            activation, then its wait edge (both
                                                            always allocated, also when consumed
                                                            at once)
    28  release x                              §4.3 semaphore  -
    29  finalize r                             B3/B8 cleanup slice of r's head finalizer (scheduling) -
    30  cancel r                               T14 host cancel of a task's run r  -
    31  release-world                          T21          -
    32  open-scope st s                        T16 open (with-scope)  explicit scope s (= fresh)
    33  close-scope s                          T16 close (with-scope end)  -
    34  detach k s                             Q10 detach task k to open scope s  -
    35  finally-enter st                       B3 a finally region opens (body)  -
    36  finally-exit st                        B3 the innermost region closes (body, or the
                                                            cleanup slice of an unwinding run;
                                                            committed at the block's start) -
    37  slice-exit r                           Z#35 the slice of a cancelled run returns (after
                                                            its last finally block; T13) -
  Indices 0-24 are unchanged; later items get the next indices.

  Outcome {world accepted}. Refusal = (input world, false). Validity tokens (§2, V#5) have
  one check per kind: `run-tok-ok` (run with that stamp exists, slice, mode normal or
  unwinding with a head finalizer), `fire-tok-ok` (edge exists and is armed), `res-tok-ok`
  (resource row exists); `item-token-ok` picks the item's (true for host operations without
  a token). An invalid token is a refusal: world unchanged (L4).

  Body effects (T1, T7, T17) advance the run's `effect-index` by one; `at` of what they
  create is the index before the effect. Z#55: `arm` (T17 and its park, spindel.v2.engine) is one
  effect; `arm-raw` adds the resource only, the park advances the index.

  Theorems (kernel-checked when the namespace loads):
    tN-inv     inv-sample w -> inv-sample (:world (tN w ...)), for every transition, with no
               further precondition (the transitions check what they need: e.g. T7 checks that
               the creditor computation and the debtor source exist, so `edge-ok-in` holds)
    tN-refuse  (:accepted o) = false -> (:world o) = w
    tN-l4      token check false -> (:world o) = w   (t1, t7, t9, t15, t18; t17 in engine)
    dispatch-inv / dispatch-refuse / dispatch-l4   the same for `dispatch`, by `cases item`
    run-items-inv, run-items-from-empty   inv-sample holds along any item sequence
  and per helper: inv-fire-edge (T9 on any edge), inv-write-raw, inv-retire-check, ...
  The primitive edit lemmas they compose are in spindel.v2.edits (appended section).

  Modelled semantics and readings (see also the report's ambiguity list):
  - T1: kinds signal..semaphore (rerun sources are implicit, not created by T1); a new
    source has version 0, open, handles 1 (the creator's handle); inside a computation run
    the owner is the computation and the creation is recorded in its basis with at.
  - T2: version += 1, state := v (deltas are not modelled, A#1); every dep and observe edge
    on x fires (T9); the creditors of the ARMED dep edges on x (Z#59: a fired edge starts no
    marking) and every computation reachable from them through reversed dep edges (any phase)
    are computed with spindel.v2.reach's worklist (`dirty-run`), and every dep edge whose
    debtor is among them is marked (`mark-edge`, exact pending).
  - T7: only signals and cells are trackable. Inside a computation: a new dep edge at
    at = effect-index with baseline = current (state, version); cont = k unless the run
    holds finalizers or resources (§2); an adoption baseline for (at, x) is consumed. Inside
    a task: snapshot read, no edge (only effect-index advances). Otherwise refuse.
  - T7 re-reading a site: when the computation already has a dep edge at (at, x) (a prefix
    edge kept by T11, or E re-armed with its old baseline on restart, Z#22) it is reused
    (re-armed, baseline and seen advance to the current state); no fresh id is used then.
  - Edge `seen : Nat?` (Z#15) is the pair (has-seen, seen); none = (false, 0). Dep edges set
    it to the version they consumed (track read, delivery), which is the validity version of
    Z#24.
  - T8: observe registers an observe edge (creditor host = 0, phase armed) after `edge-ok-in`
    (the debtor exists). Z#15: when d is a source or a live computation it is delivered at
    once (seen := version); otherwise seen = none. On an idle computation step's T8 refuses
    (`validate-idle-todo`); the model's step uses spindel.v2.engine's T8, which validates.
    unobserve removes an observe edge.
  - T9 (`fire-edge`): only an armed edge fires. dep: if it is a member of an activation of
    the creditor's current run and the debtor is available (I13: a computation only while
    live) it is delivered (re-armed with the debtor's current baseline, seen := its version,
    slot filled), otherwise an invalidation (edge fired, creditor epoch += 1, once per fired
    edge). wait: fired, and its activation's slot is filled if the activation's run is
    current. observe: delivered when seen = none or seen < version (seen := version); stays
    armed (persistent). Slots (Z#7): `members` is a list of (edge, slot index); a fire fills
    every index listed with the edge and removes those entries (`act-fill`); `one`/`all`
    resume when remaining = 0, `any` on the first fill (`resume`: the activation and every
    edge it is the creditor of are removed, i.e. its wait members including the losers; run
    act := active). The `any` loser tasks are cancelled by spindel.v2.engine (it needs the
    cascade). TODO: savepoint edges (`fire-savepoint-todo`, layer 2).
  - T13 (`retire-check`): retirable = act done, no slice, no finalizers, no resources;
    retire removes the run row and cleanup[R] and closes the run scope. STUB: T16 is only
    `close-scope-shallow` (open := false) here. The model's step (spindel.v2.rule/world-step)
    replaces T15 by `rule/t15-full`, whose T13 is the full Z#18 retirement with the T16
    cascade (`rule/retire-full`); `dispatch` keeps this shallow version for its lemmas.
  - T15 (Z#6): refused while an edge has Z as debtor (`ack-tok-ok`); removes Z from res,
    from its run's resources and its cleanup rows, then T13.
  - T17 (Z#55, the item lives in spindel.v2.engine): `arm-raw` adds a new armed resource owned by
    the run with at = effect-index to the run's resources (no index step); engine's `arm-park` then
    parks the run on a `one` activation over the resource's wait edge (take-park), advancing the
    index once. `dispatch` refuses the item (it needs engine's park).
  - T18: only an armed resource fires (once); phase := fired; every armed wait edge whose
    debtor is z fires (T9) (Z#6: edges-ref-ok admits a resource debtor for wait edges).
  - T19: handles -= 1 on the computation/task/source/publication with that id (searched
    in that order); handles = 0 or no row refuses.
  - T20 (Z#16): `pins` is a multiset (the count of x is its multiplicity, `pin-count`; a row
    is a root while it occurs, `pin-count-pos`); pin adds one occurrence of a computation or
    source id; unpin removes one and is refused at count 0."
  (:require [ansatz.core :as a]
            [spindel.v2.state :refer :all]
            [spindel.v2.edits :refer :all]
            [spindel.v2.reach :refer [reach-run reach-mem]]))

(a/load-init!)

;; ===========================================================================
;; Part A. Outcome, items, validity tokens
;; ===========================================================================

(a/structure Outcome [] (world World) (accepted Bool))
(a/defn accept [w :- World] Outcome (Outcome.mk w true))
(a/defn refuse [w :- World] Outcome (Outcome.mk w false))

;; One constructor per modelled host/slice operation. `st` = run stamp (body-effect token),
;; `fresh` = the id the engine allocated (must be next-id), `tag`/`val` = a RunResult.
(a/inductive Item []
  (create-source [st Nat] [kind Nat] [v Nat] [fresh Nat])          ; T1 inside a run
  (create-source-top [scope Nat] [kind Nat] [v Nat] [fresh Nat])   ; T1 at top level
  (write [x Nat] [v Nat])                                          ; T2 host write
  (track [st Nat] [x Nat] [k Nat] [fresh Nat])                     ; T7
  (observe [d Nat] [cb Nat] [fresh Nat])                           ; T8
  (unobserve [e Nat])                                              ; T8
  (fire [e Nat] [tag Nat] [val Nat])                               ; T9 (cross-world / external fire)
  (resource-ack [z Nat])                                           ; T15 (+ T13)
  (arm [st Nat] [kind Nat] [k Nat] [fresh Nat])                    ; T17 + park on its wait edge (Z#55)
  (resource-fire [z Nat] [tag Nat] [val Nat])                      ; T18 (+ T9)
  (handle-drop [x Nat])                                            ; T19
  (pin [x Nat])                                                    ; T20
  (unpin [x Nat])                                                  ; T20
  (create-comp [st Nat] [c Nat] [inputs (List Nat)] [body Nat])    ; T3 inside a run
  (create-comp-top [scope Nat] [c Nat] [inputs (List Nat)] [body Nat]) ; T3 at top level
  (spawn [st Nat] [body Nat] [fresh Nat] [inputs (List Nat)])      ; T4 inside a run (§5.2 re-spawn)
  (spawn-top [scope Nat] [body Nat] [fresh Nat] [inputs (List Nat)]) ; T4 at top level
  (start [c Nat] [fresh Nat])                                      ; T5
  (await [st Nat] [ds (List Nat)] [mode Nat] [k Nat] [fresh Nat] [mine (List Nat)]) ; T6
  (dispatch-comp [c Nat] [fresh Nat])                              ; T11
  (complete [st Nat] [tag Nat] [val Nat])                          ; T12
  (schedule [r Nat])                                               ; scheduling choice (D0)
  (host-await [d Nat] [fresh Nat])                                 ; T22
  (host-unawait [e Nat])                                           ; T22
  (handle-new [x Nat])                                             ; Z#29
  (deliver [x Nat] [v Nat])                                        ; §4.3 deferred (T10)
  (post [x Nat] [v Nat])                                           ; §4.3 mailbox
  (take [st Nat] [x Nat] [k Nat] [fresh Nat])                      ; §4.3 mailbox take / semaphore acquire
  (release [x Nat])                                                ; §4.3 semaphore
  (finalize [r Nat])                                               ; B3/B8 cleanup slice (scheduling)
  (cancel [r Nat])                                                 ; T14 from the host on a task's run
  (release-world)                                                  ; T21
  (open-scope [st Nat] [s Nat])                                    ; T16 open (with-scope)
  (close-scope [s Nat])                                            ; T16 close (with-scope end)
  (detach [k Nat] [s Nat])                                         ; Q10 detach (§5.2)
  (finally-enter [st Nat])                                         ; a finally region opens (B3)
  (finally-exit [st Nat])                                          ; a finally region closes (B3)
  (slice-exit [r Nat]))                                            ; a cancelled run's slice returns (Z#35)

;; ---- validity tokens (§2, V#5): one check per token kind

(a/defn run-stamp [r :- RunRow] Nat (:stamp r))
(a/defn fins-empty [fs :- (List Finalizer)] Bool (match fs [nil true] [(cons h t) false]))
(a/defn nats-empty [xs :- (List Nat)] Bool (match xs [nil true] [(cons h t) false]))

;; R.slice, and mode normal, or mode unwinding with a head finalizer (the slice that runs is
;; then the head finalizer's: the model does not track which code a slice executes).
(a/defn run-valid [r :- RunRow] Bool
  (Bool.and (:slice r)
            (Bool.or (Nat.beq (:mode r) mode-normal)
                     (Bool.and (Nat.beq (:mode r) mode-unwinding) (Bool.not (fins-empty (:finalizers r)))))))

;; body effect / completion token: the run with that stamp, if the token is valid
(a/defn tok-run [w :- World, st :- Nat] (Option RunRow)
  (match (tbl-find run-stamp st (:runs w))
    [none (Option.none RunRow)]
    [(some r) (if (run-valid r) (Option.some RunRow r) (Option.none RunRow))]))
(a/defn run-tok-ok [w :- World, st :- Nat] Bool
  (match (tok-run w st) [none false] [(some r) true]))
;; fire token: the edge exists and is armed
(a/defn fire-tok-ok [w :- World, x :- Nat] Bool
  (match (edge-find w x) [none false] [(some e) (Nat.beq (:phase e) ph-armed)]))
;; resource fire / acknowledgement token: the resource row exists
(a/defn res-tok-ok [w :- World, z :- Nat] Bool (resource-has w z))

(a/theorem run-tok-none [w :- World, st :- Nat]
  (=> (= (run-tok-ok w st) false) (= (tok-run w st) (Option.none RunRow)))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (rfl)
  (simp [run-tok-ok ht] at h))

;; ===========================================================================
;; Part B. Row updates (each keeps the row id; the lemmas say which fields it keeps)
;; ===========================================================================

(a/defn run-tick [r :- RunRow] RunRow
  (RunRow.mk (:id r) (:of r) (:stamp r) (:epoch r) (:scope r) (:act r) (:mode r) (:slice r)
             (+ (:effect-index r) 1) (:finalizers r) (:resources r)))
;; Z#55: arming adds the resource; the effect's index step is the park's (engine `arm-park`)
(a/defn run-arm [z :- Nat, r :- RunRow] RunRow
  (RunRow.mk (:id r) (:of r) (:stamp r) (:epoch r) (:scope r) (:act r) (:mode r) (:slice r)
             (:effect-index r) (:finalizers r) (List.cons Nat z (:resources r))))
(a/defn run-unres [z :- Nat, r :- RunRow] RunRow
  (RunRow.mk (:id r) (:of r) (:stamp r) (:epoch r) (:scope r) (:act r) (:mode r) (:slice r)
             (:effect-index r) (:finalizers r) (nat-del z (:resources r))))
(a/defn run-set-act [n :- Nat, r :- RunRow] RunRow
  (RunRow.mk (:id r) (:of r) (:stamp r) (:epoch r) (:scope r) n (:mode r) (:slice r)
             (:effect-index r) (:finalizers r) (:resources r)))
;; Z#50: a fill wakes its run only when the run is parked (a done run stays done)
(a/defn wake-act [n :- Nat] Nat (if (Nat.beq n act-parked) act-active n))
(a/defn run-wake [r :- RunRow] RunRow
  (RunRow.mk (:id r) (:of r) (:stamp r) (:epoch r) (:scope r) (wake-act (:act r)) (:mode r) (:slice r)
             (:effect-index r) (:finalizers r) (:resources r)))

(a/defn comp-add-basis [b :- Created, c :- CompRow] CompRow
  (CompRow.mk (:id c) (:owner c) (:inputs c) (:body c) (:run c) (:epoch c) (:done-epoch c)
              (:pending c) (:rank c) (:version c) (:result c) (:idle c) (:validity c)
              (List.cons Created b (:basis c)) (:adopt-basis c) (:adopt-baselines c) (:handles c)))
(a/defn adopt-other [site :- Nat, x :- Nat, b :- AdoptBase] Bool
  (Bool.not (Bool.and (Nat.beq (:site b) site) (Nat.beq (:source b) x))))
(a/defn comp-consume-adopt [site :- Nat, x :- Nat, c :- CompRow] CompRow
  (CompRow.mk (:id c) (:owner c) (:inputs c) (:body c) (:run c) (:epoch c) (:done-epoch c)
              (:pending c) (:rank c) (:version c) (:result c) (:idle c) (:validity c)
              (:basis c) (:adopt-basis c) (tbl-filter (adopt-other site x) (:adopt-baselines c)) (:handles c)))
(a/defn comp-inc-epoch [c :- CompRow] CompRow
  (CompRow.mk (:id c) (:owner c) (:inputs c) (:body c) (:run c) (+ (:epoch c) 1) (:done-epoch c)
              (:pending c) (:rank c) (:version c) (:result c) (:idle c) (:validity c)
              (:basis c) (:adopt-basis c) (:adopt-baselines c) (:handles c)))
(a/defn comp-dec-handles [c :- CompRow] CompRow
  (CompRow.mk (:id c) (:owner c) (:inputs c) (:body c) (:run c) (:epoch c) (:done-epoch c)
              (:pending c) (:rank c) (:version c) (:result c) (:idle c) (:validity c)
              (:basis c) (:adopt-basis c) (:adopt-baselines c) (- (:handles c) 1)))

(a/defn source-write [v :- Nat, s :- SourceRow] SourceRow
  (SourceRow.mk (:id s) (:owner s) (:kind s) v (+ (:version s) 1) (:open s) (:handles s) (:queue s)))
(a/defn source-dec-handles [s :- SourceRow] SourceRow
  (SourceRow.mk (:id s) (:owner s) (:kind s) (:state s) (:version s) (:open s) (- (:handles s) 1) (:queue s)))
(a/defn task-dec-handles [t :- TaskRow] TaskRow
  (TaskRow.mk (:id t) (:owner t) (:run t) (:result t) (- (:handles t) 1) (:inputs t)))
(a/defn pub-dec-handles [p :- PubRow] PubRow
  (PubRow.mk (:id p) (:edge p) (:basis p) (- (:handles p) 1)))
(a/defn scope-close [s :- ScopeRow] ScopeRow (ScopeRow.mk (:id s) (:parent s) (:kind s) false))
(a/defn res-set-phase [p :- Nat, z :- ResRow] ResRow
  (ResRow.mk (:id z) (:owner z) (:kind z) (:at z) p))
(a/defn cleanup-drop [z :- Nat, c :- CleanupRow] CleanupRow (CleanupRow.mk (:run c) (nat-del z (:rows c))))

;; Z#15: `seen : Nat?` is the pair (has-seen, seen); none = (false, 0)
(a/defn edge-set-phase [p :- Nat, e :- EdgeRow] EdgeRow
  (EdgeRow.mk (:id e) (:kind e) (:creditor e) (:debtor e) (:cont e) (:at e) p
              (:marked e) (:has-seen e) (:seen e) (:has-base e) (:base-value e) (:base-version e)))
;; a delivered dep edge returns to armed with its new baseline (§4.2); it consumed version
;; `ver`, which is its `seen` (Z#24)
(a/defn edge-rearm [v :- Nat, ver :- Nat, e :- EdgeRow] EdgeRow
  (EdgeRow.mk (:id e) (:kind e) (:creditor e) (:debtor e) (:cont e) (:at e) ph-armed
              (:marked e) true ver true v ver))
(a/defn edge-set-seen [n :- Nat, e :- EdgeRow] EdgeRow
  (EdgeRow.mk (:id e) (:kind e) (:creditor e) (:debtor e) (:cont e) (:at e) (:phase e)
              (:marked e) true n (:has-base e) (:base-value e) (:base-version e)))

;; ---- activation slots (Z#7): a fire of edge x fills every slot index listed with x
(a/defn slot-set [k :- Nat, i :- Nat, v :- RunResult, xs :- (List RunResult)] (List RunResult)
  (match xs [nil (List.nil RunResult)]
         [(cons h t) (List.cons RunResult (if (Nat.beq k i) v h) (slot-set (+ k 1) i v t))]))
(a/defn slots-fill [x :- Nat, v :- RunResult, ms :- (List Member), sl :- (List RunResult)] (List RunResult)
  (match ms [nil sl]
         [(cons h t) (slots-fill x v t (if (Nat.beq (:edge h) x) (slot-set 0 (:idx h) v sl) sl))]))
(a/defn mem-is [x :- Nat, m :- Member] Bool (Nat.beq (:edge m) x))
(a/defn mem-other [x :- Nat, m :- Member] Bool (Bool.not (Nat.beq (:edge m) x)))
;; fill: the slots of x's entries get v, the entries go (unfilled members only, X#4), remaining
;; drops by the number of entries
(a/defn act-fill [x :- Nat, v :- RunResult, a :- ActRow] ActRow
  (ActRow.mk (:id a) (:run a) (:mode a) (tbl-filter (mem-other x) (:members a))
             (slots-fill x v (:members a) (:slots a))
             (- (:remaining a) (tbl-count (mem-is x) (:members a))) (:cont a) (:spawned a)))

(defmacro ^:private deffield-lemmas
  "For each [fn [params] row idf? & kept-fields]: <fn>-<field> lemmas (= (field (fn params r)) (field r))."
  [& specs]
  `(do
     ~@(for [[f params row & fields] specs
             field fields
             :let [nm (symbol (str f "-" (if (keyword? field) (name field) field)))
                   app (concat [f] (map first (partition 3 params)) ['r])
                   proj (fn [x] (if (keyword? field) (list field x) (list field x)))]]
         `(a/theorem ~nm [~@params ~'r :- ~row] (~'= ~(proj app) ~(proj 'r)) (~'rfl)))))

(deffield-lemmas
  [run-tick [] RunRow run-id]
  [run-arm [z :- Nat] RunRow run-id]
  [run-unres [z :- Nat] RunRow run-id]
  [run-set-act [n :- Nat] RunRow run-id]
  [run-wake [] RunRow run-id]
  [comp-add-basis [b :- Created] CompRow comp-id :pending]
  [comp-consume-adopt [site :- Nat, x :- Nat] CompRow comp-id :pending]
  [comp-inc-epoch [] CompRow comp-id :pending]
  [comp-dec-handles [] CompRow comp-id :pending]
  [source-write [v :- Nat] SourceRow source-id]
  [source-dec-handles [] SourceRow source-id]
  [task-dec-handles [] TaskRow task-id]
  [pub-dec-handles [] PubRow pub-id]
  [scope-close [] ScopeRow scope-id]
  [res-set-phase [p :- Nat] ResRow resource-id]
  [edge-set-phase [p :- Nat] EdgeRow edge-id :kind :creditor :debtor :marked]
  [edge-rearm [v :- Nat, ver :- Nat] EdgeRow edge-id :kind :creditor :debtor :marked]
  [edge-set-seen [n :- Nat] EdgeRow edge-id :kind :creditor :debtor :marked]
  [act-fill [x :- Nat, v :- RunResult] ActRow act-id])

;; ===========================================================================
;; Part C. T9 fire (and the resume of a `one` activation)
;; ===========================================================================

;; the current state and version of a debtor (source or computation; 0 otherwise)
(a/defn deb-value [w :- World, d :- Nat] Nat
  (match (source-find w d)
    [none (match (comp-find w d) [none 0] [(some c) (:val (:result c))])]
    [(some s) (:state s)]))
(a/defn deb-version [w :- World, d :- Nat] Nat
  (match (source-find w d)
    [none (match (comp-find w d) [none 0] [(some c) (:version c)])]
    [(some s) (:version s)]))

;; run rid exists and is current: a task run, or a computation run with R.epoch = C.epoch
(a/defn run-current [w :- World, rid :- Nat] Bool
  (match (run-find w rid)
    [none false]
    [(some r) (match (comp-find w (:of r)) [none true] [(some c) (Nat.beq (:epoch r) (:epoch c))])]))
;; ... and is a run of computation c
(a/defn run-current-of [w :- World, rid :- Nat, c :- Nat] Bool
  (match (run-find w rid)
    [none false]
    [(some r) (Bool.and (Nat.beq (:of r) c) (run-current w rid))]))

;; the activation that has edge x among its unfilled members
(a/defn act-with-member [x :- Nat, as :- (List ActRow)] (Option ActRow)
  (match as [nil (Option.none ActRow)]
         [(cons h t) (if (mem-has x (:members h)) (Option.some ActRow h) (act-with-member x t))]))

;; derived status (§2): live = not idle, done-epoch = epoch, pending = 0
(a/defn comp-live [c :- CompRow] Bool
  (Bool.and (Bool.not (:idle c)) (Bool.and (Nat.beq (:done-epoch c) (:epoch c)) (Nat.beq (:pending c) 0))))
;; I13: a slot is filled from a computation only while it is live; other debtors always
(a/defn deb-avail [w :- World, d :- Nat] Bool
  (match (comp-find w d) [none true] [(some c) (comp-live c)]))
;; Z#53: the model's error code for ::closed, the reserved Nat 2 (::cancelled = 1, rule.clj
;; `cancelled-code`; the engine's opaque values start at 3)
(a/defn closed-code [] Nat 2)
;; a source without a value (Z#53): a mailbox, a semaphore, an undelivered deferred
(a/defn src-valueless [s :- SourceRow] Bool
  (Bool.or (Nat.beq (:kind s) sk-mailbox)
   (Bool.or (Nat.beq (:kind s) sk-semaphore)
            (Bool.and (Nat.beq (:kind s) sk-deferred) (Nat.beq (:version s) 0)))))
;; what a source delivers: its state as ok; once closed (final), a source without a value gives
;; err ::closed (Z#53)
(a/defn src-result [s :- SourceRow] RunResult
  (if (Bool.and (Bool.not (:open s)) (src-valueless s))
      (RunResult.mk res-err closed-code)
      (RunResult.mk res-ok (:state s))))
;; the result a debtor delivers: a computation's or task's result, a source's `src-result`
(a/defn deb-result [w :- World, d :- Nat] RunResult
  (match (comp-find w d)
    [none (match (task-find w d)
            [none (match (source-find w d)
                    [none (RunResult.mk res-ok (deb-value w d))]
                    [(some s) (src-result s)])]
            [(some t) (:result t)])]
    [(some c) (:result c)]))

;; Resume (T6): the activation is removed with its wait (and savepoint) members, i.e. every
;; edge it is the creditor of; dep members are the computation's and stay. The run becomes
;; active if it is parked (Z#50: otherwise it stays as it is, a done run is never revived);
;; its next slice is a scheduling choice, not modelled here.
(a/defn resume [w :- World, a :- ActRow] World
  (run-upd (drop-act w (:id a)) (:run a) run-wake))

;; Fill the slots of edge x in activation a with v (T6, T9, Z#7). `one`/`all` resume when
;; remaining reaches 0, `any` on its first fill; otherwise the activation is updated.
(a/defn act-ready [a :- ActRow] Bool (Bool.or (Nat.beq (:mode a) am-any) (Nat.beq (:remaining a) 0)))
(a/defn fill-slot [w :- World, a :- ActRow, x :- Nat, v :- RunResult] World
  (if (act-ready (act-fill x v a)) (resume w a) (act-upd w (:id a) (act-fill x v))))

;; §4.5.3: a dep fire that is not a delivery is an invalidation: epoch step, edge stays fired
(a/defn invalidate [w :- World, e :- EdgeRow] World
  (comp-upd (edge-upd w (:id e) (edge-set-phase ph-fired)) (:creditor e) comp-inc-epoch))

;; D1 final debtors: a closed source, a delivered deferred (version > 0, §4.3), a completed
;; task; never a computation (Z#32)
(a/defn src-delivered [s :- SourceRow] Bool (Bool.and (Nat.beq (:kind s) sk-deferred) (Nat.blt 0 (:version s))))
(a/defn deb-final [w :- World, d :- Nat] Bool
  (match (source-find w d)
    [none (match (task-find w d)
            [none false]
            [(some t) (Bool.not (Nat.beq (:tag (:result t)) res-none))])]
    [(some s) (Bool.or (Bool.not (:open s)) (src-delivered s))]))

;; §4.2: a delivered dep edge returns to armed with its new baseline, unless its debtor is
;; final; then it is removed (Z#39)
(a/defn dep-consumed [w :- World, e :- EdgeRow] World
  (if (deb-final w (:debtor e))
      (remove-edge w (:id e))
      (edge-upd w (:id e) (edge-rearm (deb-value w (:debtor e)) (deb-version w (:debtor e))))))
(a/defn deliver-dep [w :- World, e :- EdgeRow, a :- ActRow] World
  (fill-slot (dep-consumed w e) a (:id e)
             (deb-result w (:debtor e))))
(a/defn fire-dep [w :- World, e :- EdgeRow] World
  (match (act-with-member (:id e) (:acts w))
    [none (invalidate w e)]
    [(some a) (if (Bool.and (run-current-of w (:run a) (:creditor e)) (deb-avail w (:debtor e)))
                  (deliver-dep w e a)
                  (invalidate w e))]))

;; a host wait (creditor 0, T22) is delivered to the host and consumed
(a/defn fire-wait-act [res :- RunResult, w :- World, e :- EdgeRow] World
  (match (act-find w (:creditor e))
    [none (edge-upd w (:id e) (edge-set-phase ph-fired))]
    [(some a) (if (run-current w (:run a))
                  (fill-slot (edge-upd w (:id e) (edge-set-phase ph-fired)) a (:id e) res)
                  (edge-upd w (:id e) (edge-set-phase ph-fired)))]))
(a/defn fire-wait [res :- RunResult, w :- World, e :- EdgeRow] World
  (if (Nat.beq (:creditor e) 0) (remove-edge w (:id e)) (fire-wait-act res w e)))

;; observe edges are persistent: a fire delivers (value, version) to the host and sets
;; seen := version; a version <= seen is a no-op (§4.2); seen = none delivers (Z#15)
(a/defn observe-new [e :- EdgeRow, ver :- Nat] Bool (Bool.or (Bool.not (:has-seen e)) (Nat.blt (:seen e) ver)))
(a/defn fire-observe [w :- World, e :- EdgeRow] World
  (if (observe-new e (deb-version w (:debtor e)))
      (edge-upd w (:id e) (edge-set-seen (deb-version w (:debtor e))))
      w))

;; TODO(savepoint, layer 2): fill, resume once, remove the edge, publication keeps its basis.
(a/defn fire-savepoint-todo [w :- World, e :- EdgeRow] World w)

;; T9 fire(E, result). The result is delivered to the resumed continuation (opaque: A#1), so
;; it does not enter the state; it is kept as a parameter for the oracle's trace.
(a/defn fire-edge [res :- RunResult, w :- World, x :- Nat] World
  (match (edge-find w x)
    [none w]
    [(some e) (if (Nat.beq (:phase e) ph-armed)
                  (if (Nat.beq (:kind e) ek-dep) (fire-dep w e)
                      (if (Nat.beq (:kind e) ek-wait) (fire-wait res w e)
                          (if (Nat.beq (:kind e) ek-observe) (fire-observe w e)
                              (fire-savepoint-todo w e))))
                  w)]))

;; ---- fire preserves inv-sample

(a/theorem inv-resume [w :- World, a :- ActRow]
  (=> (= (inv-sample w) true) (= (inv-sample (resume w a)) true))
  (intro h)
  (exact (inv-run-upd (drop-act w (:id a)) (:run a) run-wake run-wake-run-id
           (inv-drop-act w (:id a) h))))

(a/theorem inv-fill-slot [w :- World, a :- ActRow, x :- Nat, v :- RunResult]
  (=> (= (inv-sample w) true) (= (inv-sample (fill-slot w a x v)) true))
  (intro h)
  (cases hm (act-ready (act-fill x v a)))
  (simp only [fill-slot hm]) (exact (inv-act-upd w (:id a) (act-fill x v) (act-fill-act-id x v) h))
  (simp only [fill-slot hm]) (exact (inv-resume w a h)))

(a/theorem inv-edge-set-phase [w :- World, x :- Nat, p :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (edge-upd w x (edge-set-phase p))) true))
  (exact (inv-edge-upd w x (edge-set-phase p) (edge-set-phase-edge-id p) (edge-set-phase-kind p)
           (edge-set-phase-creditor p) (edge-set-phase-debtor p) (edge-set-phase-marked p))))

(a/theorem inv-invalidate [w :- World, e :- EdgeRow]
  (=> (= (inv-sample w) true) (= (inv-sample (invalidate w e)) true))
  (intro h)
  (exact (inv-comp-upd (edge-upd w (:id e) (edge-set-phase ph-fired)) (:creditor e) comp-inc-epoch
           comp-inc-epoch-comp-id comp-inc-epoch-pending (inv-edge-set-phase w (:id e) ph-fired h))))

(a/theorem inv-dep-consumed [w :- World, e :- EdgeRow]
  (=> (= (inv-sample w) true) (= (inv-sample (dep-consumed w e)) true))
  (intro h)
  (cases hf (deb-final w (:debtor e)))
  (simp only [dep-consumed hf])
  (exact (inv-edge-upd w (:id e) (edge-rearm (deb-value w (:debtor e)) (deb-version w (:debtor e)))
           (edge-rearm-edge-id _ _) (edge-rearm-kind _ _) (edge-rearm-creditor _ _)
           (edge-rearm-debtor _ _) (edge-rearm-marked _ _) h))
  (simp only [dep-consumed hf]) (exact (inv-remove-edge w (:id e) h)))

;; the edit leaves the activation and run tables alone
(a/theorem dep-consumed-acts [w :- World, e :- EdgeRow] (= (:acts (dep-consumed w e)) (:acts w))
  (cases hf (deb-final w (:debtor e)))
  (simp only [dep-consumed hf edge-upd set-edges])
  (simp only [dep-consumed hf remove-edge])
  (cases ho (edge-find w (:id e))) (case' [some x]) (case' [none])
  (simp only [ho])
  (cases hm (:marked x))
  (all_goals (simp only [ho hm comp-upd edge-del set-comps set-edges])))
(a/theorem dep-consumed-runs [w :- World, e :- EdgeRow] (= (:runs (dep-consumed w e)) (:runs w))
  (cases hf (deb-final w (:debtor e)))
  (simp only [dep-consumed hf edge-upd set-edges])
  (simp only [dep-consumed hf remove-edge])
  (cases ho (edge-find w (:id e))) (case' [some x]) (case' [none])
  (simp only [ho])
  (cases hm (:marked x))
  (all_goals (simp only [ho hm comp-upd edge-del set-comps set-edges])))

(a/theorem inv-fire-dep [w :- World, e :- EdgeRow]
  (=> (= (inv-sample w) true) (= (inv-sample (fire-dep w e)) true))
  (intro h)
  (cases ha (act-with-member (:id e) (:acts w))) (case' [some a]) (case' [none])
  (simp only [fire-dep ha]) (exact (inv-invalidate w e h))
  (cases hc (Bool.and (run-current-of w (:run a) (:creditor e)) (deb-avail w (:debtor e))))
  (simp only [fire-dep ha hc]) (exact (inv-invalidate w e h))
  (simp only [fire-dep ha hc deliver-dep])
  (exact (inv-fill-slot _ a _ _ (inv-dep-consumed w e h))))

(a/theorem inv-fire-wait-act [res :- RunResult, w :- World, e :- EdgeRow]
  (=> (= (inv-sample w) true) (= (inv-sample (fire-wait-act res w e)) true))
  (intro h)
  (cases ha (act-find w (:creditor e))) (case' [some a]) (case' [none])
  (simp only [fire-wait-act ha]) (exact (inv-edge-set-phase w (:id e) ph-fired h))
  (cases hc (run-current w (:run a)))
  (simp only [fire-wait-act ha hc]) (exact (inv-edge-set-phase w (:id e) ph-fired h))
  (simp only [fire-wait-act ha hc]) (exact (inv-fill-slot _ a _ _ (inv-edge-set-phase w (:id e) ph-fired h))))

(a/theorem inv-fire-wait [res :- RunResult, w :- World, e :- EdgeRow]
  (=> (= (inv-sample w) true) (= (inv-sample (fire-wait res w e)) true))
  (intro h)
  (cases hc (Nat.beq (:creditor e) 0))
  (simp only [fire-wait hc]) (exact (inv-fire-wait-act res w e h))
  (simp only [fire-wait hc]) (exact (inv-remove-edge w (:id e) h)))

(a/theorem inv-fire-observe [w :- World, e :- EdgeRow]
  (=> (= (inv-sample w) true) (= (inv-sample (fire-observe w e)) true))
  (intro h)
  (cases hs (observe-new e (deb-version w (:debtor e))))
  (simp only [fire-observe hs]) (exact h)
  (simp only [fire-observe hs])
  (exact (inv-edge-upd w (:id e) (edge-set-seen (deb-version w (:debtor e)))
           (edge-set-seen-edge-id _) (edge-set-seen-kind _) (edge-set-seen-creditor _)
           (edge-set-seen-debtor _) (edge-set-seen-marked _) h)))

(a/theorem inv-fire-edge [res :- RunResult, w :- World, x :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (fire-edge res w x)) true))
  (intro h)
  (cases hf (edge-find w x)) (case' [some e]) (case' [none])
  (simp only [fire-edge hf]) (exact h)
  (cases hp (Nat.beq (:phase e) ph-armed))
  (simp only [fire-edge hf hp]) (exact h)
  (cases hk1 (Nat.beq (:kind e) ek-dep))
  (cases hk2 (Nat.beq (:kind e) ek-wait))
  (cases hk3 (Nat.beq (:kind e) ek-observe))
  (simp only [fire-edge hf hp hk1 hk2 hk3 fire-savepoint-todo]) (exact h)
  (simp only [fire-edge hf hp hk1 hk2 hk3]) (exact (inv-fire-observe w e h))
  (simp only [fire-edge hf hp hk1 hk2]) (exact (inv-fire-wait res w e h))
  (simp only [fire-edge hf hp hk1]) (exact (inv-fire-dep w e h)))

;; ===========================================================================
;; Part D. Transitions
;; ===========================================================================

;; ---- T1 create-source

(a/defn src-kind-ok [kind :- Nat] Bool (Nat.ble kind sk-semaphore))
(a/defn in-comp [w :- World, r :- RunRow] Bool (comp-has w (:of r)))
;; §5.2: inside a computation run the owner is the computation, inside a task run its run scope
(a/defn src-owner [w :- World, r :- RunRow] Nat (if (in-comp w r) (:of r) (:scope r)))
(a/defn new-source [id :- Nat, owner :- Nat, kind :- Nat, v :- Nat] SourceRow
  (SourceRow.mk id owner kind v 0 true 1 (List.nil Nat)))
;; §5.2: a computation run records the creation in its basis, with at = effect-index
(a/defn record-basis [w :- World, r :- RunRow, id :- Nat] World
  (if (in-comp w r) (comp-upd w (:of r) (comp-add-basis (Created.mk id (:effect-index r)))) w))

(a/defn create-source-raw [w :- World, r :- RunRow, kind :- Nat, v :- Nat] World
  (run-upd (record-basis (bump (source-ins w (new-source (:next-id w) (src-owner w r) kind v))) r (:next-id w))
           (:id r) run-tick))

(a/defn t1-create-source [w :- World, st :- Nat, kind :- Nat, v :- Nat, fresh :- Nat] Outcome
  (match (tok-run w st)
    [none (refuse w)]
    [(some r) (if (Bool.and (Nat.beq fresh (:next-id w)) (src-kind-ok kind))
                  (accept (create-source-raw w r kind v))
                  (refuse w))]))

(a/defn scope-open-at [w :- World, s :- Nat] Bool
  (match (scope-find w s) [none false] [(some sc) (:open sc)]))

(a/defn t1-create-source-top [w :- World, scope :- Nat, kind :- Nat, v :- Nat, fresh :- Nat] Outcome
  (if (Bool.and (Bool.and (Nat.beq fresh (:next-id w)) (src-kind-ok kind)) (scope-open-at w scope))
      (accept (bump (source-ins w (new-source (:next-id w) scope kind v))))
      (refuse w)))

(a/theorem inv-record-basis [w :- World, r :- RunRow, id :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (record-basis w r id)) true))
  (intro h)
  (cases hc (in-comp w r))
  (simp only [record-basis hc]) (exact h)
  (simp only [record-basis hc])
  (exact (inv-comp-upd w (:of r) (comp-add-basis (Created.mk id (:effect-index r)))
           (comp-add-basis-comp-id _) (comp-add-basis-pending _) h)))

(a/theorem inv-create-source-raw [w :- World, r :- RunRow, kind :- Nat, v :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (create-source-raw w r kind v)) true))
  (intro h)
  (simp only [create-source-raw])
  (exact (inv-run-upd _ (:id r) run-tick run-tick-run-id
           (inv-record-basis _ r (:next-id w)
             (inv-source-ins-fresh w (new-source (:next-id w) (src-owner w r) kind v) (rfl) h)))))

(a/theorem t1-inv [w :- World, st :- Nat, kind :- Nat, v :- Nat, fresh :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t1-create-source w st kind v fresh))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t1-create-source ht refuse]) (exact h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (src-kind-ok kind)))
  (simp only [t1-create-source ht hg refuse]) (exact h)
  (simp only [t1-create-source ht hg accept]) (exact (inv-create-source-raw w r kind v h)))

(a/theorem t1-refuse [w :- World, st :- Nat, kind :- Nat, v :- Nat, fresh :- Nat]
  (=> (= (:accepted (t1-create-source w st kind v fresh)) false) (= (:world (t1-create-source w st kind v fresh)) w))
  (intro ha)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t1-create-source ht refuse])
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (src-kind-ok kind)))
  (simp only [t1-create-source ht hg refuse])
  (simp [t1-create-source ht hg accept] at ha))

(a/theorem t1-l4 [w :- World, st :- Nat, kind :- Nat, v :- Nat, fresh :- Nat]
  (=> (= (run-tok-ok w st) false) (= (:world (t1-create-source w st kind v fresh)) w))
  (intro hf)
  (simp only [t1-create-source (run-tok-none w st hf) refuse]))

(a/theorem t1-top-inv [w :- World, scope :- Nat, kind :- Nat, v :- Nat, fresh :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t1-create-source-top w scope kind v fresh))) true))
  (intro h)
  (cases hg (Bool.and (Bool.and (Nat.beq fresh (:next-id w)) (src-kind-ok kind)) (scope-open-at w scope)))
  (simp only [t1-create-source-top hg refuse]) (exact h)
  (simp only [t1-create-source-top hg accept])
  (exact (inv-source-ins-fresh w (new-source (:next-id w) scope kind v) (rfl) h)))

(a/theorem t1-top-refuse [w :- World, scope :- Nat, kind :- Nat, v :- Nat, fresh :- Nat]
  (=> (= (:accepted (t1-create-source-top w scope kind v fresh)) false)
      (= (:world (t1-create-source-top w scope kind v fresh)) w))
  (intro ha)
  (cases hg (Bool.and (Bool.and (Nat.beq fresh (:next-id w)) (src-kind-ok kind)) (scope-open-at w scope)))
  (simp only [t1-create-source-top hg refuse])
  (simp [t1-create-source-top hg accept] at ha))

;; ---- T2 write (signals and cells)

(a/defn writable [s :- SourceRow] Bool
  (Bool.and (:open s) (Bool.or (Nat.beq (:kind s) sk-signal) (Nat.beq (:kind s) sk-cell))))

;; ids of the dep and observe edges whose debtor is d (the edges a write to d fires)
(a/defn edges-onto [d :- Nat, es :- (List EdgeRow)] (List Nat)
  (match es [nil (List.nil Nat)]
         [(cons h t) (if (Bool.and (Nat.beq (:debtor h) d)
                                   (Bool.or (Nat.beq (:kind h) ek-dep) (Nat.beq (:kind h) ek-observe)))
                         (List.cons Nat (:id h) (edges-onto d t))
                         (edges-onto d t))]))

;; creditors of the dep edges on d: the reverse dep graph, as a successor function for reach
(a/defn dep-creditors [es :- (List EdgeRow), d :- Nat] (List Nat)
  (match es [nil (List.nil Nat)]
         [(cons h t) (if (Bool.and (Nat.beq (:debtor h) d) (Nat.beq (:kind h) ek-dep))
                         (List.cons Nat (:creditor h) (dep-creditors t d))
                         (dep-creditors t d))]))

(a/defn edge-count [es :- (List EdgeRow)] Nat
  (match es [nil 0] [(cons h t) (+ (edge-count t) 1)]))

;; creditors of the ARMED dep edges on d: the computations a write to d invalidates (Z#59)
(a/defn armed-creditors [es :- (List EdgeRow), d :- Nat] (List Nat)
  (match es [nil (List.nil Nat)]
         [(cons h t) (if (Bool.and (Bool.and (Nat.beq (:debtor h) d) (Nat.beq (:kind h) ek-dep)) (Nat.beq (:phase h) ph-armed))
                         (List.cons Nat (:creditor h) (armed-creditors t d))
                         (armed-creditors t d))]))

;; the computations reachable from `roots` through reversed dep edges (any phase), roots included.
;; Fuel 2|E|+1 >= |roots| + sum |succ v| + 1 (each dep edge is one successor entry, the roots are
;; dep creditors), so the worklist converges; the inv-sample theorems do not depend on it (tests
;; check `converged`).
(a/defn dirty-from [w :- World, roots :- (List Nat)] ReachResult
  (reach-run (+ (* 2 (edge-count (:edges w))) 1) (dep-creditors (:edges w)) roots))
;; §4.5.1 (Z#59): a write to x marks from the computations whose dep edge on x fires (was armed),
;; then follows their dep out-edges in any phase. A fired edge on x starts no marking.
(a/defn dirty-run [w :- World, x :- Nat] ReachResult (dirty-from w (armed-creditors (:edges w) x)))
(a/defn dirty-set [w :- World, x :- Nat] (List Nat) (:visited (dirty-run w x)))
;; every computation reachable from c through reversed dep edges, any phase (T3's mark-from)
(a/defn cone-set [w :- World, c :- Nat] (List Nat) (:visited (dirty-from w (dep-creditors (:edges w) c))))

;; ids of the dep edges whose debtor is in m: the in-edges from computations being marked
(a/defn mark-targets [m :- (List Nat), es :- (List EdgeRow)] (List Nat)
  (match es [nil (List.nil Nat)]
         [(cons h t) (if (Bool.and (Nat.beq (:kind h) ek-dep) (reach-mem (:debtor h) m))
                         (List.cons Nat (:id h) (mark-targets m t))
                         (mark-targets m t))]))

(a/defn write-raw [w :- World, x :- Nat, v :- Nat] World
  (nat-fold mark-edge
            (nat-fold (fire-edge (RunResult.mk res-ok v)) (source-upd w x (source-write v)) (edges-onto x (:edges w)))
            (mark-targets (dirty-set w x) (:edges w))))

(a/defn t2-write [w :- World, x :- Nat, v :- Nat] Outcome
  (match (source-find w x)
    [none (refuse w)]
    [(some s) (if (writable s) (accept (write-raw w x v)) (refuse w))]))

(a/theorem inv-write-raw [w :- World, x :- Nat, v :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (write-raw w x v)) true))
  (intro h)
  (simp only [write-raw])
  (exact (nat-fold-inv mark-edge mark-edge-inv-sample (mark-targets (dirty-set w x) (:edges w)) _
           (nat-fold-inv (fire-edge (RunResult.mk res-ok v)) (inv-fire-edge (RunResult.mk res-ok v))
             (edges-onto x (:edges w)) _
             (inv-source-upd w x (source-write v) (source-write-source-id v) h)))))

(a/theorem t2-inv [w :- World, x :- Nat, v :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t2-write w x v))) true))
  (intro h)
  (cases hs (source-find w x)) (case' [some s]) (case' [none])
  (simp only [t2-write hs refuse]) (exact h)
  (cases hg (writable s))
  (simp only [t2-write hs hg refuse]) (exact h)
  (simp only [t2-write hs hg accept]) (exact (inv-write-raw w x v h)))

(a/theorem t2-refuse [w :- World, x :- Nat, v :- Nat]
  (=> (= (:accepted (t2-write w x v)) false) (= (:world (t2-write w x v)) w))
  (intro ha)
  (cases hs (source-find w x)) (case' [some s]) (case' [none])
  (simp only [t2-write hs refuse])
  (cases hg (writable s))
  (simp only [t2-write hs hg refuse])
  (simp [t2-write hs hg accept] at ha))

;; ---- T7 track

(a/defn trackable [s :- SourceRow] Bool
  (Bool.or (Nat.beq (:kind s) sk-signal) (Nat.beq (:kind s) sk-cell)))
;; §2 re-entrant sites: cont = k only without finalizers and outstanding resources
;; (a track reads one source, like a mode-`one` await)
(a/defn track-cont [r :- RunRow, k :- Nat] Nat
  (if (Bool.and (fins-empty (:finalizers r)) (nats-empty (:resources r))) k cont-restart))
;; §4.4: the baseline is the current state; a first track's delivery is <nil, value, nil>, an
;; adopted site's is <adopted baseline, value>; either way the baseline then is the current state
(a/defn track-edge [r :- RunRow, x :- Nat, s :- SourceRow, k :- Nat] EdgeRow
  (EdgeRow.mk 0 ek-dep (:of r) x (track-cont r k) (:effect-index r) ph-armed false true (:version s)
              true (:state s) (:version s)))
;; re-reading a site whose edge exists (a prefix edge kept by T11, or E re-armed with its old
;; baseline on restart, Z#22): the edge is reused; the baseline advances to the current state
(a/defn edge-reread [c :- Nat, s :- SourceRow, e :- EdgeRow] EdgeRow
  (EdgeRow.mk (:id e) (:kind e) (:creditor e) (:debtor e) c (:at e) ph-armed (:marked e) true (:version s)
              true (:state s) (:version s)))
;; the dep edge of computation c at site `at` on debtor d
(a/defn site-edge-p [c :- Nat, at :- Nat, d :- Nat, e :- EdgeRow] Bool
  (Bool.and (Nat.beq (:kind e) ek-dep)
            (Bool.and (Nat.beq (:creditor e) c) (Bool.and (Nat.beq (:at e) at) (Nat.beq (:debtor e) d)))))
(a/defn site-edge [es :- (List EdgeRow), c :- Nat, at :- Nat, d :- Nat] (Option EdgeRow)
  (match es [nil (Option.none EdgeRow)]
         [(cons h t) (if (site-edge-p c at d h) (Option.some EdgeRow h) (site-edge t c at d))]))

(deffield-lemmas
  [edge-reread [c :- Nat, s :- SourceRow] EdgeRow edge-id :kind :creditor :debtor :marked])
(a/defn opt-some [A :- Type :implicit, o :- (Option A)] Bool (match o [none false] [(some r) true]))

;; Z#48: on a closed (final) source the read delivers once and the edge is consumed in the same
;; commit (as an await on a final debtor, T6/T10); a new edge's id stays allocated
(a/defn track-fin [s :- SourceRow, y :- Nat, w :- World] World (if (:open s) w (remove-edge w y)))
(a/defn track-new [w :- World, r :- RunRow, x :- Nat, s :- SourceRow, k :- Nat] World
  (comp-upd (track-fin s (:next-id w) (insert-edge-fresh w (track-edge r x s k))) (:of r) (comp-consume-adopt (:effect-index r) x)))
(a/defn track-raw [w :- World, r :- RunRow, x :- Nat, s :- SourceRow, k :- Nat] World
  (run-upd (match (site-edge (:edges w) (:of r) (:effect-index r) x)
             [none (track-new w r x s k)]
             [(some e) (comp-upd (track-fin s (:id e) (edge-upd w (:id e) (edge-reread (track-cont r k) s)))
                                 (:of r) (comp-consume-adopt (:effect-index r) x))])
           (:id r) run-tick))

(a/defn t7-track [w :- World, st :- Nat, x :- Nat, k :- Nat, fresh :- Nat] Outcome
  (match (tok-run w st)
    [none (refuse w)]
    [(some r)
     (match (source-find w x)
       [none (refuse w)]
       [(some s)
        (if (trackable s)
            (if (comp-has w (:of r))
                (if (Bool.or (Nat.beq fresh (:next-id w)) (opt-some (site-edge (:edges w) (:of r) (:effect-index r) x)))
                    (accept (track-raw w r x s k)) (refuse w))
                (if (task-has w (:of r)) (accept (run-upd w (:id r) run-tick)) (refuse w)))
            (refuse w))])]))

(a/theorem track-edge-ok [w :- World, r :- RunRow, x :- Nat, s :- SourceRow, k :- Nat]
  (=> (= (comp-has w (:of r)) true) (= (source-find w x) (Option.some SourceRow s))
      (= (edge-ok-in w (track-edge r x s k)) true))
  (intros hc hs)
  (have hx (= (tbl-has source-id x (:sources w)) true))
  (exact (tbl-find-has SourceRow source-id x s (:sources w) hs))
  (simp only [comp-has] at hc)
  (simp [edge-ok-in edge-ok cred-ok deb-ok track-edge hc hx]))

(a/theorem inv-track-fin [s :- SourceRow, y :- Nat, w :- World]
  (=> (= (inv-sample w) true) (= (inv-sample (track-fin s y w)) true))
  (intro h)
  (cases ho (:open s))
  (case [true] (simp only [track-fin ho]) (exact h))
  (case [false] (simp only [track-fin ho]) (exact (inv-remove-edge w y h))))

(a/theorem inv-track-raw [w :- World, r :- RunRow, x :- Nat, s :- SourceRow, k :- Nat]
  (=> (= (comp-has w (:of r)) true) (= (source-find w x) (Option.some SourceRow s))
      (= (inv-sample w) true) (= (inv-sample (track-raw w r x s k)) true))
  (intros hc hs h)
  (have h2 (= (inv-sample (match (site-edge (:edges w) (:of r) (:effect-index r) x)
                             [none (track-new w r x s k)]
                             [(some e) (comp-upd (track-fin s (:id e) (edge-upd w (:id e) (edge-reread (track-cont r k) s)))
                                                 (:of r) (comp-consume-adopt (:effect-index r) x))])) true))
  (cases he (site-edge (:edges w) (:of r) (:effect-index r) x)) (case' [some e]) (case' [none])
  (simp only [track-new])
  (exact (inv-comp-upd _ (:of r) (comp-consume-adopt (:effect-index r) x)
           (comp-consume-adopt-comp-id _ _) (comp-consume-adopt-pending _ _)
           (inv-track-fin s (:next-id w) _ (insert-edge-fresh-inv-sample w (track-edge r x s k) (track-edge-ok w r x s k hc hs) h))))
  (exact (inv-comp-upd _ (:of r) (comp-consume-adopt (:effect-index r) x)
           (comp-consume-adopt-comp-id _ _) (comp-consume-adopt-pending _ _)
           (inv-track-fin s (:id e) _
             (inv-edge-upd w (:id e) (edge-reread (track-cont r k) s) (edge-reread-edge-id _ _) (edge-reread-kind _ _)
               (edge-reread-creditor _ _) (edge-reread-debtor _ _) (edge-reread-marked _ _) h))))
  (simp only [track-raw])
  (exact (inv-run-upd _ (:id r) run-tick run-tick-run-id h2)))

(a/theorem t7-inv [w :- World, st :- Nat, x :- Nat, k :- Nat, fresh :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t7-track w st x k fresh))) true))
  (intro h)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t7-track ht refuse]) (exact h)
  (cases hs (source-find w x)) (case' [some s]) (case' [none])
  (simp only [t7-track ht hs refuse]) (exact h)
  (cases hk (trackable s))
  (simp only [t7-track ht hs hk refuse]) (exact h)
  (cases hc (comp-has w (:of r)))
  (cases hta (task-has w (:of r)))
  (simp only [t7-track ht hs hk hc hta refuse]) (exact h)
  (simp only [t7-track ht hs hk hc hta accept]) (exact (inv-run-upd w (:id r) run-tick run-tick-run-id h))
  (cases hf (Bool.or (Nat.beq fresh (:next-id w)) (opt-some (site-edge (:edges w) (:of r) (:effect-index r) x))))
  (simp only [t7-track ht hs hk hc hf refuse]) (exact h)
  (simp only [t7-track ht hs hk hc hf accept]) (exact (inv-track-raw w r x s k hc hs h)))

(a/theorem t7-refuse [w :- World, st :- Nat, x :- Nat, k :- Nat, fresh :- Nat]
  (=> (= (:accepted (t7-track w st x k fresh)) false) (= (:world (t7-track w st x k fresh)) w))
  (intro ha)
  (cases ht (tok-run w st)) (case' [some r]) (case' [none])
  (simp only [t7-track ht refuse])
  (cases hs (source-find w x)) (case' [some s]) (case' [none])
  (simp only [t7-track ht hs refuse])
  (cases hk (trackable s))
  (simp only [t7-track ht hs hk refuse])
  (cases hc (comp-has w (:of r)))
  (cases hta (task-has w (:of r)))
  (simp only [t7-track ht hs hk hc hta refuse])
  (simp [t7-track ht hs hk hc hta accept] at ha)
  (cases hf (Bool.or (Nat.beq fresh (:next-id w)) (opt-some (site-edge (:edges w) (:of r) (:effect-index r) x))))
  (simp only [t7-track ht hs hk hc hf refuse])
  (simp [t7-track ht hs hk hc hf accept] at ha))

(a/theorem t7-l4 [w :- World, st :- Nat, x :- Nat, k :- Nat, fresh :- Nat]
  (=> (= (run-tok-ok w st) false) (= (:world (t7-track w st x k fresh)) w))
  (intro hf)
  (simp only [t7-track (run-tok-none w st hf) refuse]))

;; ---- T8 observe / unobserve

;; Z#15: registration delivers at once when d is a source or a live computation (seen := its
;; version); otherwise seen = none and the first delivery is the settle (d is demanded by the
;; T5/T11 item that follows, reading in the docstring)
(a/defn deb-ready [w :- World, d :- Nat] Bool
  (Bool.or (source-has w d) (match (comp-find w d) [none false] [(some c) (comp-live c)])))
(a/defn observe-edge [w :- World, d :- Nat, cb :- Nat] EdgeRow
  (EdgeRow.mk 0 ek-observe 0 d cb 0 ph-armed false (deb-ready w d) (if (deb-ready w d) (deb-version w d) 0)
              false 0 0))
(a/defn idle-comp [w :- World, d :- Nat] Bool
  (match (comp-find w d) [none false] [(some c) (:idle c)]))

;; TODO(validation, §3.4 R#3): observing an idle computation must first validate it
;; (reactivate or re-run). Not modelled yet: such an observe refuses (`validate-idle-todo`).
(a/defn validate-idle-todo [w :- World] Outcome (refuse w))

(a/defn t8-observe [w :- World, d :- Nat, cb :- Nat, fresh :- Nat] Outcome
  (if (Bool.and (Nat.beq fresh (:next-id w)) (edge-ok-in w (observe-edge w d cb)))
      (if (idle-comp w d) (validate-idle-todo w) (accept (insert-edge-fresh w (observe-edge w d cb))))
      (refuse w)))

(a/defn t8-unobserve [w :- World, x :- Nat] Outcome
  (match (edge-find w x)
    [none (refuse w)]
    [(some e) (if (Nat.beq (:kind e) ek-observe) (accept (remove-edge w x)) (refuse w))]))

(a/theorem t8-observe-inv [w :- World, d :- Nat, cb :- Nat, fresh :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t8-observe w d cb fresh))) true))
  (intro h)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (edge-ok-in w (observe-edge w d cb))))
  (simp only [t8-observe hg refuse]) (exact h)
  (cases hi (idle-comp w d))
  (simp only [t8-observe hg hi accept])
  (have he (= (edge-ok-in w (observe-edge w d cb)) true))
  (simp only [Bool.and_eq_true] at hg) (exact (And.right hg))
  (exact (insert-edge-fresh-inv-sample w (observe-edge w d cb) he h))
  (simp only [t8-observe hg hi validate-idle-todo refuse]) (exact h))

(a/theorem t8-observe-refuse [w :- World, d :- Nat, cb :- Nat, fresh :- Nat]
  (=> (= (:accepted (t8-observe w d cb fresh)) false) (= (:world (t8-observe w d cb fresh)) w))
  (intro ha)
  (cases hg (Bool.and (Nat.beq fresh (:next-id w)) (edge-ok-in w (observe-edge w d cb))))
  (simp only [t8-observe hg refuse])
  (cases hi (idle-comp w d))
  (simp [t8-observe hg hi accept] at ha)
  (simp only [t8-observe hg hi validate-idle-todo refuse]))

(a/theorem t8-unobserve-inv [w :- World, x :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t8-unobserve w x))) true))
  (intro h)
  (cases hf (edge-find w x)) (case' [some e]) (case' [none])
  (simp only [t8-unobserve hf refuse]) (exact h)
  (cases hk (Nat.beq (:kind e) ek-observe))
  (simp only [t8-unobserve hf hk refuse]) (exact h)
  (simp only [t8-unobserve hf hk accept]) (exact (inv-remove-edge w x h)))

(a/theorem t8-unobserve-refuse [w :- World, x :- Nat]
  (=> (= (:accepted (t8-unobserve w x)) false) (= (:world (t8-unobserve w x)) w))
  (intro ha)
  (cases hf (edge-find w x)) (case' [some e]) (case' [none])
  (simp only [t8-unobserve hf refuse])
  (cases hk (Nat.beq (:kind e) ek-observe))
  (simp only [t8-unobserve hf hk refuse])
  (simp [t8-unobserve hf hk accept] at ha))

;; ---- T9 fire as an item (an external / cross-world fire carrying the edge id)

(a/defn t9-fire [w :- World, x :- Nat, tag :- Nat, v :- Nat] Outcome
  (if (fire-tok-ok w x) (accept (fire-edge (RunResult.mk tag v) w x)) (refuse w)))

(a/theorem t9-inv [w :- World, x :- Nat, tag :- Nat, v :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t9-fire w x tag v))) true))
  (intro h)
  (cases hg (fire-tok-ok w x))
  (simp only [t9-fire hg refuse]) (exact h)
  (simp only [t9-fire hg accept]) (exact (inv-fire-edge (RunResult.mk tag v) w x h)))

(a/theorem t9-refuse [w :- World, x :- Nat, tag :- Nat, v :- Nat]
  (=> (= (:accepted (t9-fire w x tag v)) false) (= (:world (t9-fire w x tag v)) w))
  (intro ha)
  (cases hg (fire-tok-ok w x))
  (simp only [t9-fire hg refuse])
  (simp [t9-fire hg accept] at ha))

(a/theorem t9-l4 [w :- World, x :- Nat, tag :- Nat, v :- Nat]
  (=> (= (fire-tok-ok w x) false) (= (:world (t9-fire w x tag v)) w))
  (intro hg) (simp only [t9-fire hg refuse]))

;; ---- T13 retire? and T15 resource-ack

(a/defn retirable [r :- RunRow] Bool
  (Bool.and (Nat.beq (:act r) act-done)
            (Bool.and (Bool.not (:slice r))
                      (Bool.and (fins-empty (:finalizers r)) (nats-empty (:resources r))))))

;; STUB(T16), superseded in the step by spindel.v2.rule/retire-full (Z#18 order, T16 cascade).
;; Retiring closes the run scope via T16. Here the scope is only marked closed
;; (`close-scope-shallow`). Cancelling the work it owns, closing its explicit child scopes and
;; sources and removing the empty subtree are T16's cancel cascade (next batch). Once the run
;; row and cleanup[R] are gone the scope has no retention reason (a run scope is reachable only
;; from its run), so Rule R cancels what it still owns and removes it.
(a/defn close-scope-shallow [w :- World, s :- Nat] World (scope-upd w s scope-close))

(a/defn retire [w :- World, r :- RunRow] World
  (cleanup-del (run-del (close-scope-shallow w (:scope r)) (:id r)) (:id r)))

;; T13: called on every path that can make the predicate true
(a/defn retire-check [w :- World, rid :- Nat] World
  (match (run-find w rid)
    [none w]
    [(some r) (if (retirable r) (retire w r) w)]))

;; remove Z from res, from its run's resources and from its run's cleanup rows
(a/defn ack-raw [w :- World, z :- Nat, owner :- Nat] World
  (cleanup-upd (run-upd (resource-del w z) owner (run-unres z)) owner (cleanup-drop z)))

;; T15 (Z#6): the acknowledgement token needs the resource row and no edge with Z as debtor
(a/defn ack-tok-ok [w :- World, z :- Nat] Bool
  (Bool.and (resource-has w z) (tbl-all (no-debtor z) (:edges w))))
(a/defn t15-resource-ack [w :- World, z :- Nat] Outcome
  (if (tbl-all (no-debtor z) (:edges w))
      (match (resource-find w z)
        [none (refuse w)]
        [(some zr) (accept (retire-check (ack-raw w z (:owner zr)) (:owner zr)))])
      (refuse w)))

(a/theorem inv-retire [w :- World, r :- RunRow]
  (=> (= (inv-sample w) true) (= (inv-sample (retire w r)) true))
  (intro h)
  (simp only [retire close-scope-shallow])
  (exact (inv-cleanup-del _ (:id r) (inv-run-del _ (:id r)
           (inv-scope-upd w (:scope r) scope-close scope-close-scope-id h)))))

(a/theorem inv-retire-check [w :- World, rid :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (retire-check w rid)) true))
  (intro h)
  (cases hf (run-find w rid)) (case' [some r]) (case' [none])
  (simp only [retire-check hf]) (exact h)
  (cases hr (retirable r))
  (simp only [retire-check hf hr]) (exact h)
  (simp only [retire-check hf hr]) (exact (inv-retire w r h)))

(a/theorem inv-ack-raw [w :- World, z :- Nat, owner :- Nat]
  (=> (= (tbl-all (no-debtor z) (:edges w)) true) (= (inv-sample w) true) (= (inv-sample (ack-raw w z owner)) true))
  (intros hu h)
  (simp only [ack-raw])
  (exact (inv-cleanup-upd _ owner (cleanup-drop z)
           (inv-run-upd _ owner (run-unres z) (run-unres-run-id z) (inv-resource-del w z hu h)))))

(a/theorem t15-inv [w :- World, z :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t15-resource-ack w z))) true))
  (intro h)
  (cases hu (tbl-all (no-debtor z) (:edges w)))
  (simp only [t15-resource-ack hu refuse]) (exact h)
  (cases hf (resource-find w z)) (case' [some zr]) (case' [none])
  (simp only [t15-resource-ack hu hf refuse]) (exact h)
  (simp only [t15-resource-ack hu hf accept])
  (exact (inv-retire-check _ (:owner zr) (inv-ack-raw w z (:owner zr) hu h))))

(a/theorem t15-refuse [w :- World, z :- Nat]
  (=> (= (:accepted (t15-resource-ack w z)) false) (= (:world (t15-resource-ack w z)) w))
  (intro ha)
  (cases hu (tbl-all (no-debtor z) (:edges w)))
  (simp only [t15-resource-ack hu refuse])
  (cases hf (resource-find w z)) (case' [some zr]) (case' [none])
  (simp only [t15-resource-ack hu hf refuse])
  (simp [t15-resource-ack hu hf accept] at ha))

(a/theorem res-tok-none [w :- World, z :- Nat]
  (=> (= (res-tok-ok w z) false) (= (resource-find w z) (Option.none ResRow)))
  (intro hg)
  (cases hf (resource-find w z)) (case' [some zr]) (case' [none])
  (rfl)
  (have hh (= (tbl-has resource-id z (:res w)) true))
  (exact (tbl-find-has ResRow resource-id z zr (:res w) hf))
  (simp [res-tok-ok resource-has hh] at hg))

(a/theorem t15-l4 [w :- World, z :- Nat]
  (=> (= (ack-tok-ok w z) false) (= (:world (t15-resource-ack w z)) w))
  (intro hg)
  (cases hu (tbl-all (no-debtor z) (:edges w)))
  (simp only [t15-resource-ack hu refuse])
  (have hr (= (res-tok-ok w z) false)) (simp only [ack-tok-ok hu Bool.and_true] at hg) (exact hg)
  (simp only [t15-resource-ack hu (res-tok-none w z hr) refuse]))

;; ---- T17 arm (Z#55): the resource part; the item (resource, activation, wait edge, park) is
;; spindel.v2.engine's `t17-arm`

(a/defn res-kind-ok [kind :- Nat] Bool (Nat.ble kind rk-native))
(a/defn arm-raw [w :- World, r :- RunRow, kind :- Nat] World
  (run-upd (bump (resource-ins w (ResRow.mk (:next-id w) (:id r) kind (:effect-index r) rp-armed)))
           (:id r) (run-arm (:next-id w))))

(a/theorem inv-arm-raw [w :- World, r :- RunRow, kind :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (arm-raw w r kind)) true))
  (intro h)
  (simp only [arm-raw])
  (exact (inv-run-upd _ (:id r) (run-arm (:next-id w)) (run-arm-run-id _)
           (inv-resource-ins-fresh w (ResRow.mk (:next-id w) (:id r) kind (:effect-index r) rp-armed) (rfl) h))))

;; an updated row is in the updated table
(a/theorem tbl-upd-mem-self [A :- Type, idf :- (=> A Nat), f :- (=> A A), r :- A, xs :- (List A)]
  (=> (List.Mem r xs) (List.Mem (f r) (tbl-upd idf (idf r) f xs)))
  (intro hm)
  (induction hm)
  (case' [tail b t hm2 ih])
  (case' [head t])
  (simp only [tbl-upd Nat.beq_refl])
  (exact (List.Mem.head _))
  (cases hx (Nat.beq (idf b) (idf r)))
  (simp only [tbl-upd hx]) (exact (List.Mem.tail _ ih))
  (simp only [tbl-upd hx]) (exact (List.Mem.tail _ ih)))

;; the armed run row is a row of the armed world
(a/theorem arm-raw-mem [w :- World, r :- RunRow, kind :- Nat]
  (=> (List.Mem r (:runs w)) (List.Mem (run-arm (:next-id w) r) (:runs (arm-raw w r kind))))
  (intro hm)
  (exact (tbl-upd-mem-self RunRow run-id (run-arm (:next-id w)) r (:runs w) hm)))

;; ---- T18 resource-fire

;; ids of the wait edges parked on resource z
(a/defn waits-on [z :- Nat, es :- (List EdgeRow)] (List Nat)
  (match es [nil (List.nil Nat)]
         [(cons h t) (if (Bool.and (Nat.beq (:debtor h) z) (Nat.beq (:kind h) ek-wait))
                         (List.cons Nat (:id h) (waits-on z t))
                         (waits-on z t))]))

(a/defn t18-resource-fire [w :- World, z :- Nat, tag :- Nat, v :- Nat] Outcome
  (match (resource-find w z)
    [none (refuse w)]
    [(some zr) (if (Nat.beq (:phase zr) rp-armed)
                   (accept (nat-fold (fire-edge (RunResult.mk tag v)) (resource-upd w z (res-set-phase rp-fired))
                                     (waits-on z (:edges w))))
                   (refuse w))]))

(a/theorem t18-inv [w :- World, z :- Nat, tag :- Nat, v :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t18-resource-fire w z tag v))) true))
  (intro h)
  (cases hf (resource-find w z)) (case' [some zr]) (case' [none])
  (simp only [t18-resource-fire hf refuse]) (exact h)
  (cases hp (Nat.beq (:phase zr) rp-armed))
  (simp only [t18-resource-fire hf hp refuse]) (exact h)
  (simp only [t18-resource-fire hf hp accept])
  (exact (nat-fold-inv (fire-edge (RunResult.mk tag v)) (inv-fire-edge (RunResult.mk tag v)) (waits-on z (:edges w)) _
           (inv-resource-upd w z (res-set-phase rp-fired) (res-set-phase-resource-id rp-fired) h))))

(a/theorem t18-refuse [w :- World, z :- Nat, tag :- Nat, v :- Nat]
  (=> (= (:accepted (t18-resource-fire w z tag v)) false) (= (:world (t18-resource-fire w z tag v)) w))
  (intro ha)
  (cases hf (resource-find w z)) (case' [some zr]) (case' [none])
  (simp only [t18-resource-fire hf refuse])
  (cases hp (Nat.beq (:phase zr) rp-armed))
  (simp only [t18-resource-fire hf hp refuse])
  (simp [t18-resource-fire hf hp accept] at ha))

(a/theorem t18-l4 [w :- World, z :- Nat, tag :- Nat, v :- Nat]
  (=> (= (res-tok-ok w z) false) (= (:world (t18-resource-fire w z tag v)) w))
  (intro hg) (simp only [t18-resource-fire (res-tok-none w z hg) refuse]))

;; ---- T19 handle-drop (only the counter; the §3.4 consequences are Rule R's)
;; The handle names a computation, task, source or publication; handles = 0 refuses.

(a/defn drop-pub-handle [w :- World, x :- Nat] Outcome
  (match (pub-find w x)
    [none (refuse w)]
    [(some p) (if (Nat.blt 0 (:handles p)) (accept (pub-upd w x pub-dec-handles)) (refuse w))]))
(a/defn drop-source-handle [w :- World, x :- Nat] Outcome
  (match (source-find w x)
    [none (drop-pub-handle w x)]
    [(some s) (if (Nat.blt 0 (:handles s)) (accept (source-upd w x source-dec-handles)) (refuse w))]))
(a/defn drop-task-handle [w :- World, x :- Nat] Outcome
  (match (task-find w x)
    [none (drop-source-handle w x)]
    [(some t) (if (Nat.blt 0 (:handles t)) (accept (task-upd w x task-dec-handles)) (refuse w))]))
(a/defn t19-handle-drop [w :- World, x :- Nat] Outcome
  (match (comp-find w x)
    [none (drop-task-handle w x)]
    [(some c) (if (Nat.blt 0 (:handles c)) (accept (comp-upd w x comp-dec-handles)) (refuse w))]))

(defmacro ^:private defdrop-lemmas
  "inv and refusal lemmas for one level of the T19 lookup chain."
  [f find row upd dec inv-lemma inv-args next-f next-inv next-refuse]
  (let [inv (symbol (str f "-inv")) ref (symbol (str f "-refuse"))]
    `(do
       (a/theorem ~inv [~'w :- ~'World, ~'x :- ~'Nat]
         (~'=> (~'= (~'inv-sample ~'w) true) (~'= (~'inv-sample (:world (~f ~'w ~'x))) true))
         (~'intro ~'h)
         (~'cases ~'hc (~find ~'w ~'x)) (~'case' [~'some ~'c]) (~'case' [~'none])
         ~@(if next-f
             [`(~'simp ~'only [~f ~'hc]) `(~'exact (~next-inv ~'w ~'x ~'h))]
             [`(~'simp ~'only [~f ~'hc ~'refuse]) `(~'exact ~'h)])
         (~'cases ~'hn (~'Nat.blt 0 (:handles ~'c)))
         (~'simp ~'only [~f ~'hc ~'hn ~'refuse]) (~'exact ~'h)
         (~'simp ~'only [~f ~'hc ~'hn ~'accept])
         (~'exact (~inv-lemma ~'w ~'x ~dec ~@inv-args ~'h)))
       (a/theorem ~ref [~'w :- ~'World, ~'x :- ~'Nat]
         (~'=> (~'= (:accepted (~f ~'w ~'x)) false) (~'= (:world (~f ~'w ~'x)) ~'w))
         (~'intro ~'ha)
         (~'cases ~'hc (~find ~'w ~'x)) (~'case' [~'some ~'c]) (~'case' [~'none])
         ~@(if next-f
             [`(~'simp ~'only [~f ~'hc] ~'at ~'ha) `(~'simp ~'only [~f ~'hc]) `(~'exact (~next-refuse ~'w ~'x ~'ha))]
             [`(~'simp ~'only [~f ~'hc ~'refuse])])
         (~'cases ~'hn (~'Nat.blt 0 (:handles ~'c)))
         (~'simp ~'only [~f ~'hc ~'hn ~'refuse])
         (~'simp [~f ~'hc ~'hn ~'accept] ~'at ~'ha)))))

(defdrop-lemmas drop-pub-handle pub-find PubRow pub-upd pub-dec-handles inv-pub-upd [pub-dec-handles-pub-id]
  nil nil nil)
(defdrop-lemmas drop-source-handle source-find SourceRow source-upd source-dec-handles inv-source-upd
  [source-dec-handles-source-id] drop-pub-handle drop-pub-handle-inv drop-pub-handle-refuse)
(defdrop-lemmas drop-task-handle task-find TaskRow task-upd task-dec-handles inv-task-upd
  [task-dec-handles-task-id] drop-source-handle drop-source-handle-inv drop-source-handle-refuse)
(defdrop-lemmas t19-handle-drop comp-find CompRow comp-upd comp-dec-handles inv-comp-upd
  [comp-dec-handles-comp-id comp-dec-handles-pending] drop-task-handle drop-task-handle-inv drop-task-handle-refuse)

(a/theorem t19-inv [w :- World, x :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t19-handle-drop w x))) true))
  (exact (t19-handle-drop-inv w x)))
(a/theorem t19-refuse [w :- World, x :- Nat]
  (=> (= (:accepted (t19-handle-drop w x)) false) (= (:world (t19-handle-drop w x)) w))
  (exact (t19-handle-drop-refuse w x)))

;; ---- T20 pin / unpin (Z#16: pins : id -> count, encoded as a multiset: the count of x is its
;; multiplicity in `pins`, `pin-count`; a row is a root while it occurs, i.e. count > 0)

(a/defn nat-is [x :- Nat, y :- Nat] Bool (Nat.beq y x))
(a/defn pin-count [x :- Nat, ps :- (List Nat)] Nat (tbl-count (nat-is x) ps))
;; remove one occurrence
(a/defn nat-del1 [x :- Nat, xs :- (List Nat)] (List Nat)
  (match xs [nil (List.nil Nat)] [(cons h t) (if (Nat.beq h x) t (List.cons Nat h (nat-del1 x t)))]))

(a/defn t20-pin [w :- World, x :- Nat] Outcome
  (if (Bool.or (comp-has w x) (source-has w x))
      (accept (set-pins w (List.cons Nat x (:pins w))))
      (refuse w)))

;; an unpin at count 0 is refused (Z#16)
(a/defn t20-unpin [w :- World, x :- Nat] Outcome
  (if (nat-mem x (:pins w)) (accept (set-pins w (nat-del1 x (:pins w)))) (refuse w)))

;; root while count > 0: membership in pins is a positive count
(a/theorem pin-count-pos [x :- Nat, ps :- (List Nat)]
  (= (nat-mem x ps) (Nat.blt 0 (pin-count x ps)))
  (induction ps)
  (case' [cons h t ih])
  (case' [nil])
  (simp [nat-mem pin-count tbl-count])
  (cases hb (Nat.beq h x))
  (all_goals (simp_all [nat-mem pin-count nat-is tbl-count beq-comm])))

(a/theorem t20-pin-inv [w :- World, x :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t20-pin w x))) true))
  (intro h)
  (cases hg (Bool.or (comp-has w x) (source-has w x)))
  (simp only [t20-pin hg refuse]) (exact h)
  (simp only [t20-pin hg accept]) (exact (inv-set-pins w (List.cons Nat x (:pins w)) h)))

(a/theorem t20-pin-refuse [w :- World, x :- Nat]
  (=> (= (:accepted (t20-pin w x)) false) (= (:world (t20-pin w x)) w))
  (intro ha)
  (cases hg (Bool.or (comp-has w x) (source-has w x)))
  (simp only [t20-pin hg refuse])
  (simp [t20-pin hg accept] at ha))

(a/theorem t20-unpin-inv [w :- World, x :- Nat]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (t20-unpin w x))) true))
  (intro h)
  (cases hm (nat-mem x (:pins w)))
  (simp only [t20-unpin hm refuse]) (exact h)
  (simp only [t20-unpin hm accept]) (exact (inv-set-pins w (nat-del1 x (:pins w)) h)))

(a/theorem t20-unpin-refuse [w :- World, x :- Nat]
  (=> (= (:accepted (t20-unpin w x)) false) (= (:world (t20-unpin w x)) w))
  (intro ha)
  (cases hm (nat-mem x (:pins w)))
  (simp only [t20-unpin hm refuse])
  (simp [t20-unpin hm accept] at ha))

;; ===========================================================================
;; Part E. dispatch : World -> Item -> Outcome
;; ===========================================================================

(a/defn dispatch [w :- World, it :- Item] Outcome
  (match it
    [(create-source st kind v fresh) (t1-create-source w st kind v fresh)]
    [(create-source-top scope kind v fresh) (t1-create-source-top w scope kind v fresh)]
    [(write x v) (t2-write w x v)]
    [(track st x k fresh) (t7-track w st x k fresh)]
    [(observe d cb fresh) (t8-observe w d cb fresh)]
    [(unobserve e) (t8-unobserve w e)]
    [(fire e tag val) (t9-fire w e tag val)]
    [(resource-ack z) (t15-resource-ack w z)]
    [(arm st kind k fresh) (refuse w)]
    [(resource-fire z tag val) (t18-resource-fire w z tag val)]
    [(handle-drop x) (t19-handle-drop w x)]
    [(pin x) (t20-pin w x)]
    [(unpin x) (t20-unpin w x)]
    [(create-comp st c i b) (refuse w)]
    [(create-comp-top sc c i b) (refuse w)]
    [(spawn st b fresh ins) (refuse w)]
    [(spawn-top sc b fresh ins) (refuse w)]
    [(start c fresh) (refuse w)]
    [(await st ds m k fresh mine) (refuse w)]
    [(dispatch-comp c fresh) (refuse w)]
    [(complete st tag val) (refuse w)]
    [(schedule r) (refuse w)]
    [(host-await d fresh) (refuse w)]
    [(host-unawait e) (refuse w)]
    [(handle-new x) (refuse w)]
    [(deliver x v) (refuse w)]
    [(post x v) (refuse w)]
    [(take st x k fresh) (refuse w)]
    [(release x) (refuse w)]
    [(finalize r) (refuse w)]
    [(cancel r) (refuse w)]
    [(release-world) (refuse w)]
    [(open-scope st s) (refuse w)]
    [(close-scope s) (refuse w)]
    [(detach k s) (refuse w)]
    [(finally-enter st) (refuse w)]
    [(finally-exit st) (refuse w)]
    [(slice-exit r) (refuse w)]))

;; the item's validity token (§2), true for host operations that carry none
(a/defn item-token-ok [w :- World, it :- Item] Bool
  (match it
    [(create-source st kind v fresh) (run-tok-ok w st)]
    [(create-source-top scope kind v fresh) true]
    [(write x v) true]
    [(track st x k fresh) (run-tok-ok w st)]
    [(observe d cb fresh) true]
    [(unobserve e) true]
    [(fire e tag val) (fire-tok-ok w e)]
    [(resource-ack z) (ack-tok-ok w z)]
    [(arm st kind k fresh) (run-tok-ok w st)]
    [(resource-fire z tag val) (res-tok-ok w z)]
    [(handle-drop x) true]
    [(pin x) true]
    [(unpin x) true]
    [(create-comp st c i b) (run-tok-ok w st)]
    [(create-comp-top sc c i b) true]
    [(spawn st b fresh ins) (run-tok-ok w st)]
    [(spawn-top sc b fresh ins) true]
    [(start c fresh) true]
    [(await st ds m k fresh mine) (run-tok-ok w st)]
    [(dispatch-comp c fresh) true]
    [(complete st tag val) (run-tok-ok w st)]
    [(schedule r) true]
    [(host-await d fresh) true]
    [(host-unawait e) true]
    [(handle-new x) true]
    [(deliver x v) true]
    [(post x v) true]
    [(take st x k fresh) (run-tok-ok w st)]
    [(release x) true]
    [(finalize r) true]
    [(cancel r) true]
    [(release-world) true]
    [(open-scope st s) (run-tok-ok w st)]
    [(close-scope s) true]
    [(detach k s) true]
    [(finally-enter st) (run-tok-ok w st)]
    [(finally-exit st) (run-tok-ok w st)]
    [(slice-exit r) true]))

(a/theorem dispatch-inv [w :- World, it :- Item]
  (=> (= (inv-sample w) true) (= (inv-sample (:world (dispatch w it))) true))
  (intro h)
  (cases it)
  (exact (t1-inv w _ _ _ _ h))
  (exact (t1-top-inv w _ _ _ _ h))
  (exact (t2-inv w _ _ h))
  (exact (t7-inv w _ _ _ _ h))
  (exact (t8-observe-inv w _ _ _ h))
  (exact (t8-unobserve-inv w _ h))
  (exact (t9-inv w _ _ _ h))
  (exact (t15-inv w _ h))
  (simp only [dispatch refuse]) (exact h)
  (exact (t18-inv w _ _ _ h))
  (exact (t19-inv w _ h))
  (exact (t20-pin-inv w _ h))
  (exact (t20-unpin-inv w _ h))
  (simp only [dispatch refuse]) (exact h)
  (simp only [dispatch refuse]) (exact h)
  (simp only [dispatch refuse]) (exact h)
  (simp only [dispatch refuse]) (exact h)
  (simp only [dispatch refuse]) (exact h)
  (simp only [dispatch refuse]) (exact h)
  (simp only [dispatch refuse]) (exact h)
  (simp only [dispatch refuse]) (exact h)
  (simp only [dispatch refuse]) (exact h)
  (simp only [dispatch refuse]) (exact h)
  (simp only [dispatch refuse]) (exact h)
  (simp only [dispatch refuse]) (exact h)
  (simp only [dispatch refuse]) (exact h)
  (simp only [dispatch refuse]) (exact h)
  (simp only [dispatch refuse]) (exact h)
  (simp only [dispatch refuse]) (exact h)
  (simp only [dispatch refuse]) (exact h)
  (simp only [dispatch refuse]) (exact h)
  (simp only [dispatch refuse]) (exact h)
  (simp only [dispatch refuse]) (exact h)
  (simp only [dispatch refuse]) (exact h)
  (simp only [dispatch refuse]) (exact h)
  (simp only [dispatch refuse]) (exact h)
  (simp only [dispatch refuse]) (exact h)
  (simp only [dispatch refuse]) (exact h))

(a/theorem dispatch-refuse [w :- World, it :- Item]
  (=> (= (:accepted (dispatch w it)) false) (= (:world (dispatch w it)) w))
  (intro ha)
  (cases it)
  (exact (t1-refuse w _ _ _ _ ha))
  (exact (t1-top-refuse w _ _ _ _ ha))
  (exact (t2-refuse w _ _ ha))
  (exact (t7-refuse w _ _ _ _ ha))
  (exact (t8-observe-refuse w _ _ _ ha))
  (exact (t8-unobserve-refuse w _ ha))
  (exact (t9-refuse w _ _ _ ha))
  (exact (t15-refuse w _ ha))
  (simp only [dispatch refuse])
  (exact (t18-refuse w _ _ _ ha))
  (exact (t19-refuse w _ ha))
  (exact (t20-pin-refuse w _ ha))
  (exact (t20-unpin-refuse w _ ha))
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse]))

;; L4: an operation with an invalid token changes nothing
(a/theorem dispatch-l4 [w :- World, it :- Item]
  (=> (= (item-token-ok w it) false) (= (:world (dispatch w it)) w))
  (intro hg)
  (cases it)
  (exact (t1-l4 w _ _ _ _ hg))
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (exact (t7-l4 w _ _ _ _ hg))
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (exact (t9-l4 w _ _ _ hg))
  (exact (t15-l4 w _ hg))
  (simp only [dispatch refuse])
  (exact (t18-l4 w _ _ _ hg))
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (simp [item-token-ok] at hg)
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse])
  (simp only [dispatch refuse]))

;; the step's raw part preserves the sample bundle along any item sequence
(a/defn run-items [w :- World, its :- (List Item)] World
  (match its [nil w] [(cons h t) (run-items (:world (dispatch w h)) t)]))

(a/theorem run-items-inv [its :- (List Item)]
  (forall [w :- World] (=> (= (inv-sample w) true) (= (inv-sample (run-items w its)) true)))
  (induction its)
  (case' [cons h t ih])
  (case' [nil])
  (intros w hw) (simp only [run-items]) (exact hw)
  (intros w hw) (simp only [run-items]) (exact (ih (:world (dispatch w h)) (dispatch-inv w h hw))))

(a/theorem run-items-from-empty [its :- (List Item)] (= (inv-sample (run-items empty-world its)) true)
  (exact (run-items-inv its empty-world inv-sample-empty)))
