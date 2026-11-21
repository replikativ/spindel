(ns spindel.v2.completion.quiet
  "C1 completion stability, layer 1 (notes/history/PLAN.md C1, `hq`): a step keeps a released world released
  (`step-released`) and a quiet world (released, no run) quiet.

    stays-released rb w   well-formed w and (b -> released w): the bundle copy of every well-formed lemma of the step
               (`step-stays-released`), so released stays released (`step-released`).
    host-roots-revoked w       well-formed w and K (`host-roots-revoked-rest` = `host-roots-revoked-pending-rest` and `host-roots-revoked-handles-rest`): pending-act = 0, no publication
               row, and once released no pin and no host-creditor edge (`host-roots-revoked-pending-rest`) and every computation,
               task and source has handle count 0 (`host-roots-revoked-handles-rest`, `hz-all`); `step-k`, `k-empty`. On the
               generic tree; its table (`tree/part! GK`) says where the base proof is not enough: where
               an edge is inserted (track, reactivation, await, take: no host root, `host-free`; T8,
               T22: only while not released, raw0's `world-released`/`host-await-refused`), at pin/unpin, at a
               row edit of a computation/task/source (the count stays 0: default, a site rule for
               decrements, `-open` for handle-new's h1 under the guard), at the creations (handles 1,
               only while not released: the fact `world-released w = false` comes from raw0's guards and
               is forwarded down to the creation) and at T21 (`host-roots-revoked-t21-release-world`: revoke, then
               `zero-handles-hz`).

  Both parts are restated from the generic step tree (spindel.v2.pres.tree); the bundle record and
  the primitive cells are spindel.v2.inv.copier's (`mk-bundle`, `prim!`)."
  (:require [ansatz.core :as a]
            [spindel.v2.pres.frames :as frames]
            [clojure.string :as str]
            [spindel.v2.state :refer :all]
            [spindel.v2.edits :refer :all]
            [spindel.v2.reach :refer :all]
            [spindel.v2.retain :refer :all]
            [spindel.v2.step :refer :all]
            [spindel.v2.rule :refer :all]
            [spindel.v2.engine :refer :all]
            [spindel.v2.progress.casc :refer :all]
            [spindel.v2.inv.acts :refer :all]
            [spindel.v2.inv :refer :all]
            [spindel.v2.pres.tree :as tree]
            [spindel.v2.pres.part :refer :all]
            [spindel.v2.inv.copier :refer :all]
            [spindel.v2.inv.base :refer :all]
            [spindel.v2.inv.marks-step :refer [chain-to-marks-waiting]]))

;; ===========================================================================
;; Part A. Released stays released
;; ===========================================================================

(a/defn stays-released-rest [rb :- Bool, w :- World] Bool (Bool.or (Bool.not rb) (:released w)))
(a/defn stays-released [rb :- Bool, w :- World] Bool (Bool.and (well-formed w) (stays-released-rest rb w)))

(a/theorem stays-released-well-formed [rb :- Bool, w :- World] (=> (= (stays-released rb w) true) (= (well-formed w) true))
  (intro h) (simp only [stays-released Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem stays-released-rest-of [rb :- Bool, w :- World] (=> (= (stays-released rb w) true) (= (stays-released-rest rb w) true))
  (intro h) (simp only [stays-released Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem stays-released-intro [rb :- Bool, w :- World] (=> (= (well-formed w) true) (= (stays-released-rest rb w) true) (= (stays-released rb w) true))
  (intros h1 h2) (simp only [stays-released h1 h2 Bool.and_self]))
(a/theorem stays-released-parts [rb :- Bool, w :- World]
  (=> (= (stays-released rb w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (stays-released-well-formed rb w h))))

(a/theorem stays-released-rest-set-released [rb :- Bool, w :- World]
  (= (stays-released-rest rb (set-released w true)) true)
  (simp only [stays-released-rest set-released Bool.or_true]))

(def GR (mk-bundle 'stays-released '[rb :- Bool] "stays-released-" {}))
(swap! (:renames GR) assoc 'well-formed-parts 'stays-released-parts)

(defpart GR :reads '[released])
(frames/frame-theorem! 'stays-released-rest-mark-edge 'stays-released-rest 'well-formed-mark-edge)
(frames/frame-theorem! 'stays-released-rest-unmark-edge 'stays-released-rest 'well-formed-unmark-edge)
(frames/frame-theorem! 'stays-released-rest-remove-edge 'stays-released-rest 'well-formed-remove-edge)
;; stays-released on the generic tree (spindel.v2.pres.tree): one own proof
(tree/part! GR :over '{well-formed-revoke-roots stays-released-revoke-roots})
(a/theorem stays-released-revoke-roots [rb :- Bool, w :- World]
  (=> (= (stays-released rb w) true) (= (stays-released rb (revoke-roots w)) true))
  (intro h)
  (have r (= (stays-released-rest rb (revoke-roots w)) true))
  (simp only [stays-released-rest revoke-roots set-pending-act set-pins drop-edges set-released Bool.or_true])
  (exact (stays-released-intro rb _ (well-formed-revoke-roots w (stays-released-well-formed rb w h)) r)))

(tree/restate! GR '[well-formed-raw well-formed-normalize])

(a/theorem stays-released-rule-r-round [rb :- Bool, w :- World]
  (=> (= (stays-released rb w) true) (= (filter-safe (normalize w)) true) (= (stays-released rb (rule-r-round w)) true))
  (intros h hf)
  (simp only [rule-r-round])
  (rw [rule-r-filter-eq])
  (exact (stays-released-filter-world rb _ (keep-fn (normalize w)) (stays-released-normalize rb w h) hf)))

(a/theorem stays-released-rule-r-loop [rb :- Bool, fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (stays-released rb w0) true) (= (rounds-safe-loop fuel w0) true) (= (stays-released rb (rule-r-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 h hs) (simp only [rounds-safe-loop] at hs) (simp only [rule-r-loop]) (exact (stays-released-rule-r-round rb w0 h hs)))
  (case [cons x f ih]
    (intros w0 h hs)
    (simp only [rounds-safe-loop Bool.and_eq_true] at hs)
    (have h1 := (stays-released-rule-r-round rb w0 h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false] (simp only [ho] at hs) (simp only [rule-r-loop ho]) (exact (ih (rule-r-round w0) h1 (And.right hs))))
    (case [true] (simp only [rule-r-loop ho]) (exact h1))))

(a/theorem stays-released-rule-r [rb :- Bool, w :- World]
  (=> (= (stays-released rb w) true) (= (rule-r-safe w) true) (= (stays-released rb (rule-r w)) true))
  (intros h hs) (simp only [rule-r-safe] at hs) (simp only [rule-r]) (exact (stays-released-rule-r-loop rb (rule-r-fuel w) w h hs)))

(a/theorem step-stays-released [rb :- Bool, w :- World, it :- Item]
  (=> (= (stays-released rb w) true) (= (rule-r-safe (:world (raw w it))) true) (= (stays-released rb (:world (world-step w it))) true))
  (intros h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true] (have e2 := (step-accepted w it ha)) (rw [e2]) (exact (stays-released-rule-r rb (:world (raw w it)) (stays-released-raw rb w it h) hs))))

;; Theorem (hq, released half): a step from a chain-start world keeps a released world released
(a/theorem step-released [w :- World, it :- Item]
  (=> (= (chain-start w) true) (= (:released w) true) (= (:released (:world (world-step w it))) true))
  (intros h hr)
  (have g (= (stays-released true w) true))
  (exact (stays-released-intro true w (acts-parked-well-formed w (And.left (chain-start-parts w h))) (Eq.trans (congrArg (fn [x :- Bool] (Bool.or false x)) hr) (rfl))))
  (have g2 := (stays-released-rest-of true _ (step-stays-released true w it g (step-rule-r-safe w it h))))
  (simp only [stays-released-rest Bool.not_true Bool.false_or] at g2)
  (exact g2))

;; ===========================================================================
;; Part B. K: no pending activation, no publication, and once released no pin and no host-creditor
;; edge (the roots T21 revokes stay revoked: T8, T22 and pin are refused by transition once released)
;; ===========================================================================

(a/defn pub-absent [p :- PubRow] Bool false)
(a/defn host-free [w :- World, e :- EdgeRow] Bool (Bool.or (Bool.not (:released w)) (not-host e)))
(a/defn host-roots-revoked-pending-rest [w :- World] Bool
  (Bool.and (Nat.beq (:pending-act w) 0)
   (Bool.and (tbl-all pub-absent (:pubs w))
    (Bool.or (Bool.not (:released w)) (Bool.and (nats-empty (:pins w)) (tbl-all not-host (:edges w)))))))
;; C1 quiet half, step (1): once released, every computation, task and source has handle count 0
;; (T21 zeroes them; transition refuses handle-new and every creation once released, Q8)
(a/defn h0-c [c :- CompRow] Bool (Nat.beq (:handles c) 0))
(a/defn h0-t [t :- TaskRow] Bool (Nat.beq (:handles t) 0))
(a/defn h0-s [s :- SourceRow] Bool (Nat.beq (:handles s) 0))
(a/defn hz-all [w :- World] Bool
  (Bool.and (tbl-all h0-c (:comps w)) (Bool.and (tbl-all h0-t (:tasks w)) (tbl-all h0-s (:sources w)))))
(a/defn host-roots-revoked-handles-rest [w :- World] Bool (Bool.or (Bool.not (:released w)) (hz-all w)))
(a/defn host-roots-revoked-rest [w :- World] Bool (Bool.and (host-roots-revoked-pending-rest w) (host-roots-revoked-handles-rest w)))
(a/defn host-roots-revoked [w :- World] Bool (Bool.and (well-formed w) (host-roots-revoked-rest w)))

(a/theorem host-roots-revoked-well-formed [w :- World] (=> (= (host-roots-revoked w) true) (= (well-formed w) true))
  (intro h) (simp only [host-roots-revoked Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem host-roots-revoked-rest-of [w :- World] (=> (= (host-roots-revoked w) true) (= (host-roots-revoked-rest w) true))
  (intro h) (simp only [host-roots-revoked Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem host-roots-revoked-intro [w :- World] (=> (= (well-formed w) true) (= (host-roots-revoked-rest w) true) (= (host-roots-revoked w) true))
  (intros h1 h2) (simp only [host-roots-revoked h1 h2 Bool.and_self]))
(a/theorem host-roots-revoked-parts [w :- World]
  (=> (= (host-roots-revoked w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (well-formed-parts w (host-roots-revoked-well-formed w h))))

;; the rest part from the fields it reads
(a/theorem host-roots-revoked-pending-rest-mono [w :- World, w2 :- World]
  (=> (= (:pending-act w2) (:pending-act w)) (= (:released w2) (:released w)) (= (:pins w2) (:pins w))
      (=> (= (tbl-all pub-absent (:pubs w)) true) (= (tbl-all pub-absent (:pubs w2)) true))
      (=> (= (tbl-all not-host (:edges w)) true) (= (tbl-all not-host (:edges w2)) true))
      (= (host-roots-revoked-pending-rest w) true) (= (host-roots-revoked-pending-rest w2) true))
  (intros e1 e2 e3 hp he h)
  (simp only [host-roots-revoked-pending-rest Bool.and_eq_true] at h)
  (have p2 := (hp (And.left (And.right h))))
  (have r := (And.right (And.right h)))
  (simp only [host-roots-revoked-pending-rest e1 e2 e3 p2 (And.left h) Bool.true_and])
  (cases hr (:released w))
  (case [false] (simp only [Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [hr Bool.not_true Bool.false_or Bool.and_eq_true] at r)
    (simp only [Bool.not_true Bool.false_or (And.left r) (he (And.right r)) Bool.and_self])))

(a/theorem nh-upd [x :- Nat, f :- (=> EdgeRow EdgeRow),
                   hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                   hc :- (forall [e :- EdgeRow] (= (:creditor (f e)) (:creditor e))), es :- (List EdgeRow)]
  (= (tbl-all not-host (tbl-upd edge-id x f es)) (tbl-all not-host es))
  (have hf (forall [e :- EdgeRow] (= (not-host (f e)) (not-host e))))
  (intro e) (simp only [not-host host-cred (hk e) (hc e)])
  (exact (tbl-all-upd-same EdgeRow edge-id x f not-host hf es)))
(a/theorem pa-all [ps :- (List PubRow)] (=> (= (tbl-all pub-absent ps) true) (= ps (List.nil PubRow)))
  (intro h) (cases ps) (case [nil] (rfl)) (case [cons p t] (simp [tbl-all pub-absent] at h)))

(a/theorem host-roots-revoked-pending-rest-edge-upd [w :- World, x :- Nat, f :- (=> EdgeRow EdgeRow),
                             hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                             hc :- (forall [e :- EdgeRow] (= (:creditor (f e)) (:creditor e)))]
  (=> (= (host-roots-revoked-pending-rest w) true) (= (host-roots-revoked-pending-rest (edge-upd w x f)) true))
  (intro h)
  (have e (= (:edges (edge-upd w x f)) (tbl-upd edge-id x f (:edges w)))) (rfl)
  (exact (host-roots-revoked-pending-rest-mono w (edge-upd w x f) (rfl) (rfl) (rfl) (fn [q :- (= (tbl-all pub-absent (:pubs w)) true)] q)
           (fn [q :- (= (tbl-all not-host (:edges w)) true)] (Eq.trans (congrArg (tbl-all not-host) e) (Eq.trans (nh-upd x f hk hc (:edges w)) q))) h)))
(a/theorem host-roots-revoked-pending-rest-mark-edge [w :- World, x :- Nat] (=> (= (host-roots-revoked-pending-rest w) true) (= (host-roots-revoked-pending-rest (mark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]) (exact h))
  (case [some e] (cases hm (:marked e))
    (case [true] (simp only [mark-edge hf hm]) (exact h))
    (case [false] (simp only [mark-edge hf hm])
      (exact (host-roots-revoked-pending-rest-edge-upd w x (edge-set-marked true) (fn [q :- EdgeRow] (Eq.refl (:kind q))) (fn [q :- EdgeRow] (Eq.refl (:creditor q))) h)))))
(a/theorem host-roots-revoked-pending-rest-unmark-edge [w :- World, x :- Nat] (=> (= (host-roots-revoked-pending-rest w) true) (= (host-roots-revoked-pending-rest (unmark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]) (exact h))
  (case [some e] (cases hm (:marked e))
    (case [false] (simp only [unmark-edge hf hm]) (exact h))
    (case [true] (simp only [unmark-edge hf hm])
      (exact (host-roots-revoked-pending-rest-edge-upd w x (edge-set-marked false) (fn [q :- EdgeRow] (Eq.refl (:kind q))) (fn [q :- EdgeRow] (Eq.refl (:creditor q))) h)))))
(a/theorem host-roots-revoked-pending-rest-edge-del [w :- World, x :- Nat] (=> (= (host-roots-revoked-pending-rest w) true) (= (host-roots-revoked-pending-rest (edge-del w x)) true))
  (intro h)
  (have e (= (:edges (edge-del w x)) (tbl-del edge-id x (:edges w)))) (rfl)
  (exact (host-roots-revoked-pending-rest-mono w (edge-del w x) (rfl) (rfl) (rfl) (fn [q :- (= (tbl-all pub-absent (:pubs w)) true)] q)
           (fn [q :- (= (tbl-all not-host (:edges w)) true)]
             (Eq.trans (congrArg (tbl-all not-host) e)
               (tbl-all-del EdgeRow edge-id x not-host not-host (fn [r :- EdgeRow, a1 :- (= (not-host r) true), a2 :- (= (Nat.beq (edge-id r) x) false)] a1) (:edges w) q))) h)))
(a/theorem host-roots-revoked-pending-rest-remove-edge [w :- World, x :- Nat] (=> (= (host-roots-revoked-pending-rest w) true) (= (host-roots-revoked-pending-rest (remove-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]) (exact h))
  (case [some e] (cases hm (:marked e))
    (all_goals (simp only [remove-edge hf hm]))
    (all_goals (exact (host-roots-revoked-pending-rest-edge-del w x h)))))
(a/theorem host-roots-revoked-pending-rest-filter-edges [w :- World, w2 :- World, p :- (=> EdgeRow Bool)]
  (=> (= (:pending-act w2) (:pending-act w)) (= (:released w2) (:released w)) (= (:pins w2) (:pins w)) (= (:pubs w2) (:pubs w))
      (= (:edges w2) (tbl-filter p (:edges w))) (= (host-roots-revoked-pending-rest w) true) (= (host-roots-revoked-pending-rest w2) true))
  (intros e1 e2 e3 e4 e5 h)
  (exact (host-roots-revoked-pending-rest-mono w w2 e1 e2 e3 (fn [q :- (= (tbl-all pub-absent (:pubs w)) true)] (Eq.trans (congrArg (tbl-all pub-absent) e4) q))
           (fn [q :- (= (tbl-all not-host (:edges w)) true)] (Eq.trans (congrArg (tbl-all not-host) e5) (tbl-all-filter EdgeRow not-host p (:edges w) q))) h)))
(a/theorem host-roots-revoked-pending-rest-drop-cred [w :- World, a :- Nat] (=> (= (host-roots-revoked-pending-rest w) true) (= (host-roots-revoked-pending-rest (drop-cred-edges w a)) true))
  (intro h) (exact (host-roots-revoked-pending-rest-filter-edges w (drop-cred-edges w a) (cred-ne a) (rfl) (rfl) (rfl) (rfl) (rfl) h)))
(a/theorem host-roots-revoked-pending-rest-drop-edges [w :- World, p :- (=> EdgeRow Bool)] (=> (= (host-roots-revoked-pending-rest w) true) (= (host-roots-revoked-pending-rest (drop-edges w p)) true))
  (intro h) (exact (host-roots-revoked-pending-rest-filter-edges w (drop-edges w p) p (rfl) (rfl) (rfl) (rfl) (rfl) h)))
(a/theorem host-roots-revoked-pending-rest-filter [w :- World, K :- (=> Nat Bool)] (=> (= (host-roots-revoked-pending-rest w) true) (= (host-roots-revoked-pending-rest (filter-world K w)) true))
  (intro h)
  (exact (host-roots-revoked-pending-rest-mono w (filter-world K w) (rfl) (rfl) (rfl)
           (fn [q :- (= (tbl-all pub-absent (:pubs w)) true)] (tbl-all-keep-same PubRow K pub-id pub-absent (:pubs w) q))
           (fn [q :- (= (tbl-all not-host (:edges w)) true)] (tbl-all-keep-same EdgeRow K edge-id not-host (:edges w) q)) h)))
(a/theorem host-roots-revoked-pending-rest-pub-upd [w :- World, x :- Nat, f :- (=> PubRow PubRow)] (=> (= (host-roots-revoked-pending-rest w) true) (= (host-roots-revoked-pending-rest (pub-upd w x f)) true))
  (intro h)
  (have e (= (:pubs (pub-upd w x f)) (tbl-upd pub-id x f (:pubs w)))) (rfl)
  (exact (host-roots-revoked-pending-rest-mono w (pub-upd w x f) (rfl) (rfl) (rfl)
           (fn [q :- (= (tbl-all pub-absent (:pubs w)) true)]
             (Eq.trans (congrArg (tbl-all pub-absent) e) (Eq.trans (tbl-all-upd-same PubRow pub-id x f pub-absent (fn [p :- PubRow] (rfl)) (:pubs w)) q)))
           (fn [q :- (= (tbl-all not-host (:edges w)) true)] q) h)))
;; a new edge that is not a host root, or the world is not released
(a/theorem host-free-rel [w :- World, e :- EdgeRow] (=> (= (host-free w e) true) (= (:released w) true) (= (not-host e) true))
  (intros hf hr) (simp only [host-free hr Bool.not_true Bool.false_or] at hf) (exact hf))
(a/theorem nh-cons [x :- EdgeRow, xs :- (List EdgeRow)]
  (=> (= (not-host x) true) (= (tbl-all not-host xs) true) (= (tbl-all not-host (List.cons EdgeRow x xs)) true))
  (intros h1 h2) (simp only [tbl-all h1 h2 Bool.and_self]))
(a/theorem host-roots-revoked-pending-rest-mono-rel [w :- World, w2 :- World]
  (=> (= (:pending-act w2) (:pending-act w)) (= (:released w2) (:released w)) (= (:pins w2) (:pins w))
      (=> (= (tbl-all pub-absent (:pubs w)) true) (= (tbl-all pub-absent (:pubs w2)) true))
      (=> (= (:released w) true) (= (tbl-all not-host (:edges w)) true) (= (tbl-all not-host (:edges w2)) true))
      (= (host-roots-revoked-pending-rest w) true) (= (host-roots-revoked-pending-rest w2) true))
  (intros e1 e2 e3 hp he h)
  (simp only [host-roots-revoked-pending-rest Bool.and_eq_true] at h)
  (have p2 := (hp (And.left (And.right h))))
  (have r := (And.right (And.right h)))
  (simp only [host-roots-revoked-pending-rest e1 e2 e3 p2 (And.left h) Bool.true_and])
  (cases hr (:released w))
  (case [false] (simp only [Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [hr Bool.not_true Bool.false_or Bool.and_eq_true] at r)
    (simp only [Bool.not_true Bool.false_or (And.left r) (he hr (And.right r)) Bool.and_self])))
;; a new edge that is not a host root, or the world is not released
(a/theorem host-roots-revoked-pending-rest-insert [w :- World, e :- EdgeRow] (=> (= (host-free w e) true) (= (host-roots-revoked-pending-rest w) true) (= (host-roots-revoked-pending-rest (insert-edge-fresh w e)) true))
  (intros hf h)
  (have e1 (= (:edges (insert-edge-fresh w e)) (List.cons EdgeRow (edge-set-marked false (edge-set-id (:next-id w) e)) (:edges w)))) (rfl)
  (have nh (= (not-host (edge-set-marked false (edge-set-id (:next-id w) e))) (not-host e))) (rfl)
  (exact (host-roots-revoked-pending-rest-mono-rel w (insert-edge-fresh w e) (rfl) (rfl) (rfl) (fn [q :- (= (tbl-all pub-absent (:pubs w)) true)] q)
           (fn [hr :- (= (:released w) true), q :- (= (tbl-all not-host (:edges w)) true)]
             (Eq.trans (congrArg (tbl-all not-host) e1) (nh-cons _ _ (Eq.trans nh (host-free-rel w e hf hr)) q)))
           h)))

(a/theorem host-free-nh [w :- World, e :- EdgeRow] (=> (= (not-host e) true) (= (host-free w e) true))
  (intro h) (simp only [host-free h Bool.or_true]))
(a/theorem host-free-open [w :- World, e :- EdgeRow] (=> (= (world-released w) false) (= (host-free w e) true))
  (intro h) (simp only [world-released] at h) (simp only [host-free h Bool.not_false Bool.true_or]))
(a/theorem host-await-root [w :- World, d :- Nat] (=> (= (host-await-refused w d) false) (= (world-released w) false))
  (intro h) (cases hr (world-released w)) (case [false] (rfl)) (case [true] (simp [host-await-refused hr] at h)))
(a/theorem next-pos [w :- World] (=> (= (well-formed w) true) (= (Nat.beq (:next-id w) 0) false))
  (intro h)
  (have p := (And.right (And.right (well-formed-parts w h))))
  (simp only [ids-ok ids-below Bool.and_eq_true Nat.blt_eq] at p)
  (have q := (And.left (And.right p)))
  (cases hb (Nat.beq (:next-id w) 0)) (case [false] (rfl))
  (case [true] (have z := (Nat.eq_of_beq_eq_true hb)) (omega)))
(a/theorem take-edge-nh [r :- RunRow, w :- World, x :- Nat] (=> (= (well-formed w) true) (= (not-host (take-edge r (:next-id w) x)) true))
  (intro h) (simp only [not-host host-cred take-edge ek-wait ek-observe (next-pos w h)]))

;; ---- the handle part (host-roots-revoked-handles-rest)
(a/theorem host-roots-revoked-rest-k0 [w :- World] (=> (= (host-roots-revoked-rest w) true) (= (host-roots-revoked-pending-rest w) true))
  (intro h) (simp only [host-roots-revoked-rest Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem host-roots-revoked-rest-gh [w :- World] (=> (= (host-roots-revoked-rest w) true) (= (host-roots-revoked-handles-rest w) true))
  (intro h) (simp only [host-roots-revoked-rest Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem host-roots-revoked-rest-mk [w :- World] (=> (= (host-roots-revoked-pending-rest w) true) (= (host-roots-revoked-handles-rest w) true) (= (host-roots-revoked-rest w) true))
  (intros h1 h2) (simp only [host-roots-revoked-rest h1 h2 Bool.and_self]))
(a/theorem gh-open [w :- World] (=> (= (:released w) false) (= (host-roots-revoked-handles-rest w) true))
  (intro h) (simp only [host-roots-revoked-handles-rest h Bool.not_false Bool.true_or]))
(a/theorem gh-mono [w :- World, w2 :- World]
  (=> (= (:released w2) (:released w))
      (=> (= (tbl-all h0-c (:comps w)) true) (= (tbl-all h0-c (:comps w2)) true))
      (=> (= (tbl-all h0-t (:tasks w)) true) (= (tbl-all h0-t (:tasks w2)) true))
      (=> (= (tbl-all h0-s (:sources w)) true) (= (tbl-all h0-s (:sources w2)) true))
      (= (host-roots-revoked-handles-rest w) true) (= (host-roots-revoked-handles-rest w2) true))
  (intros e hc ht hs h)
  (cases hr (:released w))
  (case [false] (exact (gh-open w2 (Eq.trans e hr))))
  (case [true]
    (simp only [host-roots-revoked-handles-rest hz-all hr Bool.not_true Bool.false_or Bool.and_eq_true] at h)
    (simp only [host-roots-revoked-handles-rest hz-all e hr (hc (And.left h)) (ht (And.left (And.right h))) (hs (And.right (And.right h)))
                Bool.not_true Bool.false_or Bool.and_self])))
;; a comps-only edit
(a/theorem gh-comps [w :- World, w2 :- World]
  (=> (= (:released w2) (:released w)) (= (:tasks w2) (:tasks w)) (= (:sources w2) (:sources w))
      (=> (= (tbl-all h0-c (:comps w)) true) (= (tbl-all h0-c (:comps w2)) true))
      (= (host-roots-revoked-handles-rest w) true) (= (host-roots-revoked-handles-rest w2) true))
  (intros e1 e2 e3 hc h)
  (exact (gh-mono w w2 e1 hc (fn [q :- (= (tbl-all h0-t (:tasks w)) true)] (Eq.trans (congrArg (tbl-all h0-t) e2) q))
           (fn [q :- (= (tbl-all h0-s (:sources w)) true)] (Eq.trans (congrArg (tbl-all h0-s) e3) q)) h)))

(a/theorem beq0-eq [n :- Nat] (=> (= (Nat.beq n 0) true) (= n 0)) (intro h) (exact (Nat.eq_of_beq_eq_true h)))
(a/theorem eq-beq0 [n :- Nat] (=> (= n 0) (= (Nat.beq n 0) true)) (intro h) (simp only [h Nat.beq_refl]))
(a/theorem sub1-zero [n :- Nat] (=> (= n 0) (= (- n 1) 0)) (intro h) (simp only [h]))
(a/theorem all-upd-keep [A :- Type, idf :- (=> A Nat), x :- Nat, f :- (=> A A), p :- (=> A Bool),
                         hp :- (forall [r :- A] (=> (= (p r) true) (= (p (f r)) true))), xs :- (List A)]
  (=> (= (tbl-all p xs) true) (= (tbl-all p (tbl-upd idf x f xs)) true))
  (intro h)
  (exact (tbl-all-upd A idf x f p p (fn [r :- A, h1 :- (= (p r) true), h2 :- (= (Nat.beq (idf r) x) true)] (hp r h1))
           (fn [r :- A, h1 :- (= (p r) true), h2 :- (= (Nat.beq (idf r) x) false)] h1) xs h)))
(a/theorem all-del-keep [A :- Type, idf :- (=> A Nat), x :- Nat, p :- (=> A Bool), xs :- (List A)]
  (=> (= (tbl-all p xs) true) (= (tbl-all p (tbl-del idf x xs)) true))
  (intro h)
  (exact (tbl-all-del A idf x p p (fn [r :- A, h1 :- (= (p r) true), h2 :- (= (Nat.beq (idf r) x) false)] h1) xs h)))
;; an edit keeps a zero count
(a/theorem hc-keep [f :- (=> CompRow CompRow), hz :- (forall [c :- CompRow] (=> (= (:handles c) 0) (= (:handles (f c)) 0)))]
  (forall [c :- CompRow] (=> (= (h0-c c) true) (= (h0-c (f c)) true)))
  (intros c q) (exact (eq-beq0 _ (hz c (beq0-eq _ q)))))
(a/theorem ht-keep [f :- (=> TaskRow TaskRow), hz :- (forall [t :- TaskRow] (=> (= (:handles t) 0) (= (:handles (f t)) 0)))]
  (forall [t :- TaskRow] (=> (= (h0-t t) true) (= (h0-t (f t)) true)))
  (intros t q) (exact (eq-beq0 _ (hz t (beq0-eq _ q)))))
(a/theorem hs-keep [f :- (=> SourceRow SourceRow), hz :- (forall [s :- SourceRow] (=> (= (:handles s) 0) (= (:handles (f s)) 0)))]
  (forall [s :- SourceRow] (=> (= (h0-s s) true) (= (h0-s (f s)) true)))
  (intros s q) (exact (eq-beq0 _ (hz s (beq0-eq _ q)))))
;; handles-preserving computation edits (the pending counts of the edge edits, comps-resync)
(a/theorem hc-same [f :- (=> CompRow CompRow), hh :- (forall [c :- CompRow] (= (:handles (f c)) (:handles c)))]
  (forall [c :- CompRow] (=> (= (h0-c c) true) (= (h0-c (f c)) true)))
  (intros c q) (simp only [h0-c (hh c)]) (exact q))
(a/theorem resync-h0 [es :- (List EdgeRow), cs :- (List CompRow)]
  (=> (= (tbl-all h0-c cs) true) (= (tbl-all h0-c (comps-resync es cs)) true))
  (induction cs)
  (case [nil] (intro h) (simp only [comps-resync tbl-all]))
  (case [cons c t ih]
    (intro h) (simp only [tbl-all Bool.and_eq_true] at h)
    (have e (= (h0-c (comp-resync es c)) (h0-c c))) (rfl)
    (simp only [comps-resync tbl-all e (And.left h) (ih (And.right h)) Bool.and_self])))

(a/theorem gh-comp-upd [w :- World, x :- Nat, f :- (=> CompRow CompRow),
                        hp :- (forall [c :- CompRow] (=> (= (h0-c c) true) (= (h0-c (f c)) true)))]
  (=> (= (host-roots-revoked-handles-rest w) true) (= (host-roots-revoked-handles-rest (comp-upd w x f)) true))
  (intro h)
  (exact (gh-comps w (comp-upd w x f) (rfl) (rfl) (rfl)
           (fn [q :- (= (tbl-all h0-c (:comps w)) true)] (all-upd-keep CompRow comp-id x f h0-c hp (:comps w) q)) h)))
(a/theorem gh-task-upd [w :- World, x :- Nat, f :- (=> TaskRow TaskRow),
                        hp :- (forall [t :- TaskRow] (=> (= (h0-t t) true) (= (h0-t (f t)) true)))]
  (=> (= (host-roots-revoked-handles-rest w) true) (= (host-roots-revoked-handles-rest (task-upd w x f)) true))
  (intro h)
  (exact (gh-mono w (task-upd w x f) (rfl) (fn [q :- (= (tbl-all h0-c (:comps w)) true)] q)
           (fn [q :- (= (tbl-all h0-t (:tasks w)) true)] (all-upd-keep TaskRow task-id x f h0-t hp (:tasks w) q))
           (fn [q :- (= (tbl-all h0-s (:sources w)) true)] q) h)))
(a/theorem gh-source-upd [w :- World, x :- Nat, f :- (=> SourceRow SourceRow),
                          hp :- (forall [s :- SourceRow] (=> (= (h0-s s) true) (= (h0-s (f s)) true)))]
  (=> (= (host-roots-revoked-handles-rest w) true) (= (host-roots-revoked-handles-rest (source-upd w x f)) true))
  (intro h)
  (exact (gh-mono w (source-upd w x f) (rfl) (fn [q :- (= (tbl-all h0-c (:comps w)) true)] q)
           (fn [q :- (= (tbl-all h0-t (:tasks w)) true)] q)
           (fn [q :- (= (tbl-all h0-s (:sources w)) true)] (all-upd-keep SourceRow source-id x f h0-s hp (:sources w) q)) h)))
(a/theorem gh-comp-del [w :- World, x :- Nat] (=> (= (host-roots-revoked-handles-rest w) true) (= (host-roots-revoked-handles-rest (comp-del w x)) true))
  (intro h)
  (exact (gh-comps w (comp-del w x) (rfl) (rfl) (rfl)
           (fn [q :- (= (tbl-all h0-c (:comps w)) true)] (all-del-keep CompRow comp-id x h0-c (:comps w) q)) h)))
(a/theorem gh-mark-edge [w :- World, x :- Nat] (=> (= (host-roots-revoked-handles-rest w) true) (= (host-roots-revoked-handles-rest (mark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]) (exact h))
  (case [some e] (cases hm (:marked e))
    (case [true] (simp only [mark-edge hf hm]) (exact h))
    (case [false] (simp only [mark-edge hf hm])
      (exact (gh-comp-upd (edge-upd w x (edge-set-marked true)) (:creditor e) comp-inc-pending
               (hc-same comp-inc-pending (fn [c :- CompRow] (Eq.refl (:handles c)))) h)))))
(a/theorem gh-unmark-edge [w :- World, x :- Nat] (=> (= (host-roots-revoked-handles-rest w) true) (= (host-roots-revoked-handles-rest (unmark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]) (exact h))
  (case [some e] (cases hm (:marked e))
    (case [false] (simp only [unmark-edge hf hm]) (exact h))
    (case [true] (simp only [unmark-edge hf hm])
      (exact (gh-comp-upd (edge-upd w x (edge-set-marked false)) (:creditor e) comp-dec-pending
               (hc-same comp-dec-pending (fn [c :- CompRow] (Eq.refl (:handles c)))) h)))))
(a/theorem gh-remove-edge [w :- World, x :- Nat] (=> (= (host-roots-revoked-handles-rest w) true) (= (host-roots-revoked-handles-rest (remove-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]) (exact h))
  (case [some e] (cases hm (:marked e))
    (case [false] (simp only [remove-edge hf hm]) (exact h))
    (case [true] (simp only [remove-edge hf hm])
      (exact (gh-comp-upd (edge-del w x) (:creditor e) comp-dec-pending
               (hc-same comp-dec-pending (fn [c :- CompRow] (Eq.refl (:handles c)))) h)))))
(a/theorem gh-drop-cred [w :- World, a :- Nat] (=> (= (host-roots-revoked-handles-rest w) true) (= (host-roots-revoked-handles-rest (drop-cred-edges w a)) true))
  (intro h)
  (exact (gh-comp-upd (set-edges w (tbl-filter (cred-ne a) (:edges w))) a (comp-set-pending 0)
           (hc-same (comp-set-pending 0) (fn [c :- CompRow] (Eq.refl (:handles c)))) h)))
(a/theorem gh-drop-edges [w :- World, p :- (=> EdgeRow Bool)] (=> (= (host-roots-revoked-handles-rest w) true) (= (host-roots-revoked-handles-rest (drop-edges w p)) true))
  (intro h)
  (exact (gh-comps w (drop-edges w p) (rfl) (rfl) (rfl)
           (fn [q :- (= (tbl-all h0-c (:comps w)) true)] (resync-h0 (tbl-filter p (:edges w)) (:comps w) q)) h)))
(a/theorem gh-filter [w :- World, K :- (=> Nat Bool)] (=> (= (host-roots-revoked-handles-rest w) true) (= (host-roots-revoked-handles-rest (filter-world K w)) true))
  (intro h)
  (exact (gh-mono w (filter-world K w) (rfl)
           (fn [q :- (= (tbl-all h0-c (:comps w)) true)] (tbl-all-keep-same CompRow K comp-id h0-c (:comps w) q))
           (fn [q :- (= (tbl-all h0-t (:tasks w)) true)] (tbl-all-keep-same TaskRow K task-id h0-t (:tasks w) q))
           (fn [q :- (= (tbl-all h0-s (:sources w)) true)] (tbl-all-keep-same SourceRow K source-id h0-s (:sources w) q)) h)))

;; the rest part, combined
(a/theorem host-roots-revoked-rest-edge-upd [w :- World, x :- Nat, f :- (=> EdgeRow EdgeRow),
                             hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                             hc :- (forall [e :- EdgeRow] (= (:creditor (f e)) (:creditor e)))]
  (=> (= (host-roots-revoked-rest w) true) (= (host-roots-revoked-rest (edge-upd w x f)) true))
  (intro h) (apply host-roots-revoked-rest-mk) (exact (host-roots-revoked-pending-rest-edge-upd w x f hk hc (host-roots-revoked-rest-k0 w h))) (exact (Eq.trans (rfl) (host-roots-revoked-rest-gh w h))))
(a/theorem host-roots-revoked-rest-mark-edge [w :- World, x :- Nat] (=> (= (host-roots-revoked-rest w) true) (= (host-roots-revoked-rest (mark-edge w x)) true))
  (intro h) (apply host-roots-revoked-rest-mk) (exact (host-roots-revoked-pending-rest-mark-edge w x (host-roots-revoked-rest-k0 w h))) (exact (gh-mark-edge w x (host-roots-revoked-rest-gh w h))))
(a/theorem host-roots-revoked-rest-unmark-edge [w :- World, x :- Nat] (=> (= (host-roots-revoked-rest w) true) (= (host-roots-revoked-rest (unmark-edge w x)) true))
  (intro h) (apply host-roots-revoked-rest-mk) (exact (host-roots-revoked-pending-rest-unmark-edge w x (host-roots-revoked-rest-k0 w h))) (exact (gh-unmark-edge w x (host-roots-revoked-rest-gh w h))))
(a/theorem host-roots-revoked-rest-remove-edge [w :- World, x :- Nat] (=> (= (host-roots-revoked-rest w) true) (= (host-roots-revoked-rest (remove-edge w x)) true))
  (intro h) (apply host-roots-revoked-rest-mk) (exact (host-roots-revoked-pending-rest-remove-edge w x (host-roots-revoked-rest-k0 w h))) (exact (gh-remove-edge w x (host-roots-revoked-rest-gh w h))))
(a/theorem host-roots-revoked-rest-drop-cred [w :- World, a :- Nat] (=> (= (host-roots-revoked-rest w) true) (= (host-roots-revoked-rest (drop-cred-edges w a)) true))
  (intro h) (apply host-roots-revoked-rest-mk) (exact (host-roots-revoked-pending-rest-drop-cred w a (host-roots-revoked-rest-k0 w h))) (exact (gh-drop-cred w a (host-roots-revoked-rest-gh w h))))
(a/theorem host-roots-revoked-rest-drop-act [w :- World, a :- Nat] (=> (= (host-roots-revoked-rest w) true) (= (host-roots-revoked-rest (drop-act w a)) true))
  (intro h) (apply host-roots-revoked-rest-mk) (exact (host-roots-revoked-pending-rest-drop-cred w a (host-roots-revoked-rest-k0 w h))) (exact (Eq.trans (rfl) (gh-drop-cred w a (host-roots-revoked-rest-gh w h)))))
(a/theorem host-roots-revoked-rest-drop-edges [w :- World, p :- (=> EdgeRow Bool)] (=> (= (host-roots-revoked-rest w) true) (= (host-roots-revoked-rest (drop-edges w p)) true))
  (intro h) (apply host-roots-revoked-rest-mk) (exact (host-roots-revoked-pending-rest-drop-edges w p (host-roots-revoked-rest-k0 w h))) (exact (gh-drop-edges w p (host-roots-revoked-rest-gh w h))))
(a/theorem host-roots-revoked-rest-filter [w :- World, K :- (=> Nat Bool)] (=> (= (host-roots-revoked-rest w) true) (= (host-roots-revoked-rest (filter-world K w)) true))
  (intro h) (apply host-roots-revoked-rest-mk) (exact (host-roots-revoked-pending-rest-filter w K (host-roots-revoked-rest-k0 w h))) (exact (gh-filter w K (host-roots-revoked-rest-gh w h))))
(a/theorem host-roots-revoked-rest-pub-upd [w :- World, x :- Nat, f :- (=> PubRow PubRow)] (=> (= (host-roots-revoked-rest w) true) (= (host-roots-revoked-rest (pub-upd w x f)) true))
  (intro h) (apply host-roots-revoked-rest-mk) (exact (host-roots-revoked-pending-rest-pub-upd w x f (host-roots-revoked-rest-k0 w h))) (exact (Eq.trans (rfl) (host-roots-revoked-rest-gh w h))))
(a/theorem host-roots-revoked-rest-insert [w :- World, e :- EdgeRow] (=> (= (host-free w e) true) (= (host-roots-revoked-rest w) true) (= (host-roots-revoked-rest (insert-edge-fresh w e)) true))
  (intros hf h) (apply host-roots-revoked-rest-mk) (exact (host-roots-revoked-pending-rest-insert w e hf (host-roots-revoked-rest-k0 w h))) (exact (Eq.trans (rfl) (host-roots-revoked-rest-gh w h))))
(a/theorem host-roots-revoked-insert-edge-fresh [w :- World, e :- EdgeRow]
  (=> (= (edge-ok-in w e) true) (= (host-free w e) true) (= (host-roots-revoked w) true) (= (host-roots-revoked (insert-edge-fresh w e)) true))
  (intros he hf h)
  (exact (host-roots-revoked-intro _ (well-formed-insert-edge-fresh w e he (host-roots-revoked-well-formed w h)) (host-roots-revoked-rest-insert w e hf (host-roots-revoked-rest-of w h)))))
(a/theorem host-roots-revoked-insert-edge-checked [w :- World, e :- EdgeRow]
  (=> (= (host-free w e) true) (= (host-roots-revoked w) true) (= (host-roots-revoked (insert-edge-checked w e)) true))
  (intros hf h)
  (cases hk (edge-ok-in w e))
  (case [false] (simp only [insert-edge-checked hk]) (exact h))
  (case [true] (simp only [insert-edge-checked hk]) (exact (host-roots-revoked-insert-edge-fresh w e hk hf h))))
(a/theorem host-roots-revoked-rest-comp-del [w :- World, x :- Nat] (=> (= (host-roots-revoked-rest w) true) (= (host-roots-revoked-rest (comp-del w x)) true))
  (intro h) (apply host-roots-revoked-rest-mk) (exact (Eq.trans (rfl) (host-roots-revoked-rest-k0 w h))) (exact (gh-comp-del w x (host-roots-revoked-rest-gh w h))))
;; a row edit that keeps a zero count; one that sets 1 only while not released (handle-new's world-released)
(a/theorem host-roots-revoked-rest-comp-upd [w :- World, x :- Nat, f :- (=> CompRow CompRow),
                             hz :- (forall [c :- CompRow] (=> (= (:handles c) 0) (= (:handles (f c)) 0)))]
  (=> (= (host-roots-revoked-rest w) true) (= (host-roots-revoked-rest (comp-upd w x f)) true))
  (intro h) (apply host-roots-revoked-rest-mk) (exact (Eq.trans (rfl) (host-roots-revoked-rest-k0 w h))) (exact (gh-comp-upd w x f (hc-keep f hz) (host-roots-revoked-rest-gh w h))))
(a/theorem host-roots-revoked-rest-task-upd [w :- World, x :- Nat, f :- (=> TaskRow TaskRow),
                             hz :- (forall [t :- TaskRow] (=> (= (:handles t) 0) (= (:handles (f t)) 0)))]
  (=> (= (host-roots-revoked-rest w) true) (= (host-roots-revoked-rest (task-upd w x f)) true))
  (intro h) (apply host-roots-revoked-rest-mk) (exact (Eq.trans (rfl) (host-roots-revoked-rest-k0 w h))) (exact (gh-task-upd w x f (ht-keep f hz) (host-roots-revoked-rest-gh w h))))
(a/theorem host-roots-revoked-rest-source-upd [w :- World, x :- Nat, f :- (=> SourceRow SourceRow),
                               hz :- (forall [s :- SourceRow] (=> (= (:handles s) 0) (= (:handles (f s)) 0)))]
  (=> (= (host-roots-revoked-rest w) true) (= (host-roots-revoked-rest (source-upd w x f)) true))
  (intro h) (apply host-roots-revoked-rest-mk) (exact (Eq.trans (rfl) (host-roots-revoked-rest-k0 w h))) (exact (gh-source-upd w x f (hs-keep f hz) (host-roots-revoked-rest-gh w h))))
(a/theorem host-roots-revoked-rest-open [w2 :- World]
  (=> (= (:released w2) false) (= (host-roots-revoked-pending-rest w2) true) (= (host-roots-revoked-rest w2) true))
  (intros hr h) (apply host-roots-revoked-rest-mk) (exact h) (exact (gh-open w2 hr)))
(a/theorem root-open [w :- World] (=> (= (world-released w) false) (= (:released w) false))
  (intro h) (simp only [world-released] at h) (exact h))
(a/theorem body-root [w :- World, st :- Nat] (=> (= (create-in-scope-refused w st) false) (= (world-released w) false))
  (intro h) (cases hr (world-released w)) (case [false] (rfl)) (case [true] (simp [create-in-scope-refused hr Bool.or_true Bool.true_or] at h)))
(a/theorem cc-root [w :- World, st :- Nat] (=> (= (create-refused w st) false) (= (world-released w) false))
  (intro h) (cases hr (world-released w)) (case [false] (rfl)) (case [true] (simp [create-refused hr Bool.or_true] at h)))

;; ---- host-roots-revoked on the generic tree (spindel.v2.pres.tree)
(def GK (mk-bundle 'host-roots-revoked [] "host-roots-revoked-"
          ;; a row edit's cell takes "a zero count stays zero"; by default the count is copied
          {'well-formed-comp-upd ['(fn [c :- CompRow, z :- (= (:handles c) 0)] z) 5]
           'well-formed-task-upd ['(fn [t :- TaskRow, z :- (= (:handles t) 0)] z) 4]
           'well-formed-source-upd ['(fn [t :- SourceRow, z :- (= (:handles t) 0)] z) 4]
           'well-formed-serve-or ['(fn [t :- SourceRow, z :- (= (:handles t) 0)] z) 5]}))
(swap! (:renames GK) assoc 'well-formed-parts 'host-roots-revoked-parts
       'well-formed-insert-edge-fresh 'host-roots-revoked-insert-edge-fresh 'well-formed-insert-edge-checked 'host-roots-revoked-insert-edge-checked)

(defpart GK :reads '[comps edges pending-act pins pubs released sources tasks])
(prim! GK 'well-formed-edge-upd '(host-roots-revoked-rest-edge-upd w x f hk hc R))
(prim! GK 'well-formed-mark-edge '(host-roots-revoked-rest-mark-edge w x R))
(prim! GK 'well-formed-unmark-edge '(host-roots-revoked-rest-unmark-edge w x R))
(prim! GK 'well-formed-remove-edge '(host-roots-revoked-rest-remove-edge w x R))
(prim! GK 'well-formed-drop-cred-edges '(host-roots-revoked-rest-drop-cred w a R))
(prim! GK 'well-formed-drop-act '(host-roots-revoked-rest-drop-act w a R))
(prim! GK 'well-formed-drop-edges '(host-roots-revoked-rest-drop-edges w p R))
(prim! GK 'well-formed-filter-world '(host-roots-revoked-rest-filter w K R))
(prim! GK 'well-formed-pub-upd '(host-roots-revoked-rest-pub-upd w x f R))
(prim! GK 'well-formed-comp-del-unref '(host-roots-revoked-rest-comp-del w x R))

;; row edits: a zero count stays zero (default: the count is copied); handle-new's h1 only while not released
(a/theorem host-roots-revoked-comp-upd [w :- World, x :- Nat, f :- (=> CompRow CompRow),
                        hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                        hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                        hz :- (forall [c :- CompRow] (=> (= (:handles c) 0) (= (:handles (f c)) 0)))]
  (=> (= (host-roots-revoked w) true) (= (host-roots-revoked (comp-upd w x f)) true))
  (intro h) (exact (host-roots-revoked-intro _ (well-formed-comp-upd w x f hid hp (host-roots-revoked-well-formed w h)) (host-roots-revoked-rest-comp-upd w x f hz (host-roots-revoked-rest-of w h)))))
(a/theorem host-roots-revoked-task-upd [w :- World, x :- Nat, f :- (=> TaskRow TaskRow),
                        hf :- (forall [r :- TaskRow] (= (task-id (f r)) (task-id r))),
                        hz :- (forall [t :- TaskRow] (=> (= (:handles t) 0) (= (:handles (f t)) 0)))]
  (=> (= (host-roots-revoked w) true) (= (host-roots-revoked (task-upd w x f)) true))
  (intro h) (exact (host-roots-revoked-intro _ (well-formed-task-upd w x f hf (host-roots-revoked-well-formed w h)) (host-roots-revoked-rest-task-upd w x f hz (host-roots-revoked-rest-of w h)))))
(a/theorem host-roots-revoked-source-upd [w :- World, x :- Nat, f :- (=> SourceRow SourceRow),
                          hf :- (forall [r :- SourceRow] (= (source-id (f r)) (source-id r))),
                          hz :- (forall [t :- SourceRow] (=> (= (:handles t) 0) (= (:handles (f t)) 0)))]
  (=> (= (host-roots-revoked w) true) (= (host-roots-revoked (source-upd w x f)) true))
  (intro h) (exact (host-roots-revoked-intro _ (well-formed-source-upd w x f hf (host-roots-revoked-well-formed w h)) (host-roots-revoked-rest-source-upd w x f hz (host-roots-revoked-rest-of w h)))))
(a/theorem host-roots-revoked-comp-upd-open [w :- World, x :- Nat, f :- (=> CompRow CompRow),
                             hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                             hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c)))]
  (=> (= (world-released w) false) (= (host-roots-revoked w) true) (= (host-roots-revoked (comp-upd w x f)) true))
  (intros hr0 h) (exact (host-roots-revoked-intro _ (well-formed-comp-upd w x f hid hp (host-roots-revoked-well-formed w h)) (host-roots-revoked-rest-open (comp-upd w x f) (root-open w hr0) (Eq.trans (rfl) (host-roots-revoked-rest-k0 w (host-roots-revoked-rest-of w h)))))))
(a/theorem host-roots-revoked-task-upd-open [w :- World, x :- Nat, f :- (=> TaskRow TaskRow),
                             hf :- (forall [r :- TaskRow] (= (task-id (f r)) (task-id r)))]
  (=> (= (world-released w) false) (= (host-roots-revoked w) true) (= (host-roots-revoked (task-upd w x f)) true))
  (intros hr0 h) (exact (host-roots-revoked-intro _ (well-formed-task-upd w x f hf (host-roots-revoked-well-formed w h)) (host-roots-revoked-rest-open (task-upd w x f) (root-open w hr0) (Eq.trans (rfl) (host-roots-revoked-rest-k0 w (host-roots-revoked-rest-of w h)))))))
(a/theorem host-roots-revoked-source-upd-open [w :- World, x :- Nat, f :- (=> SourceRow SourceRow),
                               hf :- (forall [r :- SourceRow] (= (source-id (f r)) (source-id r)))]
  (=> (= (world-released w) false) (= (host-roots-revoked w) true) (= (host-roots-revoked (source-upd w x f)) true))
  (intros hr0 h) (exact (host-roots-revoked-intro _ (well-formed-source-upd w x f hf (host-roots-revoked-well-formed w h)) (host-roots-revoked-rest-open (source-upd w x f) (root-open w hr0) (Eq.trans (rfl) (host-roots-revoked-rest-k0 w (host-roots-revoked-rest-of w h)))))))
;; creations (handles 1): only while not released
(a/theorem host-roots-revoked-comp-ins-fresh [w :- World, r :- CompRow]
  (=> (= (world-released w) false) (= (comp-id r) (:next-id w)) (= (:pending r) (marked-in (:id r) (:edges w)))
      (= (host-roots-revoked w) true) (= (host-roots-revoked (bump (comp-ins w r))) true))
  (intros hr0 hr hp h) (exact (host-roots-revoked-intro _ (well-formed-comp-ins-fresh w r hr hp (host-roots-revoked-well-formed w h)) (host-roots-revoked-rest-open (bump (comp-ins w r)) (root-open w hr0) (Eq.trans (rfl) (host-roots-revoked-rest-k0 w (host-roots-revoked-rest-of w h)))))))
(a/theorem host-roots-revoked-task-ins-fresh [w :- World, r :- TaskRow]
  (=> (= (world-released w) false) (= (task-id r) (:next-id w)) (= (host-roots-revoked w) true) (= (host-roots-revoked (bump (task-ins w r))) true))
  (intros hr0 hr h) (exact (host-roots-revoked-intro _ (well-formed-task-ins-fresh w r hr (host-roots-revoked-well-formed w h)) (host-roots-revoked-rest-open (bump (task-ins w r)) (root-open w hr0) (Eq.trans (rfl) (host-roots-revoked-rest-k0 w (host-roots-revoked-rest-of w h)))))))
(a/theorem host-roots-revoked-source-ins-fresh [w :- World, r :- SourceRow]
  (=> (= (world-released w) false) (= (source-id r) (:next-id w)) (= (host-roots-revoked w) true) (= (host-roots-revoked (bump (source-ins w r))) true))
  (intros hr0 hr h) (exact (host-roots-revoked-intro _ (well-formed-source-ins-fresh w r hr (host-roots-revoked-well-formed w h)) (host-roots-revoked-rest-open (bump (source-ins w r)) (root-open w hr0) (Eq.trans (rfl) (host-roots-revoked-rest-k0 w (host-roots-revoked-rest-of w h)))))))
(swap! (:renames GK) assoc
       'well-formed-comp-upd 'host-roots-revoked-comp-upd 'well-formed-task-upd 'host-roots-revoked-task-upd 'well-formed-source-upd 'host-roots-revoked-source-upd
       'well-formed-comp-ins-fresh 'host-roots-revoked-comp-ins-fresh 'well-formed-task-ins-fresh 'host-roots-revoked-task-ins-fresh 'well-formed-source-ins-fresh 'host-roots-revoked-source-ins-fresh)

;; row functions that keep the count only per case
(a/theorem task-cancel-result-hk [t :- TaskRow] (= (:handles (task-cancel-result t)) (:handles t))
  (cases hb (Nat.beq (:tag (:result t)) res-none)) (all_goals (simp only [task-cancel-result hb])))
(a/theorem source-consume-hk [s :- SourceRow] (= (:handles (source-consume s)) (:handles s))
  (cases ha (source-available s))
  (all_goals (simp only [source-consume ha]))
  (cases hk (Nat.beq (:kind s) sk-mailbox)) (all_goals (simp only [hk])))
(a/theorem await-edge-nh [w :- World, r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, d :- Nat]
  (=> (= (Nat.beq a 0) false) (= (not-host (await-edge w r a mode k d)) true))
  (intro ha)
  (cases hd (as-dep w r d))
  (all_goals (simp only [not-host host-cred await-edge hd ek-wait ek-dep ek-observe ha])))

;; The handle clause at a row edit that sets the count: a decrement, a zeroing and the two per-case
;; functions keep a zero count (the cell's last argument); handle-new's h1 takes the guard (`-open`).
(def ^:private gk-row-sites
  (let [upd '{comp [well-formed-comp-upd host-roots-revoked-comp-upd CompRow [hid hp]] task [well-formed-task-upd host-roots-revoked-task-upd TaskRow [hf]]
              source [well-formed-source-upd host-roots-revoked-source-upd SourceRow [hf]]}
        zero (fn [row pf] (list 'fn ['c :- row 'z :- '(= (:handles c) 0)] pf))]
    (into {} (for [[F pf] '{comp-dec-handles (sub1-zero (:handles c) z) task-dec-handles (sub1-zero (:handles c) z)
                            source-dec-handles (sub1-zero (:handles c) z)
                            comp-no-handles (Eq.refl 0) task-no-handles (Eq.refl 0) source-no-handles (Eq.refl 0)
                            task-cancel-result (Eq.trans (task-cancel-result-hk c) z)
                            source-consume (Eq.trans (source-consume-hk c) z)
                            comp-first-handle :open task-first-handle :open source-first-handle :open}
                   :let [[p cell row hs] (upd (symbol (first (str/split (name F) #"-"))))]]
               [[p F] (if (= pf :open)
                        (concat [(symbol (str cell "-open")) 'w 'x F] hs '[h0 h1])
                        (concat [cell 'w 'x F] hs [(zero row pf) 'h0]))]))))

(tree/part! GK
  :over '{well-formed-t20-pin         host-roots-revoked-t20-pin
          well-formed-t20-unpin       host-roots-revoked-t20-unpin
          well-formed-t21-release-world host-roots-revoked-t21-release-world
          well-formed-serve-or        host-roots-revoked-serve-or
          well-formed-await-wire      host-roots-revoked-await-wire
          well-formed-await-raw       host-roots-revoked-await-raw}
  ;; ---- sites: the row edits that set a handle count; the creations (their cells take the guard first)
  :sites (merge gk-row-sites
                (tree/row-sites 'well-formed-comp-ins-fresh (constantly true) (fn [F] (list 'host-roots-revoked-comp-ins-fresh 'w F 'h2 'h0 'h1 'h3)))
                (tree/row-sites 'well-formed-task-ins-fresh (constantly true) (fn [F] (list 'host-roots-revoked-task-ins-fresh 'w F 'h1 'h0 'h2)))
                (tree/row-sites 'well-formed-source-ins-fresh (constantly true) (fn [F] (list 'host-roots-revoked-source-ins-fresh 'w F 'h1 'h0 'h2))))
  ;; ---- facts from the path: a creation, handle-new's h1 and pin run only while not released
  ;; (raw0's guards); a new edge is no host root, or the world is not released
  :ctx '{well-formed-comp-ins-fresh             [(= (world-released w) false)]
         well-formed-task-ins-fresh             [(= (world-released w) false)]
         well-formed-source-ins-fresh           [(= (world-released w) false)]
         [well-formed-comp-upd comp-first-handle]         [(= (world-released w) false)]
         [well-formed-task-upd task-first-handle]         [(= (world-released w) false)]
         [well-formed-source-upd source-first-handle]     [(= (world-released w) false)]
         well-formed-t20-pin                    [(= (world-released w) false)]
         well-formed-insert-edge-fresh   [(= (host-free w e) true)]
         well-formed-insert-edge-checked        [(= (host-free w e) true)]}
  :own '{well-formed-await-step     [ha0 (= (Nat.beq a 0) false)]     ; the fresh activation's id
         well-formed-t8-observe-any-kind        [hr0 (= (world-released w) false)]
         well-formed-host-await-raw [hr0 (= (world-released w) false)]
         well-formed-stream-rows    [hr0 (= (world-released w) false)]     ; the second row is inserted after the first:
         well-formed-append-raw     [hr0 (= (world-released w) false)]}    ; the guard is of the world before both
  :pass '{;; edges that are no host root: track, reactivation (dep edges), await (a dep edge, or a wait
          ;; edge whose creditor is the fresh activation), take (a wait edge, creditor the fresh activation)
          well-formed-track-raw  {[well-formed-insert-edge-fresh (track-edge r x s k)] [(host-free-nh w (track-edge r x s k) (Eq.refl true))]}
          well-formed-react-add  {[well-formed-insert-edge-checked (valid-edge w c v)] [(host-free-nh w (valid-edge w c v) (Eq.refl true))]}
          well-formed-await-step {[well-formed-insert-edge-checked (await-edge (:world acc) r a mode k d)] [(host-free-nh _ _ (await-edge-nh _ r a mode k d ha0))]}
          well-formed-take-park  {[well-formed-insert-edge-checked (take-edge r (:next-id w) x)] [(host-free-nh _ _ (take-edge-nh r w x (base-of w h)))]}
          ;; host roots: T8 and T22 add one, refused by transition once released (world-released, host-await-refused)
          well-formed-t8-observe-any-kind        {[well-formed-insert-edge-fresh (observe-edge w d cb)] [(host-free-open w _ hr0)]}
          well-formed-host-await-raw {[well-formed-insert-edge-checked (host-wait-edge d)] [(host-free-open w _ hr0)]}
          well-formed-stream-rows    {well-formed-source-ins-fresh [hr0]}
          well-formed-append-raw     {well-formed-source-ins-fresh [hr0]}
          ;; transition: the guards give the facts
          well-formed-transition-create-source     {well-formed-t1-create-source [(body-root w st hc)]}
          well-formed-transition-create-source-top {well-formed-t1-create-source-top [hc]}
          well-formed-transition-observe           {well-formed-t8-observe [hc]}
          well-formed-transition-pin               {well-formed-t20-pin [hc]}
          well-formed-transition-create-comp       {well-formed-t3-create [(cc-root w st hc)]}
          well-formed-transition-create-comp-top   {well-formed-t3-create-top [hc]}
          well-formed-transition-spawn             {well-formed-t4-spawn [(body-root w st hc)]}
          well-formed-transition-spawn-top         {well-formed-t4-spawn-top [hc]}
          well-formed-transition-host-await        {well-formed-t22-host-await [(host-await-root w _ hc)]}
          well-formed-transition-handle-new        {well-formed-t-handle-new [hc]}
          well-formed-transition-create-link       {well-formed-t-create-link [(cc-root w st hc)]}
          well-formed-transition-create-link-top   {well-formed-t-create-link-top [hc]}
          well-formed-transition-link-demand       {well-formed-t-link-demand [hc]}
          well-formed-transition-link-realize      {well-formed-t-link-realize [hc]}
          well-formed-transition-append            {well-formed-t-append [hc]}})

;; await: the member edges' creditor is the fresh activation, whose id is not 0
(tree/restate! GK '[well-formed-await-step well-formed-await-pre well-formed-await-post])
(a/theorem host-roots-revoked-await-wire [r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, ds :- (List Nat)]
  (=> (= (Nat.beq a 0) false)
      (forall [acc :- AwAcc] (=> (= (host-roots-revoked (:world acc)) true) (= (host-roots-revoked (:world (await-wire r a mode k acc ds))) true))))
  (intro ha0)
  (induction ds)
  (case' [cons d t ih])
  (case' [nil])
  (intros acc h) (simp only [await-wire]) (exact h)
  (intros acc h) (simp only [await-wire]) (exact (ih _ (host-roots-revoked-await-step r a mode k acc d ha0 h))))
(a/theorem host-roots-revoked-await-raw [w :- World, r :- RunRow, ds :- (List Nat), mode :- Nat, k :- Nat, mine :- (List Nat)]
  (=> (= (host-roots-revoked w) true) (= (host-roots-revoked (await-raw w r ds mode k mine)) true))
  (intro h)
  (have h1 (= (host-roots-revoked (:world (await-acc w r ds mode k mine))) true))
  (exact (host-roots-revoked-await-wire r (:next-id w) mode k (nat-distinct ds) (next-pos w (host-roots-revoked-well-formed w h))
           (AwAcc.mk (await-pre w r ds mode k mine) (List.nil DE) true) (host-roots-revoked-await-pre w r ds mode k mine h)))
  (exact (host-roots-revoked-await-post (:next-id w) (:id r) ds (await-acc w r ds mode k mine) h1)))

;; pin and unpin
(a/theorem gk0-set-pins-cons [w :- World, x :- Nat] (=> (= (world-released w) false) (= (host-roots-revoked-pending-rest w) true) (= (host-roots-revoked-pending-rest (set-pins w (List.cons Nat x (:pins w)))) true))
  (intros hr h) (simp only [world-released] at hr)
  (simp only [host-roots-revoked-pending-rest Bool.and_eq_true] at h)
  (have hr2 (= (:released (set-pins w (List.cons Nat x (:pins w)))) false)) (exact hr)
  (simp only [host-roots-revoked-pending-rest hr2 Bool.not_false Bool.or_true Bool.and_true])
  (simp only [Bool.and_eq_true]) (exact (And.intro (And.left h) (And.intro (And.left (And.right h)) True.intro))))
(a/theorem nat-del1-empty [x :- Nat, xs :- (List Nat)] (=> (= (nats-empty xs) true) (= (nats-empty (nat-del1 x xs)) true))
  (intro h) (cases xs) (case [nil] (simp only [nat-del1 nats-empty])) (case [cons y t] (simp [nats-empty] at h)))
(a/theorem gk0-set-pins-del [w :- World, x :- Nat] (=> (= (host-roots-revoked-pending-rest w) true) (= (host-roots-revoked-pending-rest (set-pins w (nat-del1 x (:pins w)))) true))
  (intro h)
  (simp only [host-roots-revoked-pending-rest Bool.and_eq_true] at h)
  (have r := (And.right (And.right h)))
  (cases hr (:released w))
  (case [false]
    (have hr2 (= (:released (set-pins w (nat-del1 x (:pins w)))) false)) (exact hr)
    (simp only [host-roots-revoked-pending-rest hr2 Bool.not_false Bool.or_true Bool.and_true])
    (simp only [Bool.and_eq_true]) (exact (And.intro (And.left h) (And.intro (And.left (And.right h)) True.intro))))
  (case [true]
    (simp only [hr Bool.not_true Bool.false_or Bool.and_eq_true] at r)
    (have hr2 (= (:released (set-pins w (nat-del1 x (:pins w)))) true)) (exact hr)
    (have p := (nat-del1-empty x (:pins w) (And.left r)))
    (have e1 (= (:pins (set-pins w (nat-del1 x (:pins w)))) (nat-del1 x (:pins w)))) (rfl)
    (simp only [host-roots-revoked-pending-rest hr2 e1 p (And.left h) (And.left (And.right h)) (And.right r) Bool.not_true Bool.false_or Bool.and_self])))
(a/theorem host-roots-revoked-set-pins-cons [w :- World, x :- Nat] (=> (= (world-released w) false) (= (host-roots-revoked-rest w) true) (= (host-roots-revoked-rest (set-pins w (List.cons Nat x (:pins w)))) true))
  (intros hr h) (apply host-roots-revoked-rest-mk) (exact (gk0-set-pins-cons w x hr (host-roots-revoked-rest-k0 w h))) (exact (Eq.trans (rfl) (host-roots-revoked-rest-gh w h))))
(a/theorem host-roots-revoked-set-pins-del [w :- World, x :- Nat] (=> (= (host-roots-revoked-rest w) true) (= (host-roots-revoked-rest (set-pins w (nat-del1 x (:pins w)))) true))
  (intro h) (apply host-roots-revoked-rest-mk) (exact (gk0-set-pins-del w x (host-roots-revoked-rest-k0 w h))) (exact (Eq.trans (rfl) (host-roots-revoked-rest-gh w h))))
(a/theorem host-roots-revoked-t20-pin [w :- World, x :- Nat]
  (=> (= (world-released w) false) (= (host-roots-revoked w) true) (= (host-roots-revoked (:world (t20-pin w x))) true))
  (intros hr0 h)
  (cases hg (pin-target w x))
  (simp only [t20-pin hg refuse]) (exact h)
  (simp only [t20-pin hg accept])
  (exact (host-roots-revoked-intro _ (well-formed-set-pins w (List.cons Nat x (:pins w)) (host-roots-revoked-well-formed w h)) (host-roots-revoked-set-pins-cons w x hr0 (host-roots-revoked-rest-of w h)))))
(a/theorem host-roots-revoked-t20-unpin [w :- World, x :- Nat]
  (=> (= (host-roots-revoked w) true) (= (host-roots-revoked (:world (t20-unpin w x))) true))
  (intro h)
  (cases hm (nat-mem x (:pins w)))
  (simp only [t20-unpin hm refuse]) (exact h)
  (simp only [t20-unpin hm accept])
  (exact (host-roots-revoked-intro _ (well-formed-set-pins w (nat-del1 x (:pins w)) (host-roots-revoked-well-formed w h)) (host-roots-revoked-set-pins-del w x (host-roots-revoked-rest-of w h)))))
;; T21 revokes the roots: no pin, no host-creditor edge, no pending activation
(a/theorem host-roots-revoked-pending-rest-revoke [w :- World] (=> (= (host-roots-revoked-pending-rest w) true) (= (host-roots-revoked-pending-rest (revoke-roots w)) true))
  (intro h)
  (simp only [host-roots-revoked-pending-rest Bool.and_eq_true] at h)
  (have e1 (= (:edges (revoke-roots w)) (tbl-filter not-host (:edges w)))) (rfl)
  (have e2 (= (:pubs (revoke-roots w)) (:pubs w))) (rfl)
  (have e3 (= (:released (revoke-roots w)) true)) (rfl)
  (have e4 (= (:pins (revoke-roots w)) (List.nil Nat))) (rfl)
  (have e5 (= (:pending-act (revoke-roots w)) 0)) (rfl)
  (simp only [host-roots-revoked-pending-rest e1 e2 e3 e4 e5 (And.left (And.right h)) (tbl-all-filter-self EdgeRow not-host (:edges w))
              nats-empty Nat.beq_refl Bool.not_true Bool.false_or Bool.and_self]))
;; ---- T21: revoke, then zero every handle (the fold over the comp/task/source/pub ids)
(a/defn h0-or-c [ys :- (List Nat), c :- CompRow] Bool (Bool.or (h0-c c) (nat-mem (comp-id c) ys)))
(a/defn h0-or-t [ys :- (List Nat), t :- TaskRow] Bool (Bool.or (h0-t t) (nat-mem (task-id t) ys)))
(a/defn h0-or-s [ys :- (List Nat), s :- SourceRow] Bool (Bool.or (h0-s s) (nat-mem (source-id s) ys)))
(a/theorem fold-h0-c [ys :- (List Nat)]
  (forall [w :- World] (=> (= (tbl-all (h0-or-c ys) (:comps w)) true) (= (tbl-all h0-c (:comps (nat-fold comp-zero-handles w ys))) true)))
  (induction ys)
  (case [nil]
    (intros w h) (simp only [nat-fold])
    (apply (tbl-all-mono CompRow (h0-or-c (List.nil Nat)) h0-c _ (:comps w) h))
    (intros r q) (simp only [h0-or-c nat-mem Bool.or_false] at q) (exact q))
  (case [cons y t ih]
    (intros w h) (simp only [nat-fold]) (apply (ih (comp-zero-handles w y)))
    (have hin (forall [r :- CompRow] (=> (= (h0-or-c (List.cons Nat y t) r) true) (= (Nat.beq (comp-id r) y) true) (= (h0-or-c t (comp-no-handles r)) true))))
    (intros r h1 h2) (simp only [h0-or-c h0-c comp-no-handles Nat.beq_refl Bool.true_or])
    (have hout (forall [r :- CompRow] (=> (= (h0-or-c (List.cons Nat y t) r) true) (= (Nat.beq (comp-id r) y) false) (= (h0-or-c t r) true))))
    (intros r h1 h2) (simp only [h0-or-c nat-mem (beq-symm-false _ _ h2)] at h1) (simp only [h0-or-c]) (exact h1)
    (exact (tbl-all-upd CompRow comp-id y comp-no-handles _ _ hin hout (:comps w) h))))
(a/theorem fold-h0-t [ys :- (List Nat)]
  (forall [w :- World] (=> (= (tbl-all (h0-or-t ys) (:tasks w)) true) (= (tbl-all h0-t (:tasks (nat-fold task-zero-handles w ys))) true)))
  (induction ys)
  (case [nil]
    (intros w h) (simp only [nat-fold])
    (apply (tbl-all-mono TaskRow (h0-or-t (List.nil Nat)) h0-t _ (:tasks w) h))
    (intros r q) (simp only [h0-or-t nat-mem Bool.or_false] at q) (exact q))
  (case [cons y t ih]
    (intros w h) (simp only [nat-fold]) (apply (ih (task-zero-handles w y)))
    (have hin (forall [r :- TaskRow] (=> (= (h0-or-t (List.cons Nat y t) r) true) (= (Nat.beq (task-id r) y) true) (= (h0-or-t t (task-no-handles r)) true))))
    (intros r h1 h2) (simp only [h0-or-t h0-t task-no-handles Nat.beq_refl Bool.true_or])
    (have hout (forall [r :- TaskRow] (=> (= (h0-or-t (List.cons Nat y t) r) true) (= (Nat.beq (task-id r) y) false) (= (h0-or-t t r) true))))
    (intros r h1 h2) (simp only [h0-or-t nat-mem (beq-symm-false _ _ h2)] at h1) (simp only [h0-or-t]) (exact h1)
    (exact (tbl-all-upd TaskRow task-id y task-no-handles _ _ hin hout (:tasks w) h))))
(a/theorem fold-h0-s [ys :- (List Nat)]
  (forall [w :- World] (=> (= (tbl-all (h0-or-s ys) (:sources w)) true) (= (tbl-all h0-s (:sources (nat-fold source-zero-handles w ys))) true)))
  (induction ys)
  (case [nil]
    (intros w h) (simp only [nat-fold])
    (apply (tbl-all-mono SourceRow (h0-or-s (List.nil Nat)) h0-s _ (:sources w) h))
    (intros r q) (simp only [h0-or-s nat-mem Bool.or_false] at q) (exact q))
  (case [cons y t ih]
    (intros w h) (simp only [nat-fold]) (apply (ih (source-zero-handles w y)))
    (have hin (forall [r :- SourceRow] (=> (= (h0-or-s (List.cons Nat y t) r) true) (= (Nat.beq (source-id r) y) true) (= (h0-or-s t (source-no-handles r)) true))))
    (intros r h1 h2) (simp only [h0-or-s h0-s source-no-handles Nat.beq_refl Bool.true_or])
    (have hout (forall [r :- SourceRow] (=> (= (h0-or-s (List.cons Nat y t) r) true) (= (Nat.beq (source-id r) y) false) (= (h0-or-s t r) true))))
    (intros r h1 h2) (simp only [h0-or-s nat-mem (beq-symm-false _ _ h2)] at h1) (simp only [h0-or-s]) (exact h1)
    (exact (tbl-all-upd SourceRow source-id y source-no-handles _ _ hin hout (:sources w) h))))

;; the folds are frames for the other tables (`ff-<field>-<fold>`)
(doseq [[fld ty] '[[comps (List CompRow)] [tasks (List TaskRow)] [sources (List SourceRow)] [released Bool]]
        fo '[comp-zero-handles task-zero-handles source-zero-handles pub-zero-handles]
        :when (not (#{'[comps comp-zero-handles] '[tasks task-zero-handles] '[sources source-zero-handles]} [fld fo]))]
  (let [k (keyword (name fld))]
    (eval `(a/theorem ~(symbol (str "ff-" fld "-" fo)) [~'w :- ~'World, ~'ys :- (~'List ~'Nat)]
             (~'= (~k (~'nat-fold ~fo ~'w ~'ys)) (~k ~'w))
             (~'exact (~'nat-fold-frame ~ty (~'fn [~'v :- ~'World] (~k ~'v)) ~fo (~'fn [~'v :- ~'World, ~'y :- ~'Nat] (~'Eq.refl (~k ~'v))) ~'ys ~'w))))))

(a/theorem zero-handles-hz [w :- World] (= (hz-all (zero-handles w)) true)
  (have c0 (= (tbl-all (h0-or-c (tbl-ids comp-id (:comps w))) (:comps w)) true))
  (apply all-of-mem) (intros c hm) (simp only [h0-or-c (mem-ids-has CompRow comp-id c (:comps w) hm) Bool.or_true])
  (have t0 (= (tbl-all (h0-or-t (tbl-ids task-id (:tasks w))) (:tasks w)) true))
  (apply all-of-mem) (intros c hm) (simp only [h0-or-t (mem-ids-has TaskRow task-id c (:tasks w) hm) Bool.or_true])
  (have s0 (= (tbl-all (h0-or-s (tbl-ids source-id (:sources w))) (:sources w)) true))
  (apply all-of-mem) (intros c hm) (simp only [h0-or-s (mem-ids-has SourceRow source-id c (:sources w) hm) Bool.or_true])
  (have c1 := (fold-h0-c (tbl-ids comp-id (:comps w)) w c0))
  (have t1 (= (tbl-all (h0-or-t (tbl-ids task-id (:tasks w))) (:tasks (nat-fold comp-zero-handles w (tbl-ids comp-id (:comps w))))) true))
  (rw [ff-tasks-comp-zero-handles]) (exact t0)
  (have t2 := (fold-h0-t (tbl-ids task-id (:tasks w)) _ t1))
  (have s1 (= (tbl-all (h0-or-s (tbl-ids source-id (:sources w))) (:sources (nat-fold task-zero-handles (nat-fold comp-zero-handles w (tbl-ids comp-id (:comps w))) (tbl-ids task-id (:tasks w))))) true))
  (rw [ff-sources-task-zero-handles ff-sources-comp-zero-handles]) (exact s0)
  (have s2 := (fold-h0-s (tbl-ids source-id (:sources w)) _ s1))
  (simp only [zero-handles hz-all ff-comps-pub-zero-handles ff-comps-source-zero-handles ff-comps-task-zero-handles
              ff-tasks-pub-zero-handles ff-tasks-source-zero-handles ff-sources-pub-zero-handles c1 t2 s2 Bool.and_self]))

(a/theorem zero-handles-rel [w :- World] (= (:released (zero-handles w)) (:released w))
  (simp only [zero-handles ff-released-pub-zero-handles ff-released-source-zero-handles ff-released-task-zero-handles ff-released-comp-zero-handles]))

(a/theorem gk0-zero-handles [w :- World] (=> (= (host-roots-revoked-pending-rest w) true) (= (host-roots-revoked-pending-rest (zero-handles w)) true))
  (intro h)
  (have hp (forall [v :- World, y :- Nat] (=> (= (host-roots-revoked-pending-rest v) true) (= (host-roots-revoked-pending-rest (pub-zero-handles v y)) true))))
  (intros v y q) (exact (host-roots-revoked-pending-rest-pub-upd v y pub-no-handles q))
  (have hs (forall [v :- World, y :- Nat] (=> (= (host-roots-revoked-pending-rest v) true) (= (host-roots-revoked-pending-rest (source-zero-handles v y)) true))))
  (intros v y q) (exact (Eq.trans (rfl) q))
  (have ht (forall [v :- World, y :- Nat] (=> (= (host-roots-revoked-pending-rest v) true) (= (host-roots-revoked-pending-rest (task-zero-handles v y)) true))))
  (intros v y q) (exact (Eq.trans (rfl) q))
  (have hc (forall [v :- World, y :- Nat] (=> (= (host-roots-revoked-pending-rest v) true) (= (host-roots-revoked-pending-rest (comp-zero-handles v y)) true))))
  (intros v y q) (exact (Eq.trans (rfl) q))
  (simp only [zero-handles])
  (exact (nat-fold-pres host-roots-revoked-pending-rest pub-zero-handles hp _ _ (nat-fold-pres host-roots-revoked-pending-rest source-zero-handles hs _ _
           (nat-fold-pres host-roots-revoked-pending-rest task-zero-handles ht _ _ (nat-fold-pres host-roots-revoked-pending-rest comp-zero-handles hc _ _ h))))))

(a/theorem host-roots-revoked-zero-revoke [w :- World] (=> (= (host-roots-revoked w) true) (= (host-roots-revoked (zero-handles (revoke-roots w))) true))
  (intro h)
  (have k0 := (gk0-zero-handles _ (host-roots-revoked-pending-rest-revoke w (host-roots-revoked-rest-k0 w (host-roots-revoked-rest-of w h)))))
  (have hr (= (:released (zero-handles (revoke-roots w))) true)) (exact (Eq.trans (zero-handles-rel _) (rfl)))
  (have g (= (host-roots-revoked-handles-rest (zero-handles (revoke-roots w))) true))
  (simp only [host-roots-revoked-handles-rest hr (zero-handles-hz (revoke-roots w)) Bool.or_true])
  (exact (host-roots-revoked-intro _ (well-formed-zero-handles _ (well-formed-revoke-roots w (host-roots-revoked-well-formed w h))) (host-roots-revoked-rest-mk _ k0 g))))

;; T21 (`t21-release-world`): revoke, zero the handles, close the root scope
(tree/restate! GK '[well-formed-run-cascade])
(a/theorem host-roots-revoked-t21-release-world [w :- World]
  (=> (= (host-roots-revoked w) true) (= (host-roots-revoked (:world (t21-release-world w))) true))
  (intro h)
  (cases hr (:released w))
  (simp only [t21-release-world hr accept release-world-raw])
  (exact (host-roots-revoked-run-cascade _ _ (host-roots-revoked-zero-revoke w h)))
  (simp only [t21-release-world hr refuse]) (exact h))

;; serve-or's `keep` row edit keeps a zero count (its callers: enqueue, permit)
(tree/restate! GK '[well-formed-fire-edge])
(a/theorem host-roots-revoked-serve-or [w :- World, x :- Nat, res :- RunResult, keep :- (=> SourceRow SourceRow),
                        hk :- (forall [s :- SourceRow] (= (source-id (keep s)) (source-id s))),
                        hz :- (forall [t :- SourceRow] (=> (= (:handles t) 0) (= (:handles (keep t)) 0)))]
  (=> (= (host-roots-revoked w) true) (= (host-roots-revoked (serve-or w x res keep)) true))
  (intro h)
  (cases hz0 (Nat.beq (oldest-waiter w x) 0))
  (simp only [serve-or hz0]) (exact (host-roots-revoked-fire-edge res w _ h))
  (simp only [serve-or hz0]) (exact (host-roots-revoked-source-upd w x keep hk hz h)))

(tree/restate! GK '[well-formed-raw well-formed-normalize])

(a/theorem host-roots-revoked-rule-r-round [w :- World]
  (=> (= (host-roots-revoked w) true) (= (filter-safe (normalize w)) true) (= (host-roots-revoked (rule-r-round w)) true))
  (intros h hf)
  (simp only [rule-r-round])
  (rw [rule-r-filter-eq])
  (exact (host-roots-revoked-filter-world _ (keep-fn (normalize w)) (host-roots-revoked-normalize w h) hf)))

(a/theorem host-roots-revoked-rule-r-loop [fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (host-roots-revoked w0) true) (= (rounds-safe-loop fuel w0) true) (= (host-roots-revoked (rule-r-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 h hs) (simp only [rounds-safe-loop] at hs) (simp only [rule-r-loop]) (exact (host-roots-revoked-rule-r-round w0 h hs)))
  (case [cons x f ih]
    (intros w0 h hs)
    (simp only [rounds-safe-loop Bool.and_eq_true] at hs)
    (have h1 := (host-roots-revoked-rule-r-round w0 h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false] (simp only [ho] at hs) (simp only [rule-r-loop ho]) (exact (ih (rule-r-round w0) h1 (And.right hs))))
    (case [true] (simp only [rule-r-loop ho]) (exact h1))))

(a/theorem host-roots-revoked-rule-r [w :- World]
  (=> (= (host-roots-revoked w) true) (= (rule-r-safe w) true) (= (host-roots-revoked (rule-r w)) true))
  (intros h hs) (simp only [rule-r-safe] at hs) (simp only [rule-r]) (exact (host-roots-revoked-rule-r-loop (rule-r-fuel w) w h hs)))

(a/theorem step-host-roots-revoked [w :- World, it :- Item]
  (=> (= (host-roots-revoked w) true) (= (rule-r-safe (:world (raw w it))) true) (= (host-roots-revoked (:world (world-step w it))) true))
  (intros h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true] (have e2 := (step-accepted w it ha)) (rw [e2]) (exact (host-roots-revoked-rule-r (:world (raw w it)) (host-roots-revoked-raw w it h) hs))))

;; Theorem (K): no pending activation, no publication, and once released no pin and no host-creditor
;; edge, through every step from a chain-start world; the empty world has it
(a/theorem step-k [w :- World, it :- Item]
  (=> (= (chain-start w) true) (= (host-roots-revoked-rest w) true) (= (host-roots-revoked-rest (:world (world-step w it))) true))
  (intros h hk)
  (exact (host-roots-revoked-rest-of _ (step-host-roots-revoked w it (host-roots-revoked-intro w (acts-parked-well-formed w (And.left (chain-start-parts w h))) hk) (step-rule-r-safe w it h)))))
(a/theorem k-empty [] (= (host-roots-revoked-rest empty-world) true) (rfl))
