(ns spindel.v2.completion.quiet
  "C1 completion stability, layer 1 (notes/history/PLAN.md C1, `hq`): a step keeps a released world released
  (`step-released`) and a quiet world (released, no run) quiet.

    grel rb w   inv-sample w and (b -> released w): the bundle copy of every inv-sample lemma of the step
               (`step-grel`), so released stays released (`step-released`).
    gk w       inv-sample w and K (`gk-rest` = `gk0-rest` and `gh-rest`): pending-act = 0, no publication
               row, and once released no pin and no host-creditor edge (`gk0-rest`) and every computation,
               task and source has handle count 0 (`gh-rest`, `hz-all`); `step-k`, `k-empty`. The copy is
               generic except where an edge is inserted (track, reactivation, await, take: no host root,
               `host-free`; T8, T22: only while not released, raw0's `root-shut`/`host-await-bad`), at
               pin/unpin, at a row edit of a computation/task/source (the count stays 0: default, `-z` for
               decrements, `-open` for handle-new's h1 under the guard), at the creations (handles 1, only
               while not released: `hr0 : root-shut w = false` threaded from raw0's guards through
               `gk-threaded`) and at T21 (`t-release-world-gk`: revoke, then `zero-handles-hz`).

  The copy machinery is spindel.v2.inv.copier's (`mk-bundle`, `prim!`, `lcopy!`)."
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
            [spindel.v2.inv.copier :refer :all]
            [spindel.v2.inv.base :refer :all]
            [spindel.v2.inv.marks-step :refer [p3l]]))

;; ===========================================================================
;; Part A. Released stays released
;; ===========================================================================

(a/defn grel-rest [rb :- Bool, w :- World] Bool (Bool.or (Bool.not rb) (:released w)))
(a/defn grel [rb :- Bool, w :- World] Bool (Bool.and (inv-sample w) (grel-rest rb w)))

(a/theorem grel-sample [rb :- Bool, w :- World] (=> (= (grel rb w) true) (= (inv-sample w) true))
  (intro h) (simp only [grel Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem grel-rest-of [rb :- Bool, w :- World] (=> (= (grel rb w) true) (= (grel-rest rb w) true))
  (intro h) (simp only [grel Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem grel-intro [rb :- Bool, w :- World] (=> (= (inv-sample w) true) (= (grel-rest rb w) true) (= (grel rb w) true))
  (intros h1 h2) (simp only [grel h1 h2 Bool.and_self]))
(a/theorem grel-parts [rb :- Bool, w :- World]
  (=> (= (grel rb w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (grel-sample rb w h))))

(a/theorem grel-rest-set-released [rb :- Bool, w :- World]
  (= (grel-rest rb (set-released w true)) true)
  (simp only [grel-rest set-released Bool.or_true]))

(def GR (mk-bundle 'grel '[rb :- Bool] "grel-" {}))
(swap! (:renames GR) assoc 'inv-parts 'grel-parts)

(defpart GR :reads '[released])
(frames/frame-theorem! 'grel-rest-mark-edge 'grel-rest 'mark-edge-inv-sample)
(frames/frame-theorem! 'grel-rest-unmark-edge 'grel-rest 'unmark-edge-inv-sample)
(frames/frame-theorem! 'grel-rest-remove-edge 'grel-rest 'inv-remove-edge)
;; grel on the generic tree (spindel.v2.pres.tree): one own proof
(tree/part! GR :over '{inv-revoke-roots grel-revoke-roots})
(a/theorem grel-revoke-roots [rb :- Bool, w :- World]
  (=> (= (grel rb w) true) (= (grel rb (revoke-roots w)) true))
  (intro h)
  (have r (= (grel-rest rb (revoke-roots w)) true))
  (simp only [grel-rest revoke-roots set-pending-act set-pins drop-edges set-released Bool.or_true])
  (exact (grel-intro rb _ (inv-revoke-roots w (grel-sample rb w h)) r)))

(tree/restate! GR '[raw-inv inv-normalize])

(a/theorem grel-rule-r-round [rb :- Bool, w :- World]
  (=> (= (grel rb w) true) (= (filter-safe (normalize w)) true) (= (grel rb (rule-r-round w)) true))
  (intros h hf)
  (simp only [rule-r-round])
  (rw [rule-r-filter-eq])
  (exact (grel-filter-world rb _ (keep-fn (normalize w)) (grel-normalize rb w h) hf)))

(a/theorem grel-rr-loop [rb :- Bool, fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (grel rb w0) true) (= (rr-safe fuel w0) true) (= (grel rb (rr-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 h hs) (simp only [rr-safe] at hs) (simp only [rr-loop]) (exact (grel-rule-r-round rb w0 h hs)))
  (case [cons x f ih]
    (intros w0 h hs)
    (simp only [rr-safe Bool.and_eq_true] at hs)
    (have h1 := (grel-rule-r-round rb w0 h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false] (simp only [ho] at hs) (simp only [rr-loop ho]) (exact (ih (rule-r-round w0) h1 (And.right hs))))
    (case [true] (simp only [rr-loop ho]) (exact h1))))

(a/theorem grel-rule-r [rb :- Bool, w :- World]
  (=> (= (grel rb w) true) (= (rule-r-safe w) true) (= (grel rb (rule-r w)) true))
  (intros h hs) (simp only [rule-r-safe] at hs) (simp only [rule-r]) (exact (grel-rr-loop rb (rr-fuel w) w h hs)))

(a/theorem step-grel [rb :- Bool, w :- World, it :- Item]
  (=> (= (grel rb w) true) (= (rule-r-safe (:world (raw w it))) true) (= (grel rb (:world (world-step w it))) true))
  (intros h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true] (have e2 := (step-accepted w it ha)) (rw [e2]) (exact (grel-rule-r rb (:world (raw w it)) (raw-grel rb w it h) hs))))

;; Theorem (hq, released half): a step from a p3b world keeps a released world released
(a/theorem step-released [w :- World, it :- Item]
  (=> (= (p3b w) true) (= (:released w) true) (= (:released (:world (world-step w it))) true))
  (intros h hr)
  (have g (= (grel true w) true))
  (exact (grel-intro true w (ga-sample w (And.left (p3b-parts w h))) (Eq.trans (congrArg (fn [x :- Bool] (Bool.or false x)) hr) (rfl))))
  (have g2 := (grel-rest-of true _ (step-grel true w it g (step-rule-r-safe w it h))))
  (simp only [grel-rest Bool.not_true Bool.false_or] at g2)
  (exact g2))

;; ===========================================================================
;; Part B. K: no pending activation, no publication, and once released no pin and no host-creditor
;; edge (the roots T21 revokes stay revoked: T8, T22 and pin are refused by raw0 once released)
;; ===========================================================================

(a/defn pub-absent [p :- PubRow] Bool false)
(a/defn host-free [w :- World, e :- EdgeRow] Bool (Bool.or (Bool.not (:released w)) (not-host e)))
(a/defn gk0-rest [w :- World] Bool
  (Bool.and (Nat.beq (:pending-act w) 0)
   (Bool.and (tbl-all pub-absent (:pubs w))
    (Bool.or (Bool.not (:released w)) (Bool.and (nats-empty (:pins w)) (tbl-all not-host (:edges w)))))))
;; C1 quiet half, step (1): once released, every computation, task and source has handle count 0
;; (T21 zeroes them; raw0 refuses handle-new and every creation once released, Q8)
(a/defn h0-c [c :- CompRow] Bool (Nat.beq (:handles c) 0))
(a/defn h0-t [t :- TaskRow] Bool (Nat.beq (:handles t) 0))
(a/defn h0-s [s :- SourceRow] Bool (Nat.beq (:handles s) 0))
(a/defn hz-all [w :- World] Bool
  (Bool.and (tbl-all h0-c (:comps w)) (Bool.and (tbl-all h0-t (:tasks w)) (tbl-all h0-s (:sources w)))))
(a/defn gh-rest [w :- World] Bool (Bool.or (Bool.not (:released w)) (hz-all w)))
(a/defn gk-rest [w :- World] Bool (Bool.and (gk0-rest w) (gh-rest w)))
(a/defn gk [w :- World] Bool (Bool.and (inv-sample w) (gk-rest w)))

(a/theorem gk-sample [w :- World] (=> (= (gk w) true) (= (inv-sample w) true))
  (intro h) (simp only [gk Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem gk-rest-of [w :- World] (=> (= (gk w) true) (= (gk-rest w) true))
  (intro h) (simp only [gk Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem gk-intro [w :- World] (=> (= (inv-sample w) true) (= (gk-rest w) true) (= (gk w) true))
  (intros h1 h2) (simp only [gk h1 h2 Bool.and_self]))
(a/theorem gk-parts [w :- World]
  (=> (= (gk w) true)
      (And (= (pending-exact w) true) (And (= (edges-ref-ok w) true) (= (ids-ok w) true))))
  (intro h) (exact (inv-parts w (gk-sample w h))))

;; the rest part from the fields it reads
(a/theorem gk0-rest-mono [w :- World, w2 :- World]
  (=> (= (:pending-act w2) (:pending-act w)) (= (:released w2) (:released w)) (= (:pins w2) (:pins w))
      (=> (= (tbl-all pub-absent (:pubs w)) true) (= (tbl-all pub-absent (:pubs w2)) true))
      (=> (= (tbl-all not-host (:edges w)) true) (= (tbl-all not-host (:edges w2)) true))
      (= (gk0-rest w) true) (= (gk0-rest w2) true))
  (intros e1 e2 e3 hp he h)
  (simp only [gk0-rest Bool.and_eq_true] at h)
  (have p2 := (hp (And.left (And.right h))))
  (have r := (And.right (And.right h)))
  (simp only [gk0-rest e1 e2 e3 p2 (And.left h) Bool.true_and])
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

(a/theorem gk0-rest-edge-upd [w :- World, x :- Nat, f :- (=> EdgeRow EdgeRow),
                             hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                             hc :- (forall [e :- EdgeRow] (= (:creditor (f e)) (:creditor e)))]
  (=> (= (gk0-rest w) true) (= (gk0-rest (edge-upd w x f)) true))
  (intro h)
  (have e (= (:edges (edge-upd w x f)) (tbl-upd edge-id x f (:edges w)))) (rfl)
  (exact (gk0-rest-mono w (edge-upd w x f) (rfl) (rfl) (rfl) (fn [q :- (= (tbl-all pub-absent (:pubs w)) true)] q)
           (fn [q :- (= (tbl-all not-host (:edges w)) true)] (Eq.trans (congrArg (tbl-all not-host) e) (Eq.trans (nh-upd x f hk hc (:edges w)) q))) h)))
(a/theorem gk0-rest-mark-edge [w :- World, x :- Nat] (=> (= (gk0-rest w) true) (= (gk0-rest (mark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]) (exact h))
  (case [some e] (cases hm (:marked e))
    (case [true] (simp only [mark-edge hf hm]) (exact h))
    (case [false] (simp only [mark-edge hf hm])
      (exact (gk0-rest-edge-upd w x (edge-set-marked true) (fn [q :- EdgeRow] (Eq.refl (:kind q))) (fn [q :- EdgeRow] (Eq.refl (:creditor q))) h)))))
(a/theorem gk0-rest-unmark-edge [w :- World, x :- Nat] (=> (= (gk0-rest w) true) (= (gk0-rest (unmark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]) (exact h))
  (case [some e] (cases hm (:marked e))
    (case [false] (simp only [unmark-edge hf hm]) (exact h))
    (case [true] (simp only [unmark-edge hf hm])
      (exact (gk0-rest-edge-upd w x (edge-set-marked false) (fn [q :- EdgeRow] (Eq.refl (:kind q))) (fn [q :- EdgeRow] (Eq.refl (:creditor q))) h)))))
(a/theorem gk0-rest-edge-del [w :- World, x :- Nat] (=> (= (gk0-rest w) true) (= (gk0-rest (edge-del w x)) true))
  (intro h)
  (have e (= (:edges (edge-del w x)) (tbl-del edge-id x (:edges w)))) (rfl)
  (exact (gk0-rest-mono w (edge-del w x) (rfl) (rfl) (rfl) (fn [q :- (= (tbl-all pub-absent (:pubs w)) true)] q)
           (fn [q :- (= (tbl-all not-host (:edges w)) true)]
             (Eq.trans (congrArg (tbl-all not-host) e)
               (tbl-all-del EdgeRow edge-id x not-host not-host (fn [r :- EdgeRow, a1 :- (= (not-host r) true), a2 :- (= (Nat.beq (edge-id r) x) false)] a1) (:edges w) q))) h)))
(a/theorem gk0-rest-remove-edge [w :- World, x :- Nat] (=> (= (gk0-rest w) true) (= (gk0-rest (remove-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]) (exact h))
  (case [some e] (cases hm (:marked e))
    (all_goals (simp only [remove-edge hf hm]))
    (all_goals (exact (gk0-rest-edge-del w x h)))))
(a/theorem gk0-rest-filter-edges [w :- World, w2 :- World, p :- (=> EdgeRow Bool)]
  (=> (= (:pending-act w2) (:pending-act w)) (= (:released w2) (:released w)) (= (:pins w2) (:pins w)) (= (:pubs w2) (:pubs w))
      (= (:edges w2) (tbl-filter p (:edges w))) (= (gk0-rest w) true) (= (gk0-rest w2) true))
  (intros e1 e2 e3 e4 e5 h)
  (exact (gk0-rest-mono w w2 e1 e2 e3 (fn [q :- (= (tbl-all pub-absent (:pubs w)) true)] (Eq.trans (congrArg (tbl-all pub-absent) e4) q))
           (fn [q :- (= (tbl-all not-host (:edges w)) true)] (Eq.trans (congrArg (tbl-all not-host) e5) (tbl-all-filter EdgeRow not-host p (:edges w) q))) h)))
(a/theorem gk0-rest-drop-cred [w :- World, a :- Nat] (=> (= (gk0-rest w) true) (= (gk0-rest (drop-cred-edges w a)) true))
  (intro h) (exact (gk0-rest-filter-edges w (drop-cred-edges w a) (cred-ne a) (rfl) (rfl) (rfl) (rfl) (rfl) h)))
(a/theorem gk0-rest-drop-edges [w :- World, p :- (=> EdgeRow Bool)] (=> (= (gk0-rest w) true) (= (gk0-rest (drop-edges w p)) true))
  (intro h) (exact (gk0-rest-filter-edges w (drop-edges w p) p (rfl) (rfl) (rfl) (rfl) (rfl) h)))
(a/theorem gk0-rest-filter [w :- World, K :- (=> Nat Bool)] (=> (= (gk0-rest w) true) (= (gk0-rest (filter-world K w)) true))
  (intro h)
  (exact (gk0-rest-mono w (filter-world K w) (rfl) (rfl) (rfl)
           (fn [q :- (= (tbl-all pub-absent (:pubs w)) true)] (tbl-all-keep-same PubRow K pub-id pub-absent (:pubs w) q))
           (fn [q :- (= (tbl-all not-host (:edges w)) true)] (tbl-all-keep-same EdgeRow K edge-id not-host (:edges w) q)) h)))
(a/theorem gk0-rest-pub-upd [w :- World, x :- Nat, f :- (=> PubRow PubRow)] (=> (= (gk0-rest w) true) (= (gk0-rest (pub-upd w x f)) true))
  (intro h)
  (have e (= (:pubs (pub-upd w x f)) (tbl-upd pub-id x f (:pubs w)))) (rfl)
  (exact (gk0-rest-mono w (pub-upd w x f) (rfl) (rfl) (rfl)
           (fn [q :- (= (tbl-all pub-absent (:pubs w)) true)]
             (Eq.trans (congrArg (tbl-all pub-absent) e) (Eq.trans (tbl-all-upd-same PubRow pub-id x f pub-absent (fn [p :- PubRow] (rfl)) (:pubs w)) q)))
           (fn [q :- (= (tbl-all not-host (:edges w)) true)] q) h)))
;; a new edge that is not a host root, or the world is not released
(a/theorem host-free-rel [w :- World, e :- EdgeRow] (=> (= (host-free w e) true) (= (:released w) true) (= (not-host e) true))
  (intros hf hr) (simp only [host-free hr Bool.not_true Bool.false_or] at hf) (exact hf))
(a/theorem nh-cons [x :- EdgeRow, xs :- (List EdgeRow)]
  (=> (= (not-host x) true) (= (tbl-all not-host xs) true) (= (tbl-all not-host (List.cons EdgeRow x xs)) true))
  (intros h1 h2) (simp only [tbl-all h1 h2 Bool.and_self]))
(a/theorem gk0-rest-mono-rel [w :- World, w2 :- World]
  (=> (= (:pending-act w2) (:pending-act w)) (= (:released w2) (:released w)) (= (:pins w2) (:pins w))
      (=> (= (tbl-all pub-absent (:pubs w)) true) (= (tbl-all pub-absent (:pubs w2)) true))
      (=> (= (:released w) true) (= (tbl-all not-host (:edges w)) true) (= (tbl-all not-host (:edges w2)) true))
      (= (gk0-rest w) true) (= (gk0-rest w2) true))
  (intros e1 e2 e3 hp he h)
  (simp only [gk0-rest Bool.and_eq_true] at h)
  (have p2 := (hp (And.left (And.right h))))
  (have r := (And.right (And.right h)))
  (simp only [gk0-rest e1 e2 e3 p2 (And.left h) Bool.true_and])
  (cases hr (:released w))
  (case [false] (simp only [Bool.not_false Bool.true_or]))
  (case [true]
    (simp only [hr Bool.not_true Bool.false_or Bool.and_eq_true] at r)
    (simp only [Bool.not_true Bool.false_or (And.left r) (he hr (And.right r)) Bool.and_self])))
;; a new edge that is not a host root, or the world is not released
(a/theorem gk0-rest-insert [w :- World, e :- EdgeRow] (=> (= (host-free w e) true) (= (gk0-rest w) true) (= (gk0-rest (insert-edge-fresh w e)) true))
  (intros hf h)
  (have e1 (= (:edges (insert-edge-fresh w e)) (List.cons EdgeRow (edge-set-marked false (edge-set-id (:next-id w) e)) (:edges w)))) (rfl)
  (have nh (= (not-host (edge-set-marked false (edge-set-id (:next-id w) e))) (not-host e))) (rfl)
  (exact (gk0-rest-mono-rel w (insert-edge-fresh w e) (rfl) (rfl) (rfl) (fn [q :- (= (tbl-all pub-absent (:pubs w)) true)] q)
           (fn [hr :- (= (:released w) true), q :- (= (tbl-all not-host (:edges w)) true)]
             (Eq.trans (congrArg (tbl-all not-host) e1) (nh-cons _ _ (Eq.trans nh (host-free-rel w e hf hr)) q)))
           h)))

(a/theorem host-free-nh [w :- World, e :- EdgeRow] (=> (= (not-host e) true) (= (host-free w e) true))
  (intro h) (simp only [host-free h Bool.or_true]))
(a/theorem host-free-open [w :- World, e :- EdgeRow] (=> (= (root-shut w) false) (= (host-free w e) true))
  (intro h) (simp only [root-shut] at h) (simp only [host-free h Bool.not_false Bool.true_or]))
(a/theorem host-await-root [w :- World, d :- Nat] (=> (= (host-await-bad w d) false) (= (root-shut w) false))
  (intro h) (cases hr (root-shut w)) (case [false] (rfl)) (case [true] (simp [host-await-bad hr] at h)))
(a/theorem next-pos [w :- World] (=> (= (inv-sample w) true) (= (Nat.beq (:next-id w) 0) false))
  (intro h)
  (have p := (And.right (And.right (inv-parts w h))))
  (simp only [ids-ok ids-below Bool.and_eq_true Nat.blt_eq] at p)
  (have q := (And.left (And.right p)))
  (cases hb (Nat.beq (:next-id w) 0)) (case [false] (rfl))
  (case [true] (have z := (Nat.eq_of_beq_eq_true hb)) (omega)))
(a/theorem take-edge-nh [r :- RunRow, w :- World, x :- Nat] (=> (= (inv-sample w) true) (= (not-host (take-edge r (:next-id w) x)) true))
  (intro h) (simp only [not-host host-cred take-edge ek-wait ek-observe (next-pos w h)]))

;; ---- the handle part (gh-rest)
(a/theorem gk-rest-k0 [w :- World] (=> (= (gk-rest w) true) (= (gk0-rest w) true))
  (intro h) (simp only [gk-rest Bool.and_eq_true] at h) (exact (And.left h)))
(a/theorem gk-rest-gh [w :- World] (=> (= (gk-rest w) true) (= (gh-rest w) true))
  (intro h) (simp only [gk-rest Bool.and_eq_true] at h) (exact (And.right h)))
(a/theorem gk-rest-mk [w :- World] (=> (= (gk0-rest w) true) (= (gh-rest w) true) (= (gk-rest w) true))
  (intros h1 h2) (simp only [gk-rest h1 h2 Bool.and_self]))
(a/theorem gh-open [w :- World] (=> (= (:released w) false) (= (gh-rest w) true))
  (intro h) (simp only [gh-rest h Bool.not_false Bool.true_or]))
(a/theorem gh-mono [w :- World, w2 :- World]
  (=> (= (:released w2) (:released w))
      (=> (= (tbl-all h0-c (:comps w)) true) (= (tbl-all h0-c (:comps w2)) true))
      (=> (= (tbl-all h0-t (:tasks w)) true) (= (tbl-all h0-t (:tasks w2)) true))
      (=> (= (tbl-all h0-s (:sources w)) true) (= (tbl-all h0-s (:sources w2)) true))
      (= (gh-rest w) true) (= (gh-rest w2) true))
  (intros e hc ht hs h)
  (cases hr (:released w))
  (case [false] (exact (gh-open w2 (Eq.trans e hr))))
  (case [true]
    (simp only [gh-rest hz-all hr Bool.not_true Bool.false_or Bool.and_eq_true] at h)
    (simp only [gh-rest hz-all e hr (hc (And.left h)) (ht (And.left (And.right h))) (hs (And.right (And.right h)))
                Bool.not_true Bool.false_or Bool.and_self])))
;; a comps-only edit
(a/theorem gh-comps [w :- World, w2 :- World]
  (=> (= (:released w2) (:released w)) (= (:tasks w2) (:tasks w)) (= (:sources w2) (:sources w))
      (=> (= (tbl-all h0-c (:comps w)) true) (= (tbl-all h0-c (:comps w2)) true))
      (= (gh-rest w) true) (= (gh-rest w2) true))
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
  (=> (= (gh-rest w) true) (= (gh-rest (comp-upd w x f)) true))
  (intro h)
  (exact (gh-comps w (comp-upd w x f) (rfl) (rfl) (rfl)
           (fn [q :- (= (tbl-all h0-c (:comps w)) true)] (all-upd-keep CompRow comp-id x f h0-c hp (:comps w) q)) h)))
(a/theorem gh-task-upd [w :- World, x :- Nat, f :- (=> TaskRow TaskRow),
                        hp :- (forall [t :- TaskRow] (=> (= (h0-t t) true) (= (h0-t (f t)) true)))]
  (=> (= (gh-rest w) true) (= (gh-rest (task-upd w x f)) true))
  (intro h)
  (exact (gh-mono w (task-upd w x f) (rfl) (fn [q :- (= (tbl-all h0-c (:comps w)) true)] q)
           (fn [q :- (= (tbl-all h0-t (:tasks w)) true)] (all-upd-keep TaskRow task-id x f h0-t hp (:tasks w) q))
           (fn [q :- (= (tbl-all h0-s (:sources w)) true)] q) h)))
(a/theorem gh-source-upd [w :- World, x :- Nat, f :- (=> SourceRow SourceRow),
                          hp :- (forall [s :- SourceRow] (=> (= (h0-s s) true) (= (h0-s (f s)) true)))]
  (=> (= (gh-rest w) true) (= (gh-rest (source-upd w x f)) true))
  (intro h)
  (exact (gh-mono w (source-upd w x f) (rfl) (fn [q :- (= (tbl-all h0-c (:comps w)) true)] q)
           (fn [q :- (= (tbl-all h0-t (:tasks w)) true)] q)
           (fn [q :- (= (tbl-all h0-s (:sources w)) true)] (all-upd-keep SourceRow source-id x f h0-s hp (:sources w) q)) h)))
(a/theorem gh-comp-del [w :- World, x :- Nat] (=> (= (gh-rest w) true) (= (gh-rest (comp-del w x)) true))
  (intro h)
  (exact (gh-comps w (comp-del w x) (rfl) (rfl) (rfl)
           (fn [q :- (= (tbl-all h0-c (:comps w)) true)] (all-del-keep CompRow comp-id x h0-c (:comps w) q)) h)))
(a/theorem gh-mark-edge [w :- World, x :- Nat] (=> (= (gh-rest w) true) (= (gh-rest (mark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [mark-edge hf]) (exact h))
  (case [some e] (cases hm (:marked e))
    (case [true] (simp only [mark-edge hf hm]) (exact h))
    (case [false] (simp only [mark-edge hf hm])
      (exact (gh-comp-upd (edge-upd w x (edge-set-marked true)) (:creditor e) comp-inc-pending
               (hc-same comp-inc-pending (fn [c :- CompRow] (Eq.refl (:handles c)))) h)))))
(a/theorem gh-unmark-edge [w :- World, x :- Nat] (=> (= (gh-rest w) true) (= (gh-rest (unmark-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [unmark-edge hf]) (exact h))
  (case [some e] (cases hm (:marked e))
    (case [false] (simp only [unmark-edge hf hm]) (exact h))
    (case [true] (simp only [unmark-edge hf hm])
      (exact (gh-comp-upd (edge-upd w x (edge-set-marked false)) (:creditor e) comp-dec-pending
               (hc-same comp-dec-pending (fn [c :- CompRow] (Eq.refl (:handles c)))) h)))))
(a/theorem gh-remove-edge [w :- World, x :- Nat] (=> (= (gh-rest w) true) (= (gh-rest (remove-edge w x)) true))
  (intro h)
  (cases hf (edge-find w x))
  (case [none] (simp only [remove-edge hf]) (exact h))
  (case [some e] (cases hm (:marked e))
    (case [false] (simp only [remove-edge hf hm]) (exact h))
    (case [true] (simp only [remove-edge hf hm])
      (exact (gh-comp-upd (edge-del w x) (:creditor e) comp-dec-pending
               (hc-same comp-dec-pending (fn [c :- CompRow] (Eq.refl (:handles c)))) h)))))
(a/theorem gh-drop-cred [w :- World, a :- Nat] (=> (= (gh-rest w) true) (= (gh-rest (drop-cred-edges w a)) true))
  (intro h)
  (exact (gh-comp-upd (set-edges w (tbl-filter (cred-ne a) (:edges w))) a (comp-set-pending 0)
           (hc-same (comp-set-pending 0) (fn [c :- CompRow] (Eq.refl (:handles c)))) h)))
(a/theorem gh-drop-edges [w :- World, p :- (=> EdgeRow Bool)] (=> (= (gh-rest w) true) (= (gh-rest (drop-edges w p)) true))
  (intro h)
  (exact (gh-comps w (drop-edges w p) (rfl) (rfl) (rfl)
           (fn [q :- (= (tbl-all h0-c (:comps w)) true)] (resync-h0 (tbl-filter p (:edges w)) (:comps w) q)) h)))
(a/theorem gh-filter [w :- World, K :- (=> Nat Bool)] (=> (= (gh-rest w) true) (= (gh-rest (filter-world K w)) true))
  (intro h)
  (exact (gh-mono w (filter-world K w) (rfl)
           (fn [q :- (= (tbl-all h0-c (:comps w)) true)] (tbl-all-keep-same CompRow K comp-id h0-c (:comps w) q))
           (fn [q :- (= (tbl-all h0-t (:tasks w)) true)] (tbl-all-keep-same TaskRow K task-id h0-t (:tasks w) q))
           (fn [q :- (= (tbl-all h0-s (:sources w)) true)] (tbl-all-keep-same SourceRow K source-id h0-s (:sources w) q)) h)))

;; the rest part, combined
(a/theorem gk-rest-edge-upd [w :- World, x :- Nat, f :- (=> EdgeRow EdgeRow),
                             hk :- (forall [e :- EdgeRow] (= (:kind (f e)) (:kind e))),
                             hc :- (forall [e :- EdgeRow] (= (:creditor (f e)) (:creditor e)))]
  (=> (= (gk-rest w) true) (= (gk-rest (edge-upd w x f)) true))
  (intro h) (apply gk-rest-mk) (exact (gk0-rest-edge-upd w x f hk hc (gk-rest-k0 w h))) (exact (Eq.trans (rfl) (gk-rest-gh w h))))
(a/theorem gk-rest-mark-edge [w :- World, x :- Nat] (=> (= (gk-rest w) true) (= (gk-rest (mark-edge w x)) true))
  (intro h) (apply gk-rest-mk) (exact (gk0-rest-mark-edge w x (gk-rest-k0 w h))) (exact (gh-mark-edge w x (gk-rest-gh w h))))
(a/theorem gk-rest-unmark-edge [w :- World, x :- Nat] (=> (= (gk-rest w) true) (= (gk-rest (unmark-edge w x)) true))
  (intro h) (apply gk-rest-mk) (exact (gk0-rest-unmark-edge w x (gk-rest-k0 w h))) (exact (gh-unmark-edge w x (gk-rest-gh w h))))
(a/theorem gk-rest-remove-edge [w :- World, x :- Nat] (=> (= (gk-rest w) true) (= (gk-rest (remove-edge w x)) true))
  (intro h) (apply gk-rest-mk) (exact (gk0-rest-remove-edge w x (gk-rest-k0 w h))) (exact (gh-remove-edge w x (gk-rest-gh w h))))
(a/theorem gk-rest-drop-cred [w :- World, a :- Nat] (=> (= (gk-rest w) true) (= (gk-rest (drop-cred-edges w a)) true))
  (intro h) (apply gk-rest-mk) (exact (gk0-rest-drop-cred w a (gk-rest-k0 w h))) (exact (gh-drop-cred w a (gk-rest-gh w h))))
(a/theorem gk-rest-drop-act [w :- World, a :- Nat] (=> (= (gk-rest w) true) (= (gk-rest (drop-act w a)) true))
  (intro h) (apply gk-rest-mk) (exact (gk0-rest-drop-cred w a (gk-rest-k0 w h))) (exact (Eq.trans (rfl) (gh-drop-cred w a (gk-rest-gh w h)))))
(a/theorem gk-rest-drop-edges [w :- World, p :- (=> EdgeRow Bool)] (=> (= (gk-rest w) true) (= (gk-rest (drop-edges w p)) true))
  (intro h) (apply gk-rest-mk) (exact (gk0-rest-drop-edges w p (gk-rest-k0 w h))) (exact (gh-drop-edges w p (gk-rest-gh w h))))
(a/theorem gk-rest-filter [w :- World, K :- (=> Nat Bool)] (=> (= (gk-rest w) true) (= (gk-rest (filter-world K w)) true))
  (intro h) (apply gk-rest-mk) (exact (gk0-rest-filter w K (gk-rest-k0 w h))) (exact (gh-filter w K (gk-rest-gh w h))))
(a/theorem gk-rest-pub-upd [w :- World, x :- Nat, f :- (=> PubRow PubRow)] (=> (= (gk-rest w) true) (= (gk-rest (pub-upd w x f)) true))
  (intro h) (apply gk-rest-mk) (exact (gk0-rest-pub-upd w x f (gk-rest-k0 w h))) (exact (Eq.trans (rfl) (gk-rest-gh w h))))
(a/theorem gk-rest-insert [w :- World, e :- EdgeRow] (=> (= (host-free w e) true) (= (gk-rest w) true) (= (gk-rest (insert-edge-fresh w e)) true))
  (intros hf h) (apply gk-rest-mk) (exact (gk0-rest-insert w e hf (gk-rest-k0 w h))) (exact (Eq.trans (rfl) (gk-rest-gh w h))))
(a/theorem gk-insert-edge-fresh [w :- World, e :- EdgeRow]
  (=> (= (edge-ok-in w e) true) (= (host-free w e) true) (= (gk w) true) (= (gk (insert-edge-fresh w e)) true))
  (intros he hf h)
  (exact (gk-intro _ (insert-edge-fresh-inv-sample w e he (gk-sample w h)) (gk-rest-insert w e hf (gk-rest-of w h)))))
(a/theorem gk-insert-edge-checked [w :- World, e :- EdgeRow]
  (=> (= (host-free w e) true) (= (gk w) true) (= (gk (insert-edge-checked w e)) true))
  (intros hf h)
  (cases hk (edge-ok-in w e))
  (case [false] (simp only [insert-edge-checked hk]) (exact h))
  (case [true] (simp only [insert-edge-checked hk]) (exact (gk-insert-edge-fresh w e hk hf h))))
(a/theorem gk-rest-comp-del [w :- World, x :- Nat] (=> (= (gk-rest w) true) (= (gk-rest (comp-del w x)) true))
  (intro h) (apply gk-rest-mk) (exact (Eq.trans (rfl) (gk-rest-k0 w h))) (exact (gh-comp-del w x (gk-rest-gh w h))))
;; a row edit that keeps a zero count; one that sets 1 only while not released (handle-new's root-shut)
(a/theorem gk-rest-comp-upd [w :- World, x :- Nat, f :- (=> CompRow CompRow),
                             hz :- (forall [c :- CompRow] (=> (= (:handles c) 0) (= (:handles (f c)) 0)))]
  (=> (= (gk-rest w) true) (= (gk-rest (comp-upd w x f)) true))
  (intro h) (apply gk-rest-mk) (exact (Eq.trans (rfl) (gk-rest-k0 w h))) (exact (gh-comp-upd w x f (hc-keep f hz) (gk-rest-gh w h))))
(a/theorem gk-rest-task-upd [w :- World, x :- Nat, f :- (=> TaskRow TaskRow),
                             hz :- (forall [t :- TaskRow] (=> (= (:handles t) 0) (= (:handles (f t)) 0)))]
  (=> (= (gk-rest w) true) (= (gk-rest (task-upd w x f)) true))
  (intro h) (apply gk-rest-mk) (exact (Eq.trans (rfl) (gk-rest-k0 w h))) (exact (gh-task-upd w x f (ht-keep f hz) (gk-rest-gh w h))))
(a/theorem gk-rest-source-upd [w :- World, x :- Nat, f :- (=> SourceRow SourceRow),
                               hz :- (forall [s :- SourceRow] (=> (= (:handles s) 0) (= (:handles (f s)) 0)))]
  (=> (= (gk-rest w) true) (= (gk-rest (source-upd w x f)) true))
  (intro h) (apply gk-rest-mk) (exact (Eq.trans (rfl) (gk-rest-k0 w h))) (exact (gh-source-upd w x f (hs-keep f hz) (gk-rest-gh w h))))
(a/theorem gk-rest-open [w2 :- World]
  (=> (= (:released w2) false) (= (gk0-rest w2) true) (= (gk-rest w2) true))
  (intros hr h) (apply gk-rest-mk) (exact h) (exact (gh-open w2 hr)))
(a/theorem root-open [w :- World] (=> (= (root-shut w) false) (= (:released w) false))
  (intro h) (simp only [root-shut] at h) (exact h))
(a/theorem body-root [w :- World, st :- Nat] (=> (= (body-shut w st) false) (= (root-shut w) false))
  (intro h) (cases hr (root-shut w)) (case [false] (rfl)) (case [true] (simp [body-shut hr Bool.or_true Bool.true_or] at h)))
(a/theorem cc-root [w :- World, st :- Nat] (=> (= (cc-shut w st) false) (= (root-shut w) false))
  (intro h) (cases hr (root-shut w)) (case [false] (rfl)) (case [true] (simp [cc-shut hr Bool.or_true] at h)))

;; ---- the GK copy
;; threaded: every theorem between a raw0 arm guarded by root-shut/body-shut/cc-shut and a row creation
;; with handles 1 (or handle-new's h1) takes `hr0 : root-shut w = false` after its binders
(def ^:private gk-threaded
  '[inv-create-comp-raw t3-inv t3-top-inv inv-create-link-cur t-create-link-inv t-create-link-top-inv
    inv-create-source-cur t1-full-inv t1-body-inv inv-create-stream-cur t1-stream-inv inv-stream-rows t1-top-inv
    t1-top-full-inv inv-spawn-rows t4-inv t4-top-inv inv-link-demand-raw t-link-demand-inv inv-link-next-raw
    link-realize-raw-inv t-link-realize-inv inv-append-raw t-append-inv
    t-handle-new-inv new-task-handle-inv new-source-handle-inv])
(defn- nbinders [n] (count (take-nth 3 (nth (@#'spindel.v2.inv.copier/theorem-source n) 2))))
(def GK (mk-bundle 'gk [] "gk-"
          (merge {'inv-comp-upd ['(fn [c :- CompRow, z :- (= (:handles c) 0)] z) 5]
                  'inv-task-upd ['(fn [t :- TaskRow, z :- (= (:handles t) 0)] z) 4]
                  'inv-source-upd ['(fn [t :- SourceRow, z :- (= (:handles t) 0)] z) 4]
                  'inv-serve-or ['(fn [t :- SourceRow, z :- (= (:handles t) 0)] z) 5]
                  'inv-comp-ins-fresh ['hr0 2] 'inv-task-ins-fresh ['hr0 2] 'inv-source-ins-fresh ['hr0 2]}
                 (into {} (for [n gk-threaded] [n ['hr0 (nbinders n)]])))))
(swap! (:renames GK) assoc 'inv-parts 'gk-parts
       'insert-edge-fresh-inv-sample 'gk-insert-edge-fresh 'inv-insert-edge-checked 'gk-insert-edge-checked)

(defpart GK :reads '[comps edges pending-act pins pubs released sources tasks])
(prim! GK 'inv-edge-upd '(gk-rest-edge-upd w x f hk hc R))
(prim! GK 'mark-edge-inv-sample '(gk-rest-mark-edge w x R))
(prim! GK 'unmark-edge-inv-sample '(gk-rest-unmark-edge w x R))
(prim! GK 'inv-remove-edge '(gk-rest-remove-edge w x R))
(prim! GK 'inv-drop-cred '(gk-rest-drop-cred w a R))
(prim! GK 'inv-drop-act '(gk-rest-drop-act w a R))
(prim! GK 'inv-drop-edges '(gk-rest-drop-edges w p R))
(prim! GK 'inv-filter-world '(gk-rest-filter w K R))
(prim! GK 'inv-pub-upd '(gk-rest-pub-upd w x f R))
(prim! GK 'inv-comp-del-unref '(gk-rest-comp-del w x R))

;; row edits: a zero count stays zero (default: the count is copied); handle-new's h1 only while not released
(a/theorem gk-comp-upd [w :- World, x :- Nat, f :- (=> CompRow CompRow),
                        hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                        hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c))),
                        hz :- (forall [c :- CompRow] (=> (= (:handles c) 0) (= (:handles (f c)) 0)))]
  (=> (= (gk w) true) (= (gk (comp-upd w x f)) true))
  (intro h) (exact (gk-intro _ (inv-comp-upd w x f hid hp (gk-sample w h)) (gk-rest-comp-upd w x f hz (gk-rest-of w h)))))
(a/theorem gk-task-upd [w :- World, x :- Nat, f :- (=> TaskRow TaskRow),
                        hf :- (forall [r :- TaskRow] (= (task-id (f r)) (task-id r))),
                        hz :- (forall [t :- TaskRow] (=> (= (:handles t) 0) (= (:handles (f t)) 0)))]
  (=> (= (gk w) true) (= (gk (task-upd w x f)) true))
  (intro h) (exact (gk-intro _ (inv-task-upd w x f hf (gk-sample w h)) (gk-rest-task-upd w x f hz (gk-rest-of w h)))))
(a/theorem gk-source-upd [w :- World, x :- Nat, f :- (=> SourceRow SourceRow),
                          hf :- (forall [r :- SourceRow] (= (source-id (f r)) (source-id r))),
                          hz :- (forall [t :- SourceRow] (=> (= (:handles t) 0) (= (:handles (f t)) 0)))]
  (=> (= (gk w) true) (= (gk (source-upd w x f)) true))
  (intro h) (exact (gk-intro _ (inv-source-upd w x f hf (gk-sample w h)) (gk-rest-source-upd w x f hz (gk-rest-of w h)))))
(a/theorem gk-comp-upd-open [w :- World, x :- Nat, f :- (=> CompRow CompRow),
                             hid :- (forall [c :- CompRow] (= (comp-id (f c)) (comp-id c))),
                             hp :- (forall [c :- CompRow] (= (:pending (f c)) (:pending c)))]
  (=> (= (root-shut w) false) (= (gk w) true) (= (gk (comp-upd w x f)) true))
  (intros hr0 h) (exact (gk-intro _ (inv-comp-upd w x f hid hp (gk-sample w h)) (gk-rest-open (comp-upd w x f) (root-open w hr0) (Eq.trans (rfl) (gk-rest-k0 w (gk-rest-of w h)))))))
(a/theorem gk-task-upd-open [w :- World, x :- Nat, f :- (=> TaskRow TaskRow),
                             hf :- (forall [r :- TaskRow] (= (task-id (f r)) (task-id r)))]
  (=> (= (root-shut w) false) (= (gk w) true) (= (gk (task-upd w x f)) true))
  (intros hr0 h) (exact (gk-intro _ (inv-task-upd w x f hf (gk-sample w h)) (gk-rest-open (task-upd w x f) (root-open w hr0) (Eq.trans (rfl) (gk-rest-k0 w (gk-rest-of w h)))))))
(a/theorem gk-source-upd-open [w :- World, x :- Nat, f :- (=> SourceRow SourceRow),
                               hf :- (forall [r :- SourceRow] (= (source-id (f r)) (source-id r)))]
  (=> (= (root-shut w) false) (= (gk w) true) (= (gk (source-upd w x f)) true))
  (intros hr0 h) (exact (gk-intro _ (inv-source-upd w x f hf (gk-sample w h)) (gk-rest-open (source-upd w x f) (root-open w hr0) (Eq.trans (rfl) (gk-rest-k0 w (gk-rest-of w h)))))))
;; creations (handles 1): only while not released
(a/theorem gk-comp-ins-fresh [w :- World, r :- CompRow]
  (=> (= (root-shut w) false) (= (comp-id r) (:next-id w)) (= (:pending r) (marked-in (:id r) (:edges w)))
      (= (gk w) true) (= (gk (bump (comp-ins w r))) true))
  (intros hr0 hr hp h) (exact (gk-intro _ (inv-comp-ins-fresh w r hr hp (gk-sample w h)) (gk-rest-open (bump (comp-ins w r)) (root-open w hr0) (Eq.trans (rfl) (gk-rest-k0 w (gk-rest-of w h)))))))
(a/theorem gk-task-ins-fresh [w :- World, r :- TaskRow]
  (=> (= (root-shut w) false) (= (task-id r) (:next-id w)) (= (gk w) true) (= (gk (bump (task-ins w r))) true))
  (intros hr0 hr h) (exact (gk-intro _ (inv-task-ins-fresh w r hr (gk-sample w h)) (gk-rest-open (bump (task-ins w r)) (root-open w hr0) (Eq.trans (rfl) (gk-rest-k0 w (gk-rest-of w h)))))))
(a/theorem gk-source-ins-fresh [w :- World, r :- SourceRow]
  (=> (= (root-shut w) false) (= (source-id r) (:next-id w)) (= (gk w) true) (= (gk (bump (source-ins w r))) true))
  (intros hr0 hr h) (exact (gk-intro _ (inv-source-ins-fresh w r hr (gk-sample w h)) (gk-rest-open (bump (source-ins w r)) (root-open w hr0) (Eq.trans (rfl) (gk-rest-k0 w (gk-rest-of w h)))))))
(swap! (:renames GK) assoc
       'inv-comp-upd 'gk-comp-upd 'inv-comp-upd-z 'gk-comp-upd 'inv-comp-upd-open 'gk-comp-upd-open
       'inv-task-upd 'gk-task-upd 'inv-task-upd-z 'gk-task-upd 'inv-task-upd-open 'gk-task-upd-open
       'inv-source-upd 'gk-source-upd 'inv-source-upd-z 'gk-source-upd 'inv-source-upd-open 'gk-source-upd-open
       'inv-comp-ins-fresh 'gk-comp-ins-fresh 'inv-task-ins-fresh 'gk-task-ins-fresh 'inv-source-ins-fresh 'gk-source-ins-fresh)

;; patches compose (a theorem may get several)
(defn- gk-patch! [n f] (let [old (get @(:patches GK) n identity)] (patch! GK n (comp f old))))

;; a source theorem with one more premise (named hn) in front
(defn- add-premise [prem hn form]
  (let [[hd nm binders stmt & proof] form
        stmt2 (if (and (seq? stmt) (= '=> (first stmt))) (apply list '=> prem (rest stmt)) (list '=> prem stmt))
        [t1 & more] proof
        t1b (cond (and (seq? t1) (= 'intro (first t1))) [(list 'intros hn (second t1))]
                  (and (seq? t1) (= 'intros (first t1))) [(apply list 'intros hn (rest t1))]
                  :else [(list 'intro hn) t1])]
    (apply list hd nm binders stmt2 (concat t1b more))))
(defn- repl-form [old new] (fn [form] (subst-forms #(= % old) (fn [_] new) form)))

;; edges that are no host root: track, reactivation (dep edges), await (a dep edge, or a wait edge
;; whose creditor is the fresh activation), take (a wait edge, creditor the fresh activation)
(gk-patch! 'inv-track-raw
  (repl-form '(insert-edge-fresh-inv-sample w (track-edge r x s k) (track-edge-ok w r x s k hc hs) h)
             '(insert-edge-fresh-inv-sample w (track-edge r x s k) (track-edge-ok w r x s k hc hs) (host-free-nh w (track-edge r x s k) (Eq.refl true)) h)))
(gk-patch! 'inv-react-add
  (repl-form '(inv-insert-edge-checked w _ h) '(inv-insert-edge-checked w (valid-edge w c v) (host-free-nh w (valid-edge w c v) (Eq.refl true)) h)))
(a/theorem await-edge-nh [w :- World, r :- RunRow, a :- Nat, mode :- Nat, k :- Nat, d :- Nat]
  (=> (= (Nat.beq a 0) false) (= (not-host (await-edge w r a mode k d)) true))
  (intro ha)
  (cases hd (as-dep w r d))
  (all_goals (simp only [not-host host-cred await-edge hd ek-wait ek-dep ek-observe ha])))
(gk-patch! 'inv-await-step
  (fn [form] (->> form
                  (add-premise '(= (Nat.beq a 0) false) 'ha0)
                  (subst-forms #(= % '(inv-insert-edge-checked _ _ h))
                               (fn [_] '(inv-insert-edge-checked _ _ (host-free-nh _ _ (await-edge-nh _ r a mode k d ha0)) h))))))
(gk-patch! 'inv-await-wire
  (fn [form] (->> form
                  (add-premise '(= (Nat.beq a 0) false) 'ha0)
                  (subst-forms #(= % '(inv-await-step r a mode k acc d h)) (fn [_] '(inv-await-step r a mode k acc d ha0 h))))))
(gk-patch! 'inv-await-raw
  (fn [form] (subst-forms #(and (seq? %) (= 'inv-await-wire (first %)))
                          (fn [[hd r n m k ds & more]] (apply list hd r n m k ds '(next-pos w (gk-sample w h)) more)) form)))
(gk-patch! 'inv-take-park
  (repl-form '(inv-insert-edge-checked _ _ (inv-act-ins-fresh w (take-act w r k) (rfl) h))
             '(inv-insert-edge-checked _ (take-edge r (:next-id w) x) (host-free-nh _ _ (take-edge-nh r w x (gk-sample w h)))
                (inv-act-ins-fresh w (take-act w r k) (rfl) h))))

;; host roots: T8 and T22 add one, refused by raw0 once released (root-shut, host-await-bad); pin
(gk-patch! 't8-full-inv
  (fn [form] (->> form
                  (add-premise '(= (root-shut w) false) 'hr0)
                  (subst-forms #(= % '(insert-edge-fresh-inv-sample w (observe-edge w d cb) he h))
                               (fn [_] '(insert-edge-fresh-inv-sample w (observe-edge w d cb) he (host-free-open w _ hr0) h))))))
(gk-patch! 't8-obs-inv
  (fn [form] (->> form
                  (add-premise '(= (root-shut w) false) 'hr0)
                  (subst-forms #(= % '(t8-full-inv w d cb fresh h)) (fn [_] '(t8-full-inv w d cb fresh hr0 h))))))
(gk-patch! 'inv-host-await-raw
  (fn [form] (->> form
                  (add-premise '(= (root-shut w) false) 'hr0)
                  (subst-forms #(= % '(inv-insert-edge-checked w (host-wait-edge d) h))
                               (fn [_] '(inv-insert-edge-checked w (host-wait-edge d) (host-free-open w _ hr0) h))))))
(gk-patch! 't22-inv
  (fn [form] (->> form
                  (add-premise '(= (root-shut w) false) 'hr0)
                  (subst-forms #(= % '(inv-host-await-raw w d h)) (fn [_] '(inv-host-await-raw w d hr0 h))))))
(a/theorem gk0-set-pins-cons [w :- World, x :- Nat] (=> (= (root-shut w) false) (= (gk0-rest w) true) (= (gk0-rest (set-pins w (List.cons Nat x (:pins w)))) true))
  (intros hr h) (simp only [root-shut] at hr)
  (simp only [gk0-rest Bool.and_eq_true] at h)
  (have hr2 (= (:released (set-pins w (List.cons Nat x (:pins w)))) false)) (exact hr)
  (simp only [gk0-rest hr2 Bool.not_false Bool.or_true Bool.and_true])
  (simp only [Bool.and_eq_true]) (exact (And.intro (And.left h) (And.intro (And.left (And.right h)) True.intro))))
(a/theorem nat-del1-empty [x :- Nat, xs :- (List Nat)] (=> (= (nats-empty xs) true) (= (nats-empty (nat-del1 x xs)) true))
  (intro h) (cases xs) (case [nil] (simp only [nat-del1 nats-empty])) (case [cons y t] (simp [nats-empty] at h)))
(a/theorem gk0-set-pins-del [w :- World, x :- Nat] (=> (= (gk0-rest w) true) (= (gk0-rest (set-pins w (nat-del1 x (:pins w)))) true))
  (intro h)
  (simp only [gk0-rest Bool.and_eq_true] at h)
  (have r := (And.right (And.right h)))
  (cases hr (:released w))
  (case [false]
    (have hr2 (= (:released (set-pins w (nat-del1 x (:pins w)))) false)) (exact hr)
    (simp only [gk0-rest hr2 Bool.not_false Bool.or_true Bool.and_true])
    (simp only [Bool.and_eq_true]) (exact (And.intro (And.left h) (And.intro (And.left (And.right h)) True.intro))))
  (case [true]
    (simp only [hr Bool.not_true Bool.false_or Bool.and_eq_true] at r)
    (have hr2 (= (:released (set-pins w (nat-del1 x (:pins w)))) true)) (exact hr)
    (have p := (nat-del1-empty x (:pins w) (And.left r)))
    (have e1 (= (:pins (set-pins w (nat-del1 x (:pins w)))) (nat-del1 x (:pins w)))) (rfl)
    (simp only [gk0-rest hr2 e1 p (And.left h) (And.left (And.right h)) (And.right r) Bool.not_true Bool.false_or Bool.and_self])))
(a/theorem gk-set-pins-cons [w :- World, x :- Nat] (=> (= (root-shut w) false) (= (gk-rest w) true) (= (gk-rest (set-pins w (List.cons Nat x (:pins w)))) true))
  (intros hr h) (apply gk-rest-mk) (exact (gk0-set-pins-cons w x hr (gk-rest-k0 w h))) (exact (Eq.trans (rfl) (gk-rest-gh w h))))
(a/theorem gk-set-pins-del [w :- World, x :- Nat] (=> (= (gk-rest w) true) (= (gk-rest (set-pins w (nat-del1 x (:pins w)))) true))
  (intro h) (apply gk-rest-mk) (exact (gk0-set-pins-del w x (gk-rest-k0 w h))) (exact (Eq.trans (rfl) (gk-rest-gh w h))))
(override! GK 't20-pin-inv '[]
  '(a/theorem t20-pin-gk [w :- World, x :- Nat]
     (=> (= (root-shut w) false) (= (gk w) true) (= (gk (:world (t20-pin w x))) true))
     (intros hr0 h)
     (cases hg (pin-target w x))
     (simp only [t20-pin hg refuse]) (exact h)
     (simp only [t20-pin hg accept])
     (exact (gk-intro _ (inv-set-pins w (List.cons Nat x (:pins w)) (gk-sample w h)) (gk-set-pins-cons w x hr0 (gk-rest-of w h))))))
(override! GK 't20-unpin-inv '[]
  '(a/theorem t20-unpin-gk [w :- World, x :- Nat]
     (=> (= (gk w) true) (= (gk (:world (t20-unpin w x))) true))
     (intro h)
     (cases hm (nat-mem x (:pins w)))
     (simp only [t20-unpin hm refuse]) (exact h)
     (simp only [t20-unpin hm accept])
     (exact (gk-intro _ (inv-set-pins w (nat-del1 x (:pins w)) (gk-sample w h)) (gk-set-pins-del w x (gk-rest-of w h))))))
;; T21 revokes the roots: no pin, no host-creditor edge, no pending activation
(a/theorem gk0-rest-revoke [w :- World] (=> (= (gk0-rest w) true) (= (gk0-rest (revoke-roots w)) true))
  (intro h)
  (simp only [gk0-rest Bool.and_eq_true] at h)
  (have e1 (= (:edges (revoke-roots w)) (tbl-filter not-host (:edges w)))) (rfl)
  (have e2 (= (:pubs (revoke-roots w)) (:pubs w))) (rfl)
  (have e3 (= (:released (revoke-roots w)) true)) (rfl)
  (have e4 (= (:pins (revoke-roots w)) (List.nil Nat))) (rfl)
  (have e5 (= (:pending-act (revoke-roots w)) 0)) (rfl)
  (simp only [gk0-rest e1 e2 e3 e4 e5 (And.left (And.right h)) (tbl-all-filter-self EdgeRow not-host (:edges w))
              nats-empty Nat.beq_refl Bool.not_true Bool.false_or Bool.and_self]))
;; ---- T21: revoke, then zero every handle (the fold over the comp/task/source/pub ids)
(a/defn h0-or-c [ys :- (List Nat), c :- CompRow] Bool (Bool.or (h0-c c) (nat-mem (comp-id c) ys)))
(a/defn h0-or-t [ys :- (List Nat), t :- TaskRow] Bool (Bool.or (h0-t t) (nat-mem (task-id t) ys)))
(a/defn h0-or-s [ys :- (List Nat), s :- SourceRow] Bool (Bool.or (h0-s s) (nat-mem (source-id s) ys)))
(a/theorem fold-h0-c [ys :- (List Nat)]
  (forall [w :- World] (=> (= (tbl-all (h0-or-c ys) (:comps w)) true) (= (tbl-all h0-c (:comps (nat-fold comp-h0-at w ys))) true)))
  (induction ys)
  (case [nil]
    (intros w h) (simp only [nat-fold])
    (apply (tbl-all-mono CompRow (h0-or-c (List.nil Nat)) h0-c _ (:comps w) h))
    (intros r q) (simp only [h0-or-c nat-mem Bool.or_false] at q) (exact q))
  (case [cons y t ih]
    (intros w h) (simp only [nat-fold]) (apply (ih (comp-h0-at w y)))
    (have hin (forall [r :- CompRow] (=> (= (h0-or-c (List.cons Nat y t) r) true) (= (Nat.beq (comp-id r) y) true) (= (h0-or-c t (comp-h0 r)) true))))
    (intros r h1 h2) (simp only [h0-or-c h0-c comp-h0 Nat.beq_refl Bool.true_or])
    (have hout (forall [r :- CompRow] (=> (= (h0-or-c (List.cons Nat y t) r) true) (= (Nat.beq (comp-id r) y) false) (= (h0-or-c t r) true))))
    (intros r h1 h2) (simp only [h0-or-c nat-mem (beq-symm-false _ _ h2)] at h1) (simp only [h0-or-c]) (exact h1)
    (exact (tbl-all-upd CompRow comp-id y comp-h0 _ _ hin hout (:comps w) h))))
(a/theorem fold-h0-t [ys :- (List Nat)]
  (forall [w :- World] (=> (= (tbl-all (h0-or-t ys) (:tasks w)) true) (= (tbl-all h0-t (:tasks (nat-fold task-h0-at w ys))) true)))
  (induction ys)
  (case [nil]
    (intros w h) (simp only [nat-fold])
    (apply (tbl-all-mono TaskRow (h0-or-t (List.nil Nat)) h0-t _ (:tasks w) h))
    (intros r q) (simp only [h0-or-t nat-mem Bool.or_false] at q) (exact q))
  (case [cons y t ih]
    (intros w h) (simp only [nat-fold]) (apply (ih (task-h0-at w y)))
    (have hin (forall [r :- TaskRow] (=> (= (h0-or-t (List.cons Nat y t) r) true) (= (Nat.beq (task-id r) y) true) (= (h0-or-t t (task-h0 r)) true))))
    (intros r h1 h2) (simp only [h0-or-t h0-t task-h0 Nat.beq_refl Bool.true_or])
    (have hout (forall [r :- TaskRow] (=> (= (h0-or-t (List.cons Nat y t) r) true) (= (Nat.beq (task-id r) y) false) (= (h0-or-t t r) true))))
    (intros r h1 h2) (simp only [h0-or-t nat-mem (beq-symm-false _ _ h2)] at h1) (simp only [h0-or-t]) (exact h1)
    (exact (tbl-all-upd TaskRow task-id y task-h0 _ _ hin hout (:tasks w) h))))
(a/theorem fold-h0-s [ys :- (List Nat)]
  (forall [w :- World] (=> (= (tbl-all (h0-or-s ys) (:sources w)) true) (= (tbl-all h0-s (:sources (nat-fold source-h0-at w ys))) true)))
  (induction ys)
  (case [nil]
    (intros w h) (simp only [nat-fold])
    (apply (tbl-all-mono SourceRow (h0-or-s (List.nil Nat)) h0-s _ (:sources w) h))
    (intros r q) (simp only [h0-or-s nat-mem Bool.or_false] at q) (exact q))
  (case [cons y t ih]
    (intros w h) (simp only [nat-fold]) (apply (ih (source-h0-at w y)))
    (have hin (forall [r :- SourceRow] (=> (= (h0-or-s (List.cons Nat y t) r) true) (= (Nat.beq (source-id r) y) true) (= (h0-or-s t (source-h0 r)) true))))
    (intros r h1 h2) (simp only [h0-or-s h0-s source-h0 Nat.beq_refl Bool.true_or])
    (have hout (forall [r :- SourceRow] (=> (= (h0-or-s (List.cons Nat y t) r) true) (= (Nat.beq (source-id r) y) false) (= (h0-or-s t r) true))))
    (intros r h1 h2) (simp only [h0-or-s nat-mem (beq-symm-false _ _ h2)] at h1) (simp only [h0-or-s]) (exact h1)
    (exact (tbl-all-upd SourceRow source-id y source-h0 _ _ hin hout (:sources w) h))))

;; the folds are frames for the other tables (`ff-<field>-<fold>`)
(doseq [[fld ty] '[[comps (List CompRow)] [tasks (List TaskRow)] [sources (List SourceRow)] [released Bool]]
        fo '[comp-h0-at task-h0-at source-h0-at pub-h0-at]
        :when (not (#{'[comps comp-h0-at] '[tasks task-h0-at] '[sources source-h0-at]} [fld fo]))]
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
  (have t1 (= (tbl-all (h0-or-t (tbl-ids task-id (:tasks w))) (:tasks (nat-fold comp-h0-at w (tbl-ids comp-id (:comps w))))) true))
  (rw [ff-tasks-comp-h0-at]) (exact t0)
  (have t2 := (fold-h0-t (tbl-ids task-id (:tasks w)) _ t1))
  (have s1 (= (tbl-all (h0-or-s (tbl-ids source-id (:sources w))) (:sources (nat-fold task-h0-at (nat-fold comp-h0-at w (tbl-ids comp-id (:comps w))) (tbl-ids task-id (:tasks w))))) true))
  (rw [ff-sources-task-h0-at ff-sources-comp-h0-at]) (exact s0)
  (have s2 := (fold-h0-s (tbl-ids source-id (:sources w)) _ s1))
  (simp only [zero-handles hz-all ff-comps-pub-h0-at ff-comps-source-h0-at ff-comps-task-h0-at
              ff-tasks-pub-h0-at ff-tasks-source-h0-at ff-sources-pub-h0-at c1 t2 s2 Bool.and_self]))

(a/theorem zero-handles-rel [w :- World] (= (:released (zero-handles w)) (:released w))
  (simp only [zero-handles ff-released-pub-h0-at ff-released-source-h0-at ff-released-task-h0-at ff-released-comp-h0-at]))

(a/theorem gk0-zero-handles [w :- World] (=> (= (gk0-rest w) true) (= (gk0-rest (zero-handles w)) true))
  (intro h)
  (have hp (forall [v :- World, y :- Nat] (=> (= (gk0-rest v) true) (= (gk0-rest (pub-h0-at v y)) true))))
  (intros v y q) (exact (gk0-rest-pub-upd v y pub-h0 q))
  (have hs (forall [v :- World, y :- Nat] (=> (= (gk0-rest v) true) (= (gk0-rest (source-h0-at v y)) true))))
  (intros v y q) (exact (Eq.trans (rfl) q))
  (have ht (forall [v :- World, y :- Nat] (=> (= (gk0-rest v) true) (= (gk0-rest (task-h0-at v y)) true))))
  (intros v y q) (exact (Eq.trans (rfl) q))
  (have hc (forall [v :- World, y :- Nat] (=> (= (gk0-rest v) true) (= (gk0-rest (comp-h0-at v y)) true))))
  (intros v y q) (exact (Eq.trans (rfl) q))
  (simp only [zero-handles])
  (exact (nat-fold-pres gk0-rest pub-h0-at hp _ _ (nat-fold-pres gk0-rest source-h0-at hs _ _
           (nat-fold-pres gk0-rest task-h0-at ht _ _ (nat-fold-pres gk0-rest comp-h0-at hc _ _ h))))))

(a/theorem gk-zero-revoke [w :- World] (=> (= (gk w) true) (= (gk (zero-handles (revoke-roots w))) true))
  (intro h)
  (have k0 := (gk0-zero-handles _ (gk0-rest-revoke w (gk-rest-k0 w (gk-rest-of w h)))))
  (have hr (= (:released (zero-handles (revoke-roots w))) true)) (exact (Eq.trans (zero-handles-rel _) (rfl)))
  (have g (= (gh-rest (zero-handles (revoke-roots w))) true))
  (simp only [gh-rest hr (zero-handles-hz (revoke-roots w)) Bool.or_true])
  (exact (gk-intro _ (inv-zero-handles _ (inv-revoke-roots w (gk-sample w h))) (gk-rest-mk _ k0 g))))

;; T21 (`t-release-world`): revoke, zero the handles, close the root scope
(override! GK 't-release-world-inv '[inv-run-cascade]
  '(a/theorem t-release-world-gk [w :- World]
     (=> (= (gk w) true) (= (gk (:world (t-release-world w))) true))
     (intro h)
     (cases hr (:released w))
     (simp only [t-release-world hr accept release-world-raw])
     (exact (gk-run-cascade _ _ (gk-zero-revoke w h)))
     (simp only [t-release-world hr refuse]) (exact h)))

;; serve-or's `keep` row edit keeps a zero count (its callers: enqueue, permit)
(override! GK 'inv-serve-or '[inv-fire-edge]
  '(a/theorem gk-serve-or [w :- World, x :- Nat, res :- RunResult, keep :- (=> SourceRow SourceRow),
                           hk :- (forall [s :- SourceRow] (= (source-id (keep s)) (source-id s))),
                           hz :- (forall [t :- SourceRow] (=> (= (:handles t) 0) (= (:handles (keep t)) 0)))]
     (=> (= (gk w) true) (= (gk (serve-or w x res keep)) true))
     (intro h)
     (cases hz0 (Nat.beq (oldest-waiter w x) 0))
     (simp only [serve-or hz0]) (exact (gk-fire-edge res w _ h))
     (simp only [serve-or hz0]) (exact (gk-source-upd w x keep hk hz h))))

;; the handle clause: a row edit that sets the count (dec/h0) states that it keeps a zero count
;; (`-z`); handle-new's h1 takes the guard (`-open`)
(def ^:private hz-info '{inv-comp-upd [CompRow 5] inv-task-upd [TaskRow 4] inv-source-upd [SourceRow 4]})
(def ^:private hz-dec '#{comp-dec-handles task-dec-handles source-dec-handles})
(def ^:private hz-h0 '#{comp-h0 task-h0 source-h0})
(def ^:private hz-h1 '#{comp-h1 task-h1 source-h1})
;; row functions that keep the count only per case
(a/theorem task-cancel-result-hk [t :- TaskRow] (= (:handles (task-cancel-result t)) (:handles t))
  (cases hb (Nat.beq (:tag (:result t)) res-none)) (all_goals (simp only [task-cancel-result hb])))
(a/theorem source-consume-hk [s :- SourceRow] (= (:handles (source-consume s)) (:handles s))
  (cases ha (src-available s))
  (all_goals (simp only [source-consume ha]))
  (cases hk (Nat.beq (:kind s) sk-mailbox)) (all_goals (simp only [hk])))
(def ^:private hz-hk '{task-cancel-result task-cancel-result-hk source-consume source-consume-hk})
(defn- hz-patch [form]
  (subst-forms
    (fn [y] (and (seq? y) (hz-info (first y)) (> (count y) 3) (some #(contains? % (nth y 3)) [hz-dec hz-h0 hz-h1 hz-hk])))
    (fn [y] (let [[row k] (hz-info (first y)) f (nth y 3) args (vec (rest y))
                  pf (cond
                       (hz-hk f) (list 'fn ['c :- row 'z :- '(= (:handles c) 0)] (list 'Eq.trans (list (hz-hk f) 'c) 'z))
                       (hz-dec f)
                       (list 'fn ['c :- row 'z :- '(= (:handles c) 0)] '(sub1-zero (:handles c) z))
                       :else (list 'fn ['c :- row 'z :- '(= (:handles c) 0)] '(Eq.refl 0)))]
              (if (hz-h1 f)
                (apply list (symbol (str (first y) "-open")) (concat (take k args) ['hr0] (drop k args)))
                (apply list (symbol (str (first y) "-z")) (concat (take k args) [pf] (drop k args))))))
    form))
(doseq [n gk-threaded] (gk-patch! n #(add-premise '(= (root-shut w) false) 'hr0 %)))
(doseq [[n _] @@#'spindel.v2.inv.copier/source-theorems] (gk-patch! n hz-patch))

;; raw0: the guards give the hypotheses
(def ^:private gk-raw0-guard
  '{t1-body-inv (body-root w st hc) t4-inv (body-root w st hc) t3-inv (cc-root w st hc) t-create-link-inv (cc-root w st hc)
    t1-top-full-inv hc t3-top-inv hc t4-top-inv hc t-handle-new-inv hc t-create-link-top-inv hc t-link-demand-inv hc
    t-link-realize-inv hc t-append-inv hc})
(gk-patch! 'raw0-inv
  (fn [form] (clojure.walk/postwalk
               (fn [y] (if (and (seq? y) (contains? gk-raw0-guard (first y)))
                         (list (list 'fn '[hr0 :- (= (root-shut w) false)] y) (gk-raw0-guard (first y)))
                         y))
               form)))
(gk-patch! 'raw0-inv
  (fn [form] (->> form
                  (subst-forms #(= % '(t8-obs-inv w _ _ _ h)) (fn [_] '(t8-obs-inv w _ _ _ hc h)))
                  (subst-forms #(= % '(t20-pin-inv w _ h)) (fn [_] '(t20-pin-inv w _ hc h)))
                  (subst-forms #(= % '(t22-inv w _ _ h)) (fn [_] '(t22-inv w _ _ (host-await-root w _ hc) h))))))

(lcopy! GK 'raw-inv)
(lcopy! GK 'inv-normalize)

(a/theorem gk-rule-r-round [w :- World]
  (=> (= (gk w) true) (= (filter-safe (normalize w)) true) (= (gk (rule-r-round w)) true))
  (intros h hf)
  (simp only [rule-r-round])
  (rw [rule-r-filter-eq])
  (exact (gk-filter-world _ (keep-fn (normalize w)) (gk-normalize w h) hf)))

(a/theorem gk-rr-loop [fuel :- (List Nat)]
  (forall [w0 :- World] (=> (= (gk w0) true) (= (rr-safe fuel w0) true) (= (gk (rr-loop fuel (rule-r-round w0))) true)))
  (induction fuel)
  (case [nil] (intros w0 h hs) (simp only [rr-safe] at hs) (simp only [rr-loop]) (exact (gk-rule-r-round w0 h hs)))
  (case [cons x f ih]
    (intros w0 h hs)
    (simp only [rr-safe Bool.and_eq_true] at hs)
    (have h1 := (gk-rule-r-round w0 h (And.left hs)))
    (cases ho (no-orphans (rule-r-round w0)))
    (case [false] (simp only [ho] at hs) (simp only [rr-loop ho]) (exact (ih (rule-r-round w0) h1 (And.right hs))))
    (case [true] (simp only [rr-loop ho]) (exact h1))))

(a/theorem gk-rule-r [w :- World]
  (=> (= (gk w) true) (= (rule-r-safe w) true) (= (gk (rule-r w)) true))
  (intros h hs) (simp only [rule-r-safe] at hs) (simp only [rule-r]) (exact (gk-rr-loop (rr-fuel w) w h hs)))

(a/theorem step-gk [w :- World, it :- Item]
  (=> (= (gk w) true) (= (rule-r-safe (:world (raw w it))) true) (= (gk (:world (world-step w it))) true))
  (intros h hs)
  (cases ha (:accepted (raw w it)))
  (case [false] (have e1 := (step-refuse w it ha)) (simp only [e1 refuse]) (exact h))
  (case [true] (have e2 := (step-accepted w it ha)) (rw [e2]) (exact (gk-rule-r (:world (raw w it)) (raw-gk w it h) hs))))

;; Theorem (K): no pending activation, no publication, and once released no pin and no host-creditor
;; edge, through every step from a p3b world; the empty world has it
(a/theorem step-k [w :- World, it :- Item]
  (=> (= (p3b w) true) (= (gk-rest w) true) (= (gk-rest (:world (world-step w it))) true))
  (intros h hk)
  (exact (gk-rest-of _ (step-gk w it (gk-intro w (ga-sample w (And.left (p3b-parts w h))) hk) (step-rule-r-safe w it h)))))
(a/theorem k-empty [] (= (gk-rest empty-world) true) (rfl))
