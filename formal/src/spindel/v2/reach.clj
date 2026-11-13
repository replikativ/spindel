(ns spindel.v2.reach
  "Generic least fixpoints over Nat nodes, kernel-checked (Init only).

  Reach (retention, spec §3.2): `Reach succ roots x` is the least set that
  contains `roots` and is closed under `succ`. `reach-run fuel succ roots`
  is the executable worklist. It returns a `ReachResult` {visited, converged},
  where converged means the worklist emptied before fuel ran out. One unit of
  fuel is one worklist pop, so `fuel >= |roots| + (sum of |succ v| over the
  reachable v) + 1` converges (an observation, not a theorem here: the
  theorems below are conditional on `converged`).

    reach-run-sound     v in visited -> Reach succ roots v
    reach-run-roots     converged, r in roots -> r in visited
    reach-run-closed    converged, a in visited, b in succ a -> b in visited
    reach-run-complete  converged, Reach succ roots x -> x in visited
    reach-run-iff       converged -> (reach-mem x visited = true <-> Reach succ roots x)
    reach-run-mem-iff   converged -> (List.Mem x visited <-> Reach succ roots x)
    (-roots-mem / -closed-mem: the same two over List.Mem)
    reach-frame         (forall z, Reach succ roots z -> succ2 z = succ z) ->
                        (Reach succ2 roots x <-> Reach succ roots x); -roots: also roots2 = roots
    reach-run-frame     same hypothesis -> reach-run fuel succ2 roots = reach-run fuel succ roots

  The worklist invariant (every seen and every queued node is Reach; every
  seen node's successors are seen or queued) is proved once, by induction on
  fuel over arbitrary work/seen: reach-closure-sound / -seen / -work / -closed.

  Derive (blockedness, spec §4.5 item 6): `Derive base deps leaf x` is the
  least predicate such that `base x = true` and every dep y of x is a leaf or
  is itself derived. The constructor states this as `leaf y = false -> Derive y`,
  because Lean's kernel rejects the nested `leaf y = true \\/ Derive y` form
  (see notes/ansatz-gaps.md). `derive-run fuel base deps leaf nodes` runs rounds
  over the candidate list `nodes`. Each round adds every candidate whose deps
  are all leaf-or-derived. converged means some round added nothing.
  |nodes| + 1 rounds suffice (again not proved here).

    derive-run-sound     x in derived -> Derive x
    derive-run-complete  deps of nodes are in nodes or are leaves, converged,
                         Derive x, x in nodes -> x in derived
    derive-run-iff       under the same hypotheses, (x in derived <-> Derive x)

  Membership is the Bool `reach-mem`, because it runs in the oracle.
  `reach-mem-iff` bridges it to `List.Mem`."
  (:require [ansatz.core :as a]))

(a/load-init!)

;; ---------------------------------------------------------------------------
;; Reach and the executable worklist

(a/inductive Reach [succ (=> Nat (List Nat)) roots (List Nat)] :in Prop :indices [x Nat]
  (root [x Nat] [h (List.Mem Nat x roots)] :where [x])
  (step [x Nat] [y Nat] [hx (Reach succ roots x)] [hy (List.Mem Nat y (succ x))] :where [y]))

(a/defn reach-mem [x :- Nat, xs :- (List Nat)] Bool
  (match xs [nil false]
         [(cons h t) (if (Nat.beq x h) true (reach-mem x t))]))

(a/structure ReachResult [] (visited (List Nat)) (converged Bool))

(a/defn reach-closure [fuel :- Nat, succ :- (=> Nat (List Nat)), work :- (List Nat), seen :- (List Nat)] ReachResult
  (match fuel
    [zero (match work [nil (ReachResult.mk seen true)] [(cons h t) (ReachResult.mk seen false)])]
    [(succ n) (match work
                [nil (ReachResult.mk seen true)]
                [(cons x rest) (if (reach-mem x seen)
                                 (reach-closure n succ rest seen)
                                 (reach-closure n succ (List.append Nat (succ x) rest) (List.cons Nat x seen)))])]))

(a/defn reach-run [fuel :- Nat, succ :- (=> Nat (List Nat)), roots :- (List Nat)] ReachResult
  (reach-closure fuel succ roots (List.nil Nat)))

;; ---------------------------------------------------------------------------
;; Bool membership

(a/theorem reach-mem-iff [x :- Nat, xs :- (List Nat)]
  (Iff (= (reach-mem x xs) true) (List.Mem x xs))
  (induction xs)
  (case' [cons head tail ih])
  (case' [nil])
  (simp [reach-mem])
  (intro h) (cases h)
  (cases hb (Nat.beq x head))
  (all_goals (simp [reach-mem hb ih]))
  (constructor)
  (intro h) (exact (List.Mem.tail head h))
  (intro h) (cases h)
  (simp [Nat.beq_refl] at hb)
  (assumption)
  (have he (= x head) (Nat.eq_of_beq_eq_true x head hb))
  (subst he)
  (exact (List.Mem.head tail)))

(a/theorem reach-mem-append [x :- Nat, a :- (List Nat), b :- (List Nat)]
  (= (reach-mem x (List.append a b)) (Bool.or (reach-mem x a) (reach-mem x b)))
  (induction a)
  (case' [cons head tail ih])
  (case' [nil])
  (simp [reach-mem List.append])
  (change (= (reach-mem x (List.cons head (List.append tail b))) (Bool.or (reach-mem x (List.cons head tail)) (reach-mem x b))))
  (cases hb (Nat.beq x head))
  (all_goals (simp [reach-mem hb ih])))

(a/theorem reach-mem-app [x :- Nat, a :- (List Nat), b :- (List Nat)]
  (= (reach-mem x (HAppend.hAppend a b)) (Bool.or (reach-mem x a) (reach-mem x b)))
  (exact (reach-mem-append x a b)))

(a/theorem reach-mem-cons [z :- Nat, x :- Nat, t :- (List Nat)]
  (= (reach-mem z (List.cons x t)) (Bool.or (Nat.beq z x) (reach-mem z t)))
  (cases hb (Nat.beq z x))
  (all_goals (simp [reach-mem hb])))

;; ---------------------------------------------------------------------------
;; The worklist invariant, proved once by induction on fuel (general work/seen):
;;   every seen and every queued node is Reach (reach-closure-sound);
;;   every seen node's successors are seen or queued (reach-closure-closed).

(a/theorem reach-closure-sound
  [succ :- (=> Nat (List Nat)), roots :- (List Nat), fuel :- Nat]
  (forall [work :- (List Nat)] (forall [seen :- (List Nat)]
    (=> (forall [z :- Nat] (=> (= (reach-mem z seen) true) (Reach succ roots z)))
        (forall [z :- Nat] (=> (= (reach-mem z work) true) (Reach succ roots z)))
        (forall [v :- Nat] (=> (= (reach-mem v (ReachResult.visited (reach-closure fuel succ work seen))) true)
                               (Reach succ roots v))))))
  (induction fuel)
  (case [zero]
    (intro work seen hs hw v hv)
    (cases work)
    (all_goals (simp [reach-closure] at hv))
    (all_goals (exact (hs v hv))))
  (case [succ n ih]
    (intro work seen hs hw v hv)
    (cases work)
    (case [nil] (simp [reach-closure] at hv) (exact (hs v hv)))
    (case [cons x rest]
      (cases hm (reach-mem x seen))
      (case [true]
        (simp [reach-closure hm] at hv)
        (have hw2 (forall [z :- Nat] (=> (= (reach-mem z rest) true) (Reach succ roots z))))
        (intro z hz) (apply hw) (simp [reach-mem-cons hz])
        (exact (ih rest seen hs hw2 v hv)))
      (case [false]
        (simp [reach-closure hm] at hv)
        (have hx (Reach succ roots x))
        (apply hw) (simp [reach-mem-cons Nat.beq_refl])
        (have hs2 (forall [z :- Nat] (=> (= (reach-mem z (List.cons x seen)) true) (Reach succ roots z))))
        (intro z hz)
        (simp [reach-mem-cons] at hz)
        (rcases hz (or h1 h2))
        (subst h1) (exact hx)
        (exact (hs z h2))
        (have hw2 (forall [z :- Nat] (=> (= (reach-mem z (HAppend.hAppend (succ x) rest)) true) (Reach succ roots z))))
        (intro z hz)
        (simp [reach-mem-app] at hz)
        (rcases hz (or h1 h2))
        (exact (Reach.step x z hx (Iff.mp (reach-mem-iff z (succ x)) h1)))
        (apply hw) (simp [reach-mem-cons h2])
        (exact (ih (HAppend.hAppend (succ x) rest) (List.cons x seen) hs2 hw2 v hv))))))

(a/theorem reach-closure-seen
  [succ :- (=> Nat (List Nat)), fuel :- Nat]
  (forall [work :- (List Nat)] (forall [seen :- (List Nat)] (forall [v :- Nat]
    (=> (= (reach-mem v seen) true)
        (= (reach-mem v (ReachResult.visited (reach-closure fuel succ work seen))) true)))))
  (induction fuel)
  (case [zero]
    (intro work seen v hv)
    (cases work)
    (all_goals (simp [reach-closure hv])))
  (case [succ n ih]
    (intro work seen v hv)
    (cases work)
    (case [nil] (simp [reach-closure hv]))
    (case [cons x rest]
      (cases hm (reach-mem x seen))
      (case [true] (simp [reach-closure hm]) (exact (ih rest seen v hv)))
      (case [false] (simp [reach-closure hm])
        (apply ih) (simp [reach-mem-cons hv])))))

(a/theorem reach-closure-work
  [succ :- (=> Nat (List Nat)), fuel :- Nat]
  (forall [work :- (List Nat)] (forall [seen :- (List Nat)] (forall [v :- Nat]
    (=> (= (ReachResult.converged (reach-closure fuel succ work seen)) true)
        (= (reach-mem v work) true)
        (= (reach-mem v (ReachResult.visited (reach-closure fuel succ work seen))) true)))))
  (induction fuel)
  (case [zero]
    (intro work seen v hc hv)
    (cases work)
    (case [nil] (simp [reach-mem] at hv))
    (case [cons x rest] (simp [reach-closure] at hc)))
  (case [succ n ih]
    (intro work seen v hc hv)
    (cases work)
    (case [nil] (simp [reach-mem] at hv))
    (case [cons x rest]
      (simp [reach-mem-cons] at hv)
      (cases hm (reach-mem x seen))
      (case [true]
        (simp [reach-closure hm] at hc)
        (simp [reach-closure hm])
        (rcases hv (or h1 h2))
        (rw [h1]) (exact (reach-closure-seen succ n rest seen x hm))
        (exact (ih rest seen v hc h2)))
      (case [false]
        (simp [reach-closure hm] at hc)
        (simp [reach-closure hm])
        (rcases hv (or h1 h2))
        (rw [h1]) (apply reach-closure-seen) (simp [reach-mem-cons Nat.beq_refl])
        (apply (ih (HAppend.hAppend (succ x) rest) (List.cons x seen) v hc))
        (simp [reach-mem-app h2])))))

(a/theorem reach-closure-closed
  [succ :- (=> Nat (List Nat)), fuel :- Nat]
  (forall [work :- (List Nat)] (forall [seen :- (List Nat)]
    (=> (forall [a :- Nat] (=> (= (reach-mem a seen) true)
          (forall [b :- Nat] (=> (= (reach-mem b (succ a)) true)
             (= (Bool.or (reach-mem b seen) (reach-mem b work)) true)))))
        (= (ReachResult.converged (reach-closure fuel succ work seen)) true)
        (forall [a :- Nat] (=> (= (reach-mem a (ReachResult.visited (reach-closure fuel succ work seen))) true)
          (forall [b :- Nat] (=> (= (reach-mem b (succ a)) true)
             (= (reach-mem b (ReachResult.visited (reach-closure fuel succ work seen))) true))))))))
  (induction fuel)
  (case [zero]
    (intro work seen hi hc a ha b hb)
    (cases work)
    (case [nil] (simp [reach-closure] at ha) (simp [reach-closure])
      (have h := (hi a ha b hb)) (simp [reach-mem] at h) (exact h))
    (case [cons x rest] (simp [reach-closure] at hc)))
  (case [succ n ih]
    (intro work seen hi hc)
    (cases work)
    (case [nil] (intro a ha b hb) (simp [reach-closure] at ha) (simp [reach-closure])
      (have h := (hi a ha b hb)) (simp [reach-mem] at h) (exact h))
    (case [cons x rest]
      (cases hm (reach-mem x seen))
      (case [true]
        (simp [reach-closure hm] at hc)
        (simp [reach-closure hm])
        (apply (ih rest seen _ hc))
        (intro a ha b hb)
        (have h := (hi a ha b hb))
        (simp [reach-mem-cons] at h)
        (rcases h (or h1 (or h2 h3)))
        (simp [h1])
        (rw [h2]) (simp [hm])
        (simp [h3]))
      (case [false]
        (simp [reach-closure hm] at hc)
        (simp [reach-closure hm])
        (apply (ih (HAppend.hAppend (succ x) rest) (List.cons x seen) _ hc))
        (intro a ha b hb)
        (simp [reach-mem-cons] at ha)
        (rcases ha (or h1 h2))
        (rw [h1] at hb) (simp [reach-mem-app hb])
        (have h := (hi a h2 b hb))
        (simp [reach-mem-cons] at h)
        (rcases h (or g1 (or g2 g3)))
        (simp [reach-mem-cons g1])
        (simp [reach-mem-cons g2])
        (simp [reach-mem-app g3])))))

;; ---------------------------------------------------------------------------
;; From roots: soundness, roots, closure, completeness

(a/theorem reach-run-sound
  [fuel :- Nat, succ :- (=> Nat (List Nat)), roots :- (List Nat), v :- Nat]
  (=> (= (reach-mem v (ReachResult.visited (reach-run fuel succ roots))) true)
      (Reach succ roots v))
  (intro hv)
  (apply (reach-closure-sound succ roots fuel roots (List.nil Nat) _ _ v hv))
  (intro z hz) (simp [reach-mem] at hz)
  (intro z hz) (exact (Reach.root z (Iff.mp (reach-mem-iff z roots) hz))))

(a/theorem reach-run-roots
  [fuel :- Nat, succ :- (=> Nat (List Nat)), roots :- (List Nat), r :- Nat]
  (=> (= (ReachResult.converged (reach-run fuel succ roots)) true)
      (= (reach-mem r roots) true)
      (= (reach-mem r (ReachResult.visited (reach-run fuel succ roots))) true))
  (intro hc hr)
  (exact (reach-closure-work succ fuel roots (List.nil Nat) r hc hr)))

(a/theorem reach-run-closed
  [fuel :- Nat, succ :- (=> Nat (List Nat)), roots :- (List Nat), a :- Nat, b :- Nat]
  (=> (= (ReachResult.converged (reach-run fuel succ roots)) true)
      (= (reach-mem a (ReachResult.visited (reach-run fuel succ roots))) true)
      (= (reach-mem b (succ a)) true)
      (= (reach-mem b (ReachResult.visited (reach-run fuel succ roots))) true))
  (intro hc ha hb)
  (apply (reach-closure-closed succ fuel roots (List.nil Nat) _ hc a ha b hb))
  (intro z hz) (simp [reach-mem] at hz))

(a/theorem reach-run-complete
  [fuel :- Nat, succ :- (=> Nat (List Nat)), roots :- (List Nat), x :- Nat]
  (=> (= (ReachResult.converged (reach-run fuel succ roots)) true)
      (Reach succ roots x)
      (= (reach-mem x (ReachResult.visited (reach-run fuel succ roots))) true))
  (intro hc h)
  (induction h)
  (case [root r hr]
    (exact (reach-run-roots fuel succ roots r hc (Iff.mpr (reach-mem-iff r roots) hr))))
  (case [step p q hp ihp hq]
    (exact (reach-run-closed fuel succ roots p q hc ihp (Iff.mpr (reach-mem-iff q (succ p)) hq)))))

(a/theorem reach-run-iff
  [fuel :- Nat, succ :- (=> Nat (List Nat)), roots :- (List Nat), x :- Nat]
  (=> (= (ReachResult.converged (reach-run fuel succ roots)) true)
      (Iff (= (reach-mem x (ReachResult.visited (reach-run fuel succ roots))) true)
           (Reach succ roots x)))
  (intro hc)
  (constructor)
  (exact (reach-run-sound fuel succ roots x))
  (exact (reach-run-complete fuel succ roots x hc)))

(a/theorem reach-run-mem-iff
  [fuel :- Nat, succ :- (=> Nat (List Nat)), roots :- (List Nat), x :- Nat]
  (=> (= (ReachResult.converged (reach-run fuel succ roots)) true)
      (Iff (List.Mem x (ReachResult.visited (reach-run fuel succ roots)))
           (Reach succ roots x)))
  (intro hc)
  (constructor)
  (intro h) (exact (reach-run-sound fuel succ roots x (Iff.mpr (reach-mem-iff x (ReachResult.visited (reach-run fuel succ roots))) h)))
  (intro h) (exact (Iff.mp (reach-mem-iff x (ReachResult.visited (reach-run fuel succ roots))) (reach-run-complete fuel succ roots x hc h))))

(a/theorem reach-run-roots-mem
  [fuel :- Nat, succ :- (=> Nat (List Nat)), roots :- (List Nat), r :- Nat]
  (=> (= (ReachResult.converged (reach-run fuel succ roots)) true)
      (List.Mem r roots)
      (List.Mem r (ReachResult.visited (reach-run fuel succ roots))))
  (intro hc hr)
  (exact (Iff.mp (reach-mem-iff r (ReachResult.visited (reach-run fuel succ roots)))
           (reach-run-roots fuel succ roots r hc (Iff.mpr (reach-mem-iff r roots) hr)))))

(a/theorem reach-run-closed-mem
  [fuel :- Nat, succ :- (=> Nat (List Nat)), roots :- (List Nat), a :- Nat, b :- Nat]
  (=> (= (ReachResult.converged (reach-run fuel succ roots)) true)
      (List.Mem a (ReachResult.visited (reach-run fuel succ roots)))
      (List.Mem b (succ a))
      (List.Mem b (ReachResult.visited (reach-run fuel succ roots))))
  (intro hc ha hb)
  (exact (Iff.mp (reach-mem-iff b (ReachResult.visited (reach-run fuel succ roots)))
           (reach-run-closed fuel succ roots a b hc
             (Iff.mpr (reach-mem-iff a (ReachResult.visited (reach-run fuel succ roots))) ha)
             (Iff.mpr (reach-mem-iff b (succ a)) hb)))))

;; ---------------------------------------------------------------------------
;; Derive: the least fixpoint for blockedness (spec §4.5 item 6)

(a/inductive Derive [base (=> Nat Bool) deps (=> Nat (List Nat)) leaf (=> Nat Bool)] :in Prop :indices [x Nat]
  (mk [x Nat] [hb (= (base x) true)]
      [hd (forall [y :- Nat] (=> (List.Mem y (deps x)) (= (leaf y) false) (Derive base deps leaf y)))]
      :where [x]))

(a/defn derive-deps-ok [leaf :- (=> Nat Bool), derived :- (List Nat), ys :- (List Nat)] Bool
  (match ys [nil true]
         [(cons y t) (Bool.and (Bool.or (leaf y) (reach-mem y derived)) (derive-deps-ok leaf derived t))]))

(a/defn derive-ok [base :- (=> Nat Bool), deps :- (=> Nat (List Nat)), leaf :- (=> Nat Bool),
                   derived :- (List Nat), x :- Nat] Bool
  (Bool.and (base x) (derive-deps-ok leaf derived (deps x))))

(a/defn derive-fresh [base :- (=> Nat Bool), deps :- (=> Nat (List Nat)), leaf :- (=> Nat Bool),
                      derived :- (List Nat), nodes :- (List Nat)] (List Nat)
  (match nodes [nil (List.nil Nat)]
         [(cons x t) (if (Bool.and (Bool.not (reach-mem x derived)) (derive-ok base deps leaf derived x))
                       (List.cons Nat x (derive-fresh base deps leaf derived t))
                       (derive-fresh base deps leaf derived t))]))

(a/structure DeriveResult [] (derived (List Nat)) (converged Bool))

(a/defn derive-loop [fuel :- Nat, base :- (=> Nat Bool), deps :- (=> Nat (List Nat)), leaf :- (=> Nat Bool),
                     nodes :- (List Nat), derived :- (List Nat)] DeriveResult
  (match fuel
    [zero (match (derive-fresh base deps leaf derived nodes)
            [nil (DeriveResult.mk derived true)]
            [(cons h t) (DeriveResult.mk derived false)])]
    [(succ n) (match (derive-fresh base deps leaf derived nodes)
                [nil (DeriveResult.mk derived true)]
                [(cons h t) (derive-loop n base deps leaf nodes
                              (List.append Nat (List.cons Nat h t) derived))])]))

(a/defn derive-run [fuel :- Nat, base :- (=> Nat Bool), deps :- (=> Nat (List Nat)), leaf :- (=> Nat Bool),
                    nodes :- (List Nat)] DeriveResult
  (derive-loop fuel base deps leaf nodes (List.nil Nat)))

;; ---------------------------------------------------------------------------
;; Derive proofs

(a/theorem derive-deps-ok-sound [leaf :- (=> Nat Bool), derived :- (List Nat), ys :- (List Nat)]
  (=> (= (derive-deps-ok leaf derived ys) true)
      (forall [y :- Nat] (=> (= (reach-mem y ys) true) (= (leaf y) false) (= (reach-mem y derived) true))))
  (induction ys)
  (case [nil] (intro h y hy) (simp [reach-mem] at hy))
  (case [cons a t ih]
    (intro h y hy hl)
    (simp [derive-deps-ok] at h)
    (rcases h [h1 h2])
    (simp [reach-mem-cons] at hy)
    (rcases hy (or e1 e2))
    (rw [e1] at hl) (rw [e1]) (simp [hl] at h1) (exact h1)
    (exact (ih h2 y e2 hl))))

(a/theorem derive-deps-ok-complete [leaf :- (=> Nat Bool), derived :- (List Nat), ys :- (List Nat)]
  (=> (forall [y :- Nat] (=> (= (reach-mem y ys) true) (= (leaf y) false) (= (reach-mem y derived) true)))
      (= (derive-deps-ok leaf derived ys) true))
  (induction ys)
  (case [nil] (intro h) (simp [derive-deps-ok]))
  (case [cons a t ih]
    (intro h)
    (have ht (= (derive-deps-ok leaf derived t) true))
    (apply ih) (intro y hy hl) (apply (h y _ hl)) (simp [reach-mem-cons hy])
    (have ha (= (reach-mem a (List.cons a t)) true))
    (simp [reach-mem-cons Nat.beq_refl])
    (cases hl (leaf a))
    (case [false] (simp [derive-deps-ok ht hl (h a ha hl)]))
    (case [true] (simp [derive-deps-ok ht hl]))))

(a/theorem derive-fresh-ok
  [base :- (=> Nat Bool), deps :- (=> Nat (List Nat)), leaf :- (=> Nat Bool), derived :- (List Nat), nodes :- (List Nat)]
  (forall [x :- Nat]
    (=> (= (reach-mem x (derive-fresh base deps leaf derived nodes)) true)
        (= (derive-ok base deps leaf derived x) true)))
  (induction nodes)
  (case [nil] (intro x hx) (simp [derive-fresh reach-mem] at hx))
  (case [cons a t ih]
    (intro x hx)
    (cases hc (Bool.and (Bool.not (reach-mem a derived)) (derive-ok base deps leaf derived a)))
    (case [false] (simp [derive-fresh hc] at hx) (exact (ih x hx)))
    (case [true]
      (simp [derive-fresh hc reach-mem-cons] at hx)
      (rcases hx (or e1 e2))
      (rw [e1]) (simp at hc) (exact (And.right hc))
      (exact (ih x e2)))))

(a/theorem derive-fresh-nil
  [base :- (=> Nat Bool), deps :- (=> Nat (List Nat)), leaf :- (=> Nat Bool), derived :- (List Nat), nodes :- (List Nat)]
  (=> (= (derive-fresh base deps leaf derived nodes) (List.nil Nat))
      (forall [x :- Nat]
        (=> (= (reach-mem x nodes) true)
            (= (derive-ok base deps leaf derived x) true)
            (= (reach-mem x derived) true))))
  (induction nodes)
  (case [nil] (intro hf x hx) (simp [reach-mem] at hx))
  (case [cons a t ih]
    (intro hf x hx hok)
    (cases hc (Bool.and (Bool.not (reach-mem a derived)) (derive-ok base deps leaf derived a)))
    (case [true] (simp [derive-fresh hc] at hf))
    (case [false]
      (simp [derive-fresh hc] at hf)
      (simp [reach-mem-cons] at hx)
      (rcases hx (or e1 e2))
      (rw [e1] at hok) (rw [e1])
      (cases hm (reach-mem a derived))
      (simp [hm hok] at hc)
      (rfl)
      (exact (ih hf x e2 hok)))))

(a/theorem derive-ok-sound
  [base :- (=> Nat Bool), deps :- (=> Nat (List Nat)), leaf :- (=> Nat Bool), derived :- (List Nat), x :- Nat]
  (=> (forall [z :- Nat] (=> (= (reach-mem z derived) true) (Derive base deps leaf z)))
      (= (derive-ok base deps leaf derived x) true)
      (Derive base deps leaf x))
  (intro hs h)
  (simp [derive-ok] at h)
  (rcases h [hb hd])
  (apply (Derive.mk x hb))
  (intro y hy hl)
  (exact (hs y (derive-deps-ok-sound leaf derived (deps x) hd y (Iff.mpr (reach-mem-iff y (deps x)) hy) hl))))

(a/theorem derive-loop-sound
  [base :- (=> Nat Bool), deps :- (=> Nat (List Nat)), leaf :- (=> Nat Bool), nodes :- (List Nat), fuel :- Nat]
  (forall [derived :- (List Nat)]
    (=> (forall [z :- Nat] (=> (= (reach-mem z derived) true) (Derive base deps leaf z)))
        (forall [v :- Nat] (=> (= (reach-mem v (DeriveResult.derived (derive-loop fuel base deps leaf nodes derived))) true)
                               (Derive base deps leaf v)))))
  (induction fuel)
  (case [zero]
    (intro derived hs v hv)
    (cases hf (derive-fresh base deps leaf derived nodes))
    (all_goals (simp [derive-loop hf] at hv))
    (all_goals (exact (hs v hv))))
  (case [succ n ih]
    (intro derived hs v hv)
    (cases hf (derive-fresh base deps leaf derived nodes))
    (case [nil] (simp [derive-loop hf] at hv) (exact (hs v hv)))
    (case [cons h t]
      (simp [derive-loop hf] at hv)
      (have hfr (forall [z :- Nat] (=> (= (reach-mem z (List.cons h t)) true) (Derive base deps leaf z))))
      (intro z hz)
      (apply (derive-ok-sound base deps leaf derived z hs))
      (apply (derive-fresh-ok base deps leaf derived nodes z))
      (rw [hf]) (exact hz)
      (apply (ih _ _ v hv))
      (intro z hz)
      (simp [reach-mem-cons reach-mem-app] at hz)
      (rcases hz (or e1 (or e2 e3)))
      (apply hfr) (simp [reach-mem-cons e1])
      (apply hfr) (simp [reach-mem-cons e2])
      (exact (hs z e3)))))

(a/theorem derive-loop-fix
  [base :- (=> Nat Bool), deps :- (=> Nat (List Nat)), leaf :- (=> Nat Bool), nodes :- (List Nat), fuel :- Nat]
  (forall [derived :- (List Nat)]
    (=> (= (DeriveResult.converged (derive-loop fuel base deps leaf nodes derived)) true)
        (= (derive-fresh base deps leaf (DeriveResult.derived (derive-loop fuel base deps leaf nodes derived)) nodes)
           (List.nil Nat))))
  (induction fuel)
  (case [zero]
    (intro derived hc)
    (cases hf (derive-fresh base deps leaf derived nodes))
    (case [nil] (simp [derive-loop hf]))
    (case [cons h t] (simp [derive-loop hf] at hc)))
  (case [succ n ih]
    (intro derived hc)
    (cases hf (derive-fresh base deps leaf derived nodes))
    (case [nil] (simp [derive-loop hf]))
    (case [cons h t] (simp [derive-loop hf] at hc) (simp [derive-loop hf]) (exact (ih _ hc)))))

(a/theorem derive-run-sound
  [fuel :- Nat, base :- (=> Nat Bool), deps :- (=> Nat (List Nat)), leaf :- (=> Nat Bool), nodes :- (List Nat), x :- Nat]
  (=> (= (reach-mem x (DeriveResult.derived (derive-run fuel base deps leaf nodes))) true)
      (Derive base deps leaf x))
  (intro hx)
  (apply (derive-loop-sound base deps leaf nodes fuel (List.nil Nat) _ x hx))
  (intro z hz) (simp [reach-mem] at hz))

;; The step of completeness (the minor premise of the induction on Derive; ansatz >= 0.2.606
;; gives `induction` the reflexive field's IH, tracker #1).
(a/theorem derive-run-complete-step
  [fuel :- Nat, base :- (=> Nat Bool), deps :- (=> Nat (List Nat)), leaf :- (=> Nat Bool), nodes :- (List Nat)]
  (=> (forall [a :- Nat] (=> (= (reach-mem a nodes) true)
        (forall [b :- Nat] (=> (= (reach-mem b (deps a)) true) (= (leaf b) false) (= (reach-mem b nodes) true)))))
      (= (DeriveResult.converged (derive-run fuel base deps leaf nodes)) true)
      (forall [p :- Nat]
        (=> (= (base p) true)
            (forall [y :- Nat] (=> (List.Mem y (deps p)) (= (leaf y) false) (Derive base deps leaf y)))
            (forall [y :- Nat] (=> (List.Mem y (deps p)) (= (leaf y) false)
                                   (= (reach-mem y nodes) true)
                                   (= (reach-mem y (DeriveResult.derived (derive-run fuel base deps leaf nodes))) true)))
            (= (reach-mem p nodes) true)
            (= (reach-mem p (DeriveResult.derived (derive-run fuel base deps leaf nodes))) true))))
  (intro hcl hc p hb hdd ih hp)
  (have hok (= (derive-ok base deps leaf (DeriveResult.derived (derive-run fuel base deps leaf nodes)) p) true))
  (simp [derive-ok hb])
  (apply derive-deps-ok-complete)
  (intro y hy hl)
  (exact (ih y (Iff.mp (reach-mem-iff y (deps p)) hy) hl (hcl p hp y hy hl)))
  (exact (derive-fresh-nil base deps leaf (DeriveResult.derived (derive-run fuel base deps leaf nodes)) nodes
           (derive-loop-fix base deps leaf nodes fuel (List.nil Nat) hc) p hp hok)))

(a/theorem derive-run-complete
  [fuel :- Nat, base :- (=> Nat Bool), deps :- (=> Nat (List Nat)), leaf :- (=> Nat Bool), nodes :- (List Nat), x :- Nat]
  (=> (forall [a :- Nat] (=> (= (reach-mem a nodes) true)
        (forall [b :- Nat] (=> (= (reach-mem b (deps a)) true) (= (leaf b) false) (= (reach-mem b nodes) true)))))
      (= (DeriveResult.converged (derive-run fuel base deps leaf nodes)) true)
      (Derive base deps leaf x)
      (= (reach-mem x nodes) true)
      (= (reach-mem x (DeriveResult.derived (derive-run fuel base deps leaf nodes))) true))
  (intro hcl hc hd)
  (induction hd)
  (case [mk p hb hdd ih]
    (exact (derive-run-complete-step fuel base deps leaf nodes hcl hc p hb hdd ih))))

(a/theorem derive-run-iff
  [fuel :- Nat, base :- (=> Nat Bool), deps :- (=> Nat (List Nat)), leaf :- (=> Nat Bool), nodes :- (List Nat), x :- Nat]
  (=> (forall [a :- Nat] (=> (= (reach-mem a nodes) true)
        (forall [b :- Nat] (=> (= (reach-mem b (deps a)) true) (= (leaf b) false) (= (reach-mem b nodes) true)))))
      (= (DeriveResult.converged (derive-run fuel base deps leaf nodes)) true)
      (= (reach-mem x nodes) true)
      (Iff (= (reach-mem x (DeriveResult.derived (derive-run fuel base deps leaf nodes))) true)
           (Derive base deps leaf x)))
  (intro hcl hc hx)
  (constructor)
  (exact (derive-run-sound fuel base deps leaf nodes x))
  (intro hd)
  (exact (derive-run-complete fuel base deps leaf nodes x hcl hc hd hx)))

;; ---------------------------------------------------------------------------
;; Frames: a successor function that agrees with succ on every Reach node has the same
;; Reach set (reach-frame, reach-frame-roots) and the same worklist run at any fuel
;; (reach-closure-frame, reach-run-frame).


(a/theorem reach-frame [succ :- (=> Nat (List Nat)), succ2 :- (=> Nat (List Nat)), roots :- (List Nat), x :- Nat]
  (=> (forall [z :- Nat] (=> (Reach succ roots z) (= (succ2 z) (succ z))))
      (Iff (Reach succ2 roots x) (Reach succ roots x)))
  (intro h)
  (constructor)
  (intro hx)
  (induction hx)
  (case [root r hr] (exact (Reach.root r hr)))
  (case [step p q hp ihp hq]
    (have e := (h p ihp))
    (rw [e] at hq)
    (exact (Reach.step p q ihp hq)))
  (intro hx)
  (induction hx)
  (case [root r hr] (exact (Reach.root r hr)))
  (case [step p q hp ihp hq]
    (have e := (h p hp))
    (have hq2 (List.Mem q (succ2 p))) (rw [e]) (exact hq)
    (exact (Reach.step p q ihp hq2))))

(a/theorem reach-frame-roots [succ :- (=> Nat (List Nat)), succ2 :- (=> Nat (List Nat)),
                              roots :- (List Nat), roots2 :- (List Nat), x :- Nat]
  (=> (= roots2 roots)
      (forall [z :- Nat] (=> (Reach succ roots z) (= (succ2 z) (succ z))))
      (Iff (Reach succ2 roots2 x) (Reach succ roots x)))
  (intro hr h)
  (rw [hr])
  (exact (reach-frame succ succ2 roots x h)))

(a/theorem reach-closure-frame
  [succ :- (=> Nat (List Nat)), succ2 :- (=> Nat (List Nat)), roots :- (List Nat), fuel :- Nat]
  (=> (forall [z :- Nat] (=> (Reach succ roots z) (= (succ2 z) (succ z))))
      (forall [work :- (List Nat)] (forall [seen :- (List Nat)]
        (=> (forall [z :- Nat] (=> (= (reach-mem z work) true) (Reach succ roots z)))
            (= (reach-closure fuel succ2 work seen) (reach-closure fuel succ work seen))))))
  (intro hs)
  (induction fuel)
  (case [zero]
    (intro work seen hw)
    (cases work)
    (all_goals (simp [reach-closure])))
  (case [succ n ih]
    (intro work seen hw)
    (cases work)
    (case [nil] (simp [reach-closure]))
    (case [cons x rest]
      (have hx (Reach succ roots x))
      (apply hw) (simp [reach-mem-cons Nat.beq_refl])
      (cases hm (reach-mem x seen))
      (case [true]
        (simp [reach-closure hm])
        (apply ih)
        (intro z hz) (apply hw) (simp [reach-mem-cons hz]))
      (case [false]
        (simp [reach-closure hm (hs x hx)])
        (apply ih)
        (intro z hz)
        (simp [reach-mem-app] at hz)
        (rcases hz (or h1 h2))
        (exact (Reach.step x z hx (Iff.mp (reach-mem-iff z (succ x)) h1)))
        (apply hw) (simp [reach-mem-cons h2])))))

(a/theorem reach-run-frame
  [fuel :- Nat, succ :- (=> Nat (List Nat)), succ2 :- (=> Nat (List Nat)), roots :- (List Nat)]
  (=> (forall [z :- Nat] (=> (Reach succ roots z) (= (succ2 z) (succ z))))
      (= (reach-run fuel succ2 roots) (reach-run fuel succ roots)))
  (intro hs)
  (simp only [reach-run])
  (apply (reach-closure-frame succ succ2 roots fuel hs roots (List.nil Nat)))
  (intro z hz) (exact (Reach.root z (Iff.mp (reach-mem-iff z roots) hz))))

;; ---------------------------------------------------------------------------
;; List-fuel worklist. Introduced because ansatz <= 0.2.604 compiled the Nat-fuel
;; `reach-closure` through Nat.recCompiled with an eager IH (tracker #7); since 0.2.613 both
;; compile to a direct self-call and cost the same (measured: 3001 nodes, 38 ms each). The
;; list form stays because the fuel-sufficiency theorems (`reach-run-l-conv`,
;; `live-converged-all`, ...) count list cells; `reach-closure-l` is the same worklist with one
;; cell per unit of fuel and equals reach-closure at the list's length (reach-run-l-eq), so
;; every reach-run theorem applies to it. `dirty-run` (step.clj) uses the Nat form.

(a/defn reach-closure-l [fuel :- (List Nat), succ :- (=> Nat (List Nat)), work :- (List Nat), seen :- (List Nat)] ReachResult
  (match fuel
    [nil (match work [nil (ReachResult.mk seen true)] [(cons h t) (ReachResult.mk seen false)])]
    [(cons u n) (match work
                  [nil (ReachResult.mk seen true)]
                  [(cons x rest) (if (reach-mem x seen)
                                   (reach-closure-l n succ rest seen)
                                   (reach-closure-l n succ (List.append Nat (succ x) rest) (List.cons Nat x seen)))])]))

(a/defn reach-run-l [fuel :- (List Nat), succ :- (=> Nat (List Nat)), roots :- (List Nat)] ReachResult
  (reach-closure-l fuel succ roots (List.nil Nat)))

(a/theorem reach-closure-succ-nil [n :- Nat, succ :- (=> Nat (List Nat)), seen :- (List Nat)]
  (= (reach-closure (+ n 1) succ (List.nil Nat) seen) (ReachResult.mk seen true))
  (rfl))

(a/theorem reach-closure-succ-cons [n :- Nat, succ :- (=> Nat (List Nat)), x :- Nat, rest :- (List Nat), seen :- (List Nat)]
  (= (reach-closure (+ n 1) succ (List.cons Nat x rest) seen)
     (if (reach-mem x seen)
       (reach-closure n succ rest seen)
       (reach-closure n succ (List.append Nat (succ x) rest) (List.cons Nat x seen))))
  (rfl))

(a/theorem reach-closure-l-eq [succ :- (=> Nat (List Nat)), fuel :- (List Nat)]
  (forall [work :- (List Nat)] (forall [seen :- (List Nat)]
    (= (reach-closure-l fuel succ work seen) (reach-closure (List.length fuel) succ work seen))))
  (induction fuel)
  (case [nil] (intro work seen) (cases work) (all_goals (simp [reach-closure-l reach-closure List.length])))
  (case [cons u t ih]
    (intro work seen)
    (cases work)
    (case [nil] (simp [reach-closure-l List.length reach-closure-succ-nil]))
    (case [cons x rest]
      (cases hm (reach-mem x seen))
      (all_goals (simp [reach-closure-l List.length reach-closure-succ-cons hm ih])))))

(a/theorem reach-run-l-eq [fuel :- (List Nat), succ :- (=> Nat (List Nat)), roots :- (List Nat)]
  (= (reach-run-l fuel succ roots) (reach-run (List.length fuel) succ roots))
  (simp only [reach-run-l reach-run])
  (exact (reach-closure-l-eq succ fuel roots (List.nil Nat))))

;; ---------------------------------------------------------------------------
;; List-fuel Derive rounds (runtime; same reason as reach-closure-l): `derive-run-l` is
;; `derive-run` at the list's length (`derive-run-l-eq`), so derive-run-sound/-complete apply.

(a/defn derive-loop-l [fuel :- (List Nat), base :- (=> Nat Bool), deps :- (=> Nat (List Nat)), leaf :- (=> Nat Bool),
                       nodes :- (List Nat), derived :- (List Nat)] DeriveResult
  (match fuel
    [nil (match (derive-fresh base deps leaf derived nodes)
           [nil (DeriveResult.mk derived true)]
           [(cons h t) (DeriveResult.mk derived false)])]
    [(cons u n) (match (derive-fresh base deps leaf derived nodes)
                  [nil (DeriveResult.mk derived true)]
                  [(cons h t) (derive-loop-l n base deps leaf nodes
                                (List.append Nat (List.cons Nat h t) derived))])]))

(a/defn derive-run-l [fuel :- (List Nat), base :- (=> Nat Bool), deps :- (=> Nat (List Nat)), leaf :- (=> Nat Bool),
                      nodes :- (List Nat)] DeriveResult
  (derive-loop-l fuel base deps leaf nodes (List.nil Nat)))

(a/theorem derive-loop-succ-nil [n :- Nat, base :- (=> Nat Bool), deps :- (=> Nat (List Nat)), leaf :- (=> Nat Bool),
                                 nodes :- (List Nat), derived :- (List Nat)]
  (=> (= (derive-fresh base deps leaf derived nodes) (List.nil Nat))
      (= (derive-loop (Nat.succ n) base deps leaf nodes derived) (DeriveResult.mk derived true)))
  (intro hf) (simp [derive-loop hf]))

(a/theorem derive-loop-succ-cons [n :- Nat, base :- (=> Nat Bool), deps :- (=> Nat (List Nat)), leaf :- (=> Nat Bool),
                                  nodes :- (List Nat), derived :- (List Nat), h :- Nat, t :- (List Nat)]
  (=> (= (derive-fresh base deps leaf derived nodes) (List.cons Nat h t))
      (= (derive-loop (Nat.succ n) base deps leaf nodes derived)
         (derive-loop n base deps leaf nodes (List.append Nat (List.cons Nat h t) derived))))
  (intro hf) (simp [derive-loop hf]))

(a/theorem derive-loop-l-eq [base :- (=> Nat Bool), deps :- (=> Nat (List Nat)), leaf :- (=> Nat Bool),
                             nodes :- (List Nat), fuel :- (List Nat)]
  (forall [derived :- (List Nat)]
    (= (derive-loop-l fuel base deps leaf nodes derived) (derive-loop (List.length fuel) base deps leaf nodes derived)))
  (induction fuel)
  (case [nil]
    (intro derived)
    (cases hf (derive-fresh base deps leaf derived nodes))
    (all_goals (simp only [derive-loop-l derive-loop List.length hf])))
  (case [cons u t ih]
    (intro derived)
    (have hl (= (List.length (List.cons Nat u t)) (Nat.succ (List.length t)))) (rfl)
    (rw [hl])
    (cases hf (derive-fresh base deps leaf derived nodes))
    (case [nil] (rw [(derive-loop-succ-nil (List.length t) base deps leaf nodes derived hf)]) (simp only [derive-loop-l hf]))
    (case [cons h t2]
      (rw [(derive-loop-succ-cons (List.length t) base deps leaf nodes derived h t2 hf)])
      (simp only [derive-loop-l hf])
      (exact (ih (List.append Nat (List.cons Nat h t2) derived))))))

(a/theorem derive-run-l-eq [fuel :- (List Nat), base :- (=> Nat Bool), deps :- (=> Nat (List Nat)), leaf :- (=> Nat Bool),
                            nodes :- (List Nat)]
  (= (derive-run-l fuel base deps leaf nodes) (derive-run (List.length fuel) base deps leaf nodes))
  (simp only [derive-run-l derive-run])
  (exact (derive-loop-l-eq base deps leaf nodes fuel (List.nil Nat))))

;; ---------------------------------------------------------------------------
;; Fuel sufficiency of the list-fuel worklist (obligation P1). Potential argument: with a
;; node universe `us` outside of which every node has no successors, the potential
;; |work| + (sum over u in us, u unseen, of |succ u|) (`unseen-cost`, counted with the
;; multiplicity of u in us, so no duplicate-freedom is needed) drops by at least one per pop:
;; a seen node leaves the worklist; an unseen node x pushes |succ x| and its own term
;; (>= |succ x| when x is in us, and succ x = [] otherwise) leaves the sum.
;;   reach-closure-l-conv   potential <= |fuel| -> converged
;;   reach-run-l-conv       |roots| + unseen-cost succ [] us <= |fuel| -> converged

(a/defn unseen-cost [succ :- (=> Nat (List Nat)), seen :- (List Nat), us :- (List Nat)] Nat
  (match us [nil 0]
         [(cons u t) (+ (if (reach-mem u seen) 0 (List.length (succ u))) (unseen-cost succ seen t))]))

(a/theorem unseen-cost-mono [succ :- (=> Nat (List Nat)), x :- Nat, seen :- (List Nat), us :- (List Nat)]
  (<= (unseen-cost succ (List.cons Nat x seen) us) (unseen-cost succ seen us))
  (induction us)
  (case [nil] (simp [unseen-cost]))
  (case [cons u t ih]
    (cases hs (reach-mem u seen))
    (case [true]
      (have hs2 (= (reach-mem u (List.cons Nat x seen)) true)) (simp [reach-mem-cons hs])
      (simp only [unseen-cost hs hs2]) (omega))
    (case [false]
      (cases hs2 (reach-mem u (List.cons Nat x seen)))
      (all_goals (simp only [unseen-cost hs hs2]))
      (all_goals (omega)))))

(a/theorem beq-symm-false [a :- Nat, b :- Nat] (=> (= (Nat.beq a b) false) (= (Nat.beq b a) false))
  (intro h)
  (cases hb (Nat.beq b a))
  (case [false] (rfl))
  (case [true]
    (have he (= b a)) (exact (Nat.eq_of_beq_eq_true hb))
    (rw [he] at h) (simp [Nat.beq_refl] at h)))

(a/theorem unseen-cost-drop [succ :- (=> Nat (List Nat)), x :- Nat, seen :- (List Nat), us :- (List Nat)]
  (=> (= (reach-mem x seen) false) (= (reach-mem x us) true)
      (<= (+ (unseen-cost succ (List.cons Nat x seen) us) (List.length (succ x))) (unseen-cost succ seen us)))
  (intro hx)
  (induction us)
  (case [nil] (intro hm) (simp [reach-mem] at hm))
  (case [cons u t ih]
    (intro hm)
    (cases hxu (Nat.beq x u))
    (case [true]
      (have he (= x u)) (exact (Nat.eq_of_beq_eq_true hxu))
      (rw [← he])
      (have hc (= (reach-mem x (List.cons Nat x seen)) true)) (simp [reach-mem-cons Nat.beq_refl])
      (have hm2 := (unseen-cost-mono succ x seen t))
      (simp only [unseen-cost hc hx])
      (omega))
    (case [false]
      (have ht (= (reach-mem x t) true)) (simp only [reach-mem-cons hxu Bool.false_or] at hm) (exact hm)
      (have hux (= (Nat.beq u x) false)) (exact (beq-symm-false x u hxu))
      (have hc (= (reach-mem u (List.cons Nat x seen)) (reach-mem u seen))) (simp only [reach-mem-cons hux Bool.false_or])
      (have h2 := (ih ht))
      (simp only [unseen-cost hc])
      (omega))))

(a/theorem list-length-append [l1 :- (List Nat), l2 :- (List Nat)]
  (= (List.length (List.append Nat l1 l2)) (+ (List.length l1) (List.length l2)))
  (induction l1)
  (case [nil] (simp [List.append List.length]))
  (case [cons h t ih] (simp only [List.append List.length ih]) (omega)))

(a/theorem reach-closure-l-conv [succ :- (=> Nat (List Nat)), us :- (List Nat),
                                 hu :- (forall [x :- Nat] (=> (= (reach-mem x us) false) (= (succ x) (List.nil Nat)))),
                                 fuel :- (List Nat)]
  (forall [work :- (List Nat), seen :- (List Nat)]
    (=> (<= (+ (List.length work) (unseen-cost succ seen us)) (List.length fuel))
        (= (:converged (reach-closure-l fuel succ work seen)) true)))
  (induction fuel)
  (case [nil]
    (intros work seen h)
    (cases work)
    (case [nil] (simp [reach-closure-l]))
    (case [cons x rest] (simp only [List.length] at h) (omega)))
  (case [cons v f ih]
    (intros work seen h)
    (cases work)
    (case [nil] (simp [reach-closure-l]))
    (case [cons x rest]
      (simp only [List.length] at h)
      (cases hm (reach-mem x seen))
      (case [true]
        (simp only [reach-closure-l hm])
        (apply (ih rest seen))
        (omega))
      (case [false]
        (simp only [reach-closure-l hm])
        (apply (ih (List.append Nat (succ x) rest) (List.cons Nat x seen)))
        (rw [list-length-append])
        (cases hxu (reach-mem x us))
        (case [true]
          (have hd := (unseen-cost-drop succ x seen us hm hxu))
          (omega))
        (case [false]
          (have hn (= (succ x) (List.nil Nat))) (exact (hu x hxu))
          (have hd := (unseen-cost-mono succ x seen us))
          (rw [hn])
          (simp only [List.length])
          (omega))))))

(a/theorem reach-run-l-conv [fuel :- (List Nat), succ :- (=> Nat (List Nat)), roots :- (List Nat), us :- (List Nat)]
  (=> (forall [x :- Nat] (=> (= (reach-mem x us) false) (= (succ x) (List.nil Nat))))
      (<= (+ (List.length roots) (unseen-cost succ (List.nil Nat) us)) (List.length fuel))
      (= (:converged (reach-run-l fuel succ roots)) true))
  (intros hu h)
  (simp only [reach-run-l])
  (exact (reach-closure-l-conv succ us hu fuel roots (List.nil Nat) h)))

;; ---------------------------------------------------------------------------
;; Fuel independence (Z#52: the cleanup ancestors are recomputed in the filtered world, whose
;; fuel list is shorter): once converged, more fuel changes nothing, so two converged runs over
;; the same successors agree whatever their fuels (`reach-run-conv-eq`). `unseen-cost-le1`:
;; with at most one successor per node the potential is at most |us|.

(a/theorem reach-closure-more [succ :- (=> Nat (List Nat)), k :- Nat, fuel :- Nat]
  (forall [work :- (List Nat), seen :- (List Nat)]
    (=> (= (:converged (reach-closure fuel succ work seen)) true)
        (= (reach-closure (+ fuel k) succ work seen) (reach-closure fuel succ work seen))))
  (induction fuel)
  (case [zero]
    (intros work seen h)
    (rw [Nat.zero_add])
    (cases work)
    (case [nil] (cases k) (rfl) (rfl))
    (case [cons x rest] (have z (= false true)) (exact h) (cases z)))
  (case [succ n ih]
    (intros work seen h)
    (have h2 (= (:converged (reach-closure (+ n 1) succ work seen)) true)) (exact h)
    (have e (= (+ (Nat.succ n) k) (+ (+ n k) 1))) (omega)
    (rw [e])
    (show (= (reach-closure (+ (+ n k) 1) succ work seen) (reach-closure (+ n 1) succ work seen)))
    (cases work)
    (case [nil] (simp only [reach-closure-succ-nil]))
    (case [cons x rest]
      (simp only [reach-closure-succ-cons])
      (simp only [reach-closure-succ-cons] at h2)
      (cases hm (reach-mem x seen))
      (case [true] (simp only [hm] at h2) (simp only [hm]) (exact (ih rest seen h2)))
      (case [false] (simp only [hm] at h2) (simp only [hm]) (exact (ih _ _ h2))))))

(a/theorem reach-run-conv-eq [f1 :- Nat, f2 :- Nat, succ :- (=> Nat (List Nat)), roots :- (List Nat)]
  (=> (= (:converged (reach-run f1 succ roots)) true) (= (:converged (reach-run f2 succ roots)) true)
      (= (reach-run f1 succ roots) (reach-run f2 succ roots)))
  (intros h1 h2)
  (simp only [reach-run] at h1 h2)
  (simp only [reach-run])
  (have a := (reach-closure-more succ f2 f1 roots (List.nil Nat) h1))
  (have b := (reach-closure-more succ f1 f2 roots (List.nil Nat) h2))
  (have e (= (+ f1 f2) (+ f2 f1))) (omega)
  (rw [e] at a)
  (exact (Eq.trans (Eq.symm a) b)))

(a/theorem unseen-cost-le1 [succ :- (=> Nat (List Nat)), seen :- (List Nat), us :- (List Nat),
                            h1 :- (forall [x :- Nat] (<= (List.length (succ x)) 1))]
  (<= (unseen-cost succ seen us) (List.length us))
  (induction us)
  (case [nil] (simp [unseen-cost]))
  (case [cons u t ih]
    (have hu := (h1 u))
    (cases hm (reach-mem u seen))
    (all_goals (simp only [unseen-cost hm List.length]))
    (all_goals (omega))))
