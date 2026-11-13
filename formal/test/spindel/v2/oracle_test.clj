(ns spindel.v2.oracle-test
  "The differential oracle (spindel.v2.oracle) over the engine log samples copied into
  test/spindel/v2/oracle/ (from ../spindel-v2/.internal/oracle/, read-only there):
    sample 3  engine ca72c3b, step.clj table order (the primary target), 34 commits
    sample 1  legacy engine-shaped payloads, 10 commits (signal, computation, observe)
    sample 2  legacy, sample 3's scenario (tasks, await all, deferred/mailbox, host read,
              finally + cancel/finalize)
  Every divergence is listed below with its triage, as the exact set of divergent cells
  [table id field], so any change in the engine log, the adapter or the model shows here.
    sample 4  regenerated on engine a28563d (engine-v2, spec Z#35-Z#44), 40 commits, the
              scenario of samples 2/3 (atomic commits, resume at the fill, `[:schedule r]`
              after every start/dispatch, logged finally enter/exit, task inputs)
    sample 5  engine a28563d, 40 commits: scope close, closed sources (refused write/post),
              open-scope / detach / close-scope
    sample 6  engine a28563d, 30 commits: Z#39 cancel -> dep creditor, Z#41 detach re-parent
    sample 7  regenerated for Z#51 (Z#48 track on a closed source consumes its edge, Z#49 logged
              `[:slice-exit r]`, T13 within the slice-exit commit), 22 commits
    sample 8  Z#51: reactivation takes no dep edge on a final debtor, 18 commits
    sample 9  Z#52: cleanup keeps its run scope's current ancestors across a detach (the I1
              counterexample shape), 23 commits (regenerated for Z#55: the offload is one `arm`
              item, the ack retires within its commit)
    sample 10 Z#53/Z#54: a task and a computation take a mailbox owned by a cancelled task's run
              scope; the close wakes both with err ::closed (Nat 2), 20 commits
    sample 11 Z#55: a timer is one `[:arm st :timer k fresh]` item; cancelling the task cancels the
              resource, whose acknowledgement is its own item right after the cancel, 7 commits
    sample 12 Z#57 (engine 4d8a06e): a take on a closed source hands out its backlog, then fails
              at once with err ::closed, 17 commits
    sample 13 Z#59 (engine e735039): the L5 counterexample trace (a group await's fired sibling,
              a later write), 26 commits
  Samples 7-11 regenerated against engine engine-v2 27fc1e4 (Z#53-Z#56; ::closed = 2, opaque
  values from 3). Samples 4 and 6-11 replay with no divergence; sample 5 predates Z#48 (its only
  divergence is the dep edge the old engine keeps on a closed signal); samples 1-6 predate the
  Nat-2 reservation and the one-item `arm` (none of them arms a resource).
  Classes: (a) adapter/projection bug (none open), (b) model bug vs spec, (c) engine bug vs spec,
  (d) spec ambiguity / log contract, (p) pending model change (other pass), (g) granularity:
  only the engine's slice-exit/resume lag differs (`oracle/quiesce` resolves it).

  Triage of sample 3 (spec v1.5.1 section; core.cljc = ../spindel-v2 engine source):
  :c-schedule-entry   `[:schedule r]` commits before the slice is entered: the projection has
                      R.slice = false (start!/resume! call commit! before slice!). §11.4: a
                      scheduling choice is an item; its effect is the slice.
  :d-idle-at-demand   CLOSED by Z#33 (demand clears `idle` in the demanding transition; the
                      model now does it too, engine.clj B23).
  :c-settle-after-complete  complete! (computation) commits before settle! (§4.5.2 belongs to
                      T12; §5.1 commits atomically): the member delivery / observe seen lag one
                      commit. The commit also shows the slice-exit lag (g).
  :c-dispatch-entry   dispatch! commits before E is consumed (T11 \"Edge: E is consumed\":
                      re-armed with its baseline): E still fired in the projection.
  :c-host-await-fast  value-async commits :host-await before the fast-path fire-wait! (T22
                      on a final debtor: consumed in the same transition, B10).
  :c-no-detach        task 10 (done, handles 1) keeps owner = scope 9 after scope 9 is removed
                      (commit 26 on): Rule R step 2 (W#6, X#5) sets owner := none for a
                      surviving task whose owner is removed.
  :c-finalize-entry   `[:finalize r]` commits before its cleanup slice is entered (R.slice =
                      false in the projection), as :c-schedule-entry; the slice then runs every
                      finally block and retires R with no item: the driver replays it as
                      `finally-exit` items (`oracle/implicit-cleanup`, Z#35: the whole chain in
                      the one cleanup slice) and the slice's return as `slice-exit`
                      (`oracle/implicit-exits`).
  :d-cancel-value     the ::cancelled error is an opaque interned value in this old log ([:err 17]);
                      the model's code is rule.clj `cancelled-code`, the reserved Nat 1 that the
                      engine interns ::cancelled to since 1236b6e (task 28's result).
  Since the source/finalizer/cancel items landed (engine.clj F2) the oracle replays every commit
  of the samples (no skip, no re-sync): the former :p-finalize cells of commit 33 ([:scopes 30],
  [:tasks 28 :run], [:runs 29], cleanup) are gone; :g at 18 (deliver) and 21 (post) is the
  resume lag (the model resumes the filled activation at the fill)."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.set :as set]
            [spindel.v2.state :as s]
            [spindel.v2.engine :as en]
            [spindel.v2.inv :as inv]
            [spindel.v2.oracle :as o]))

(def dir "test/spindel/v2/oracle/")
(defn- log [n] (o/read-log (str dir "log-sample-" n ".edn")))

(defn- cells [d] (set (map (juxt :table :id :field) (:diffs-all d))))
(defn- by-commit [res] (into (sorted-map) (map (juxt :commit cells)) (:divergences res)))

(def sample-3-known
  "commit -> [triage classes, divergent cells]"
  {5 [[:c-schedule-entry] #{[:runs 8 :slice]}]
   10 [[:c-settle-after-complete :g] #{[:scopes 17 :row] [:comps 4 :idle] [:comps 4 :run] [:comps 4 :validity]
                                       [:runs 16 :row] [:edges 14 :row] [:edges 18 :row] [:acts 13 :members]
                                       [:acts 13 :remaining] [:acts 13 :slots] [:cleanup nil :cleanup]}]
   11 [[:c-schedule-entry] #{[:runs 11 :slice]}]
   15 [[:c-dispatch-entry] #{[:edges 22 :phase]}]
   17 [[:c-settle-after-complete :g] #{[:scopes 24 :row] [:comps 4 :run] [:runs 23 :row] [:edges 21 :seen]
                                       [:cleanup nil :cleanup]}]
   19 [[:c-schedule-entry] #{[:runs 8 :slice]}]
   22 [[:c-schedule-entry] #{[:runs 11 :slice]}]
   23 [[:g] #{[:scopes 12 :row] [:tasks 10 :run] [:runs 8 :act] [:runs 11 :row] [:acts 25 :row] [:cleanup nil :cleanup]}]
   24 [[:c-schedule-entry] #{[:runs 8 :slice]}]
   25 [[:g] #{[:scopes 9 :row] [:tasks 7 :run] [:tasks 10 :owner] [:runs 8 :row] [:cleanup nil :cleanup]}]
   26 [[:c-host-await-fast :c-no-detach] #{[:tasks 10 :owner] [:edges 27 :row]}]
   27 [[:c-no-detach] #{[:tasks 10 :owner]}]
   28 [[:c-no-detach :c-schedule-entry] #{[:tasks 10 :owner] [:runs 29 :slice]}]
   29 [[:c-no-detach] #{[:tasks 10 :owner]}]
   30 [[:c-no-detach] #{[:tasks 10 :owner]}]
   18 [[:g] #{[:acts 13 :row] [:runs 8 :act]}]
   21 [[:g] #{[:acts 19 :row] [:runs 11 :act]}]
   31 [[:c-no-detach :d-cancel-value] #{[:tasks 10 :owner] [:tasks 28 :result]}]
   32 [[:c-no-detach :d-cancel-value :c-finalize-entry] #{[:tasks 10 :owner] [:tasks 28 :result] [:runs 29 :slice]}]
   33 [[:c-no-detach :d-cancel-value] #{[:tasks 10 :owner] [:tasks 28 :result]}]})

(deftest projection-roundtrip
  (testing "adapter self-check: every projection survives proj->world -> world->proj"
    (doseq [n [1 2 3 4 5 6 7 8 9 10 11]] (is (= [] (o/roundtrip (log n))) (str "sample " n)))))

(defn- common-checks [res msg]
  (is (every? #(= (:engine (:accepted %)) (:model (:accepted %))) (:divergences res)) (str msg ": accepted flags"))
  (is (every? #(empty? (:failed-flags %)) (:divergences res)) (str msg ": honest flags + tripwire"))
  (is (not-any? :implicit-schedule-refused (:divergences res)) (str msg ": implicit schedules admitted")))

(deftest sample-3-table-format
  (let [res (o/replay (log 3))]
    (is (= {:format :table :commits 34 :checked 34 :markers 0 :skipped {} :resyncs 0
            :implicit-schedules 2 :implicit-finally 3 :implicit-cleanup 1 :n-divergences 20 :n-granularity 4}
           (select-keys res [:format :commits :checked :markers :skipped :resyncs :implicit-schedules
                             :implicit-finally :implicit-cleanup :n-divergences :n-granularity])))
    (common-checks res "sample 3")
    (is (= (update-vals sample-3-known second) (by-commit res)) "known divergences (cells)")
    (is (= #{18 21 23 25} (set (map :commit (filter #(= :granularity (:class %)) (:divergences res)))))
        "granularity-only commits")))

(deftest sample-3-strict
  (testing "without the pending deviations, the mailbox state (p) and wait-edge `at` (d) show"
    (let [res (o/replay (log 3) :strict? true)]
      (is (some #(contains? (cells %) [:sources 6 :state]) (:divergences res)) ":mailbox-state")
      (is (some #(contains? (cells %) [:edges 14 :at]) (:divergences res)) ":wait-at"))))

(deftest sample-1-legacy
  ;; legacy engine: a demand on a fresh idle computation stepped its epoch (commit 2 on;
  ;; the engine of sample 3 no longer does), commits before settle / E consumption as above
  (let [res (o/replay (log 1))]
    (is (= {:format :legacy :commits 10 :checked 10 :skipped {} :resyncs 0 :implicit-schedules 2 :n-divergences 8}
           (select-keys res [:format :commits :checked :skipped :resyncs :implicit-schedules :n-divergences])))
    (common-checks res "sample 1")
    (is (= #{2 3 4 5 6 7 8 9} (set (keys (by-commit res)))))))

(deftest sample-2-legacy
  ;; no skip and no re-sync any more, so the legacy epoch step at demand (commit 7, as in
  ;; sample 1: [:comps 4 :epoch], then :done-epoch) persists to the end
  (let [res (o/replay (log 2))]
    (is (= {:format :legacy :commits 34 :checked 28 :markers 6 :skipped {} :resyncs 0
            :implicit-schedules 8 :implicit-finally 3 :implicit-cleanup 1 :n-divergences 27 :n-granularity 0}
           (select-keys res [:format :commits :checked :markers :skipped :resyncs :implicit-schedules
                             :implicit-finally :implicit-cleanup :n-divergences :n-granularity])))
    (common-checks res "sample 2")
    (is (= (set (range 7 34)) (set (keys (by-commit res)))))
    (is (every? #(contains? (cells %) [:comps 4 :epoch]) (:divergences res)) "the legacy epoch step")))

;; Samples 4 (regenerated), 5 and 6: engine a28563d on engine-v2, after the alignment pass
;; (Z#35-Z#44; ::cancelled = reserved Nat 1). Every item replays in lockstep (no skip, no
;; re-sync, no implicit schedule or finally region); refused items carry no projection (sample 5
;; commits 13, 14: a write and a post to a closed source, Z#37), so only the accepted flag is
;; compared. The one implicit step is the return of a cancelled run's cleanup slice (Z#35:
;; `finally-exit` commits at the block's start, the slice returns without an item), replayed
;; as the model's `slice-exit` (`oracle/implicit-exits`): sample 4 commit 39 (run 29).
;; Known divergences: none in samples 4 and 6. Sample 5 commit 11 `[:track 12 7 11 14]` tracks
;; signal 7, closed (final) since task 4's run retired (T13 closes its run scope's sources); the
;; engine of this log (a28563d) keeps the new dep edge 14 armed on the final debtor, against the
;; literal I5. Z#48 (engine 6136b5b, sample 7 commit 9) consumes the edge in the same commit, and
;; so does the model now: sample 5 diverges in the one cell [:edges 14 :row] from commit 11 until
;; computation 10 goes idle (commit 39, where the old engine records the edge as a validity entry
;; [7 0]; a final debtor needs none). Class (p-log): the log predates Z#48.
(def sample-5-old-edge
  (merge (zipmap (concat [11 12] (range 15 39)) (repeat #{[:edges 14 :row]}))
         {39 #{[:comps 10 :validity]}}))

(defn- aligned
  ([n commits] (aligned n commits {} 0))
  ([n commits known n-gran]
   (let [res (o/replay (log n))]
     (is (= {:format :table :commits commits :checked commits :markers 0 :skipped {} :resyncs 0
             :implicit-schedules 0 :implicit-finally 0 :n-divergences (count known) :n-granularity n-gran}
            (select-keys res [:format :commits :checked :markers :skipped :resyncs :implicit-schedules
                              :implicit-finally :n-divergences :n-granularity]))
         (str "sample " n))
     (common-checks res (str "sample " n))
     (is (= known (by-commit res)) (str "sample " n ": known divergences"))
     res)))

(deftest sample-4-table-format
  (let [res (aligned 4 40)]
    (is (= 1 (:implicit-exits res)) "run 29's cleanup slice returns before commit 39"))
  (testing "strict: only the mailbox state remains"
    (let [res (o/replay (log 4) :strict? true)]
      (is (= #{[:sources 6 :state]} (set (mapcat cells (:divergences res))))))))

(deftest sample-5-table-format
  ;; scope close, closed sources (write/post refused), open-scope/detach/close-scope
  (let [res (aligned 5 40 sample-5-old-edge 0)
        log5 (log 5)
        w11 (reduce (fn [w c] (:world (en/world-step w (:item (o/adapt :table {:post (:proj c)} (:item c))))))
                    s/empty-world (take 12 log5))]
    (is (true? (inv/lit-i5-dep-final w11)) "Z#48: track on a closed signal consumes its dep edge (literal I5)")
    (is (not (s/edge-has w11 14)) "edge 14 consumed, its id allocated")
    (is (< 14 (:next-id w11)))
    (is (= [13 14] (keep-indexed (fn [i c] (when-not (:accepted c) i)) log5)) "the refused items")
    (is (every? #(not (contains? % :proj)) (remove :accepted log5)) "refused items carry no projection")))

(deftest sample-6-table-format
  ;; Z#39 (cancel -> dep creditor), Z#41 (detach re-parents the run scope)
  (aligned 6 30))

;; Sample 7 (regenerated for Z#51 on the engine that retires before the slice-exit commit):
;; Z#48 (commit 9 `[:track 10 6 9 12]` tracks signal 6, closed since task 3's run retired: the engine
;; and the model consume edge 12 in the same commit, no edge row, the id allocated) and Z#49 (commit
;; 19 is the engine's `[:slice-exit 15]`; the driver uses the logged item, no implicit exit). The
;; former granularity divergence at commit 19 (the engine committed the item before T13 retired
;; run 15) is gone: the engine now retires within the item.
(deftest sample-7-table-format
  (let [res (aligned 7 22)
        log7 (log 7)
        w9 (reduce (fn [w c] (:world (en/world-step w (:item (o/adapt :table {:post (:proj c)} (:item c))))))
                   s/empty-world (take 10 log7))]
    (is (nil? (:implicit-exits res)) "Z#49: the logged slice-exit, no implicit one")
    (is (= [:slice-exit 15] (:item (nth log7 19))))
    (is (not (s/edge-has w9 12)) "Z#48: edge 12 consumed in the track commit")
    (is (= {} (get-in (nth log7 9) [:proj :edges 12] {})) "the engine agrees")
    (is (true? (inv/lit-i5-dep-final w9)))))

;; Sample 8 (Z#51): computation 10 tracks signal 7 of task 4's run scope, completes and goes idle
;; (unobserve, validity (7, 0)); task 4 completes, T13 closes signal 7; observing 10 again
;; (commit 16 `[:observe 10 15 16]`; regenerated with ::closed = 2, so the opaque Nats start at 3) reactivates it with no dep edge on the closed signal (consumed,
;; no id: next-id 16 -> 17 for the observe edge alone), live, delivered at once.
(deftest sample-8-table-format
  (let [res (aligned 8 18)
        log8 (log 8)
        w16 (reduce (fn [w c] (:world (en/world-step w (:item (o/adapt :table {:post (:proj c)} (:item c))))))
                    s/empty-world (take 17 log8))]
    (is (= [:observe 10 15 16] (:item (nth log8 16))))
    (is (true? (inv/lit-i5-dep-final w16)) "Z#51: no armed dep edge on the closed signal 7")
    (is (not-any? #(and (= 1 (:kind %)) (= 7 (:debtor %))) (:edges w16)))
    (is (= 17 (:next-id w16)))
    (is (some #(and (= 10 (:id %)) (not (:idle %)) (= (:epoch %) (:done-epoch %))) (:comps w16)) "10 is live")))

;; Sample 9 (Z#52; regenerated against 27fc1e4 for Z#55): the I1 counterexample shape. Task 11's run 12
;; spawns task 14 (run 15, scope 16 under 12's scope 13); 15 offloads (commit 12, `[:arm 15 :offload 13 20]`:
;; resource 20, activation 21, wait edge 22, ONE effect-index step, the run parks) and is cancelled
;; (commit 13: unwinding, cleanup[15], the resource cancelling, activation 21 and edge 22 removed); task 11 is
;; detached to the explicit scope 8 (commit 14: scope 13's parent := 8); closing 8 (17) and completing run 6
;; (18) close 8 and 7. Both stay, kept by cleanup[15]'s CURRENT ancestor chain 16 -> 13 -> 8 -> 7 -> 2
;; (Z#52). The refused fire (commit 20, `[:resource-fire 20]`, the resource is cancelling) maps to the
;; model's refused T18; the ack (21) retires 15 within the commit (Z#55) and the chain goes.
;; The two former divergences are gone: the effect index (d-offload-index, settled by Z#55: one effect)
;; and the ack granularity (g, settled by Z#55: T15 runs T13 before the commit).
(deftest sample-9-table-format
  (let [res (aligned 9 23)
        log9 (log 9)
        ws (reductions (fn [w c] (:world (en/world-step w (:item (o/adapt :table {:post (:proj c) :w w} (:item c))))))
                       s/empty-world log9)]
    (is (= [:arm 15 :offload 13 20] (:item (nth log9 12))))
    (let [w12 (nth ws 13)]
      (is (= [s/act-parked 2] ((juxt :act :effect-index) (first (filter #(= 15 (:id %)) (:runs w12)))))
          "one effect (create-source at 0, the arm at 1), the run parks")
      (is (= [1 s/rk-offload] ((juxt :at :kind) (first (filter #(= 20 (:id %)) (:res w12))))))
      (is (some #(and (= 21 (:id %)) (= 15 (:run %))) (:acts w12)) "activation 21")
      (is (some #(and (= 22 (:id %)) (= s/ek-wait (:kind %)) (= 21 (:creditor %)) (= 20 (:debtor %))) (:edges w12)) "wait edge 22 on 20"))
    (is (= [:detach 11 8] (:item (nth log9 14))))
    (is (every? true? (map inv/lit-i1-scope ws)) "literal I1 (scope parent) at every commit")
    (let [w20 (nth ws 21)]
      (is (some #(and (= 13 (:id %)) (= 8 (:parent %))) (:scopes w20)) "13 re-parented to 8 (Z#41)")
      (is (every? (set (map :id (:scopes w20))) [7 8 13 16]) "the closed chain is kept by cleanup[15] (Z#52)")
      (is (every? #(not (:open %)) (filter #(#{7 8 13 16} (:id %)) (:scopes w20)))))
    (is (= [:resource-ack 20] (:item (nth log9 21))))
    (is (= [2] (map :id (:scopes (nth ws 22)))) "the ack retires 15 within its commit; the chain goes")))

;; Sample 10 (Z#53, Z#54): task 4's run 5 creates mailbox 7 (owned by its run scope 6) and parks on
;; deferred 3; task 8's run 11 takes 7 (commit 7, `[:take 11 7 7 13]`: activation 13, wait edge 14) and so
;; does computation 15's run 17 (commit 12, `[:take 17 7 12 19]`: a take, not a dep edge, Z#54). Host cancel
;; of run 5 (commit 13) closes scope 6's subtree: mailbox 7 is closed and both takers wake with err ::closed
;; (Nat 2, Z#53); task 8 completes with that error (commit 15), computation 15 with its catch value.
(deftest sample-10-table-format
  (let [_ (aligned 10 20)
        log10 (log 10)
        ws (reductions (fn [w c] (:world (en/world-step w (:item (o/adapt :table {:post (:proj c) :w w} (:item c))))))
                       s/empty-world log10)
        w13 (nth ws 14)]
    (is (= [:take 17 7 12 19] (:item (nth log10 12))))
    (is (= [:cancel 5] (:item (nth log10 13))))
    (is (some #(and (= 7 (:id %)) (not (:open %))) (:sources w13)) "mailbox 7 closed")
    (is (every? #(= s/act-active (:act %)) (filter #(#{11 17} (:id %)) (:runs w13))) "both takers woke")
    (is (empty? (filter #(#{13 14 19 20} (:id %)) (concat (:acts w13) (:edges w13)))) "their activations and wait edges are gone")
    (is (= [:complete 11 2 2] (:item (nth log10 15))) "task 8 completes with err ::closed (2)")
    (is (every? true? (map inv/lit-i5-dep-final ws)))))

;; Sample 11 (Z#55): task 3's run 4 sleeps: `[:arm 4 :timer 4 6]` (commit 2) allocates resource 6,
;; activation 7 and wait edge 8, parks the run and steps its effect index once. The host cancel (4)
;; unwinds run 4 (activation 7 and edge 8 removed, resource 6 cancelling); the unscheduled timer joins at
;; once and acknowledges as its own item (5), which T15 accepts any time after the cancel and which
;; retires run 4 within the item.
(deftest sample-11-table-format
  (let [_ (aligned 11 7)
        log11 (log 11)
        ws (vec (reductions (fn [w c] (:world (en/world-step w (:item (o/adapt :table {:post (:proj c) :w w} (:item c))))))
                            s/empty-world log11))
        w2 (nth ws 3) w4 (nth ws 5) w5 (nth ws 6)]
    (is (= [:arm 4 :timer 4 6] (:item (nth log11 2))))
    (is (= [s/act-parked 1 [6]] ((juxt :act :effect-index (comp vec :resources)) (first (:runs w2)))))
    (is (= [[7 4] [8 s/ek-wait 7 6]] [((juxt :id :run) (first (:acts w2))) ((juxt :id :kind :creditor :debtor) (first (:edges w2)))]))
    (is (= s/rp-cancelling (:phase (first (:res w4)))))
    (is (empty? (:acts w4)))
    (is (= [:resource-ack 6] (:item (nth log11 5))))
    (is (empty? (:runs w5)) "the ack retires run 4 within the item")
    (is (empty? (:res w5)))))
;; Sample 12 (Z#57, engine engine-v2 4d8a06e): task 4's run 5 creates mailbox 7 (owned by its run scope 6)
;; and posts message 7; the host cancel of run 5 (commit 6) closes the scope's subtree, Rule R detaches the
;; closed mailbox (owner 0) with its backlog [7]. Run 12 takes from it (commit 10, `[:take 12 7 8 14]`): the
;; backlog is still handed out (version 1 -> 2, ids 14 and 15 allocated, nothing kept); run 17's take (commit
;; 14) finds it closed and empty and fails at once with err ::closed (2): no version step, ids 19 and 20
;; allocated and not kept, the run keeps its slice and completes with that error (commit 15).
(deftest sample-12-table-format
  (let [_ (aligned 12 17)
        log12 (log 12)
        ws (vec (reductions (fn [w c] (:world (en/world-step w (:item (o/adapt :table {:post (:proj c) :w w} (:item c))))))
                            s/empty-world log12))
        src7 (fn [w] (first (filter #(= 7 (:id %)) (:sources w))))]
    (is (= [:take 12 7 8 14] (:item (nth log12 10))))
    (is (= [0 false [7] 1] ((juxt :owner :open (comp vec :queue) :version) (src7 (nth ws 10)))) "closed, detached, backlog [7]")
    (is (= [[] 2 16] [(vec (:queue (src7 (nth ws 11)))) (:version (src7 (nth ws 11))) (:next-id (nth ws 11))]) "the backlog is consumed")
    (is (= [:take 17 7 8 19] (:item (nth log12 14))))
    (let [w (nth ws 15) r (first (filter #(= 17 (:id %)) (:runs w)))]
      (is (= [2 21] [(:version (src7 w)) (:next-id w)]) "Z#57: no version step, two ids allocated")
      (is (empty? (:acts w)) "no activation kept")
      (is (empty? (:edges w)) "no wait edge kept")
      (is (= [s/act-active true 1] ((juxt :act :slice :effect-index) r)) "the run keeps its slice"))
    (is (= [:complete 17 2 2] (:item (nth log12 15))) "task 16 completes with err ::closed (2)")))

;; Sample 13 (Z#59, engine engine-v2 e735039, the model's former L5 counterexample): computation 5 awaits
;; signals 3 and 4 in one `all` await (dep edges 15, 16 at the same site, commit 10); computation 6 awaits 5
;; (edge 11) and is observed. Writes to 3 and 4 fire both edges of 5 and mark 11 -> 5. T11 dispatches 5
;; (commit 16): E = 15, the earliest fired edge in creation order, re-armed for the restart; its sibling 16
;; at the same site is cut (Z#59). The new run completes without awaiting: 5 settles, 11 is unmarked. A later
;; write to 4 (commit 23) fires nothing armed and marks nothing (Z#59: a fired or absent edge starts no
;; marking), so 6 stays live with nothing pending.
(deftest sample-13-table-format
  (let [_ (aligned 13 26)
        log13 (log 13)
        ws (vec (reductions (fn [w c] (:world (en/world-step w (:item (o/adapt :table {:post (:proj c) :w w} (:item c))))))
                            s/empty-world log13))
        edge (fn [w x] (first (filter #(= x (:id %)) (:edges w))))
        comp (fn [w x] (first (filter #(= x (:id %)) (:comps w))))]
    (is (= [:await 12 [3 4] :all 13 14 []] (:item (nth log13 10))))
    (is (= [:dispatch 5 17] (:item (nth log13 16))))
    (let [w (nth ws 16)]
      (is (= [s/ph-fired s/ph-fired] (map #(:phase (edge w %)) [15 16])) "both edges of 5 fired")
      (is (true? (:marked (edge w 11)))))
    (let [w (nth ws 17)]
      (is (= s/ph-armed (:phase (edge w 15))) "E = 15 re-armed for the restart")
      (is (nil? (edge w 16)) "the sibling at E's site is cut (Z#59)"))
    (is (= [:write 4 20] (:item (nth log13 23))))
    (let [w (nth ws 24)]
      (is (empty? (filter :marked (:edges w))) "the write marks nothing")
      (is (= [0 true] ((juxt :pending #(= (:epoch %) (:done-epoch %))) (comp w 6))) "6 stays live"))))

;; ---------------------------------------------------------------------------
;; Layer 2 (notes/LAYER2.md): a fork's own log replays from its parent's world at the fork commit.
;; sample 14 (engine 7598069): a host fork of a world holding a signal, an observed computation,
;; a task parked on a timer and a task parked on an offload. The child's first turn settles the
;; inherited offload with err ::forked (the timer stays armed) and the child writes the signal;
;; the parent's offload completes on its own. The worlds share one allocator: the replay raises
;; `next-id` between items (`o/align`, kept by `spindel.v2.skip/p3l-skip-ids`).
(deftest sample-14-fork
  (let [pl (o/read-log "test/spindel/v2/oracle/log-sample-14-parent.edn")
        cl (vec (filter :proj (o/read-log "test/spindel/v2/oracle/log-sample-14-child.edn")))
        pr (o/replay pl :family? true :worlds? true)
        at (first (keep-indexed (fn [i c] (when (= :fork-host (first (:item c))) i)) pl))
        cr (o/replay cl :family? true :init (nth (:worlds pr) at))]
    (is (= [:fork-host 22] (:item (nth pl at))))
    (is (= [23 0 0] ((juxt :checked :n-divergences :resyncs) pr)) "the parent, across the fork")
    (is (= [:write 3 15] (:item (first cl))) "the child's log starts after the fork")
    (is (= [[:resource-fire 18 2 16] [:resource-ack 18]] (map :item (subvec cl 1 3))) "the inherited offload fails with ::forked")
    (is (= [13 0 0] ((juxt :checked :n-divergences :resyncs) cr)) "the child, from the parent's world at the fork")
    (is (pos? (:skipped-ids pr))) (is (pos? (:skipped-ids cr)))))

;; sample 15 (engine feat/v2-layer2-conformance): the `(fork)` effect in a task body. The parent's run keeps its slice
;; and continues with [:parent child]; the child's copy of the run is resumed at the effect
;; (`o/fork-child`: armed, fired and acknowledged resource), writes the signal and completes; the
;; parent's completion closes the fork's owner scope, which releases the child (its last commit).
(deftest sample-15-fork-effect
  (let [pl (o/read-log "test/spindel/v2/oracle/log-sample-15-parent.edn")
        cl (o/read-log "test/spindel/v2/oracle/log-sample-15-child-released.edn")
        pr (o/replay pl :family? true :worlds? true)
        at (first (keep-indexed (fn [i c] (when (= :fork (first (:item c))) i)) pl))
        [_ r _child] (:item (nth pl at))
        fc (o/fork-child (nth (:worlds pr) (dec at)) r)
        cr (o/replay cl :family? true :init (:world fc))]
    (is (= [:fork 11 16] (:item (nth pl at))) "ids 13-15 are the child's resource, activation and edge")
    (is (= [20 0 0] ((juxt :checked :n-divergences :resyncs) pr)) "the parent: its run keeps the slice across the fork")
    (is (true? (:accepted fc)) "the child's run is parked at the effect and resumed")
    (is (= [:schedule 11] (:item (nth cl 1))) "the child's copy of the run gets its slice")
    (is (= [:release-world] (:item (peek cl))) "the owner scope's close releases the child")
    (is (= [9 0 0] ((juxt :checked :n-divergences :resyncs) cr)))))

;; sample 16 (engine feat/v2-savepoint-resource: a savepoint is a resource the run arms). Task a's
;; savepoint is resumed in place (T18 + T15); task b's publication is instantiated twice and then
;; abandoned (T14, the resource joins at once); task c is parked at another savepoint when the
;; instances are made. An instance starts from the basis (the publishing world at b's publish
;; commit): its pending savepoint fires `ok v`, the other inherited one fails with ::forked.
(deftest sample-16-savepoints
  (let [pl (o/read-log "test/spindel/v2/oracle/log-sample-16-parent.edn")
        pr (o/replay pl :family? true :worlds? true)
        at (first (keep-indexed (fn [i c] (when (= [:arm 20 :savepoint] (take 3 (:item c))) i)) pl))
        basis (nth (:worlds pr) at)
        inst (fn [n] (vec (filter :proj (o/read-log (str "test/spindel/v2/oracle/log-sample-16-inst" n ".edn")))))]
    (is (= [[:arm 5 :savepoint 5 7] [:resource-fire 7 1 6] [:resource-ack 7] [:schedule 5]] (map :item (subvec pl 3 7)))
        "publish, then the in-place resume")
    (is (= [[:cancel 20] [:resource-ack 22] [:cancel 13] [:resource-ack 15]] (map :item (subvec pl 16 20))) "abandon")
    (is (= [22 0 0] ((juxt :checked :n-divergences :resyncs) pr)))
    (doseq [n [1 2]]
      (let [l (inst n) r (o/replay l :family? true :init basis)]
        (is (= [[:resource-fire 22 1] [:resource-ack 22] [:resource-fire 15 2] [:resource-ack 15]] (map (comp vec (partial take 3) :item) (subvec l 0 4)))
            "activate: the pending savepoint fires ok, the other one err ::forked")
        (is (= [13 0 0] ((juxt :checked :n-divergences :resyncs) r)) (str "instance " n))))))
