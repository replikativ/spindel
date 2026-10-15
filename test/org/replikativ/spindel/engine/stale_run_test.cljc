(ns org.replikativ.spindel.engine.stale-run-test
  "Regression: a run invalidated while in flight must not certify its result.

  Found by the differential DOM fuzzer (defect 1 of
  `dom/differential_fuzz_regressions_test.cljs`), reduced here to the engine.

  Shape: a parent P tracks signal A, re-creates keyed child spins, and awaits
  them IN ORDER. Each child also tracks A and then awaits a deferred. A change
  of A that PREPENDS a child:

  - reaches the old child as an observer of A, but `:signal-change` filters it
    out as a descendant observer (P re-creates it) — it is not resumed;
  - P's re-run awaits the new first child, which suspends;
  - the batch ends; the old child's await is still parked on the deferred.

  Before the fix nothing invalidated the old child: its freshness relied on
  P's re-run reaching it INSIDE the batch (the await fast path is off there).
  The delivery then completed the old child's run — which read A before the
  change — and cached it as :clean; P reached the child afterwards, the
  re-registration was a B-gate no-op (identical captures), and the stale
  result was served for good. The same happened when the old child had
  already COMPLETED before the change, and when a running child was dirtied
  by the B-gate (changed captures) and its old run completed first.

  The rule (formalism §3.4): a run may cache its result as clean only if
  nothing invalidated the node since the run began. `invalidate-node` marks an
  in-flight run `:stale-run?`; `cache-result!` then keeps the node :dirty."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]])
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.addressing :as eaddr]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]))

#?(:clj
   (do
     (defn- keyed
       "Mint the spins in `thunk` under an item-keyed chain-head — what
       `ifor-each` does — so a child's id follows its key, not its position."
       [k thunk]
       (let [c (ec/current-execution-context)
             prev (eaddr/get-chain-head c)]
         (eaddr/set-chain-head! c (keyword (str "keyed-" (eaddr/chain-hash {:keyed k} prev))))
         (try (thunk) (finally (eaddr/set-chain-head! c prev)))))

     (defn- await-in-order
       "A spin awaiting `children` one after the other (`ifor-each`'s loop)."
       [children]
       (spin (loop [r children acc []]
               (if (empty? r)
                 acc
                 (recur (rest r) (conj acc (await (first r))))))))

     (defn- tracking-child
       "A child that tracks `a` at the top, then awaits `(gate id)` (nil: none).
       Resolves to `[id (count (:xs a))]`."
       [ids a gate id]
       (let [s (keyed id (fn []
                           (spin (let [{s :new} (track a)
                                       g (gate id)
                                       _ (when g (await g))]
                                   [id (count (:xs s))]))))]
         (swap! ids assoc id (spin-core/spin-id s))
         s))

     (defn- run-parent!
       "Start a parent that tracks `a` and awaits one `make-child` per `:xs`
       entry in order. Returns an atom holding the latest delivered value."
       [a make-child]
       (let [out (atom nil)
             p (spin (let [{v :new} (track a)
                           children (mapv (fn [x] (make-child (:id x))) (:xs v))]
                       (await (await-in-order children))))]
         (p (fn [v] (reset! out v)) (fn [e] (reset! out [:error e])))
         out))

     (defn- settle!
       "Wait until every posted event is processed (`events-settled?`).
       Not `await-drain-complete!`: that also waits for every spin to finish,
       and these scenarios keep spins parked on undelivered deferreds. Polls
       the condition the way `await-drain-complete!` does; the deadline only
       turns a livelock into a failure."
       [c]
       (let [deadline (+ (System/currentTimeMillis) 2000)]
         (loop []
           (cond
             (simple/events-settled? c) true
             (> (System/currentTimeMillis) deadline) (is false "events did not settle")
             :else (do (java.util.concurrent.locks.LockSupport/parkNanos 100000)
                       (recur))))))

     (defn- node [id] (ec/get-state [:nodes id]))))

#?(:clj
   (deftest in-flight-descendant-completion-is-not-certified
     (testing "prepend while the old child is suspended: its run completes
               after the change and must neither be served nor cached clean"
       (let [c (ctx/create-execution-context)]
         (try
           (binding [ec/*execution-context* c]
             (let [a (sig/signal {:xs [{:id 0}]})
                   d0 (sync/create-deferred c)   ; the old child's gate
                   d1 (sync/create-deferred c)   ; the prepended child's gate
                   ids (atom {})
                   ;; one gate map for every run: identical captures, so the
                   ;; B-gate keeps the old child — only the change of A can
                   ;; invalidate it
                   gate {0 d0 1 d1}
                   out (run-parent! a #(tracking-child ids a gate %))]
               (settle! c)
               (is (:running? (node (@ids 0))) "old child suspended on d0")

               (swap! a update :xs #(into [{:id 1}] %))
               (settle! c)
               (let [n (node (@ids 0))]
                 (is (= :dirty (:status n))
                     "the filtered descendant is invalidated at the change")
                 (is (:stale-run? n) "its in-flight run is marked stale"))

               ;; The stale run completes first — the parent is still parked
               ;; on the prepended child.
               (sync/deliver! d0 :go)
               (settle! c)
               (let [n (node (@ids 0))]
                 (is (= [0 1] (:payload (:result n)))
                     "the stale run read A before the change")
                 (is (= :dirty (:status n))
                     "…and its completion does NOT certify the result")
                 (is (not (:stale-run? n)) "the mark is consumed"))

               (sync/deliver! d1 :go)
               (settle! c)
               (is (= [[1 2] [0 2]] @out)
                   "the parent re-runs the old child against the current A")
               (is (= :clean (:status (node (@ids 0)))))))
           (finally (ctx/close-context! c)))))))

#?(:clj
   (deftest completed-descendant-reached-after-the-batch-re-runs
     (testing "the old child had COMPLETED before the change; the parent
               reaches it only after the batch ended"
       (let [c (ctx/create-execution-context)]
         (try
           (binding [ec/*execution-context* c]
             (let [a (sig/signal {:xs [{:id 0}]})
                   d1 (sync/create-deferred c)
                   ids (atom {})
                   gate {1 d1}
                   out (run-parent! a #(tracking-child ids a gate %))]
               (settle! c)
               (is (= [[0 1]] @out))
               (swap! a update :xs #(into [{:id 1}] %))
               (settle! c)
               (is (= :dirty (:status (node (@ids 0))))
                   "a completed descendant is invalidated too")
               (is (not (:stale-run? (node (@ids 0))))
                   "no run in flight, nothing to mark stale")
               (sync/deliver! d1 :go)
               (settle! c)
               (is (= [[1 2] [0 2]] @out))))
           (finally (ctx/close-context! c)))))))

#?(:clj
   (deftest b-gate-invalidated-run-completing-first-is-not-served
     (testing "a running child re-registered with CHANGED captures (B-gate):
               its old run completes before the parent reaches it"
       (let [c (ctx/create-execution-context)]
         (try
           (binding [ec/*execution-context* c]
             (let [a (sig/signal {:xs [{:id 0}] :tag :old})
                   d0 (sync/create-deferred c)
                   d1 (sync/create-deferred c)
                   ids (atom {})
                   runs (atom [])
                   out (atom nil)
                   ;; The child does NOT track A: it sees A only through the
                   ;; captured `tag`, so only the B-gate can invalidate it.
                   make-child (fn [tag id]
                                (let [s (keyed id (fn []
                                                    (spin (let [_ (await (if (= id 0) d0 d1))]
                                                            (swap! runs conj [id tag])
                                                            [id tag]))))]
                                  (swap! ids assoc id (spin-core/spin-id s))
                                  s))
                   p (spin (let [{v :new} (track a)
                                 tag (:tag v)
                                 children (mapv (fn [x] (make-child tag (:id x))) (:xs v))]
                             (await (await-in-order children))))]
               (p (fn [v] (reset! out v)) (fn [e] (reset! out [:error e])))
               (settle! c)
               (swap! a (fn [m] (-> m (assoc :tag :new) (update :xs #(into [{:id 1}] %)))))
               (settle! c)
               (is (:stale-run? (node (@ids 0)))
                   "changed captures on a running node mark its run stale")
               (sync/deliver! d0 :go)
               (settle! c)
               (is (= [[0 :old]] @runs) "the old run completed, with the old capture")
               (is (= :dirty (:status (node (@ids 0)))) "…uncertified")
               (sync/deliver! d1 :go)
               (settle! c)
               (is (= [[1 :new] [0 :new]] @out)
                   "the parent re-runs the child with its current captures")))
           (finally (ctx/close-context! c)))))))
