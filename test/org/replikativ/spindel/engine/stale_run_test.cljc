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
  nothing invalidated the node since the run began. Every fresh body entry
  starts a new run generation; `invalidate-node` records the generation it
  invalidates; `cache-result!` certifies a completion only for the node's
  current, uninvalidated generation, and ignores an older run's completion."
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
                 (is (simple/stale-run? n) "its in-flight run is marked stale"))

               ;; The stale run completes first — the parent is still parked
               ;; on the prepended child.
               (sync/deliver! d0 :go)
               (settle! c)
               (let [n (node (@ids 0))]
                 (is (= [0 1] (:payload (:result n)))
                     "the stale run read A before the change")
                 (is (= :dirty (:status n))
                     "…and its completion does NOT certify the result")
                 (is (simple/run-invalidated? n)
                     "the mark stays until a fresh run, so no second write of
                      this run can certify it"))

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
               (is (not (simple/stale-run? (node (@ids 0))))
                   "no run in flight")
               (is (simple/run-invalidated? (node (@ids 0)))
                   "but its (completed) generation is invalidated")
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
               (is (simple/stale-run? (node (@ids 0)))
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

#?(:clj
   (deftest stale-run-that-rejects-is-not-certified
     (testing "the superseded run REJECTS: the error path writes the cache
               (and used to write it twice) — neither write may certify it"
       (let [c (ctx/create-execution-context)]
         (try
           (binding [ec/*execution-context* c]
             (let [a (sig/signal {:xs [{:id 0}]})
                   d0 (sync/create-deferred c)
                   d1 (sync/create-deferred c)
                   ids (atom {})
                   gate {0 d0 1 d1}
                   ;; a child that throws when it read the OLD A
                   make-child (fn [id]
                                (let [s (keyed id (fn []
                                                    (spin (let [{s :new} (track a)
                                                                _ (await (gate id))]
                                                            (if (= 1 (count (:xs s)))
                                                              (throw (ex-info "stale read" {:id id}))
                                                              [id (count (:xs s))])))))]
                                  (swap! ids assoc id (spin-core/spin-id s))
                                  s))
                   out (run-parent! a make-child)]
               (settle! c)
               (swap! a update :xs #(into [{:id 1}] %))
               (settle! c)
               (sync/deliver! d0 :go)
               (settle! c)
               (let [n (node (@ids 0))]
                 (is (= :error (:variant (:result n))) "the stale run rejected")
                 (is (= :dirty (:status n)) "…and its error is NOT certified"))
               (sync/deliver! d1 :go)
               (settle! c)
               (is (= [[1 2] [0 2]] @out)
                   "the parent re-runs the child; the stale error never surfaces")
               (is (= :clean (:status (node (@ids 0)))))))
           (finally (ctx/close-context! c)))))))

#?(:clj
   (deftest child-created-before-the-resume-point-is-resumed-not-filtered
     (testing "a descendant created BEFORE its creator's track point is not
               re-created by the creator's resume: it must be resumed itself"
       (let [c (ctx/create-execution-context)]
         (try
           (binding [ec/*execution-context* c]
             (let [a (sig/signal 1)
                   out (atom nil)
                   cid (atom nil)
                   p (spin (let [ch (spin (let [{v :new} (track a)] v))
                                 _ (reset! cid (spin-core/spin-id ch))
                                 x (await ch)
                                 {v :new} (track a)]
                             [x v]))]
               (p (fn [v] (reset! out v)) (fn [e] (reset! out [:error e])))
               (settle! c)
               (is (= [1 1] @out))
               (reset! a 2)
               (settle! c)
               (is (= [2 2] @out) "no glitch: the child sees the change too")
               (is (= :clean (:status (node @cid)))
                   "and it is not left :dirty for good")))
           (finally (ctx/close-context! c)))))))

#?(:clj
   (deftest spin-execution-over-a-stale-run-strands-no-caller
     (testing "a :spin-execution that finds a STALE run starts a fresh one;
               the stale run's invoker (claimed first) still gets the value"
       (let [c (ctx/create-execution-context)]
         (try
           (binding [ec/*execution-context* c]
             (let [d (sync/create-deferred c)
                   input (atom 1)          ; read BEFORE the await
                   runs (atom 0)
                   s (spin (let [v @input
                                 _ (swap! runs inc)
                                 _ (await d)]
                             v))
                   id (spin-core/spin-id s)
                   first-cb (promise)
                   second-cb (promise)]
               (ec/enqueue-event! {:type :spin-execution :id id :spin s
                                   :resolve-fn #(deliver first-cb [:ok %])
                                   :reject-fn #(deliver first-cb [:error %])})
               (settle! c)
               (is (:running? (node id)) "first run suspended on d")
               ;; invalidate the run in flight (what a filtered descendant /
               ;; a changed-captures re-registration does)
               (reset! input 2)
               (ec/swap-state! [:nodes id] simple/invalidate-node)
               (is (simple/stale-run? (node id)))
               (ec/enqueue-event! {:type :spin-execution :id id :spin s
                                   :resolve-fn #(deliver second-cb [:ok %])
                                   :reject-fn #(deliver second-cb [:error %])})
               (settle! c)
               (is (= 2 @runs) "the stale run is not joined: a fresh run started")
               (sync/deliver! d :go)
               (settle! c)
               (is (= [:ok 2] (deref second-cb 2000 ::timeout)))
               (is (= [:ok 2] (deref first-cb 2000 ::timeout))
                   "the first claimer is handed to the fresh run, not stranded")
               (is (= :clean (:status (node id))))))
           (finally (ctx/close-context! c)))))))

#?(:clj
   (defn- causal-follow-scenario
     "World A invokes S (its first run awaits a deferred) with a
     :causal-follow callback, and forks B and C. `steps` run in order; each
     is a fn of `{:a :b :c :s :sid :d}`. Returns the deliveries as
     `[world-id value]`, and the world ids."
     [steps]
     (let [a (ctx/create-execution-context)]
       (try
         (let [d (sync/create-deferred a)
               n (atom 0)
               got (atom [])
               s (binding [ec/*execution-context* a]
                   (spin (if (= 1 (swap! n inc)) (await d) :fresh)))
               sid (spin-core/spin-id s)]
           (binding [ec/*execution-context* a
                     ec/*callback-egress-policy* :causal-follow]
             (s (fn [v] (swap! got conj [(:fork-id (ec/current-execution-context)) v]))
                (fn [e] (swap! got conj [:error (ex-message e)]))))
           (settle! a)
           (let [env {:a a :b (ctx/fork-context a) :c (ctx/fork-context a)
                      :s s :sid sid :d d}]
             (doseq [step steps] (step env))
             {:got @got
              :ids (into {} (map (fn [k] [k (:fork-id (env k))])) [:a :b :c])}))
         (finally (ctx/close-context! a))))))

#?(:clj
   (do
     (defn- complete-in! [w]
       (fn [{:keys [d] :as env}]
         (binding [ec/*execution-context* (env w)]
           (sync/deliver! d [:in w]))
         (settle! (env w))))

     (defn- supersede-in! [w]
       (fn [{:keys [s sid] :as env}]
         (let [ctx (env w)]
           (binding [ec/*execution-context* ctx]
             (simple/mark-dirty! ctx sid)
             (let [r (atom nil)
                   b (spin (await s))]
               (b #(reset! r %) #(reset! r [:error %]))
               (settle! ctx)
               (is (= :fresh @r) "the superseding await gets the fresh run"))))))

     (defn- once-per-world? [got]
       (= (count got) (count (distinct (map first got)))))))

#?(:clj
   (deftest an-invoker-callback-is-served-once-per-world
     (testing "the run completes in fork C (causal-follow fan-out); A's
               later fresh run serves A's own delivery — once per world"
       (let [{:keys [got ids]} (causal-follow-scenario
                                [(complete-in! :c) (supersede-in! :a)])]
         (is (once-per-world? got))
         (is (= #{[(:c ids) [:in :c]] [(:a ids) :fresh]} (set got)))))))

#?(:clj
   (deftest a-fork-completion-does-not-cancel-the-parents-hand-off
     (testing "C completes the copied run FIRST, then A's run is superseded:
               A must still get its delivery (from the fresh run) — a fork's
               completion is not the parent's"
       (let [{:keys [got ids]} (causal-follow-scenario
                                [(complete-in! :c) (supersede-in! :a) (complete-in! :b)])]
         (is (once-per-world? got))
         (is (some #{[(:a ids) :fresh]} got) "A is served by its fresh run")
         (is (some #{[(:c ids) [:in :c]]} got))))))

#?(:clj
   (deftest a-supersession-in-a-fork-leaves-the-parents-run-alone
     (testing "B supersedes the run in its own world; A then completes the
               ORIGINAL run in A — A's caller is served by A's run"
       (let [{:keys [got ids]} (causal-follow-scenario
                                [(supersede-in! :b) (complete-in! :c) (complete-in! :a)])]
         (is (once-per-world? got))
         (is (some #{[(:a ids) [:in :a]]} got) "A served by its own run")
         (is (some #{[(:c ids) [:in :c]]} got))))))

#?(:clj
   (deftest an-inline-superseding-run-does-not-strand-a-sibling-awaiter
     (testing "A awaits C (its run suspends); B's await supersedes C with a
               run that completes INLINE — A must still be resumed"
       (let [c (ctx/create-execution-context)]
         (try
           (binding [ec/*execution-context* c]
             (let [d (sync/create-deferred c)
                   n (atom 0)
                   ch (spin (if (= 1 (swap! n inc)) (await d) :fast))
                   ra (atom ::none)
                   rb (atom ::none)
                   a (spin (await ch))
                   b (spin (await ch))]
               (a #(reset! ra %) #(reset! ra [:error %]))
               (settle! c)
               (is (= ::none @ra) "A parked on C's first run")
               (b #(reset! rb %) #(reset! rb [:error %]))
               (settle! c)
               (is (= :fast @rb) "B got the superseding run's value inline")
               (is (= :fast @ra) "…and so did A, through the completion event")
               ;; the superseded run's late completion changes nothing
               (sync/deliver! d :slow)
               (settle! c)
               (is (= [:fast :fast] [@ra @rb]))
               (is (= :fast (:payload (:result (node (spin-core/spin-id ch))))))))
           (finally (ctx/close-context! c)))))))
