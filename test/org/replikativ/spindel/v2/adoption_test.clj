(ns org.replikativ.spindel.v2.adoption-test
  "Adoption follows the model's T1/T4/create-link and T11 (phase-d design §1.2
   R2/R3, §1.13): a candidate moves into the basis only after every
   acceptance check passed, a rejected predecessor stays in the adoption
   basis until T12."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await aseq take! offload]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.verify :as verify]
            [org.replikativ.spindel.v2.port.helpers :as h]
            [org.replikativ.spindel.incremental.interval :as iv]))

(def ^:dynamic *divergences* nil)

(defn- vworld []
  (v2/world {:verify? true :hook (verify/checking-hook *divergences*)}))

(defmacro checked [& body]
  `(binding [*divergences* (atom [])]
     ~@body
     (is (empty? @*divergences*) (str "Rule R divergences: " (vec (take 3 @*divergences*))))))

(defn- rid
  "The row ID behind handle `x`, inside a body or a world item."
  [x] (aget ^objects (v2/row-of x) rw/ID))

(defn- hid [w x] (v2/call-in! w #(rid x)))

(defn- proj [w] (v2/call-in! w #(verify/projection w)))

(defn- adoption
  "C's basis and adoption basis, as ID sets."
  [w c]
  (let [p (get-in (proj w) [:comps (hid w c)])]
    {:basis (set (map first (:basis p)))
     :adopt (set (get-in p [:adoption :basis]))}))

(defn- settle! [w] (v2/call-in! w (fn [] nil)) (v2/call-in! w (fn [] nil)))

;; ---------------------------------------------------------------------------
;; A-repl-1 (R3): rejected predecessors stay in the adoption basis

(deftest a-repl-1-source-kind-change
  ;; body sources share site -1: run 1 makes S (ord 0) and M (ord 1); run 2
  ;; makes the mailbox at ord 0, meets S, rejects it (T1: same kind) and
  ;; creates M2; S stays in the adoption basis until T12 releases it. Run 3
  ;; readopts M2.
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [s (v2/signal 0)
             gates {0 (v2/deferred) 1 (v2/deferred) 2 (v2/deferred)}
             seen (atom [])
             c (spin (let [v (iv/get-new (track s))
                           a (when (zero? v) (v2/signal 0))
                           m (v2/mailbox)]
                       (swap! seen conj [(when a (rid a)) (rid m)])
                       (await (get gates v))
                       v))
             u (v2/observe! c (fn [_ _]))
             [[sig m1]] @seen]
         (is (some? sig))
         (v2/write! s 1)
         (let [[_ m2] (peek @seen)
               a (adoption w c)]
           (is (not= m1 m2) "the mailbox at the signal's ordinal is a new source")
           (is (contains? (:basis a) m2))
           (is (not (contains? (:basis a) sig)) "the rejected signal does not move into the basis")
           (is (contains? (:adopt a) sig) "it stays in the adoption basis"))
         (v2/deliver! (gates 1) :go)
         (is (= 1 (v2/value c 2000 ::timeout)))
         (let [[_ m2] (peek @seen)
               a (adoption w c)]
           (is (= #{m2} (:basis a)) "T12 released the rejected signal")
           (is (empty? (:adopt a))))
         (v2/write! s 2)
         (let [[[_ m2] [_ m3]] (take-last 2 @seen)]
           (is (= m2 m3) "the next run readopts the mailbox"))
         (u)
         (verify/gc-settle! w)
         (let [srcs (set (keys (:sources (proj w))))
               ids (into #{} (comp cat (remove nil?)) @seen)]
           (is (empty? (filter srcs ids)) "no created source remains after demotion")))))))

(deftest a-kind-2-source-kind-change-under-a-key
  ;; A-kind-1 under a key (E1): body sources share site -1, so within K = [:k]
  ;; they are positional by n. Run 1 makes S [-1 [:k] 0] and M [-1 [:k] 1];
  ;; run 2's mailbox at n = 0 meets S, rejects it and is a new source; S stays
  ;; in the adoption basis until T12. Run 3 readopts the mailbox; demotion
  ;; leaves no row.
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [s (v2/signal 0)
             gates {0 (v2/deferred) 1 (v2/deferred) 2 (v2/deferred)}
             seen (atom [])
             c (spin (let [v (iv/get-new (track s))
                           [a m] (v2/with-key :k [(when (zero? v) (v2/signal 0)) (v2/mailbox)])]
                       (swap! seen conj [(when a (rid a)) (rid m)])
                       (await (get gates v))
                       v))
             u (v2/observe! c (fn [_ _]))
             [[sig m1]] @seen]
         (is (some? sig))
         (v2/write! s 1)
         (let [[_ m2] (peek @seen)
               a (adoption w c)]
           (is (not= m1 m2) "the mailbox at the signal's count is a new source")
           (is (contains? (:basis a) m2))
           (is (not (contains? (:basis a) sig)) "the rejected signal does not move into the basis")
           (is (contains? (:adopt a) sig) "it stays in the adoption basis"))
         (v2/deliver! (gates 1) :go)
         (is (= 1 (v2/value c 2000 ::timeout)))
         (let [[_ m2] (peek @seen)
               a (adoption w c)]
           (is (= #{m2} (:basis a)) "T12 released the rejected signal")
           (is (empty? (:adopt a))))
         (v2/write! s 2)
         (let [[[_ m2] [_ m3]] (take-last 2 @seen)]
           (is (= m2 m3) "the next run readopts the mailbox by key"))
         (u)
         (verify/gc-settle! w)
         (let [srcs (set (keys (:sources (proj w))))
               ids (into #{} (comp cat (remove nil?)) @seen)]
           (is (empty? (filter srcs ids)) "no created source remains after demotion")))))))

(deftest a-repl-1-task-changed-captures
  ;; T4: a spawn with changed captures is a fresh task; the predecessor stays
  ;; in the adoption basis and keeps running until the run completes, then
  ;; T12 cancels it.
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [s (v2/signal 0)
             never (v2/deferred)
             gates {0 (v2/deferred) 1 (v2/deferred)}
             log (atom [])
             ks (atom [])
             c (spin (let [v (iv/get-new (track s))
                           k (task (try (await never) (finally (swap! log conj [:fin v]))))]
                       (swap! ks conj (rid k))
                       (await (get gates v))
                       v))
             u (v2/observe! c (fn [_ _]))]
         (v2/write! s 1)
         (settle! w)
         (let [[k1 k2] @ks
               p (proj w)
               a (adoption w c)]
           (is (not= k1 k2) "changed captures: a fresh task")
           (is (= [] @log) "the predecessor is not cancelled at the spawn")
           (is (contains? (:adopt a) k1) "the predecessor stays in the adoption basis")
           (is (contains? (:basis a) k2))
           (is (some? (get-in p [:tasks k1 :run])) "and keeps running"))
         (v2/deliver! (gates 1) :go)
         (is (= 1 (v2/value c 2000 ::timeout)))
         (is (h/wait-until #(= [[:fin 0]] @log)) "T12 cancels the predecessor")
         (is (empty? (:adopt (adoption w c))))
         (u)
         (is (h/wait-until #(= [[:fin 0] [:fin 1]] @log)) "demotion cancels the current task"))))))

(deftest a-repl-1-sequence-changed-initial-state
  ;; create-link: a sequence with a changed initial state is a new link; the
  ;; predecessor stays in the adoption basis until T12.
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [s (v2/signal 0)
             gates {0 (v2/deferred) 1 (v2/deferred)}
             ls (atom [])
             c (spin (let [v (iv/get-new (track s))
                           xs (aseq [n v] [n (inc n)])]
                       (swap! ls conj (rid xs))
                       (await (get gates v))
                       (first (await xs))))
             u (v2/observe! c (fn [_ _]))]
         (v2/write! s 1)
         (let [[l1 l2] @ls
               a (adoption w c)]
           (is (not= l1 l2) "a changed initial state: a new sequence")
           (is (contains? (:basis a) l2))
           (is (contains? (:adopt a) l1) "the predecessor stays in the adoption basis"))
         (v2/deliver! (gates 1) :go)
         (is (= 1 (v2/value c 2000 ::timeout)))
         (let [[l1 l2] @ls
               a (adoption w c)]
           (is (= #{l2} (:basis a)))
           (is (not (contains? (:adopt a) l1)) "T12 released it"))
         (u))))))

;; ---------------------------------------------------------------------------
;; A-cut (R2): T11's cut replaces the adoption basis and baselines with the
;; latest suffix (`comp-cut-row`); Rule R cancels a superseded running task
;; that nothing else retains (§3.3 step 1.2)

(deftest a-cut-2a-superseded-task-is-cancelled-at-the-cut
  ;; run 1 spawns a polling task; runs 2 and 3 do not re-create it and never
  ;; complete. The second cut drops it (an empty suffix): nothing else
  ;; retains it, so it is cancelled there, its finally runs once.
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [s (v2/signal 0)
             never (v2/deferred)
             log (atom [])
             ks (atom [])
             c (spin (let [v (iv/get-new (track s))]
                       (when (zero? v)
                         (swap! ks conj (rid (task (try (loop [] (v2/sleep 20) (recur))
                                                        (finally (swap! log conj :fin)))))))
                       (await never)))
             u (v2/observe! c (fn [_ _]))
             [k] @ks]
         (v2/write! s 1)
         (settle! w)
         (is (= [] @log) "the first cut keeps it in the adoption basis")
         (is (= #{k} (:adopt (adoption w c))))
         (v2/write! s 2)
         (is (h/wait-until #(= [:fin] @log)) "the next cut drops it: cancelled, its finally runs")
         (is (empty? (:adopt (adoption w c))) "the empty suffix replaced the adoption basis")
         (verify/gc-settle! w)
         (is (nil? (get-in (proj w) [:tasks k])) "the row goes once its cleanup ended")
         (is (= [:fin] @log) "once")
         (u))))))

(deftest a-cut-2b-task-awaited-elsewhere-keeps-running
  (testing "a superseded task another live computation awaits runs on and completes"
    (checked
     (let [w (vworld)]
       (binding [v2/*world* w]
         (let [s (v2/signal 0)
               never (v2/deferred)
               fin (v2/deferred)
               held (atom nil)
               ks (atom [])
               c (spin (let [v (iv/get-new (track s))]
                         (when (even? v)
                           (let [k (task (await fin))]   ; the same captures in every run
                             (reset! held k)
                             (swap! ks conj (rid k))))
                         (await never)))
               u (v2/observe! c (fn [_ _]))
               k0 @held
               o (spin (await k0))
               seen (atom [])
               uo (v2/observe! o (fn [v _] (swap! seen conj v)))]
           (v2/write! s 1)
           (v2/write! s 2)
           (settle! w)
           (let [[k1 k2] @ks]
             (is (not= k1 k2) "it is not readopted by a later run of its creator")
             (is (not (contains? (:adopt (adoption w c)) k1)))
             (is (some? (get-in (proj w) [:tasks k1 :run])) "it keeps running"))
           (v2/deliver! fin :done)
           (is (h/wait-until #(= [:done] @seen)) "and completes for the computation awaiting it")
           (uo)
           (u))))))
  (testing "it is cancelled once that computation stops awaiting it"
    (checked
     (let [w (vworld)]
       (binding [v2/*world* w]
         (let [s (v2/signal 0)
               never (v2/deferred)
               log (atom [])
               held (atom nil)
               c (spin (let [v (iv/get-new (track s))]
                         (when (zero? v)
                           (reset! held (task (try (await never) (finally (swap! log conj :fin))))))
                         (await never)))
               u (v2/observe! c (fn [_ _]))
               o (spin (await @held))
               uo (v2/observe! o (fn [_ _]))]
           (v2/write! s 1)
           (v2/write! s 2)
           (settle! w)
           (is (= [] @log) "kept across both cuts by the awaiting computation")
           (uo)
           (is (h/wait-until #(= [:fin] @log)) "cancelled when it stops awaiting")
           (u)))))))

(deftest a-cut-handle-only-does-not-keep-a-running-task
  ;; §3.4: a handle admits only a completed task; the host holding the
  ;; handle (without waiting on it) does not keep the superseded task running.
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [s (v2/signal 0)
             never (v2/deferred)
             log (atom [])
             held (atom nil)
             c (spin (let [v (iv/get-new (track s))]
                       (when (zero? v)
                         (reset! held (task (try (await never) (finally (swap! log conj :fin))))))
                       (await never)))
             u (v2/observe! c (fn [_ _]))]
         (v2/write! s 1)
         (v2/write! s 2)
         (is (h/wait-until #(= [:fin] @log)) "cancelled at the second cut")
         (is (= ::v2/cancelled (try (v2/value @held 1000 ::timeout)
                                    (catch Throwable e (:spindel/cancelled (ex-data e) e))))
             "the handle reads the cancellation")
         (u))))))

(deftest a-cut-census-repeated-interruptions
  ;; I11b: retention stays bounded by the last runs. Every other run spawns a
  ;; task capturing the run's value; no run completes.
  (let [w (v2/world {:verify? true})]
    (binding [v2/*world* w]
      (let [s (v2/signal 0)
            never (v2/deferred)
            c (spin (let [v (iv/get-new (track s))]
                      (when (even? v) (task (await never) v))
                      (await never)))
            u (v2/observe! c (fn [_ _]))
            census #(do (verify/gc-settle! w)
                        (v2/call-in! w (fn [] (frequencies (map (fn [r] (aget ^objects r rw/TYPE))
                                                                (vals (aget ^objects w rw/W-REG)))))))]
        (dotimes [i 100] (v2/write! s (inc i)))
        (let [before (census)]
          (dotimes [i 10000] (v2/write! s (+ 101 i)))
          ;; coalesced writes can leave the previous run's task in the adoption
          ;; basis beside the current one (with its run, activation and wait
          ;; edge): the last two runs, never more
          (let [after (census)]
            (is (<= (get after rw/T-TASK 0) 2) (str before " -> " after))
            (is (<= (get after rw/T-RUN 0) 3) (str before " -> " after))
            (is (<= (reduce + (vals after)) (+ 4 (reduce + (vals before)))) (str before " -> " after))
            (is (<= (count (:adopt (adoption w c))) 1) "only the latest suffix")))
        (u)))))

;; ---------------------------------------------------------------------------
;; The cut keeps baselines only for edges that have one (the model's
;; `bases-of` over `has-base`: tracks, awaits of signals and cells, delivered
;; awaits re-armed with their result, reactivation edges; §4.4)

(deftest a-cut-baselines-only-for-edges-with-a-baseline
  ;; run 1 awaits a computation (delivered), tracks a signal and awaits a
  ;; deferred (pending) after its re-entry site; run 2 does none of them and
  ;; parks on a mailbox take (a wait edge). The pending await has no baseline.
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [s (v2/signal 0)
             t (v2/signal 0)
             d (v2/deferred)
             mb (v2/mailbox)
             y (spin (iv/get-new (track t)))
             c (spin (let [v (iv/get-new (track s))]
                       (when (zero? v)
                         (await y)
                         (iv/get-new (track t))
                         (await d))
                       (take! mb)))
             u (v2/observe! c (fn [_ _]))
             baselines #(set (map second (get-in (proj w) [:comps (hid w c) :adoption :baselines])))]
         (v2/write! s 1)
         (is (= #{(hid w t) (hid w y)} (baselines))
             "the tracked signal and the delivered await keep a baseline, the pending deferred none")
         (u))))))

(deftest a-cut-pending-await-does-not-retain-its-debtor
  ;; run 1 awaits a computation that is itself parked; run 2 does not await
  ;; it. The pending await has no baseline, so nothing retains the computation
  ;; after the cut: it is demoted there and its run is cancelled.
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [s (v2/signal 0)
             d (v2/deferred)
             mb (v2/mailbox)
             log (atom [])
             x (spin (try (await d) (finally (swap! log conj :x-fin))))
             c (spin (let [v (iv/get-new (track s))]
                       (when (zero? v) (await x))
                       (take! mb)))
             u (v2/observe! c (fn [_ _]))]
         (is (false? (get-in (proj w) [:comps (hid w x) :idle])) "run 1 awaits x, which runs")
         (v2/write! s 1)
         (is (h/wait-until #(= [:x-fin] @log)) "x's run is cancelled at the cut")
         (is (true? (get-in (proj w) [:comps (hid w x) :idle])) "x is demoted")
         (is (empty? (get-in (proj w) [:comps (hid w c) :adoption :baselines])))
         (u))))))

;; ---------------------------------------------------------------------------
;; Demotion of a parked computation that never completed and has a handle
;; (§3.3): step 2 cancels its stray run before step 3 demotes it, so the
;; epoch steps only when the run survives in cleanup (Z#42: a run kept in
;; cleanup is stale); kept for its handle, it takes its validity from the
;; removed edges, and an edge that never consumed a version makes it fail
;; (Z#24).

(deftest demote-parked-fresh-computation
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [d (v2/deferred)
             t (v2/signal 0)
             mb (v2/mailbox)
             row #(get-in (proj w) [:comps (hid w %)])
             x (spin (await d))
             y (spin (try (await d) (finally nil)))
             z (spin (iv/get-new (track t)) (take! mb))]
         (testing "a run that retires at the cancel leaves nothing to make stale"
           ((v2/observe! x (fn [_ _])))
           (is (= 1 (:epoch (row x))))
           (is (= :invalid (:validity (row x))) "the await never consumed a version"))
         (testing "a run kept in cleanup is made stale"
           ((v2/observe! y (fn [_ _])))
           (is (= 2 (:epoch (row y)))))
         (testing "edges that all consumed a version give the validity"
           ((v2/observe! z (fn [_ _])))
           (is (= 1 (:epoch (row z))))
           (is (= [[(hid w t) 0]] (:validity (row z))))))))))

;; ---------------------------------------------------------------------------
;; An idle computation keeps no run (§3.4); a run of it still in cleanup keeps
;; it as a tombstone (§3.2) until that run retires.

(defn- hold-until
  ;; an offload that acknowledges its cancellation only once `p` is delivered
  [started p]
  (fn []
    (deliver started true)
    (while (not (realized? p)) (try (Thread/sleep 1) (catch InterruptedException _)))
    :held))

(deftest idle-computation-keeps-no-run
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [d (v2/deferred)
             row #(get-in (proj w) [:comps (hid w %)])
             y (spin (try (await d) (finally nil)))]
         ((v2/observe! y (fn [_ _])))
         (is (true? (:idle (row y))))
         (is (nil? (:run (row y))) "demoted with its run in cleanup, it keeps no run"))))))

(deftest idle-computation-with-run-in-cleanup
  (testing "re-observed while its old run is in cleanup, it starts a fresh run"
    (checked
     (let [w (vworld)]
       (binding [v2/*world* w]
         (let [started (promise) hold (promise)
               row #(get-in (proj w) [:comps (hid w %)])
               y (spin (offload (hold-until started hold)))
               u1 (v2/observe! y (fn [_ _]))
               _ (deref started 1000 nil)
               r1 (:run (row y))]
           (u1)
           (is (true? (:idle (row y))))
           (is (nil? (:run (row y))) "idle: it keeps no run")
           (is (some? (get-in (proj w) [:runs r1])) "its old run is still in cleanup")
           (let [seen (atom [])
                 u2 (v2/observe! y (fn [v _] (swap! seen conj v)))]
             (is (false? (:idle (row y))))
             (is (not= r1 (:run (row y))) "a fresh run")
             (deliver hold true)
             (is (h/wait-until #(= [:held] @seen)))
             (is (h/wait-until #(nil? (get-in (proj w) [:runs r1]))) "the old run retires")
             (u2)))))))
  (testing "its last handle dropped while the run is in cleanup, it stays until the run retires"
    (checked
     (let [w (vworld)]
       (binding [v2/*world* w]
         (let [started (promise) hold (promise)
               y (spin (offload (hold-until started hold)))
               u (v2/observe! y (fn [_ _]))
               _ (deref started 1000 nil)
               id (hid w y)]
           (u)
           (v2/release! y)
           (is (some? (get-in (proj w) [:comps id])) "kept as its cleanup run's tombstone")
           (deliver hold true)
           (is (h/wait-until #(nil? (get-in (proj w) [:comps id]))) "removed once the run retired")))))))

(deftest every-cleanup-run-keeps-its-computation
  ;; The model keeps a computation for every cleanup entry of its runs
  ;; (`cleanup-base`: a run's stored rows hold R.of). Re-demanded and demoted
  ;; again while its first run is in cleanup, with the new run kept in
  ;; cleanup too and its last handle gone, it stays until BOTH runs retire,
  ;; whichever finishes first.
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [[s1 h1 s2 h2] (repeatedly 4 promise)
             pairs (atom [[s1 h1] [s2 h2]])
             pick! (fn [] (let [[s h] (first @pairs)] (swap! pairs rest) (hold-until s h)))
             y (spin (offload (pick!)))
             id (hid w y)
             runs-of-y #(count (filter (fn [[_ r]] (= id (:of r))) (:runs (proj w))))]
         (let [u (v2/observe! y (fn [_ _]))] (deref s1 1000 nil) (u))
         (let [u (v2/observe! y (fn [_ _]))] (deref s2 1000 nil) (u))
         (v2/release! y)
         (is (= 2 (runs-of-y)) "both runs are in cleanup")
         (is (some? (get-in (proj w) [:comps id])))
         (deliver h2 true)                    ; the new run's cleanup ends first
         (is (h/wait-until #(= 1 (runs-of-y))))
         (is (some? (get-in (proj w) [:comps id])) "kept: its first run is still in cleanup")
         (deliver h1 true)
         (is (h/wait-until #(zero? (runs-of-y))))
         (is (h/wait-until #(nil? (get-in (proj w) [:comps id]))) "removed once both runs retired"))))))

(deftest cleanup-run-count-across-a-fork
  ;; C-RUNS follows W-RUNS: a fork copies the computation row with its count
  ;; and inherits every unretired run; each world retires its own copy of the
  ;; run once and counts down its own copy of the computation. Here the child
  ;; discharges the inherited offload at its first turn, the parent waits for
  ;; the late acknowledgement: each keeps the computation exactly as long as
  ;; its own copy of the run is unretired.
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [started (promise) hold (promise)
             y (spin (offload (hold-until started hold)))
             id (hid w y)
             comp-in (fn [wx] (get-in (v2/call-in! wx #(verify/projection wx)) [:comps id]))]
         (let [u (v2/observe! y (fn [_ _]))] (deref started 1000 nil) (u))
         (let [child (v2/fork! w)
               yc (v2/in-world child y)]
           (v2/release! yc)
           (v2/release! y)
           (is (h/wait-until #(nil? (comp-in child))) "the child retires its copy of the run and drops y")
           (is (some? (comp-in w)) "the parent keeps y while its run is in cleanup")
           (deliver hold true)
           (is (h/wait-until #(nil? (comp-in w))) "then drops it")
           (v2/release-world! child)))))))
