(ns org.replikativ.spindel.engine.context-retention-test
  "Memory retention: what a context, and a node inside it, must let go of.

   1. A STOPPED, unreferenced context is collectable, also after it awaited
      a deferred (the differential DOM fuzzer's defect 4). `create-atom`
      used to register each RuntimeAtom with a Cleaner whose action closed
      over the creating context; a Cleaner keeps its action strongly
      reachable until the target is collected, and the context's state
      reaches the atom (the awaiting spin's continuation captures the
      deferred's state atom) — so the atom, the context and everything its
      continuations close over were pinned for the life of the process.
      The action now holds only the atom id and a weak reference to the
      state backend (`org.replikativ.spindel.atom`).

   2. A child its creator stopped re-creating is detached from the graph
      when the creator's run completes, and reaped once its Spin object is
      collected (`release-superseded-children!` / `superseded-child?` in
      engine/impl/simple.cljc). Before, it kept its track continuations, and
      `gc-quiescent?` refuses any spin with a track subscription: a removed
      list item stayed in state, stayed an observer of its signals, and each
      later change re-ran it as an independent observer.

   GC is measured, not waited for: a WeakReference probe polled after
   `System/gc`, with a bounded number of rounds. The reap tests drive the
   Cleaner's entry point (`try-gc-cleanup-spin!`) directly where the order
   of collection versus re-run matters, so they are deterministic."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.atom :as ratom]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.engine.nodes :as nodes]
            [org.replikativ.spindel.engine.state-backend :as backend]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]])
  (:import [java.lang.ref WeakReference]))

;; =============================================================================
;; GC measurement
;; =============================================================================

(defn- cleared?
  "Poll `refs` after `System/gc` until every WeakReference has cleared, at
   most `rounds` times. A measurement, not a synchronization: the answer
   is whether the referents are unreachable."
  [refs rounds]
  (loop [i 0]
    (cond (every? #(nil? (.get ^WeakReference %)) refs) true
          (>= i rounds) false
          :else (do (System/gc) (recur (inc i))))))

(defn- stopped-context-refs
  "Create a context, run `setup!` in it, stop it, and return weak
   references to the context record and its state backend. Nothing else
   escapes this frame."
  [setup!]
  (let [c (ctx/create-execution-context)]
    (binding [ec/*execution-context* c]
      (setup! c))
    (ctx/stop-context! c)
    [(WeakReference. c) (WeakReference. (:backend c))]))

(defn- await-deferred! [c]
  (let [d (sync/create-deferred c)]
    ((spin (await d)) (fn [_]) (fn [_]))))

;; =============================================================================
;; 1. Stopped contexts are collectable
;; =============================================================================

(deftest a-stopped-context-without-atoms-is-collected
  (testing "control: if this fails, the measurement itself is inconclusive"
    (is (cleared? (stopped-context-refs (fn [_] nil)) 50))))

(deftest stopped-contexts-that-awaited-deferreds-are-collected
  (let [refs (into [] (mapcat (fn [_] (stopped-context-refs await-deferred!)))
                   (range 25))]
    (is (cleared? refs 50)
        (str (count (remove #(nil? (.get ^WeakReference %)) refs))
             " of " (count refs) " references (context + backend per context) "
             "still reachable: the atom Cleaner pins its context"))))

(deftest stopped-contexts-with-atoms-mailboxes-and-signals-are-collected
  (let [refs (into []
                   (mapcat
                    (fn [_]
                      (stopped-context-refs
                       (fn [c]
                         (let [a  (ratom/atom 0)
                               mb (sync/create-mailbox c)
                               s  (sig/signal 1)]
                           (swap! a inc)
                           ((spin (await mb)) (fn [_]) (fn [_]))
                           ((spin (let [{v :new} (track s)] (+ v @a))) (fn [_]) (fn [_]))
                           (simple/await-drain-complete! c))))))
                   (range 10))]
    (is (cleared? refs 50))))

(deftest a-dropped-atom-still-leaves-the-live-contexts-state
  (testing "the weak cleanup path still reclaims the entry while the context lives"
    (let [c (ctx/create-execution-context)]
      (try
        (binding [ec/*execution-context* c]
          (let [id (let [a (ratom/atom :x)] (.-id ^org.replikativ.spindel.atom.RuntimeAtom a))]
            (is (some? (ec/get-state [:atoms id])))
            (is (loop [i 0]
                  (cond (nil? (ec/get-state [:atoms id])) true
                        (>= i 50) false
                        :else (do (System/gc)
                                  ;; the Cleaner thread runs the action
                                  (Thread/yield)
                                  (recur (inc i)))))
                "the atom's [:atoms id] entry is removed once the atom is collected")))
        (finally (ctx/stop-context! c))))))

;; =============================================================================
;; 2. Superseded children are reaped
;; =============================================================================

(defn- children-of [creator-id]
  (into #{} (keep (fn [[id n]] (when (= creator-id (:created-by n)) id)))
        (ec/get-state [:nodes])))

(defn- orphan-all!
  "What the Cleaner does when each Spin object is collected: mark (or reap)."
  [c ids]
  (doseq [id ids] (simple/try-gc-cleanup-spin! c id))
  (simple/await-drain-complete! c))

(defn- gone? [id signal-id]
  {:node        (contains? (ec/get-state [:nodes]) id)
   :track-subs  (contains? (ec/get-state [:track-subscriptions]) id)
   :subscribed  (boolean (some #(contains? % id) (vals (ec/get-state [:subscriptions]))))
   :observer    (contains? (nodes/get-observers (ec/get-state [:nodes signal-id])) id)})

(defn- item-of
  "The value a child spin last completed with."
  [id]
  (let [r (nodes/get-value (ec/get-state [:nodes id]))]
    (:payload r)))

(def ^:private absent {:node false :track-subs false :subscribed false :observer false})

(defn- list-parent
  "A parent tracking `s` that creates one child per item; each child also
   tracks `s` (a changed signal makes every child a descendant observer)
   and counts its body runs per item in `runs`."
  [s runs]
  (spin (let [{st :new} (track s)]
          (mapv (fn [i] (await (spin (let [{v :new} (track s)]
                                       (swap! runs update i (fnil inc 0))
                                       [i (:x v)]))))
                (:items st)))))

(defn- removed-child-scenario
  "Mount the list [0 1 2], then apply `change` (which drops item 2).
   `orphan-before?` runs the Cleaner on every child BEFORE the change (the
   Spin objects died early), otherwise after it. Returns the observations."
  [change orphan-before?]
  (let [c (ctx/create-execution-context)
        out (atom [])
        runs (atom {})]
    (try
      (binding [ec/*execution-context* c]
        (let [s (sig/signal {:items [0 1 2] :x 1})
              p (list-parent s runs)
              pid (spin-core/spin-id p)]
          (p #(swap! out conj %) #(swap! out conj [:error %]))
          (simple/await-drain-complete! c)
          (let [kids (children-of pid)
                by-item (into {} (map (fn [id] [(first (item-of id)) id])) kids)
                removed (get by-item 2)]
            (when orphan-before? (orphan-all! c kids))
            (change s)
            (simple/await-drain-complete! c)
            (when-not orphan-before? (orphan-all! c kids))
            (let [after-change (gone? removed (:id s))
                  runs-before (get @runs 2)]
              ;; A later change: must not re-run the removed item, and (for
              ;; orphan-before?) nothing is left to reap.
              (swap! s assoc :x 10)
              (simple/await-drain-complete! c)
              {:removed removed
               :after-change after-change
               :after-next-change (gone? removed (:id s))
               :removed-reran? (not= runs-before (get @runs 2))
               :out (last @out)
               :survivors (count (children-of pid))}))))
      (finally (ctx/stop-context! c)))))

(deftest a-removed-item-is-reaped-when-collected-after-the-change
  (testing "removal in the same change as a signal update"
    (let [r (removed-child-scenario #(reset! % {:items [0 1] :x 2}) false)]
      (is (some? (:removed r)))
      (is (= absent (:after-change r))
          "node, track conts, subscriptions and signal observer all gone")
      (is (= absent (:after-next-change r)))
      (is (not (:removed-reran? r)) "a later change does not re-run the removed item")
      (is (= [[0 10] [1 10]] (:out r)))
      (is (= 2 (:survivors r)) "the kept items stay")))
  (testing "removal alone (the items' tracked value is unchanged)"
    (let [r (removed-child-scenario #(swap! % update :items pop) false)]
      (is (= absent (:after-change r)))
      (is (not (:removed-reran? r)))
      (is (= 2 (:survivors r))))))

(deftest a-removed-item-collected-before-the-change-is-reaped-when-dropped
  (let [r (removed-child-scenario #(reset! % {:items [0 1] :x 2}) true)]
    (testing "orphaned while still held; reaped as soon as its creator's run drops it"
      (is (= absent (:after-change r)))
      (is (= absent (:after-next-change r)))
      (is (not (:removed-reran? r)) "it is not resumed as an independent observer")
      (is (= [[0 10] [1 10]] (:out r)))
      (is (= 2 (:survivors r))))))

(deftest a-removed-item-is-detached-before-any-gc
  (testing "its own track cont reaches its Spin object (through its awaiter's
            loop state), so GC alone could never collect it: the creator's
            completing run detaches it"
    (let [c (ctx/create-execution-context)
          runs (atom {})]
      (try
        (binding [ec/*execution-context* c]
          (let [s (sig/signal {:items [0 1 2] :x 1})
                p (list-parent s runs)
                pid (spin-core/spin-id p)]
            (p (fn [_]) (fn [_]))
            (simple/await-drain-complete! c)
            (let [removed (some #(when (= 2 (first (item-of %))) %) (children-of pid))]
              (reset! s {:items [0 1] :x 2})
              (simple/await-drain-complete! c)
              (is (= (assoc absent :node true) (gone? removed (:id s)))
                  "still in state (its Spin is not collected), but out of the graph")
              (is (= :dirty (:status (ec/get-state [:nodes removed])))
                  "a later access re-runs it instead of serving the old result")
              (swap! s assoc :x 3)
              (simple/await-drain-complete! c)
              (is (= 1 (get @runs 2)) "a later change does not re-run it")
              (orphan-all! c [removed])
              (is (= absent (gone? removed (:id s))) "reaped once collected"))))
        (finally (ctx/stop-context! c))))))

(deftest a-child-created-before-the-resume-point-is-kept
  (testing "a creator resumed from a LATER track does not re-create an earlier
            child; that child stays held and reactive even when orphaned"
    (let [c (ctx/create-execution-context)
          runs (atom 0)]
      (try
        (binding [ec/*execution-context* c]
          (let [a (sig/signal 1)
                b (sig/signal 1)
                p (spin (let [child (spin (let [{v :new} (track a)] (swap! runs inc) v))]
                          ;; fire-and-forget: nobody awaits the child
                          (child (fn [_]) (fn [_]))
                          (let [{v :new} (track b)] v)))
                pid (spin-core/spin-id p)]
            (p (fn [_]) (fn [_]))
            (simple/await-drain-complete! c)
            (let [[kid] (seq (children-of pid))]
              (is (some? kid))
              (is (= 1 @runs))
              (reset! b 2)               ; resume p from (track b)
              (simple/await-drain-complete! c)
              (orphan-all! c [kid])
              (is (contains? (ec/get-state [:nodes]) kid)
                  "held as a kept child, not reaped as superseded")
              (reset! a 2)
              (simple/await-drain-complete! c)
              (is (= 2 @runs) "still reacts to its own signal"))))
        (finally (ctx/stop-context! c))))))

(deftest a-following-fork-keeps-a-child-its-own-creator-still-holds
  (testing "the parent's creator drops the child, the fork's still holds it:
            the detach must not reach the fork through read-through state"
    (let [p (ctx/create-execution-context)]
      (try
        (let [[s t par] (binding [ec/*execution-context* p]
                          (let [s (sig/signal {:on true})
                                t (sig/signal 0)
                                par (spin (let [{v :new} (track s)]
                                            (if (:on v)
                                              (await (spin (let [{x :new} (track t)] x)))
                                              0)))]
                            [s t par]))]
          (binding [ec/*execution-context* p]
            (is (= 0 @par))
            (simple/await-drain-complete! p))
          (let [f (ctx/fork-context p)]
            (binding [ec/*execution-context* f]
              (reset! s {:on true :n 1})          ; the fork's creator re-runs, holds the child
              (simple/await-drain-complete! f))
            (binding [ec/*execution-context* p]
              (reset! s {:on false})              ; the parent's creator drops it
              (simple/await-drain-complete! p)
              (is (= 0 @par)))
            (binding [ec/*execution-context* f]
              (reset! t 5)
              (simple/await-drain-complete! f)
              (is (= 5 @par) "the child still re-runs in the fork"))))
        (finally (ctx/stop-context! p))))))

(defn- dropped-child-effects
  "A creator, while `on`, makes a child with an effect (built by
   `make-child`), stores it in a user atom and awaits it; then `on` flips
   off and the holder awaits the child again. Returns how often the child's
   body ran."
  [make-child]
  (let [c (ctx/create-execution-context)
        effects (atom 0)
        holder (atom nil)]
    (try
      (binding [ec/*execution-context* c]
        (let [on (sig/signal true)
              par (spin (let [{v :new} (track on)]
                          (if v
                            (let [child (make-child effects)]
                              (reset! holder child)
                              (await child))
                            :off)))]
          (is (= :sent @par))
          (simple/await-drain-complete! c)
          (reset! on false)
          (simple/await-drain-complete! c)
          (is (= :off @par))
          (is (= :sent @(spin (await @holder))))
          @effects))
      (finally (ctx/stop-context! c)))))

(deftest a-dropped-child-without-reactivity-is-not-re-run
  (testing "a completed child that tracks nothing keeps its clean result: a
            holder awaiting it later does not re-run its effects"
    (is (= 1 (dropped-child-effects
              (fn [effects] (spin (swap! effects inc) :sent))))))
  (testing "also when it awaited a spin that tracks nothing (an await leaves a
            persistent :await-reactive cont; that alone is no reactivity)"
    (is (= 1 (dropped-child-effects
              (fn [effects] (spin (swap! effects inc)
                                  (await (spin :g))
                                  :sent)))))))

(deftest a-fork-sweep-does-not-copy-the-parents-creator
  (testing "while a following fork defers the parent's detach, the fork's own
            generation sweep must not act on (and so copy) the parent's creator"
    (let [p (ctx/create-execution-context)]
      (try
        (let [[items par] (binding [ec/*execution-context* p]
                            (let [items (sig/signal [0 1 2])
                                  par (spin (let [{xs :new} (track items)]
                                              (mapv (fn [i] (await (spin (let [{v :new} (track items)]
                                                                           [i (count v)]))))
                                                    xs)))]
                              @par
                              (simple/await-drain-complete! p)
                              [items par]))
              pid (spin-core/spin-id par)
              f (ctx/fork-context p)
              local? #((backend/entity-locality (:backend f)) :nodes %)]
          (binding [ec/*execution-context* p]
            (reset! items [0 1])                 ; deferred: f follows p
            (simple/await-drain-complete! p))
          (binding [ec/*execution-context* f]
            (let [other (sig/signal 0)]          ; an unrelated change in the fork
              (reset! other 1)
              (simple/await-drain-complete! f)))
          (is (not (local? pid)) "the fork still reads the parent's creator through")
          (binding [ec/*execution-context* p]
            (reset! items [0 1 7])
            (simple/await-drain-complete! p)
            (is (= [[0 3] [1 3] [7 3]] @par)))
          (is (= [[0 3] [1 3] [7 3]] (binding [ec/*execution-context* f] @par))
              "the fork follows the parent's recomputed creator"))
        (finally (ctx/stop-context! p))))))

(deftest gc-cleanup-in-a-fork-never-copies-a-parent-node
  (testing "a fork's Spin object with the structural id of a PARENT node dies:
            the cleanup must not write that node (or its deps) into the
            fork's overlay, or the fork stops following the parent there"
    (let [p (ctx/create-execution-context)]
      (try
        (let [[a e] (binding [ec/*execution-context* p]
                      (let [a (sig/signal 1)
                            e (spin (* 10 (:new (track a))))]
                        @e
                        (simple/await-drain-complete! p)
                        [a e]))
              eid (spin-core/spin-id e)
              f (ctx/fork-context p)
              local? #((backend/entity-locality (:backend f)) :nodes %)]
          (is (not (local? eid)) "precondition: the fork reads e through")
          ;; what the Cleaner does when a fork-side Spin object with e's id dies
          (simple/try-gc-cleanup-spin! f eid)
          (simple/await-drain-complete! f)
          (is (not (local? eid)) "e was not copied into the fork")
          (is (not (local? (:id a))) "nor was the signal it tracks")
          (binding [ec/*execution-context* p]
            (reset! a 2)
            (simple/await-drain-complete! p)
            (is (= 20 @e)))
          (is (= 20 (binding [ec/*execution-context* f] @(spin (await e))))
              "the fork still follows the parent's recomputed e"))
        (finally (ctx/stop-context! p))))))

(deftest dependence-is-decided-per-child-over-a-shared-chain
  (testing "dropped children awaiting one shared constant chain: only the one
            that also tracks a signal is dirtied (the pass memoizes the chain)"
    (let [c (ctx/create-execution-context)
          runs (atom {})
          held (atom {})]
      (try
        (binding [ec/*execution-context* c]
          (let [on (sig/signal true)
                s (sig/signal 1)
                chain (reduce (fn [prev _] (if prev (spin (inc (await prev))) (spin 0)))
                              nil (range 20))
                par (spin (let [{v :new} (track on)]
                            (if v
                              (let [a (spin (swap! runs update :a (fnil inc 0))
                                            (+ (await chain) (:new (track s))))
                                    b (spin (swap! runs update :b (fnil inc 0))
                                            (await chain))]
                                (reset! held {:a a :b b})
                                [(await a) (await b)])
                              :off)))]
            (is (= [20 19] @par))
            (simple/await-drain-complete! c)
            (reset! on false)
            (simple/await-drain-complete! c)
            (is (= 20 @(spin (await (:a @held)))))
            (is (= 19 @(spin (await (:b @held)))))
            (is (= {:a 2 :b 1} @runs)
                "the signal-dependent child re-runs, the constant one does not")))
        (finally (ctx/stop-context! c))))))
