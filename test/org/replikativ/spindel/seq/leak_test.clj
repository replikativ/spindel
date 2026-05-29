(ns org.replikativ.spindel.seq.leak-test
  "Retention / memory-leak REGRESSION GUARDS for the async-sequence + sync +
  pubsub stack. Each pins a leak found in the 2026-05 retention audit and
  fixed in the same pass — they must stay green:

  - #1 `gen-aseq` shared-term-deferred `:pending` accumulation (one dead await
    continuation per consumed element, living in engine state). Fixed: a
    single-shot per-`anext` deferred, no shared accumulator.
  - #2 partial-cps `sequence` retaining already-consumed elements (a held
    mid-stream node pinning the whole consumed prefix). Fixed: lazy-cell
    rewrite that releases the consumed prefix.
  - #3 `Mailbox` stranded waiters — a cancelled `await` left its waiter in
    `:waiters` (pruned only on a later post). Fixed: prune cancelled waiters
    on take too.
  - #4 `pub` idle-topic mults — a high-cardinality topic-fn auto-created one
    mult per distinct topic, never reclaimed. Fixed: the pump routes only to
    subscribed topics (others dropped), and a topic is reclaimed on last untap.
  - #5 `parallel` orphaning a permanent per-call `[:parallel/results <id>]`
    entry in engine state. Fixed: initial accumulator in a LOCAL atom, reactive
    result on the spin's node (reclaimed by normal teardown).
  - #6 `Deferred` `:pending` — same pattern as #3 (cancelled awaits on a
    never-delivered deferred stranded their reader). Fixed: thread the cancel
    token, prune cancelled readers on await.
  - #7 `Semaphore` `:waiting-queue` — same pattern (cancelled acquires
    stranded their waiter, and `release` would hand the permit to a dead
    acquirer). Fixed: prune cancelled acquirers on acquire, skip them on release.

  (#3, #6, #7 are one consistency fix — cancellation-aware wait-list pruning —
  applied uniformly across the three sync primitives.)

  JVM-only (`.clj`): the structural probes read engine internals and the #2
  retention probe uses java.lang.ref.WeakReference, neither of which has a
  CLJS equivalent."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.state-backend :as backend]
            [org.replikativ.spindel.seq.core :refer [gen-aseq yield]]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.combinators :refer [parallel race]]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.semaphore :as sem]
            [org.replikativ.spindel.pubsub.pub :as pub]
            [org.replikativ.spindel.effects.await :refer [await]]
            [is.simm.partial-cps.sequence :as psq :refer [anext]])
  (:import [java.lang.ref WeakReference]))

;; =============================================================================
;; Drivers
;; =============================================================================

(defn drive-spin-aseq!
  "Consume up to `n` steps of a spindel PAsyncSeq (whose `anext` returns a Spin)
  by blocking deref. Returns the rest-seq after `n` steps, or nil if exhausted."
  [aseq n]
  (loop [s aseq i 0]
    (if (and s (< i n))
      (if-let [pair @(anext s)]
        (recur (second pair) (inc i))
        nil)
      s)))

(defn run-cps!
  "Run a partial-cps CPS fn to completion synchronously (all resolves on this
  test's sources fire inline)."
  [cps]
  (let [out (atom ::none)
        err (atom ::none)]
    (cps (fn [v] (reset! out v)) (fn [e] (reset! err e)))
    (when (not= ::none @err) (throw @err))
    @out))

(defn drive-cps-aseq!
  "Consume up to `n` steps of a partial-cps PAsyncSeq (whose `anext` returns a
  raw CPS fn). Returns the rest-seq node after `n` steps, or nil if exhausted."
  [aseq n]
  (loop [s aseq i 0]
    (if (and s (< i n))
      (if-let [pair (run-cps! (anext s))]
        (recur (second pair) (inc i))
        nil)
      s)))

;; =============================================================================
;; Engine-state probe
;; =============================================================================

(defn engine-undelivered-pending
  "Total resolve-continuations sitting in *undelivered* Deferred `:pending`
  vectors across the context's `:atoms` map.

  This is the direct, fix-agnostic signal of the gen-aseq shared-deferred
  leak: a never-delivered shared deferred accumulates one pending entry per
  consumed element, so this scales with consumption pre-fix and stays O(1)
  post-fix (each per-anext deferred is delivered, leaving `:pending` empty)."
  [ctx]
  (let [state (backend/backend-deref (:backend ctx))]
    (reduce-kv (fn [acc _id entry]
                 (let [v (:value entry)]
                   (if (and (map? v) (contains? v :pending) (not (:assigned? v)))
                     (+ acc (count (:pending v)))
                     acc)))
               0
               (:atoms state))))

(defn- gc-until
  "Force GC up to `tries` times (short pauses) until `(pred)` holds, returning
  the final `(pred)`.

  The two GC-dependent guards (#2 consumed-value release, #5 parallel
  engine-state reclamation) rely on `System/gc`, which is advisory — a single
  pass may not collect everything. Retrying until the expected condition holds
  (or we give up) removes the only real flake surface; the assertion that
  follows still fails loudly if the condition never becomes true. The
  structural guards below take no GC and need none of this."
  [pred tries]
  (loop [i 0]
    (let [ok (pred)]
      (if (or ok (>= i tries))
        ok
        (do (System/gc) (Thread/sleep 80) (recur (inc i)))))))

;; =============================================================================
;; #1 — gen-aseq shared-term-deferred pending leak
;;
;; STRUCTURAL guard (deterministic, no GC/timing): `engine-undelivered-pending`
;; reads exact engine state. Post-fix the measured value is 0 every run (the
;; per-anext deferred is always delivered); pre-fix it was 97 after 100 items.
;; The `<= 5` bound is an O(1)-vs-O(N) discriminator with headroom for benign
;; transients — NOT a fuzzy threshold.
;; =============================================================================

(deftest gen-aseq-no-shared-deferred-pending-leak
  (testing "consuming a long gen-aseq must not accumulate dead await
            continuations in engine state (shared-term-deferred :pending)"
    (let [ctx (ctx/create-execution-context)]
      (try
        (binding [ec/*execution-context* ctx]
          (let [g (gen-aseq
                   (loop [k 0]
                     (when (< k 100000)
                       (yield k)
                       (recur (inc k)))))]
            (drive-spin-aseq! g 100)
            (let [pending (engine-undelivered-pending ctx)]
              (is (<= pending 5)
                  (str "gen-aseq leak: " pending " undelivered await continuations "
                       "accumulated in engine state after consuming 100 elements "
                       "(expected O(1))")))))
        (finally
          (ctx/stop-context! ctx))))))

;; =============================================================================
;; #2 — partial-cps `sequence` consumed-value retention
;; =============================================================================

(deftest sequence-does-not-retain-consumed-values
  (testing "partial-cps `sequence` must release elements once the consumer has
            advanced past them; holding a mid-stream node must not pin earlier
            elements"
    (let [n 200
          k 100
          refs (java.util.ArrayList.)
          ;; Source produces a fresh sentinel Object per element from an int
          ;; counter, so the source chain itself retains only the int — the
          ;; ONLY retention path for the objects is the transducer's buffer.
          src (psq/make-generator-seq
               (fn [idx]
                 (fn [resolve _reject]
                   (resolve (when (< idx n)
                              (let [o (Object.)]
                                (.add refs (WeakReference. o))
                                [o (inc idx)])))))
               0)
          ;; Advance to the node at index k WITHOUT retaining the head (the
          ;; sequence head is passed straight into the driver, never bound).
          mid (drive-cps-aseq! (psq/sequence (map identity) src) k)]
      (is (some? mid) "precondition: mid-stream node exists")
      ;; GC-DEPENDENT guard. Of the first k elements (all consumed before the
      ;; held `mid` node), most must be collectable — a held mid-stream node
      ;; must not pin earlier elements. `System/gc` is advisory, so retry via
      ;; `gc-until` rather than a fixed number of passes (removes the flake
      ;; surface). In practice all 100 clear; `>= 0.8k` tolerates GC laziness
      ;; while still cleanly separating fixed (0 cleared pre-fix) from released.
      ;;
      ;; NOTE: `mid` MUST stay strongly reachable across the GCs and into the
      ;; assertion — that is the whole point. It is referenced in the message
      ;; expression so JVM locals-clearing keeps it live until the `is` runs;
      ;; without that reference it gets nulled early and the buffer is collected
      ;; regardless of any leak, masking the bug.
      (let [threshold (int (* 0.8 k))
            cleared #(count (filter (fn [w] (nil? (.get ^WeakReference w)))
                                    (take k refs)))]
        (gc-until #(>= (cleared) threshold) 15)
        (is (>= (cleared) threshold)
            (str "sequence retains consumed values: only " (cleared) "/" k
                 " elements consumed before the held node were GC'd "
                 "(expected most — a held node must not pin earlier elements); "
                 "held node present=" (some? mid)))))))

;; =============================================================================
;; #5 — parallel must not accumulate per-call engine state
;;
;; GC-DEPENDENT guard: node/`:parallel-results` reclamation is triggered by the
;; Spin Cleaner, so we converge via `gc-until`. Post-fix the engine-state size
;; returns to baseline every run (measured 0 → 0); pre-fix it grew by one
;; permanent entry per call. The `<= base + 8` bound is reclamation headroom.
;; =============================================================================

(deftest parallel-does-not-accumulate-engine-state
  (testing "repeated parallel calls must not leave per-call entries in engine
            state: there must be NO :parallel/results side key, and overall
            engine state must return to baseline once parallels are dropped"
    (let [ctx (ctx/create-execution-context)]
      (try
        (binding [ec/*execution-context* ctx]
          (let [state-size (fn []
                             (let [s (backend/backend-deref (:backend ctx))]
                               (+ (count (:nodes s))
                                  (count (:parallel/results s)) ; must remain 0 (key removed)
                                  (count (:spin-aux s)))))
                base (state-size)]
            (dotimes [_ 80] @(parallel (spin 1) (spin 2) (spin 3)))
            (gc-until #(<= (state-size) (+ base 8)) 15)
            (let [s (backend/backend-deref (:backend ctx))]
              (is (empty? (:parallel/results s))
                  "parallel must not store a permanent per-call :parallel/results entry")
              (is (<= (state-size) (+ base 8))
                  (str "parallel engine-state leak: size " (state-size)
                       " after 80 parallels dropped + GC (baseline " base ")")))))
        (finally
          (ctx/stop-context! ctx))))))

;; =============================================================================
;; #3 — Mailbox prunes cancelled waiters
;;
;; STRUCTURAL guard (deterministic). Measured `:waiters` is exactly 1 every run
;; (pre-fix ~29). The residual 1 is expected, not noise: pruning happens when
;; the NEXT take arrives, so the final race's cancelled waiter has no successor
;; to prune it. It stays at 1, never grows — the `<= 5` bound is O(1) headroom.
;; (#3/#6/#7 are the same prune-on-read design and all sit at a stable 1.)
;; =============================================================================

(deftest mailbox-prunes-cancelled-waiters
  (testing "cancelled mailbox awaits must not accumulate in :waiters; taking
            sweeps out waiters whose await was cancelled"
    (let [ctx (ctx/create-execution-context)]
      (try
        (binding [ec/*execution-context* ctx]
          (let [mbx (sync/mailbox)]
            ;; Each race cancels the losing (await mbx) branch. No message is
            ;; ever posted, so without on-take pruning these waiters would
            ;; accumulate one per iteration.
            (dotimes [_ 30]
              @(race (spin :winner) (spin (await mbx))))
            (let [waiters (count (:waiters @(.-state-atom mbx)))]
              (is (<= waiters 5)
                  (str "mailbox waiter leak: " waiters " stranded waiters after "
                       "30 cancelled awaits (expected O(1))")))))
        (finally
          (ctx/stop-context! ctx))))))

;; =============================================================================
;; #4 — pub does not accumulate idle (unsubscribed) topic mults
;;
;; STRUCTURAL guard (deterministic). Measured topic-mult count is exactly 1
;; (the single subscribed topic) every run; pre-fix it was 40 (one per distinct
;; topic seen). `<= 5` is O(subscribed-topics) headroom.
;; =============================================================================

(deftest pub-does-not-accumulate-idle-topics
  (testing "a high-cardinality topic-fn must not create a mult per distinct
            topic; only subscribed topics get a mult, others are dropped"
    (let [ctx (ctx/create-execution-context)]
      (try
        (binding [ec/*execution-context* ctx]
          (let [n 40
                items (vec (for [i (range n)] {:topic (keyword (str "t" i)) :v i}))
                src (gen-aseq
                     (loop [xs items]
                       (when (seq xs)
                         (yield (first xs))
                         (recur (rest xs)))))
                p (pub/pub src :topic)]
            (pub/sub p :t0)             ; one subscriber; starts the pump
            ;; Wait for the pump to drain the source.
            (loop [tries 0]
              (when (and (not (pub/pub-closed? p)) (< tries 300))
                (Thread/sleep 10)
                (recur (inc tries))))
            (is (pub/pub-closed? p) "precondition: pump drained the source")
            (let [topics (count @(:mults-atom p))]
              (is (<= topics 5)
                  (str "pub topic leak: " topics " topic mults retained for "
                       n " distinct topics with a single subscriber "
                       "(expected O(subscribed-topics))")))))
        (finally
          (ctx/stop-context! ctx))))))

;; =============================================================================
;; #6 — Deferred prunes cancelled readers (same pattern as Mailbox #3)
;;
;; STRUCTURAL guard (deterministic): `:pending` is a stable 1 (the last
;; cancelled reader, no successor to prune it); pre-fix ~10. See #3.
;; =============================================================================

(deftest deferred-prunes-cancelled-readers
  (testing "cancelled awaits on a never-delivered deferred must not accumulate
            in :pending; awaiting sweeps out cancelled readers"
    (let [ctx (ctx/create-execution-context)]
      (try
        (binding [ec/*execution-context* ctx]
          (let [d (sync/deferred)]
            ;; d is never delivered; each race cancels the losing (await d).
            (dotimes [_ 30]
              @(race (spin :winner) (spin (await d))))
            (let [pending (count (:pending @(.-state-atom d)))]
              (is (<= pending 5)
                  (str "deferred :pending leak: " pending " stranded readers after "
                       "30 cancelled awaits (expected O(1))")))))
        (finally
          (ctx/stop-context! ctx))))))

;; =============================================================================
;; #7 — Semaphore prunes cancelled acquirers (same pattern as Mailbox #3)
;;
;; STRUCTURAL guard (deterministic): `:waiting-queue` is a stable 1 (the last
;; cancelled acquirer, no successor to prune it); pre-fix ~29. See #3.
;; =============================================================================

(deftest semaphore-prunes-cancelled-acquirers
  (testing "cancelled acquires on an exhausted semaphore must not accumulate
            in :waiting-queue; acquiring sweeps out cancelled acquirers"
    (let [ctx (ctx/create-execution-context)]
      (try
        (binding [ec/*execution-context* ctx]
          (let [s (sem/semaphore 1)]
            ;; Take the only permit so every subsequent acquire must queue.
            @(sem/acquire s)
            ;; Each race cancels the losing acquire spin directly.
            (dotimes [_ 30]
              @(race (spin :winner) (sem/acquire s)))
            (let [waiters (count (ec/get-state [:semaphores (.-id s) :waiting-queue]))]
              (is (<= waiters 5)
                  (str "semaphore :waiting-queue leak: " waiters " stranded "
                       "acquirers after 30 cancelled acquires (expected O(1))")))))
        (finally
          (ctx/stop-context! ctx))))))
