(ns org.replikativ.spindel.spin.gc-test
  "Tests for automatic spin garbage collection cleanup.

   Validates that when Spin objects are GC'd, their runtime state is
   properly cleaned from the ExecutionContext.

   Deterministic tests (calling cleanup functions directly) are cross-platform.
   GC-triggered tests (System/gc) are JVM-only."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.engine.nodes :as nodes]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]])
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]]
                            [org.replikativ.spindel.signal :refer [signal]])))

#?(:clj (require '[org.replikativ.spindel.spin.cps :refer [spin]]
                 '[org.replikativ.spindel.signal :refer [signal]]
                 '[org.replikativ.spindel.test-async :refer [await-drain]]))

;; =============================================================================
;; Cross-platform deterministic tests for full-cleanup-spin!
;; =============================================================================

(deftest test-full-cleanup-spin-removes-all-state
  (testing "full-cleanup-spin! removes all state locations atomically"
    (async done
           (with-ctx [ctx]
             (let [s (spin 42)
                   sid (spin-core/spin-id s)]
               (run-spin! s
                          (fn [_]
              ;; Verify state exists before cleanup
                            (is (some? (rtp/get-state ctx [:nodes sid])) "Node should exist before cleanup")
                            (is (some? (rtp/get-state ctx [:spins-meta sid])) "Meta should exist before cleanup")
              ;; Note: :spin-outputs was dropped in the unified-subscription
              ;; cleanup — the spin's result lives on :nodes[sid]:result.
              ;; Run full cleanup
                            (simple/full-cleanup-spin! ctx sid)
              ;; Verify all state is gone
                            (is (nil? (rtp/get-state ctx [:nodes sid])) "Node should be removed")
                            (is (nil? (rtp/get-state ctx [:spins-meta sid])) "Meta should be removed")
                            (is (nil? (rtp/get-state ctx [:track-subscriptions sid])) "Track conts should be removed")
                            (is (nil? (rtp/get-state ctx [:await-conts sid])) "Await conts should be removed")
                            (done))
                          (fn [e] (is false (str "Spin failed: " e)) (done))))))))

(deftest test-full-cleanup-unregisters-from-signal-observers
  (testing "full-cleanup-spin! removes spin from signal observer lists"
    (async done
           (with-ctx [ctx]
             (let [sig-ref (signal 0)
                   sig-id (:id sig-ref)
                   s (spin (let [{:keys [new]} (track sig-ref)] new))
                   sid (spin-core/spin-id s)]
               (run-spin! s
                          (fn [_]
              ;; Verify spin is in signal's observers
                            (let [sig-node (rtp/get-state ctx [:nodes sig-id])]
                              (is (contains? (:observers sig-node) sid) "Spin should be in signal's observers"))
              ;; Run full cleanup
                            (simple/full-cleanup-spin! ctx sid)
              ;; Verify spin is removed from signal's observers
                            (let [sig-node (rtp/get-state ctx [:nodes sig-id])]
                              (is (not (contains? (:observers sig-node) sid)) "Spin should be removed from signal's observers"))
                            (done))
                          (fn [e] (is false (str "Spin failed: " e)) (done))))))))

(deftest test-full-cleanup-unregisters-from-spin-observers
  (testing "full-cleanup-spin! removes child from parent spin observer list"
    (async done
           (with-ctx [ctx]
             (let [p (spin 42)
                   parent-id (spin-core/spin-id p)]
               (run-spin! p
                          (fn [_]
                            (let [c (spin (* 2 (await p)))
                                  child-id (spin-core/spin-id c)]
                              (run-spin! c
                                         (fn [_]
                    ;; Verify child is in parent's observers
                                           (let [parent-node (rtp/get-state ctx [:nodes parent-id])]
                                             (is (contains? (:observers parent-node) child-id) "Child should be in parent's observers"))
                    ;; Clean up child
                                           (simple/full-cleanup-spin! ctx child-id)
                    ;; Verify child is removed from parent's observers
                                           (let [parent-node (rtp/get-state ctx [:nodes parent-id])]
                                             (is (not (contains? (:observers parent-node) child-id)) "Child should be removed from parent's observers"))
                                           (done))
                                         (fn [e] (is false (str "Child failed: " e)) (done)))))
                          (fn [e] (is false (str "Parent failed: " e)) (done))))))))

;; =============================================================================
;; Cross-platform deterministic tests for try-gc-cleanup-spin!
;; =============================================================================

(deftest test-try-gc-cleanup-no-observers
  (testing "try-gc-cleanup-spin! fully cleans spin with no observers"
    (async done
           (with-ctx [ctx]
             (let [s (spin 42)
                   sid (spin-core/spin-id s)]
               (run-spin! s
                          (fn [_]
              ;; Spin has no observers - should be fully cleaned
                            (simple/try-gc-cleanup-spin! ctx sid)
                            (is (nil? (rtp/get-state ctx [:nodes sid])) "Spin with no observers should be fully cleaned")
                            (done))
                          (fn [e] (is false (str "Spin failed: " e)) (done))))))))

(deftest test-try-gc-cleanup-with-observers-defers
  (testing "try-gc-cleanup-spin! marks spin as orphaned when it has observers"
    (async done
           (with-ctx [ctx]
             (let [p (spin 42)
                   parent-id (spin-core/spin-id p)]
               (run-spin! p
                          (fn [_]
                            (let [c (spin (* 2 (await p)))]
                              (run-spin! c
                                         (fn [_]
                    ;; Parent has observer (child) - should be deferred
                                           (simple/try-gc-cleanup-spin! ctx parent-id)
                                           (let [node (rtp/get-state ctx [:nodes parent-id])]
                                             (is (some? node) "Node should still exist (has observers)")
                                             (is (:orphaned? node) "Node should be marked orphaned"))
                                           (done))
                                         (fn [e] (is false (str "Child failed: " e)) (done)))))
                          (fn [e] (is false (str "Parent failed: " e)) (done))))))))

(deftest test-try-gc-cleanup-cascading
  (testing "Cleaning a child cascades to orphaned parent that loses last observer"
    (async done
           (with-ctx [ctx]
             (let [p (spin 42)
                   parent-id (spin-core/spin-id p)]
               (run-spin! p
                          (fn [_]
                            (let [c (spin (* 2 (await p)))
                                  child-id (spin-core/spin-id c)]
                              (run-spin! c
                                         (fn [_]
                    ;; First: orphan the parent (has observer, can't clean yet)
                                           (simple/try-gc-cleanup-spin! ctx parent-id)
                                           (is (some? (rtp/get-state ctx [:nodes parent-id])) "Parent still alive (has observer)")
                                           (is (:orphaned? (rtp/get-state ctx [:nodes parent-id])) "Parent is orphaned")
                    ;; Now clean the child - should cascade to orphaned parent
                                           (simple/try-gc-cleanup-spin! ctx child-id)
                                           (is (nil? (rtp/get-state ctx [:nodes child-id])) "Child should be cleaned")
                                           (is (nil? (rtp/get-state ctx [:nodes parent-id])) "Orphaned parent should be cleaned via cascade")
                                           (done))
                                         (fn [e] (is false (str "Child failed: " e)) (done)))))
                          (fn [e] (is false (str "Parent failed: " e)) (done))))))))

(deftest test-try-gc-cleanup-already-cleaned
  (testing "try-gc-cleanup-spin! is safe when called on already-cleaned spin"
    (async done
           (with-ctx [ctx]
             (let [s (spin 42)
                   sid (spin-core/spin-id s)]
               (run-spin! s
                          (fn [_]
              ;; Clean once
                            (simple/try-gc-cleanup-spin! ctx sid)
              ;; Clean again - should be a no-op, not throw
                            (simple/try-gc-cleanup-spin! ctx sid)
                            (is (nil? (rtp/get-state ctx [:nodes sid])) "Still cleaned")
                            (done))
                          (fn [e] (is false (str "Spin failed: " e)) (done))))))))

(deftest test-try-gc-cleanup-preserves-live-external-await
  (testing "try-gc-cleanup-spin! defers cleanup for a spin suspended on a
            Deferred/Mailbox external resource.

            Regression: without this, a fire-and-forget spawn'd spin whose
            body is mid-await on a Deferred can have its Spin Java object
            GC'd while the deferred has not yet been delivered. The Cleaner
            then fires try-gc-cleanup-spin!, which used to only check for
            observers and signal track conts — both absent for such a spin
            — and fully reaped the node + its :external-await cont. The
            Deferred's eventual delivery had nowhere to resume; the body's
            continuation (which might `deliver` to an external promise)
            never fired. Symptom in dvergr: 20% flake rate on
            discourse/personas tests where every operation completes
            (probes confirm) but await-spin still returns ::timeout
            because the outer promise was never delivered."
    (async done
           (with-ctx [ctx]
             (let [d (sync/create-deferred ctx)
                   s (spin (await d))
                   sid (spin-core/spin-id s)]
          ;; Start the body — it suspends on the deferred await, registering
          ;; an :external-await cont on the spin.
               (s (fn [_]) (fn [_]))
               (let [conts (rtp/get-state ctx [:await-conts sid])]
                 (is (some? conts) "Body must have registered an await cont before we test GC")
                 (is (some (fn [[_ v]] (= :external-await (:kind v))) conts)
                     "The cont must be :external-await (Deferred path)"))
          ;; Simulate the Spin's Cleaner firing — the user has dropped their
          ;; reference. The fix: try-gc-cleanup-spin! should see the live
          ;; external-await cont and DEFER cleanup (mark orphaned), not fully
          ;; reap the node + cont.
               (simple/try-gc-cleanup-spin! ctx sid)
               (let [node (rtp/get-state ctx [:nodes sid])]
                 (is (some? node)
                     "Node must survive try-gc-cleanup: it has a live external-await pending")
                 (is (:orphaned? node)
                     "Node must be marked :orphaned? — fully reachable for resume but reaped on next safe pass"))
               (is (seq (rtp/get-state ctx [:await-conts sid]))
                   "The :external-await cont must survive — otherwise the Deferred's eventual delivery would have nowhere to resume")
               (done))))))

#?(:clj
   ;; JVM-only: relies on `await-drain-complete!` to deterministically
   ;; wait for the spin's resolve callback (which fires `release!`) to
   ;; run before asserting. CLJS has no equivalent blocking primitive
   ;; — the drain runs on the event loop after `(d :delivered)` returns,
   ;; so an inline assertion would race with the resolve. The contract
   ;; itself (register on spawn, release on resolve) is the same on
   ;; both platforms and is exercised end-to-end by the JVM-only
   ;; `test-spawn-survives-gc-mid-await-jvm` below.
   (deftest test-spawn-registers-and-releases-keep-alive
     (testing "spawn! holds the Spin instance in [:engine/spawned] for the
              lifetime of its body, then releases it on body resolution"
       (let [ctx (ctx/create-execution-context)]
         (try
           (binding [ec/*execution-context* ctx]
             (let [d (sync/create-deferred ctx)
                   s (spin (await d))
                   sid (spin-core/spin-id s)]
               (sync/spawn! s)
               ;; Body suspends on the deferred await. The spin's instance MUST
               ;; be held in the engine's spawned-registry — otherwise GC could
               ;; reap it mid-await.
               (is (identical? s (get (rtp/get-state ctx [:engine/spawned]) sid))
                   "spawn! must register the Spin in [:engine/spawned spin-id] while body is in flight")
               ;; Deliver the deferred → body resumes → resolves → release should fire.
               (d :delivered)
               (simple/await-drain-complete! ctx)
               (is (nil? (get (rtp/get-state ctx [:engine/spawned]) sid))
                   "spawn! must release the Spin from [:engine/spawned spin-id] after body resolves")))
           (finally
             (ctx/stop-context! ctx)))))))

#?(:clj
   (deftest test-spawn-survives-gc-mid-await-jvm
     (testing "A fire-and-forget (spawn! (spin … (await ext) (deliver p …))) spin
              must survive GC while suspended on an external await. The Spin
              instance has no caller-held reference after spawn!; without
              spawn's keep-alive the Cleaner fires mid-body, reaps the await
              cont, and the eventual external delivery silently never resumes
              the body — the promise stays undelivered. This was the
              root-cause of the dvergr discourse.llm-test flake."
       (let [ctx (ctx/create-execution-context)]
         (try
           (binding [ec/*execution-context* ctx]
             (let [d (sync/create-deferred ctx)
                   p (promise)]
               ;; Fire-and-forget: the Spin instance is created inline and
               ;; passed straight to spawn!. No caller-held ref → after this
               ;; call returns, GC can reach the Spin unless spawn! holds it.
               (sync/spawn! (spin (deliver p (await d))))
               ;; Aggressively GC. With the fix, the Spin is held by
               ;; [:engine/spawned] until its body resolves, so GC can't
               ;; reap it mid-await. Without the fix, the Cleaner would
               ;; fire here, full-cleanup would clear the await cont, and
               ;; the eventual `(d :delivered)` below would have nowhere
               ;; to resume.
               (dotimes [_ 3] (System/gc) (Thread/sleep 50))
               ;; Now deliver the deferred — body should resume and put
               ;; `:delivered` on p.
               (d :delivered)
               (is (= :delivered (deref p 2000 ::timeout))
                   "Body must have resumed from the await and delivered to p")))
           (finally
             (ctx/stop-context! ctx)))))))

(deftest test-no-residual-after-bulk-cleanup
  (testing "No residual spin state after creating many spins and cleaning them"
    (async done
           (with-ctx [ctx]
             (let [spin-ids (atom [])]
          ;; Create 50 spins, collecting their IDs
               (letfn [(create-next [i]
                         (if (>= i 50)
                      ;; All created, now clean them all
                           (do
                             (doseq [sid @spin-ids]
                               (simple/full-cleanup-spin! ctx sid))
                        ;; Check no residual spin state. (:spin-outputs was
                        ;; removed in the unified-subscription cleanup.)
                             (let [nodes (rtp/get-state ctx [:nodes])
                                   spin-nodes (filter (fn [[_ node]]
                                                        (and node
                                                             (= :spin (nodes/node-type node))))
                                                      nodes)
                                   metas (rtp/get-state ctx [:spins-meta])]
                               (is (zero? (count spin-nodes))
                                   (str "Should have 0 spin nodes, found: " (count spin-nodes)))
                               (is (zero? (count metas))
                                   (str "Should have 0 spins-meta, found: " (count metas))))
                             (done))
                      ;; Create next spin
                           (let [s (spin (+ i 1))
                                 sid (spin-core/spin-id s)]
                             (swap! spin-ids conj sid)
                             (run-spin! s
                                        (fn [_] (create-next (inc i)))
                                        (fn [e] (is false (str "Spin " i " failed: " e)) (done))))))]
                 (create-next 0)))))))

;; =============================================================================
;; GC-triggered cleanup tests (JVM only - uses System/gc)
;; =============================================================================

#?(:clj
   (deftest test-spin-gc-cleanup-jvm
     (testing "GC of Spin object triggers cleanup of runtime state (JVM)"
       (let [ctx (ctx/create-execution-context)
             spin-id-holder (atom nil)]
         (try
           (binding [ec/*execution-context* ctx]
             ;; Create a spin in a local scope so it can be GC'd
             (let [s (spin 42)]
               (reset! spin-id-holder (spin-core/spin-id s))
               @s)
             ;; s is now out of scope - verify state exists
             (is (some? (rtp/get-state ctx [:nodes @spin-id-holder])) "State should exist before GC"))
           ;; Force GC (outside binding scope to ensure cleanup uses WeakRef)
           (System/gc)
           (Thread/sleep 500)
           ;; Verify state is cleaned up
           (is (nil? (rtp/get-state ctx [:nodes @spin-id-holder])) "Node should be cleaned after GC")
           (is (nil? (rtp/get-state ctx [:spins-meta @spin-id-holder])) "Meta should be cleaned after GC")
           (finally
             (ctx/stop-context! ctx)))))))

#?(:clj
   (deftest test-no-residual-after-bulk-gc-jvm
     (testing "No residual spin state after creating and GC'ing many spins (JVM)"
       (let [ctx (ctx/create-execution-context)]
         (try
           (binding [ec/*execution-context* ctx]
             ;; Create and deref 100 spins
             (dotimes [i 100]
               @(spin (+ i 1))))
           ;; Force GC multiple rounds to ensure cleanup
           (dotimes [_ 3]
             (System/gc)
             (Thread/sleep 200))
           ;; Check runtime state - should have no spin nodes left
           (let [nodes (rtp/get-state ctx [:nodes])
                 spin-nodes (filter (fn [[_ node]]
                                      (and node
                                           (= :spin (nodes/node-type node))))
                                    nodes)
                 metas (rtp/get-state ctx [:spins-meta])]
             (is (zero? (count spin-nodes)) (str "Should have 0 spin nodes, found: " (count spin-nodes)))
             (is (zero? (count metas)) (str "Should have 0 spins-meta, found: " (count metas))))
           (finally
             (ctx/stop-context! ctx)))))))

#?(:clj
   (deftest test-gc-safe-when-context-collected
     (testing "GC cleanup is safe when context itself is GC'd before spin"
       (let [spin-id-holder (atom nil)]
         ;; Create context and spin in a scope that lets them be GC'd
         (let [ctx (ctx/create-execution-context)]
           (try
             (binding [ec/*execution-context* ctx]
               (let [s (spin 42)]
                 (reset! spin-id-holder (spin-core/spin-id s))
                 @s))
             (finally
               (ctx/stop-context! ctx))))
         ;; Both ctx and spin are out of scope - force GC
         ;; This should be safe (no NPE, no errors)
         (System/gc)
         (Thread/sleep 500)
         (is true "GC cleanup should be safe even if context is GC'd first")))))
