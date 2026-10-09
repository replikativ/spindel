(ns org.replikativ.spindel.spawned-child-trampoline-test
  "A body started from inside another body runs in a trampoline of its own.

   `spawn!` inside a spin, a SynchronousExecutor running a parallel/race/work
   child inline, and a generator's first step all start a CPS body while the
   caller's trampoline is active, and all discard what the body returns. A
   body that believed the caller's trampoline would force its Thunks handed
   its `recur` back to that caller and its loop stopped at the first
   synchronous await: the child never completed."
  (:refer-clojure :exclude [await])
  (:require [is.simm.partial-cps.async :as pa]
            [is.simm.partial-cps.runtime]
            [is.simm.partial-cps.sequence :refer [anext]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.executor :as executor]
            [org.replikativ.spindel.seq.core :as seq-core]
            [org.replikativ.spindel.spin.combinators :as comb]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.test-helpers :as h]
            [org.replikativ.spindel.work :as work]
            [org.replikativ.spindel.world.what-if :as what-if]
            [org.replikativ.spindel.world.scope :as scope]
            #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])))

(defn- looper
  "A spin whose loop awaits a fresh (synchronously completing) spin per
   iteration, then returns [k iterations]."
  [k]
  (spin (loop [i 0]
          (if (< i 3)
            (do (await (spin i))
                (recur (inc i)))
            [k i]))))

(defn- expect
  "Run `s` and check its value is `expected`; then `done`."
  [s expected done]
  (h/run-spin! s
               (fn [v] (is (= expected v)) (done))
               (fn [e] (is false (str e)) (done))))

(defn- in-synchronous-context
  "Run (f done) with a context whose executor runs every task inline; the
   context is stopped once `done` is called."
  [done f]
  (let [ctx (context/create-execution-context
             {:executor (executor/synchronous-executor)})
        done (fn [] (context/stop-context! ctx) (done))]
    (binding [ec/*execution-context* ctx]
      (f done))))

;; =============================================================================
;; spawn! from inside a body
;; =============================================================================

(deftest a-child-spawned-from-a-body-runs-its-loop
  (h/async done
           (h/with-ctx [_ctx]
             (let [d (sync/deferred)]
               (h/run-spin! (spin (sync/spawn! (looper :x) {:on-success d})
                                  :ok)
                            (fn [_]) (fn [e] (is false (str e))))
               (expect (spin (await d)) [:x 3] done)))))

(deftest a-child-spawned-from-a-loop-body-runs-its-loop
  (h/async done
           (h/with-ctx [_ctx]
             (let [ds [(sync/deferred) (sync/deferred)]]
               (h/run-spin! (spin (loop [j 0]
                                    (if (< j 2)
                                      (do (sync/spawn! (looper j) {:on-success (ds j)})
                                          (recur (inc j)))
                                      :parent-done)))
                            (fn [_]) (fn [e] (is false (str e))))
               (expect (spin [(await (ds 0)) (await (ds 1))])
                       [[0 3] [1 3]] done)))))

(deftest a-child-spawned-after-an-await-runs-its-loop
  (h/async done
           (h/with-ctx [_ctx]
             (let [d (sync/deferred)
                   ready (sync/deferred)]
               (ready :go)
               (h/run-spin! (spin (await ready)
                                  (sync/spawn! (looper :after) {:on-success d})
                                  :ok)
                            (fn [_]) (fn [e] (is false (str e))))
               (expect (spin (await d)) [:after 3] done)))))

(defn- settle-loop
  "A partial-cps loop over an operation that settles at once; delivers its
   iteration count to `d`."
  [d]
  (let [block (pa/async (loop [i 0]
                          (if (< i 3)
                            (do (pa/await (fn [r _] (r nil)))
                                (recur (inc i)))
                            i)))]
    (block d (fn [e] (d e)))))

(deftest a-loop-started-by-a-spawn-callback-runs-to-its-end
  ;; The callbacks of a child spawned (and completing at once) inside a body
  ;; run where nothing returns what they hand back.
  (h/async done
           (h/with-ctx [_ctx]
             (let [ok (sync/deferred)
                   failed (sync/deferred)]
               (h/run-spin! (spin (sync/spawn! (spin :child)
                                               {:on-success (fn [_] (settle-loop ok))})
                                  (sync/spawn! (spin (throw (ex-info "child" {})))
                                               {:on-error (fn [_] (settle-loop failed))})
                                  :parent-done)
                            (fn [_]) (fn [e] (is false (str e))))
               (expect (spin [(await ok) (await failed)]) [3 3] done)))))

(deftest a-loop-started-by-a-what-if-watch-callback-runs-to-its-end
  (h/async done
           (h/with-ctx [ctx]
             (let [d (sync/deferred)
                   w (what-if/what-if ctx {})]
               (h/run-spin! (spin (what-if/watch! w #(spin :watched)
                                                  ;; the callback runs in the
                                                  ;; view; report to `ctx`
                                                  (fn [_] (settle-loop
                                                           (fn [v]
                                                             (binding [ec/*execution-context* ctx]
                                                               (d v))))))
                                  :parent-done)
                            (fn [_]) (fn [e] (is false (str e))))
               (expect (spin (await d)) 3
                       (fn [] (what-if/stop! w) (done)))))))

(deftest a-throw-in-a-later-iteration-rejects-the-spin
  ;; The body's error handler covers every iteration its trampoline forces,
  ;; not only the first one.
  (h/async done
           (h/with-ctx [_ctx]
             (let [rejections (atom 0)
                   s (spin (loop [i 0]
                             (when (= i 1)
                               (throw (ex-info "bounce-error" {})))
                             (await (fn [r _] (r nil)))
                             (recur (inc i))))]
               (h/run-spin! (spin (sync/spawn! s {:on-error (fn [_] (swap! rejections inc))})
                                  :ok)
                            (fn [_]) (fn [e] (is false (str e))))
               (h/run-spin! (spin (try (await s) :resolved
                                       (catch #?(:clj Exception :cljs :default) e
                                         (ex-message e))))
                            (fn [v]
                              (is (= "bounce-error" v))
                              (is (= 1 @rejections))
                              (done))
                            (fn [e] (is false (str e)) (done)))))))

(deftest a-throw-in-a-loop-started-by-a-spawn-callback-reaches-its-handler
  ;; The callback of a hand-written spin that completes at once starts a
  ;; loop that throws on its second iteration: the loop's own handler sees
  ;; it, once, and nothing escapes spawn!.
  (h/async done
           (h/with-ctx [_ctx]
             (let [handled (atom 0)
                   escaped (atom nil)
                   start-loop (fn [_]
                                (let [block (pa/async (loop [i 0]
                                                        (when (= i 1)
                                                          (throw (ex-info "callback-bounce" {})))
                                                        (pa/await (fn [r _] (r nil)))
                                                        (recur (inc i))))]
                                  (block (fn [_]) (fn [_] (swap! handled inc)))))]
               (try
                 (binding [pa/*in-trampoline* false]
                   (sync/spawn! (spin-core/make-spin (fn [r _] (r :now)))
                                {:on-success start-loop}))
                 (catch #?(:clj Throwable :cljs :default) e
                   (reset! escaped e)))
               (is (nil? @escaped))
               (is (= 1 @handled))
               (done)))))

(def ^:private deep 20000)

(deftest a-loop-over-a-hand-written-spin-does-not-grow-the-stack
  ;; A make-spin body starts no trampoline of its own; its synchronous
  ;; resolve must still hand the caller's Thunk back, not run the caller's
  ;; next iteration nested inside it.
  (h/async done
           (h/with-ctx [_ctx]
             (let [block (pa/async (loop [i 0]
                                     (if (< i deep)
                                       (do (pa/await (spin-core/make-spin (fn [r _] (r :ok))))
                                           (recur (inc i)))
                                       i)))]
               ;; JVM: on a thread of its own, so an overflow fails the test
               ;; (through the block's reject) instead of the runner.
               (#?(:clj future-call :cljs (fn [f] (f)))
                (fn []
                  (binding [pa/*in-trampoline* false]
                    (block (fn [v] (is (= deep v)) (done))
                           (fn [e] (is false (str (type e))) (done))))))))))

;; =============================================================================
;; Children run inline by a SynchronousExecutor
;; =============================================================================

(deftest parallel-children-run-inline-run-their-loops
  (h/async done
           (in-synchronous-context
            done
            (fn [done]
              (let [d (sync/deferred)]
                (h/run-spin! (spin (sync/spawn! (comb/parallel (looper :a) (looper :b))
                                                {:on-success d})
                                   :ok)
                             (fn [_]) (fn [e] (is false (str e))))
                (expect (spin (await d)) [[:a 3] [:b 3]] done))))))

(deftest race-children-run-inline-run-their-loops
  (h/async done
           (in-synchronous-context
            done
            (fn [done]
              (let [d (sync/deferred)]
                (h/run-spin! (spin (sync/spawn! (comb/race (looper :a) (looper :b))
                                                {:on-success d})
                                   :ok)
                             (fn [_]) (fn [e] (is false (str e))))
                (expect (spin (await d)) [:a 3] done))))))

(deftest work-children-run-inline-run-their-loops
  ;; The controller's runner is itself a looping body; it starts each child
  ;; from inside its own trampoline, and the synchronous executor runs the
  ;; child right there. Both submissions are posted from one drain event (the
  ;; slice after `gate`), so the runner takes the second one from its inbox at
  ;; once, inside the trampoline its first resume started.
  (h/async done
           (in-synchronous-context
            done
            (fn [done]
              (let [ds {:x (sync/deferred) :y (sync/deferred)}
                    gate (sync/deferred)
                    admission (work/parallel
                               {:concurrency 2}
                               (fn [v]
                                 (work/task
                                  (loop [i 0]
                                    (if (< i 3)
                                      (do (await (spin i))
                                          (recur (inc i)))
                                      ((ds v) [v i]))))))]
                (h/run-spin! (spin (await gate)
                                   (work/submit! admission :x :x)
                                   (work/submit! admission :y :y)
                                   :ok)
                             (fn [_]) (fn [e] (is false (str e))))
                (gate :go)
                (expect (spin [(await (:x ds)) (await (:y ds))])
                        [[:x 3] [:y 3]]
                        (fn [] (work/cancel! admission) (done))))))))

(deftest a-cps-task-run-inline-by-the-synchronous-executor-runs-its-loop
  ;; Not a Spin: a bare CPS body, started by an executor task from inside a
  ;; spin's body.
  (h/async done
           (in-synchronous-context
            done
            (fn [done]
              (let [d (sync/deferred)
                    task (work/task (loop [i 0]
                                      (if (< i 3)
                                        (do (await (spin i))
                                            (recur (inc i)))
                                        [:task i])))]
                (h/run-spin! (spin (executor/execute!
                                    (:executor (ec/current-execution-context))
                                    (fn [] (task d (fn [e] (d e)))))
                                   :ok)
                             (fn [_]) (fn [e] (is false (str e))))
                (expect (spin (await d)) [:task 3] done))))))

;; =============================================================================
;; A CPS operation that settles on the caller's stack
;; =============================================================================

(deftest a-loop-over-an-already-discarded-scope-runs-to-its-end
  ;; `discard!` of a scope that is already discarded resolves at once; it
  ;; must return what the awaiting loop's continuation returned.
  (h/async done
           (h/with-ctx [_ctx]
             (let [world-scope (scope/create {:purpose :test})]
               (h/run-spin!
                (spin (await (scope/discard! world-scope))
                      (loop [i 0]
                        (if (< i 3)
                          (do (await (scope/discard! world-scope))
                              (recur (inc i)))
                          i)))
                (fn [v] (is (= 3 v)) (done))
                (fn [e] (is false (str e)) (done)))))))

(deftest a-partial-cps-loop-over-fresh-spins-runs-to-its-end
  ;; A Spin invoked as a plain cps-fn completes synchronously inside its own
  ;; trampoline; the caller's `recur` Thunk its callback returns must reach
  ;; the caller's trampoline.
  (h/async done
           (h/with-ctx [_ctx]
             (let [block (pa/async (loop [i 0]
                                     (if (< i 3)
                                       (do (pa/await (spin i))
                                           (recur (inc i)))
                                       i)))]
               (block (fn [v] (is (= 3 v)) (done))
                      (fn [e] (is false (str e)) (done)))))))

(deftest a-partial-cps-loop-over-a-cached-spin-runs-to-its-end
  (h/async done
           (h/with-ctx [_ctx]
             (let [s (spin :cached)]
               (h/run-spin!
                s
                (fn [_]
                  (let [block (pa/async (loop [i 0 acc []]
                                          (if (< i 3)
                                            (recur (inc i) (conj acc (pa/await s)))
                                            acc)))]
                    (block (fn [v] (is (= [:cached :cached :cached] v)) (done))
                           (fn [e] (is false (str e)) (done)))))
                (fn [e] (is false (str e)) (done)))))))

(deftest a-partial-cps-loop-catching-a-cached-cancellation-runs-to-its-end
  ;; A cancelled spin's cached result is a cancellation, which -invoke does
  ;; not re-throw: the caller's catch-and-recur Thunk is all that is left.
  (h/async done
           (h/with-ctx [_ctx]
             (let [never (sync/deferred)
                   cancelled (spin (await never))]
               (h/run-spin!
                cancelled
                (fn [v] (is false (str "resolved " v)) (done))
                (fn [_]
                  (let [block (pa/async (loop [i 0 caught 0]
                                          (if (< i 3)
                                            (recur (inc i)
                                                   (try (pa/await cancelled) caught
                                                        (catch #?(:clj Exception :cljs :default) _
                                                          (inc caught))))
                                            caught)))]
                    (block (fn [v] (is (= 3 v)) (done))
                           (fn [e] (is false (str e)) (done))))))
               (spin-core/cancel-spin! cancelled)))))

#?(:clj
   (deftest an-operation-settling-in-a-fork-continues-in-the-fork
     ;; A plain CPS operation that resolves under a fork's binding: the
     ;; awaiting body's continuation goes on in that world, not back in the
     ;; awaiting one after its `recur`. On a fresh thread: no trampoline
     ;; state left behind by earlier tests.
     @(future
        (let [ctx (context/create-execution-context)]
          (try
            (binding [ec/*execution-context* ctx]
              (let [fork (context/fork-context ctx :mode :frozen)
                    settle-in-fork (fn [r _]
                                     (binding [ec/*execution-context* fork]
                                       (r nil))
                                     nil)
                    worlds (atom [])
                    result (promise)]
                (binding [ec/*callback-egress-policy* :causal-follow
                          pa/*in-trampoline* false]
                  ((spin (loop [i 0]
                        ;; the world each iteration (after its `recur`) runs in
                           (swap! worlds conj [i (:fork-id (ec/current-execution-context))])
                           (if (< i 2)
                             (do (await settle-in-fork)
                                 (recur (inc i)))
                             i)))
                   #(deliver result [:ok %])
                   #(deliver result [:error %])))
                (is (= [:ok 2] (deref result 5000 ::timeout)))
                (is (= [[0 (:fork-id ctx)] [1 (:fork-id fork)] [2 (:fork-id fork)]]
                       @worlds))
                (context/stop-context! fork)))
            (finally
              (context/stop-context! ctx)))))))

(def ^:dynamic *probe* nil)

(deftest a-thunk-wrapped-by-a-binding-restorer-runs-once
  ;; The operation returns a Thunk wrapping the body's own (partial-cps
  ;; restores `binding`s around the Thunks a continuation returns): the body
  ;; must continue exactly once per settlement.
  (h/async done
           (h/with-ctx [_ctx]
             (let [visits (atom [])
                   settle-now (fn [r _] (r :v))]
               (h/run-spin!
                (spin (loop [i 0]
                        (swap! visits conj i)
                        (if (< i 2)
                          (do (await (pa/async (binding [*probe* i]
                                                 (pa/await settle-now))))
                              (recur (inc i)))
                          i)))
                (fn [v]
                  (is (= 2 v))
                  (is (= [0 1 2] @visits))
                  (done))
                (fn [e] (is false (str e)) (done)))))))

(deftest a-callback-settled-in-a-fork-continues-in-the-fork
  ;; A body completing synchronously in a world it forked: the callback's
  ;; Thunk belongs to that world, not to the invoking one.
  (let [parent (context/create-execution-context)
        child (atom nil)
        seen (atom [])]
    (try
      (binding [ec/*execution-context* parent
                ec/*callback-egress-policy* :causal-follow]
        (let [s (spin-core/make-spin
                 (fn [r _]
                   (let [fork (context/fork-context parent :mode :frozen)]
                     (reset! child fork)
                     (binding [ec/*execution-context* fork]
                       (pa/with-trampoline (r :value)))))
                 :fork-settle-probe)]
          (binding [pa/*in-trampoline* false]
            (s (fn [_]
                 (swap! seen conj [:callback (:fork-id ec/*execution-context*)])
                 (is.simm.partial-cps.runtime/->thunk
                  #(swap! seen conj [:bounce (:fork-id ec/*execution-context*)])))
               (fn [e] (is false (str e)))))))
      (is (= [[:callback (:fork-id @child)] [:bounce (:fork-id @child)]] @seen))
      (finally
        (when @child (context/stop-context! @child))
        (context/stop-context! parent)))))

;; =============================================================================
;; A generator's first step
;; =============================================================================

(deftest a-generator-loops-before-its-first-yield
  (h/async done
           (h/with-ctx [_ctx]
             (let [gen (seq-core/gen-aseq
                        (loop [i 0]
                          (if (< i 3)
                            (do (await (spin i))
                                (recur (inc i)))
                            (seq-core/yield i))))]
               (expect (spin (first (await (anext gen)))) 3 done)))))
