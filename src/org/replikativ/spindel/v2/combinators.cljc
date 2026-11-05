(ns org.replikativ.spindel.v2.combinators
  "M6 phase A combinators on v2 (.internal/m6-phase-a-design.md R4, R7, R8).

   Most combinators build lazy, cached, reactive computations (spins).
   Race and timeout build eager, one-shot tasks. A race's losers
   lose its demand, so a loser demanded only by the race goes idle and its
   run is cancelled (§3.3); a loser demanded elsewhere keeps running. Tasks
   passed in are observed, never cancelled."
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.v2.core :as v2 :refer [spin task await await-all await-any]]
            [org.replikativ.spindel.incremental.interval :as iv])
  #?(:cljs (:require-macros [org.replikativ.spindel.v2.core :refer [spin task]])))

(defn parallel
  "A computation of the vector of the values of `hs`; fail-fast on the first
   error (Z#61); re-runs when any of them changes."
  [& hs]
  (let [hs (vec hs)]
    (spin (await-all hs))))

(defn race
  "An eager, one-shot task of the first completion of `hs`, including errors.
   Already-ready ties use input order. Shared tasks are observed, never
   cancelled as losers; computations lose this race's demand. Owned task
   children are cancelled when their owner finishes. For reactive
   selection, use `(spin (await-any hs))`."
  [& hs]
  (let [hs (vec hs)]
    (task (await-any hs))))

(defn sleep
  "A computation that settles with `value` after `ms` (lazy: the timer arms
   when it is demanded)."
  ([ms] (sleep ms nil))
  ([ms value] (spin (v2/sleep ms) value)))

(defn timeout
  "A one-shot task of `h`'s value, or `fallback` after `ms`.
   A timeout withdraws demand from a computation; it does not cancel a
   shared task passed as `h`."
  [h ms fallback]
  (race h (sleep ms fallback)))

(defn never
  "A deferred that is never delivered."
  []
  (v2/deferred))

(defn spawn!
  "Fire-and-forget: demands `h` and calls `on-success`/`on-error` with its
   result (host callbacks; an exception in one is reported, never re-entered).
   Returns a fn that withdraws the demand. The demand is a host root until
   it settles or is withdrawn (R7)."
  ([h] (spawn! h {}))
  ([h {:keys [on-success on-error]}]
   (let [report (fn [which t]
                  #?(:clj (binding [*out* *err*] (println "spawn!" which "callback failed:" t))
                     :cljs (js/console.error "spawn!" which "callback failed:" t)))]
     (v2/value-async h (fn [v err?]
                         (try (if err?
                                (if on-error (on-error v) (report :on-error v))
                                (when on-success (on-success v)))
                              (catch #?(:clj Throwable :cljs :default) t
                                (report (if err? :on-error :on-success) t))))))))

(defn blocking
  "A computation of `(f)` run off the world, on `:pool` (an Executor) or the
   world's executor. The calling thread's dynamic bindings are conveyed (JVM);
   on JS a returned promise is awaited. Cancellation interrupts the worker. A
   pool that would run the work on the caller (CallerRunsPolicy) is refused;
   a pool that rejects the work fails the computation."
  ([f] (blocking f nil))
  ([f opts]
   #?(:clj (when-let [p (:pool opts)]
             (when (and (instance? java.util.concurrent.ThreadPoolExecutor p)
                        (instance? java.util.concurrent.ThreadPoolExecutor$CallerRunsPolicy
                                   (.getRejectedExecutionHandler ^java.util.concurrent.ThreadPoolExecutor p)))
               (throw (ex-info "blocking: a CallerRunsPolicy pool would run on the world"
                               {:spindel/invalid :pool})))))
   (let [g #?(:clj (bound-fn* f) :cljs f)]
     (spin (v2/offload g opts)))))

;; ---------------------------------------------------------------------------
;; Rate operators (old semantics: compositions of a timer with the source).
;; `source` is a handle (awaited) or a plain value such as a tracked interval
;; (returned as is). Inside a computation that tracks a signal, the enclosing
;; computation re-runs on a change, which re-arms the timer: debounce.

(defn debounce
  "A computation that waits `ms`, then delivers `source`'s value."
  [source ms]
  (if (v2/handle? source)
    (spin (v2/sleep ms) (await source))
    (spin (v2/sleep ms) source)))

(defn throttle
  "A computation that waits 1000/`max-hz` ms, then delivers
   `(merge-fn nil value)`."
  [source max-hz merge-fn]
  (let [ms (/ 1000 max-hz)]
    (if (v2/handle? source)
      (spin (v2/sleep ms) (merge-fn nil (await source)))
      (spin (v2/sleep ms) (merge-fn nil source)))))

(defn sample
  "A computation that waits `ms`, then delivers `source`'s current value."
  [source ms]
  (debounce source ms))

(defn relieve
  "A computation of `source`'s latest value: a run whose value was overtaken
   while it waited delivers the newest one."
  [source]
  (let [latest (clojure.core/atom nil)
        version (clojure.core/atom 0)]
    (if (v2/handle? source)
      (spin (let [mine (swap! version inc)
                  v (await source)]
              (reset! latest v)
              (if (= @version mine) v @latest)))
      (spin source))))

(defn accumulate
  "A computation tracking `signal` that merges each new interval into the
   ones not yet delivered, with the associative `merge-fn` (e.g.
   iv/merge-intervals), so rate control loses no deltas."
  [signal merge-fn]
  (let [acc (clojure.core/atom nil)]
    (spin (let [cur (v2/track signal)
                merged (merge-fn @acc cur)]
            (reset! acc merged)
            merged))))

;; ---------------------------------------------------------------------------
;; Errors as values (old attempt/absolve)

(defn attempt
  "A computation that always succeeds with a zero-argument fn: it returns
   `h`'s value, or throws its error."
  [h]
  (spin (try (let [v (await h)] (fn [] v))
             (catch #?(:clj Throwable :cljs :default) t (fn [] (throw t))))))

(defn absolve
  "Inverse of attempt: a computation of calling the fn `h` delivers."
  [h]
  (spin ((await h))))

;; ---------------------------------------------------------------------------
;; Signal updates (old swap-signal-changed?, swap-await!)

(defn swap-await!
  "A task that sets `sig` to `(await (apply f current args))`, where `f`
   returns an awaitable; a write landing meanwhile re-runs `f` against the
   new value (compare-and-set retry)."
  [sig f & args]
  (task (loop []
          (let [cur (iv/get-new (v2/track sig))
                new (await (apply f cur args))]
            (if (compare-and-set! sig cur new) new (recur))))))
