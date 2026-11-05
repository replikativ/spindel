(ns org.replikativ.spindel.v2.combinators
  "M6 phase A combinators on v2 (.internal/m6-phase-a-design.md R4, R7, R8).

   They take and build computations (spins), like the old ones: lazy, cached
   and reactive. A combinator owns nothing by reference: a race's losers
   lose its demand, so a loser demanded only by the race goes idle and its
   run is cancelled (§3.3); a loser demanded elsewhere keeps running. Tasks
   passed in are observed, never cancelled."
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.v2.core :as v2 :refer [spin await await-all await-any]])
  #?(:cljs (:require-macros [org.replikativ.spindel.v2.core :refer [spin]])))

(defn parallel
  "A computation of the vector of the values of `hs`; fail-fast on the first
   error (Z#61); re-runs when any of them changes."
  [& hs]
  (let [hs (vec hs)]
    (spin (await-all hs))))

(defn race
  "A computation of the value of whichever of `hs` settles first."
  [& hs]
  (let [hs (vec hs)]
    (spin (await-any hs))))

(defn sleep
  "A computation that settles with `value` after `ms` (lazy: the timer arms
   when it is demanded)."
  ([ms] (sleep ms nil))
  ([ms value] (spin (v2/sleep ms) value)))

(defn timeout
  "The value of `h`, or `fallback` if it has not settled within `ms`."
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
   on JS a returned promise is awaited. Cancellation interrupts the worker."
  ([f] (blocking f nil))
  ([f opts]
   (let [g #?(:clj (bound-fn* f) :cljs f)]
     (spin (v2/offload g opts)))))
