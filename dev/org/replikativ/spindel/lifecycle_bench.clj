(ns org.replikativ.spindel.lifecycle-bench
  "Cost of one spin's whole lifecycle, from creation through its result: the
   constant every freshly created spin pays, whatever it computes.
   Run: clojure -J-Xmx3g -M:bench -m org.replikativ.spindel.lifecycle-bench
   Honor the shared-machine JVM lock before invoking."
  (:refer-clojure :exclude [await])
  (:require [is.simm.partial-cps.async :as cps]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.executor :as ex]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.enum-bench :as enumeration]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.cps :refer [spin]])
  (:import [java.lang.management ManagementFactory]
           [com.sun.management ThreadMXBean]))

(defn- body-fn
  "A fn creating and running one fresh spin of `kind`, returning its result."
  [kind retain!]
  (case kind
    ;; no effect site
    :L0 (fn [i] @(retain! (spin (+ i 1))))
    ;; two awaits of cached spins
    :L2-await (let [b (retain! (spin 1)) c (retain! (spin 2))]
                @b @c
                (fn [i] @(retain! (spin (+ i (await b) (await c))))))
    ;; two tracks of signals
    :L2-track (let [a (sig/signal 1) b (sig/signal 2)]
                (fn [i] @(retain! (spin (+ i (iv/get-new (track a)) (iv/get-new (track b)))))))
    ;; a parent creating and awaiting one child
    :L-child (fn [i] @(retain! (spin (inc (await (retain! (spin i)))))))))

(defn run-one [kind n warmup]
  ;; Keep EVERY created handle (including lexical children and warmup spins)
  ;; alive. No run is allowed to borrow cleanup from preceding operations.
  ;; The preallocated list's stores allocate no per-operation storage.
  (enumeration/full-gc! nil)
  (let [rt (ctx/create-execution-context :executor (ex/synchronous-executor))
        handles (java.util.ArrayList. (+ 2 (* 2 (+ n warmup))))
        retain! (fn [s] (.add handles s) s)
        active? (java.util.concurrent.atomic.AtomicBoolean. false)
        cleanup-calls (java.util.concurrent.atomic.AtomicLong. 0)
        cleanup simple/full-cleanup-spin!
        ^ThreadMXBean bean (ManagementFactory/getThreadMXBean)
        tid (.getId (Thread/currentThread))]
    (.setThreadAllocatedMemoryEnabled bean true)
    (try
      (with-redefs [simple/full-cleanup-spin!
                    (fn [world sid]
                      (when (.get active?) (.incrementAndGet cleanup-calls))
                      (cleanup world sid))]
        (binding [ec/*execution-context* rt cps/*in-trampoline* false]
          (let [f (body-fn kind retain!)]
            (dotimes [i warmup] (f i))
            (.set active? true)
            (let [bytes (.getThreadAllocatedBytes bean tid)
                  start (System/nanoTime)
                  sum (loop [i 0 acc 0] (if (< i n) (recur (inc i) (+ acc (f i))) acc))
                  elapsed (- (System/nanoTime) start)
                  allocated (- (.getThreadAllocatedBytes bean tid) bytes)]
              (.set active? false)
              (java.lang.ref.Reference/reachabilityFence handles)
              (when-not (zero? (.get cleanup-calls))
                (throw (ex-info "Cleanup contaminated lifecycle sample"
                                {:cleanup-calls (.get cleanup-calls)})))
              {:lifecycle kind :spins n :warmup warmup :checksum sum
               :retained-handles (.size handles) :cleanup-calls (.get cleanup-calls)
               :us-per-spin (/ (double elapsed) n 1000)
               :kb-per-spin (/ (double allocated) n 1024)}))))
      (finally
        (.set active? false)
        (ctx/close-context! rt)
        (java.lang.ref.Reference/reachabilityFence handles)))))

(defn -main [& kinds]
  (let [n (Long/parseLong (System/getProperty "spindel.bench.ops" "5000"))
        warmup (Long/parseLong (System/getProperty "spindel.bench.warmup" "2000"))
        kinds (if (seq kinds) (map keyword kinds) [:L0 :L2-await :L2-track :L-child])]
    (doseq [k kinds] (prn (run-one k n warmup)) (flush))
    (shutdown-agents)))
