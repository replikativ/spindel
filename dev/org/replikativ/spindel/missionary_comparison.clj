(ns org.replikativ.spindel.missionary-comparison
  "Synchronous reactive graph measurements against Missionary b.46.
   Both graphs use the same source changes and final observed values. Spindel
   retains forkable runtime state; Missionary's signal graph does not. The L0
   task comparison is a lower-bound lifecycle reference, not equivalent caching.

   Run with a JVM slot:
   clojure -J-Xmx1g -Sdeps '{:deps {missionary/missionary {:mvn/version \"b.46\"}}}'
     -M:bench -m org.replikativ.spindel.missionary-comparison

   Use -J-Dspindel.compare.kinds=fanout,chain,diamond,fanin to omit L0.
   The local Missionary checkout can be substituted with :local/root."
  (:refer-clojure :exclude [await])
  (:require [is.simm.partial-cps.async :as cps]
            [missionary.core :as m]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.executor :as ex]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.cps :refer [spin]])
  (:import [com.sun.management ThreadMXBean]
           [java.lang.management ManagementFactory]))

(defn- spindel-graph [kind source]
  (case kind
    :fanout (mapv (fn [_] (spin (iv/get-new (track source)))) (range 100))
    :chain (let [head (spin (iv/get-new (track source)))]
             [(reduce (fn [prev _] (spin (inc (await prev)))) head (range 50))])
    :diamond (let [b (spin (* 2 (iv/get-new (track source))))
                   c (spin (* 3 (iv/get-new (track source))))
                   d (spin (+ (await b) (await c)))
                   e (spin (* 2 (await d)))
                   f (spin (* 3 (await d)))
                   g (spin (+ (await e) (await f)))]
               [d g])
    :fanin (let [children (mapv (fn [_] (spin (iv/get-new (track source)))) (range 50))]
             [(spin (reduce + (mapv (fn [child] (await child)) children)))])))

(defn- missionary-graph [kind source]
  (let [leaf (fn [] (m/signal (m/latest identity source)))]
    (case kind
      :fanout (mapv (fn [_] (leaf)) (range 100))
      :chain (let [head (leaf)]
               [(reduce (fn [prev _] (m/signal (m/latest inc prev))) head (range 50))])
      :diamond (let [b (m/signal (m/latest #(* 2 %) source))
                     c (m/signal (m/latest #(* 3 %) source))
                     d (m/signal (m/latest + b c))
                     e (m/signal (m/latest #(* 2 %) d))
                     f (m/signal (m/latest #(* 3 %) d))
                     g (m/signal (m/latest + e f))]
                 [d g])
      :fanin (let [children (mapv (fn [_] (leaf)) (range 50))]
               [(m/signal (apply m/latest (fn [& values] (reduce + values)) children))]))))

(defn- expected-values [kind n]
  (case kind
    :fanout (vec (repeat 100 n))
    :chain [(+ n 50)]
    :diamond [(* 5 n) (* 25 n)]
    :fanin [(* 50 n)]))

(defn- measure-updates [update! warmup n]
  (dotimes [_ warmup] (update!))
  (let [^ThreadMXBean bean (ManagementFactory/getThreadMXBean)
        tid (.getId (Thread/currentThread))
        before-bytes (.getThreadAllocatedBytes bean tid)
        start (System/nanoTime)]
    (dotimes [_ n] (update!))
    {:ns-per-update (/ (double (- (System/nanoTime) start)) n)
     :bytes-per-update (/ (double (- (.getThreadAllocatedBytes bean tid) before-bytes)) n)}))

(defn- run-spindel [kind n warmup]
  (let [rt (ctx/create-execution-context :executor (ex/synchronous-executor))]
    (try
      (binding [ec/*execution-context* rt cps/*in-trampoline* false]
        (let [source (sig/signal 0)
              roots (spindel-graph kind source)]
          (doseq [s roots] @s)
          (let [measurement (measure-updates #(swap! source inc) warmup n)
                observed (mapv deref roots)
                expected (expected-values kind (+ n warmup))]
            (when-not (= expected observed)
              (throw (ex-info "Spindel result mismatch" {:kind kind :expected expected :observed observed})))
            measurement)))
      (finally (ctx/close-context! rt)))))

(defn- observe! [flow]
  (let [last-value (volatile! nil)
        seen (volatile! 0)
        failure (volatile! nil)
        task (m/reduce (fn [_ value]
                         (vreset! last-value value)
                         (vswap! seen inc)
                         nil)
                       nil flow)
        cancel (task (fn [_]) (fn [error] (vreset! failure error)))]
    {:last-value last-value :seen seen :failure failure :cancel cancel}))

(defn- run-missionary [kind n warmup]
  (let [source-atom (atom 0)
        source (m/signal (m/watch source-atom))
        roots (missionary-graph kind source)
        observers (mapv observe! roots)]
    (try
      (let [measurement (measure-updates #(swap! source-atom inc) warmup n)
            observed (mapv (comp deref :last-value) observers)
            expected (expected-values kind (+ n warmup))
            seen (mapv (comp deref :seen) observers)]
        (when-not (and (= expected observed)
                       (= (vec (repeat (count roots) (inc (+ n warmup)))) seen))
          (throw (ex-info "Missionary result mismatch"
                          {:kind kind :expected expected :observed observed :seen seen})))
        measurement)
      (finally (doseq [{:keys [cancel]} observers] (cancel))))))

(defn- run-spindel-l0 [n warmup]
  (let [rt (ctx/create-execution-context :executor (ex/synchronous-executor))
        retained (java.util.ArrayList.)
        next-input (volatile! 0)
        last-value (volatile! nil)]
    (try
      (binding [ec/*execution-context* rt cps/*in-trampoline* false]
        (let [step! (fn []
                      (let [i (vswap! next-input inc)
                            s (spin i)]
                        (.add retained s)
                        (vreset! last-value @s)))
              measurement (measure-updates step! warmup n)]
          (when-not (= (+ n warmup) @last-value)
            (throw (ex-info "Spindel L0 mismatch" {:observed @last-value})))
          (java.lang.ref.Reference/reachabilityFence retained)
          measurement))
      (finally (ctx/close-context! rt)))))

(defn- run-missionary-l0 [n warmup]
  (let [retained (java.util.ArrayList.)
        next-input (volatile! 0)
        last-value (volatile! nil)
        success (fn [value] (vreset! last-value value))
        failure (fn [error] (throw error))
        step! (fn []
                (let [i (vswap! next-input inc)
                      task (m/sp i)]
                  (.add retained task)
                  (task success failure)))
        measurement (measure-updates step! warmup n)]
    (when-not (= (+ n warmup) @last-value)
      (throw (ex-info "Missionary L0 mismatch" {:observed @last-value})))
    (java.lang.ref.Reference/reachabilityFence retained)
    measurement))

(defn -main [& _]
  (let [^ThreadMXBean bean (ManagementFactory/getThreadMXBean)
        n (Long/parseLong (System/getProperty "spindel.compare.ops" "1000"))
        warmup (Long/parseLong (System/getProperty "spindel.compare.warmup" "200"))
        repeats (Long/parseLong (System/getProperty "spindel.compare.repeats" "3"))
        kinds (mapv keyword (.split (System/getProperty "spindel.compare.kinds"
                                                       "l0,fanout,chain,diamond,fanin") ","))]
    (.setThreadAllocatedMemoryEnabled bean true)
    (doseq [kind kinds
            trial (range repeats)
            implementation (if (even? trial) [:spindel :missionary] [:missionary :spindel])]
      (let [result (if (= kind :l0)
                     ((case implementation
                        :spindel run-spindel-l0
                        :missionary run-missionary-l0) n warmup)
                     ((case implementation
                        :spindel run-spindel
                        :missionary run-missionary) kind n warmup))]
        (prn (merge {:kind kind :implementation implementation :trial trial
                     :operations n :warmup warmup}
                    result))
        (flush)))
    (shutdown-agents)))
