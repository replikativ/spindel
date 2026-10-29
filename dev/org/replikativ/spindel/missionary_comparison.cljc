(ns org.replikativ.spindel.missionary-comparison
  "Synchronous JVM/Node reactive graph measurements against Missionary b.46.
   Both graphs use the same source changes and final observed values. Spindel
   retains forkable runtime state; Missionary's signal graph does not. The L0
   task comparison is a lower-bound lifecycle reference, not equivalent caching.

   JVM: clojure -M:bench -m org.replikativ.spindel.missionary-comparison
   Node: clojure -M:bench:bench-js && node target/bench/compare.js
   Node configuration uses SPINDEL_COMPARE_{OPS,WARMUP,REPEATS,ENGINES,KINDS}.
   Node reports wall time; use dev/scripts/profile-reactive.cjs for allocation
   attribution, including collected objects. Profiles include setup and warmup.

   Use -J-Dspindel.compare.kinds=fanout,chain,diamond,fanin to omit L0.
   With those reactive kinds, compare the experimental bridge and standing
   observers using -J-Dspindel.compare.engines=kernel-cells,spindel-observed,missionary.
   Kernel measurements disable model diagnostics.
   The local Missionary checkout can be substituted with :local/root."
  (:refer-clojure :exclude [await])
  (:require [clojure.string :as str]
            [is.simm.partial-cps.async :as cps]
            [missionary.core :as m]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.executor :as ex]
            [org.replikativ.spindel.kernel-runtime :as k #?@(:cljs [:include-macros true])]
            [org.replikativ.spindel.compact-runtime :as c #?@(:cljs [:include-macros true])]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.cps :refer [spin]])
  #?(:clj (:import [com.sun.management ThreadMXBean]
                   [java.lang.management ManagementFactory])))

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

(defn- missionary-cp-graph [kind source]
  (let [leaf (fn [] (m/signal (m/cp (m/?< source))))]
    (case kind
      :fanout (mapv (fn [_] (leaf)) (range 100))
      :chain [(reduce (fn [prev _] (m/signal (m/cp (inc (m/?< prev)))))
                      (leaf) (range 50))]
      :diamond (let [b (m/signal (m/cp (* 2 (m/?< source))))
                     c (m/signal (m/cp (* 3 (m/?< source))))
                     d (m/signal (m/cp (+ (m/?< b) (m/?< c))))
                     e (m/signal (m/cp (* 2 (m/?< d))))
                     f (m/signal (m/cp (* 3 (m/?< d))))
                     g (m/signal (m/cp (+ (m/?< e) (m/?< f))))]
                 [d g])
      :fanin (let [children (mapv (fn [_] (leaf)) (range 50))]
               [(m/signal (m/cp
                           (loop [remaining children total 0]
                             (if-let [child (first remaining)]
                               (recur (next remaining) (+ total (m/?< child)))
                               total))))]))))

(defn- expected-values [kind n]
  (case kind
    :fanout (vec (repeat 100 n))
    :chain [(+ n 50)]
    :diamond [(* 5 n) (* 25 n)]
    :fanin [(* 50 n)]))

(defn- kernel-graph [rt kind source]
  (let [leaf (fn [id] (k/kspin rt id (iv/get-new (k/track source))))]
    (case kind
      :fanout (mapv #(leaf [:leaf %]) (range 100))
      :chain [(reduce (fn [prev i] (k/kspin rt [:chain i] (inc (k/await prev))))
                      (leaf :head) (range 50))]
      :diamond (let [b (k/kspin rt :b (* 2 (iv/get-new (k/track source))))
                     c (k/kspin rt :c (* 3 (iv/get-new (k/track source))))
                     d (k/kspin rt :d (+ (k/await b) (k/await c)))
                     e (k/kspin rt :e (* 2 (k/await d)))
                     f (k/kspin rt :f (* 3 (k/await d)))
                     g (k/kspin rt :g (+ (k/await e) (k/await f)))]
                 [d g])
      :fanin (let [children (mapv #(leaf [:leaf %]) (range 50))]
               [(k/kspin rt :root
                         (loop [children children total 0]
                           (if-let [child (first children)]
                             (recur (next children) (+ total (k/await child)))
                             total)))]))))

(defn- compact-graph [rt kind source]
  (let [leaf (fn [id] (c/cspin rt id (iv/get-new (c/track source))))]
    (case kind
      :fanout (mapv #(leaf [:leaf %]) (range 100))
      :chain [(reduce (fn [prev i] (c/cspin rt [:chain i] (inc (c/await prev))))
                      (leaf :head) (range 50))]
      :diamond (let [b (c/cspin rt :b (* 2 (iv/get-new (c/track source))))
                     c (c/cspin rt :c (* 3 (iv/get-new (c/track source))))
                     d (c/cspin rt :d (+ (c/await b) (c/await c)))
                     e (c/cspin rt :e (* 2 (c/await d)))
                     f (c/cspin rt :f (* 3 (c/await d)))
                     g (c/cspin rt :g (+ (c/await e) (c/await f)))]
                 [d g])
      :fanin (let [children (mapv #(leaf [:leaf %]) (range 50))]
               [(c/cspin rt :root
                         (loop [children children total 0]
                           (if-let [child (first children)]
                             (recur (next children) (+ total (c/await child)))
                             total)))]))))

(defn- measure-updates [update! warmup n]
  (dotimes [_ warmup] (update!))
  #?(:clj
     (let [^ThreadMXBean bean (ManagementFactory/getThreadMXBean)
           tid (.getId (Thread/currentThread))
           before-bytes (.getThreadAllocatedBytes bean tid)
           start (System/nanoTime)]
       (dotimes [_ n] (update!))
       {:ns-per-update (/ (double (- (System/nanoTime) start)) n)
        :bytes-per-update (/ (double (- (.getThreadAllocatedBytes bean tid) before-bytes)) n)})
     :cljs
     (let [start (js/performance.now)]
       (dotimes [_ n] (update!))
       {:ns-per-update (/ (* 1000000 (- (js/performance.now) start)) n)})))

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

(defn- run-spindel-observed [kind n warmup]
  (let [rt (ctx/create-execution-context :executor (ex/synchronous-executor))]
    (try
      (binding [ec/*execution-context* rt cps/*in-trampoline* false]
        (let [source (sig/signal 0)
              roots (spindel-graph kind source)
              values (mapv (fn [_] (volatile! nil)) roots)
              counts (mapv (fn [_] (volatile! 0)) roots)
              failure (volatile! nil)]
          (doseq [[root value seen] (map vector roots values counts)]
            (root #(do (vreset! value %) (vswap! seen inc)) #(vreset! failure %)))
          (let [measurement (measure-updates #(swap! source inc) warmup n)
                observed (mapv deref values)
                seen (mapv deref counts)
                expected (expected-values kind (+ n warmup))]
            (when-not (and (nil? @failure) (= expected observed)
                           (= (vec (repeat (count roots) (inc (+ n warmup)))) seen))
              (throw (ex-info "Observed Spindel result mismatch"
                              {:kind kind :expected expected :observed observed :seen seen :error @failure})))
            #?(:clj (java.lang.ref.Reference/reachabilityFence roots))
            measurement)))
      (finally (ctx/close-context! rt)))))

(defn- run-kernel
  ([kind n warmup] (run-kernel kind n warmup {}))
  ([kind n warmup options]
   (let [rt (k/runtime (merge {:diagnostics? false} options))
         source (k/signal rt :source 0)
         roots (kernel-graph rt kind source)
         values (mapv (fn [_] (volatile! nil)) roots)
         counts (mapv (fn [_] (volatile! 0)) roots)
         cancellations (mapv (fn [root value seen]
                               (k/observe! rt root
                                           #(do (vreset! value %) (vswap! seen inc))
                                           #(throw %))) roots values counts)
         input (volatile! 0)]
     (try
       (let [measurement (measure-updates #(k/set-signal! rt source (vswap! input inc)) warmup n)
             observed (mapv deref values)
             seen (mapv deref counts)
             expected (expected-values kind (+ n warmup))]
         (when-not (and (= expected observed)
                        (= (vec (repeat (count roots) (inc (+ n warmup)))) seen))
           (throw (ex-info "Kernel result mismatch"
                           {:kind kind :expected expected :observed observed :seen seen})))
         measurement)
       (finally (doseq [cancel cancellations] (cancel)))))))

(defn- run-compact
  ([kind n warmup] (run-compact kind n warmup {}))
  ([kind n warmup options]
   (let [rt (c/runtime (merge {:diagnostics? false} options))
         source (c/signal rt :source 0)
         roots (compact-graph rt kind source)
         values (mapv (fn [_] (volatile! nil)) roots)
         counts (mapv (fn [_] (volatile! 0)) roots)
         cancellations (mapv (fn [root value seen]
                               (c/observe! rt root
                                           #(do (vreset! value %) (vswap! seen inc))
                                           #(throw %))) roots values counts)
         input (volatile! 0)]
     (try
       (let [measurement (measure-updates #(c/set-signal! rt source (vswap! input inc)) warmup n)
             observed (mapv deref values)
             seen (mapv deref counts)
             expected (expected-values kind (+ n warmup))]
         (when-not (and (= expected observed)
                        (= (vec (repeat (count roots) (inc (+ n warmup)))) seen))
           (throw (ex-info "Kernel result mismatch"
                           {:kind kind :expected expected :observed observed :seen seen})))
         measurement)
       (finally (doseq [cancel cancellations] (cancel)))))))

(defn reclamation-churn
  "Report retained bookkeeping after n distinct spins have completed and lost
   their host handles. Generation history is reported separately from live rows."
  [n]
  (let [rt (c/runtime)]
    (dotimes [i n]
      (let [handle (c/cspin rt [:ephemeral i] 42)]
        (c/observe! rt handle (fn [_]) #(throw %))
        (c/notify-unreachable! rt handle)))
    (let [state (c/snapshot rt)]
      (assoc (c/storage-stats rt)
             :entities (count (:entities state))
             :generation-history (count (get-in state [:global :generation-clock]))))))

(defn- run-kernel-cells [kind n warmup]
  (run-kernel kind n warmup {:cells? true}))

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

(defn- run-missionary-graph [build kind n warmup]
  (let [source-atom (atom 0)
        source (m/signal (m/watch source-atom))
        roots (build kind source)
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

(defn- run-missionary [kind n warmup]
  (run-missionary-graph missionary-graph kind n warmup))
(defn- run-missionary-cp [kind n warmup]
  (run-missionary-graph missionary-cp-graph kind n warmup))

#?(:clj
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
         (finally (ctx/close-context! rt))))))

#?(:clj
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
       measurement)))

(defn run-case!
  "Run one matched graph, verifying final values and delivery counts."
  [implementation kind n warmup]
  (if (= kind :l0)
    #?(:clj ((case implementation :spindel run-spindel-l0 :missionary run-missionary-l0) n warmup)
       :cljs (throw (ex-info "L0 blocking comparison is JVM-only" {})))
    ((case implementation
       :spindel #?(:clj run-spindel :cljs (throw (ex-info "Use spindel-observed on JS" {})))
       :spindel-observed run-spindel-observed
       :kernel run-kernel
       :kernel-cells run-kernel-cells
       :compact run-compact
       :missionary-cp run-missionary-cp
       :missionary run-missionary) kind n warmup)))

(defn- setting [property environment fallback]
  #?(:clj (System/getProperty property fallback)
     :cljs (or (aget (.-env js/process) environment) fallback)))

(defn -main [& _]
  (let [parse #?(:clj #(Long/parseLong %) :cljs #(js/parseInt % 10))
        n (parse (setting "spindel.compare.ops" "SPINDEL_COMPARE_OPS" "10000"))
        warmup (parse (setting "spindel.compare.warmup" "SPINDEL_COMPARE_WARMUP" "10000"))
        repeats (parse (setting "spindel.compare.repeats" "SPINDEL_COMPARE_REPEATS" "3"))
        implementations (mapv keyword (str/split (setting "spindel.compare.engines" "SPINDEL_COMPARE_ENGINES"
                                                          "compact,missionary-cp,missionary") #","))
        kinds (mapv keyword (str/split (setting "spindel.compare.kinds" "SPINDEL_COMPARE_KINDS"
                                                "fanout,chain,diamond,fanin") #","))]
    #?(:clj (let [^ThreadMXBean bean (ManagementFactory/getThreadMXBean)]
              (.setThreadAllocatedMemoryEnabled bean true)))
    (when (and (some #{:l0} kinds) (some #{:kernel :kernel-cells :compact :spindel-observed :missionary-cp} implementations))
      (throw (ex-info "Experimental engines require explicit reactive benchmark kinds"
                      {:kinds kinds :engines implementations})))
    (doseq [kind kinds trial (range repeats)
            implementation (if (even? trial) implementations (reverse implementations))]
      (prn (merge {:kind kind :implementation implementation :trial trial
                   :platform #?(:clj :jvm :cljs :node) :operations n :warmup warmup
                   :profiled? (= "1" (setting "spindel.compare.profiled" "SPINDEL_COMPARE_PROFILED" "0"))}
                  (run-case! implementation kind n warmup)))
      #?(:clj (flush)))
    #?(:clj (shutdown-agents))))

#?(:cljs (set! *main-cli-fn* -main))
