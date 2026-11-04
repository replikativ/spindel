(ns org.replikativ.spindel.v2.quickbench
  "Quick v2 perf probe (ns/update), same graphs as missionary_comparison."
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.v2.core :as v2 :refer [spin track await]]
            [org.replikativ.spindel.incremental.interval :as iv])
  (:import [java.lang.management ManagementFactory]))

(defn graph [kind source]
  (let [leaf (fn [] (spin (iv/get-new (track source))))]
    (case kind
      :switch-reactive (let [left (spin (* 2 (iv/get-new (track source))))
                             right (spin (* 3 (iv/get-new (track source))))]
                         [(spin (let [n (iv/get-new (track source))]
                                  (await (if (even? n) left right))))])
      :switch (let [left (spin 10) right (spin 20)]
                [(spin (let [n (iv/get-new (track source))]
                         (+ n (await (if (even? n) left right)))))])
      :fanout (mapv (fn [_] (leaf)) (range 100))
      :chain [(reduce (fn [prev _] (spin (inc (await prev)))) (leaf) (range 50))]
      :diamond (let [b (spin (* 2 (iv/get-new (track source))))
                     c (spin (* 3 (iv/get-new (track source))))
                     d (spin (+ (await b) (await c)))
                     e (spin (* 2 (await d)))
                     f (spin (* 3 (await d)))
                     g (spin (+ (await e) (await f)))]
                 [d g])
      :fanin (let [children (mapv (fn [_] (leaf)) (range 50))]
               [(spin (loop [children children total 0]
                        (if-let [child (first children)]
                          (recur (next children) (+ total (await child)))
                          total)))])
      :child [(spin (let [n (iv/get-new (track source))
                          child (spin (* 2 n))]
                      (await child)))])))

(defn run [kind n warmup]
  (let [w (v2/world)]
    (binding [v2/*world* w]
      (let [source (v2/signal 0)
            roots (graph kind source)
            seen (volatile! 0)
            cancels (mapv #(v2/observe! % (fn [_ _] (vswap! seen inc))) roots)
            input (volatile! 0)
            upd #(v2/write! source (vswap! input inc))]
        (dotimes [_ warmup] (upd))
        (let [bean (ManagementFactory/getThreadMXBean)
              tid (.getId (Thread/currentThread))
              b0 (.getThreadAllocatedBytes ^com.sun.management.ThreadMXBean bean tid)
              t0 (System/nanoTime)]
          (dotimes [_ n] (upd))
          (let [r {:kind kind
                   :ns (long (/ (- (System/nanoTime) t0) n))
                   :bytes (long (/ (- (.getThreadAllocatedBytes ^com.sun.management.ThreadMXBean bean tid) b0) n))
                   :deliveries @seen}]
            (doseq [c cancels] (c))
            r))))))

(def mcp-ns {:chain 11108 :child 950 :diamond 4962 :fanin 56745 :fanout 32848 :switch 777 :switch-reactive 1549})

(defn report [n]
  (vec (for [k [:fanout :chain :diamond :fanin :switch :switch-reactive :child]]
         (let [r (run k n n)]
           (assoc r :x-mcp (/ (Math/round (* 100.0 (/ (:ns r) (mcp-ns k)))) 100.0))))))

;; ---------------------------------------------------------------------------
;; Load-insensitive cost: retired user instructions on this thread (perf)

(defn- thread-tid []
  (let [p (str (java.nio.file.Files/readSymbolicLink (java.nio.file.Paths/get "/proc/thread-self" (make-array String 0))))]
    (Long/parseLong (last (clojure.string/split p #"/")))))

(defn instructions
  "Retired user instructions while `(f)` runs on this thread."
  [f]
  (let [tid (thread-tid)
        out (java.io.File/createTempFile "perf" ".csv")
        pb (doto (ProcessBuilder. ["perf" "stat" "-x," "-e" "instructions:u" "-t" (str tid) "-o" (str out)])
             (.redirectErrorStream true))
        p (.start pb)]
    (Thread/sleep 200)
    (f)
    (.waitFor (.start (ProcessBuilder. ["kill" "-INT" (str (.pid p))])))
    (.waitFor p)
    ;; hybrid CPUs report one line per core type (cpu_atom, cpu_core): sum them
    (let [lines (filter #(re-find #"instructions" %) (clojure.string/split-lines (slurp out)))]
      (.delete out)
      (reduce + (for [l lines :let [v (first (clojure.string/split l #","))]
                      :when (re-matches #"\d+" v)]
                  (Long/parseLong v))))))

(defn instr-per-update [kind n]
  (let [w (v2/world)]
    (binding [v2/*world* w]
      (let [source (v2/signal 0)
            roots (graph kind source)
            cancels (mapv #(v2/observe! % (fn [_ _])) roots)
            input (volatile! 0)
            upd #(v2/write! source (vswap! input inc))]
        (dotimes [_ n] (upd))
        (let [i (instructions #(dotimes [_ n] (upd)))]
          (doseq [c cancels] (c))
          (long (/ i n)))))))
