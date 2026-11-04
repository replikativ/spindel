(ns org.replikativ.spindel.v2paged-bench
  "Paired probe: pointer rows (v2spike) vs paged ids (v2paged), same graphs."
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.v2spike :as s]
            [org.replikativ.spindel.v2paged :as p]
            [org.replikativ.spindel.v2fwd :as fw]
            [org.replikativ.spindel.incremental.interval :as iv]))

(defn- s-graph [kind src]
  (let [leaf (fn [] (s/cmp (iv/get-new (s/track src))))]
    (case kind
      :fanout (mapv (fn [_] (leaf)) (range 100))
      :chain [(reduce (fn [prev _] (s/cmp (inc (s/await prev)))) (leaf) (range 50))]
      :diamond (let [b (s/cmp (* 2 (iv/get-new (s/track src)))) c (s/cmp (* 3 (iv/get-new (s/track src))))
                     d (s/cmp (+ (s/await b) (s/await c))) e (s/cmp (* 2 (s/await d))) f (s/cmp (* 3 (s/await d)))]
                 [(s/cmp (+ (s/await e) (s/await f)))])
      :switch (let [l (s/cmp 10) r (s/cmp 20)]
                [(s/cmp (let [n (iv/get-new (s/track src))] (+ n (s/await (if (even? n) l r)))))])
      :child [(s/cmp (let [n (iv/get-new (s/track src)) c (s/cmp (* 2 n))] (s/await c)))])))

(defn- p-graph [kind src]
  (let [leaf (fn [] (p/cmp (iv/get-new (p/track src))))]
    (case kind
      :fanout (mapv (fn [_] (leaf)) (range 100))
      :chain [(reduce (fn [prev _] (p/cmp (inc (p/await prev)))) (leaf) (range 50))]
      :diamond (let [b (p/cmp (* 2 (iv/get-new (p/track src)))) c (p/cmp (* 3 (iv/get-new (p/track src))))
                     d (p/cmp (+ (p/await b) (p/await c))) e (p/cmp (* 2 (p/await d))) f (p/cmp (* 3 (p/await d)))]
                 [(p/cmp (+ (p/await e) (p/await f)))])
      :switch (let [l (p/cmp 10) r (p/cmp 20)]
                [(p/cmp (let [n (iv/get-new (p/track src))] (+ n (p/await (if (even? n) l r)))))])
      :child [(p/cmp (let [n (iv/get-new (p/track src)) c (p/cmp (* 2 n))] (p/await c)))])))

(defn- measure [upd n]
  (let [bean (java.lang.management.ManagementFactory/getThreadMXBean)
        tid (.getId (Thread/currentThread))]
    (dotimes [_ n] (upd))
    (let [b0 (.getThreadAllocatedBytes ^com.sun.management.ThreadMXBean bean tid) t0 (System/nanoTime)]
      (dotimes [_ n] (upd))
      {:ns (long (/ (- (System/nanoTime) t0) n))
       :bytes (long (/ (- (.getThreadAllocatedBytes ^com.sun.management.ThreadMXBean bean tid) b0) n))})))

(defn run-s [kind n]
  (let [w (s/world)]
    (binding [s/*world* w]
      (let [src (s/source w 0) roots (s-graph kind src) last (volatile! nil)
            _ (doseq [r roots] (s/observe! r #(vreset! last %) #(throw %)))
            i (volatile! 0)]
        (assoc (measure #(s/set-source! src (vswap! i inc)) n) :last @last)))))

(defn run-p [kind n & {:keys [forked?]}]
  (let [w0 (p/world)]
    (binding [p/*world* w0]
      (let [src (p/source w0 0) roots (p-graph kind src) last (volatile! nil)
            _ (doseq [r roots] (p/observe! w0 r #(vreset! last %) #(throw %)))
            ;; forked?: measure in a fresh fork, so every first touch copies
            w (if forked? (p/fork w0) w0)
            i (volatile! 0)]
        (assoc (measure #(p/set-source! w src (vswap! i inc)) n) :last @last)))))

(defn fork-cost
  "ns to fork a world of `size` signals+computations, and the cost of the
   first update after the fork vs a steady one."
  [size]
  (let [w (p/world)]
    (binding [p/*world* w]
      (let [src (p/source w 0)
            roots (mapv (fn [_] (p/cmp (iv/get-new (p/track src)))) (range size))
            _ (doseq [r roots] (p/observe! w r (fn [_]) #(throw %)))
            t0 (System/nanoTime)
            ws (vec (repeatedly 1000 #(p/fork w)))
            fork-ns (long (/ (- (System/nanoTime) t0) 1000))
            c (first ws)
            t1 (System/nanoTime)
            _ (p/set-source! c src 1)
            first-ns (- (System/nanoTime) t1)
            t2 (System/nanoTime)
            _ (dotimes [i 100] (p/set-source! c src (+ 2 i)))
            steady-ns (long (/ (- (System/nanoTime) t2) 100))]
        {:size size :fork-ns fork-ns :first-update-ns first-ns :steady-update-ns steady-ns
         :parent-unchanged (= 0 (p/value w src))}))))

(defn report [n]
  (vec (for [k [:fanout :chain :diamond :switch :child]]
         (let [a (run-s k n) b (run-p k n) c (run-p k n :forked? true)]
           {:kind k :ptr (:ns a) :paged (:ns b) :x (/ (Math/round (* 100.0 (/ (:ns b) (max 1 (:ns a))))) 100.0)
            :paged-forked (:ns c) :ptr-bytes (:bytes a) :paged-bytes (:bytes b) :same (= (:last a) (:last b) (:last c))}))))

(defn- f-graph [kind src]
  (let [leaf (fn [] (fw/cmp (iv/get-new (fw/track src))))]
    (case kind
      :fanout (mapv (fn [_] (leaf)) (range 100))
      :chain [(reduce (fn [prev _] (fw/cmp (inc (fw/await prev)))) (leaf) (range 50))]
      :diamond (let [b (fw/cmp (* 2 (iv/get-new (fw/track src)))) c (fw/cmp (* 3 (iv/get-new (fw/track src))))
                     d (fw/cmp (+ (fw/await b) (fw/await c))) e (fw/cmp (* 2 (fw/await d))) f (fw/cmp (* 3 (fw/await d)))]
                 [(fw/cmp (+ (fw/await e) (fw/await f)))])
      :switch (let [l (fw/cmp 10) r (fw/cmp 20)]
                [(fw/cmp (let [n (iv/get-new (fw/track src))] (+ n (fw/await (if (even? n) l r)))))])
      :child [(fw/cmp (let [n (iv/get-new (fw/track src)) c (fw/cmp (* 2 n))] (fw/await c)))])))

(defn run-f [kind n]
  (let [w (fw/world)]
    (binding [fw/*world* w]
      (let [src (fw/source w 0) roots (f-graph kind src) last (volatile! nil)
            _ (doseq [r roots] (fw/observe! r #(vreset! last %) #(throw %)))
            i (volatile! 0)]
        (assoc (measure #(fw/set-source! src (vswap! i inc)) n) :last @last)))))

(defn report-fwd [n]
  (vec (for [k [:fanout :chain :diamond :switch :child]]
         (let [a (run-s k n) b (run-f k n)]
           {:kind k :x (/ (Math/round (* 100.0 (/ (:ns b) (max 1 (:ns a))))) 100.0) :same (= (:last a) (:last b))}))))
