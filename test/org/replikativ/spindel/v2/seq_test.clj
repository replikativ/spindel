(ns org.replikativ.spindel.v2.seq-test
  "C0 async sequences: positions are values, elements are realized at most
   once per world and shared by every reader (.internal/c-async-seq-design.md)."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin task track await await-any aseq]]
            [org.replikativ.spindel.v2.rows :as rw]
            [org.replikativ.spindel.v2.verify :as verify]
            [org.replikativ.spindel.incremental.interval :as iv]))

(def ^:dynamic *divergences* nil)

(defn- vworld []
  (v2/world {:verify? true :hook (verify/checking-hook *divergences*)}))

(defmacro checked [& body]
  `(binding [*divergences* (atom [])]
     ~@body
     (is (empty? @*divergences*) (str "Rule R divergences: " (vec (take 3 @*divergences*))))))

(defn- wait-until [f]
  (loop [n 0] (cond (f) true (> n 500) false :else (do (Thread/sleep 5) (recur (inc n))))))

(defn- drain
  "A task collecting every element from position `p` (and the error, if the
   sequence fails)."
  [p]
  (task (loop [p p acc []]
          (let [step (try (await p) (catch Exception e [::error e]))]
            (cond (nil? step) acc
                  (= ::error (first step)) (conj acc [:error (ex-message (second step))])
                  :else (recur (second step) (conj acc (first step))))))))

(defn- census [w]
  (verify/gc-settle! w)
  (v2/call-in! w #(frequencies (map (fn [r] (aget ^objects r rw/TYPE)) (vals (aget ^objects w rw/W-REG))))))

(deftest a-pull-sequence-is-a-value
  (checked
   (let [w (vworld) calls (atom 0)]
     (binding [v2/*world* w]
       (let [nats (aseq [n 0] (swap! calls inc) (when (< n 4) [n (inc n)]))]
         (is (= [0 1 2 3] (v2/value (drain nats) 2000 ::timeout)))
         (is (= [0 1 2 3] (v2/value (drain nats) 2000 ::timeout)) "reading never consumes")
         (is (= 5 @calls) "each element (and the end) is realized once")
         (is (v2/ready? nats))
         (is (= [(first (v2/position-id nats)) 0] (v2/position-id nats)))))
     (v2/release-world! w))))

(deftest concurrent-readers-share-one-realization
  (checked
   (let [w (vworld) calls (atom 0)]
     (binding [v2/*world* w]
       (let [xs (aseq [n 0] (swap! calls inc) (v2/sleep 20) (when (< n 3) [(* 10 n) (inc n)]))
             a (drain xs) b (drain xs)]
         (is (= [0 10 20] (v2/value a 2000 ::timeout)))
         (is (= [0 10 20] (v2/value b 2000 ::timeout)))
         (is (= 4 @calls))))
     (v2/release-world! w))))

(deftest errors-are-memoized-per-position
  (checked
   (let [w (vworld) calls (atom 0)]
     (binding [v2/*world* w]
       (let [xs (aseq [n 0] (swap! calls inc) (if (= n 2) (throw (ex-info "boom" {})) [n (inc n)]))]
         (is (= [0 1 [:error "boom"]] (v2/value (drain xs) 2000 ::timeout)))
         (is (= [0 1 [:error "boom"]] (v2/value (drain xs) 2000 ::timeout)))
         (is (= 3 @calls) "the failing step ran once")
         (is (thrown-with-msg? Exception #"returns \[value next-state\]"
                               (v2/value (aseq [_ 0] :not-a-step) 2000 ::timeout)))))
     (v2/release-world! w))))

(deftest a-propagated-cancellation-is-memoized
  (checked
   (let [w (vworld) calls (atom 0)]
     (binding [v2/*world* w]
       (let [victim (task (v2/sleep 5000))
             _ (v2/cancel-task! victim)
             xs (aseq [n 0] (swap! calls inc) (await victim) [n (inc n)])]
         (is (thrown? Exception (v2/value xs 2000 ::timeout)) "the realizer's body failed: readers get it")
         (is (v2/ready? xs))
         (is (thrown? Exception (v2/value xs 2000 ::timeout)))
         (is (= 1 @calls))))
     (v2/release-world! w))))

(deftest a-cancelled-reader-does-not-cancel-the-realization
  (checked
   (let [w (vworld) calls (atom 0) done (atom 0) gate (promise)]
     (binding [v2/*world* w]
       (let [xs (aseq [n 0] (swap! calls inc) (v2/offload #(deref gate 2000 :late)) (swap! done inc) [n (inc n)])
             reader (task (await xs))]
         (is (wait-until #(= 1 @calls)))
         (v2/cancel-task! reader)
         (deliver gate :go)
         (is (wait-until #(= 1 @done)) "the realizer finished without its reader")
         (is (= 0 (first (v2/value xs 2000 ::timeout))))
         (is (= 1 @calls))))
     (v2/release-world! w))))

(deftest await-any-over-positions-and-deferreds
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [s (v2/stream)
             d (v2/deferred)
             t (task (let [[v _] (await-any [(v2/position s) d])] v))]
         (v2/append! s :msg)
         (is (= :msg (v2/value t 2000 ::timeout)))
         (let [t2 (task (await-any [(v2/position s) d]))]
           (v2/deliver! d :done)
           (is (= :done (v2/value t2 2000 ::timeout))))))
     (v2/release-world! w))))

(deftest the-realizer-runs-with-the-creation-bindings
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [xs (binding [*print-length* 7] (aseq [n 0] (when (zero? n) [*print-length* 1])))]
         (is (= [7] (v2/value (drain xs) 2000 ::timeout)))))
     (v2/release-world! w))))

(deftest a-computation-reads-a-sequence
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [xs (aseq [n 0] (when (< n 3) [n (inc n)]))
             c (spin (let [[a nx] (await xs) [b _] (await nx)] (+ a b)))]
         (is (= 1 (v2/value c 2000 ::timeout)))))
     (v2/release-world! w))))

(deftest a-computation-adopts-its-sequence-with-the-same-captures
  (checked
   (let [w (vworld) calls (atom 0)]
     (binding [v2/*world* w]
       (let [a (v2/signal 1)
             k (v2/signal 10)
             c (spin (let [v (iv/get-new (track a))
                           step (iv/get-new (track k))
                           xs (aseq [n 0] (swap! calls inc) [(* step n) (inc n)])
                           [_ nx] (await xs)]
                       [v (first (await nx))]))
             ;; observed, so it stays live: an idle computation drops its creations
             unobserve (v2/observe! c (fn [_ _]))]
         (is (= [1 10] (v2/value c 2000 ::timeout)))
         (is (= 2 @calls))
         (v2/write! a 2)
         (is (= [2 10] (v2/value c 2000 ::timeout)))
         (is (= 2 @calls) "V4: re-entry with the same captures adopts the sequence and its elements")
         (v2/write! k 20)
         (is (= [2 20] (v2/value c 2000 ::timeout)))
         (is (= 4 @calls) "a changed capture is a new sequence")
         (unobserve)))
     (v2/release-world! w))))

;; ---------------------------------------------------------------------------
;; Streams

(deftest a-stream-reader-sees-appends-after-its-position
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [s (v2/stream)]
         (v2/append! s :before)
         (let [p (v2/position s)
               r1 (drain p) r2 (drain p)]
           (is (not (v2/ready? p)))
           (v2/append! s 1)
           (is (v2/ready? p))
           (v2/append! s 2)
           (v2/close! s)
           (v2/append! s :refused)
           (is (= [1 2] (v2/value r1 2000 ::timeout)))
           (is (= [1 2] (v2/value r2 2000 ::timeout)) "every reader sees every element")
           (is (= [1 2] (v2/value (drain p) 2000 ::timeout)) "a position is a value: read again")
           (is (thrown-with-msg? Exception #"read through its positions" (v2/value s 2000 ::timeout)))
           (let [got (promise)]
             (v2/observe! s (fn [v err?] (deliver got [err? (ex-message v)])))
             (is (= [true "a stream is read through its positions: (position s)"] (deref got 2000 ::timeout))
                 "observe! on a stream is refused like value")))))
     (v2/release-world! w))))

(deftest a-computation-stream-ends-when-it-leaves-the-basis
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [c (spin (let [s (v2/stream) p (v2/position s)] (v2/append! s 1) p))
             p (v2/value c 2000 ::timeout)]
         ;; the host read was the only demand: the computation goes idle and
         ;; drops its basis, so its stream ends (like its tasks are cancelled)
         (is (= [1] (v2/value (drain p) 2000 ::timeout)))))
     (v2/release-world! w))))

(deftest a-stream-closed-with-an-error
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [s (v2/stream) r (drain (v2/position s))]
         (v2/append! s 1)
         (v2/close! s (ex-info "broken" {}))
         (is (= [1 [:error "broken"]] (v2/value r 2000 ::timeout)))))
     (v2/release-world! w))))

(deftest a-task-stream-ends-when-the-task-retires
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [out (v2/deferred)
             producer (task (let [s (v2/stream)]
                              (v2/deliver! out (v2/position s))
                              (v2/append! s :a)
                              (v2/append! s :b)
                              :done))
             _ (is (= :done (v2/value producer 2000 ::timeout)))
             p (v2/value out 2000 ::timeout)]
         (is (= [:a :b] (v2/value (drain p) 2000 ::timeout)) "Z#18: the producer's retirement ends the stream")))
     (v2/release-world! w))))

(defn- weak-row [h] (java.lang.ref.WeakReference. (aget ^objects (.-cell ^org.replikativ.spindel.v2.core.Handle h) 0)))

(defn- collected? [^java.lang.ref.WeakReference r]
  (loop [n 0] (cond (nil? (.get r)) true (> n 50) false :else (do (System/gc) (Thread/sleep 10) (recur (inc n))))))

(deftest the-head-retains-the-prefix-a-position-only-the-suffix
  ;; production retention (no verify registry): rows live by their handles
  (let [w (v2/world) n 200]
    (binding [v2/*world* w]
      (let [s (v2/stream)
            head (atom (v2/position s))
            first-row (weak-row @head)
            reader (atom (drain @head))]   ; a task's body keeps what it captured while its handle is held
        (dotimes [i n] (v2/append! s i))
        (v2/close! s)
        (let [mid (atom (loop [p @head i 0] (if (= i 100) p (recur (second (v2/value p)) (inc i)))))
              mid-row (weak-row @mid)]
          (is (= (range n) (v2/value @reader 5000 ::timeout)))
          (reset! reader nil)
          (System/gc)
          (is (some? (.get ^java.lang.ref.WeakReference first-row)) "holding the head keeps the realized chain")
          (reset! head nil)
          (is (collected? first-row) "behind every position, links are collected")
          (is (some? (.get ^java.lang.ref.WeakReference mid-row)) "a held position keeps its suffix")
          (reset! mid nil)
          (is (collected? mid-row))
          (is (= 200 (second (v2/position-id (v2/position s)))) "the producer keeps only its tail"))))
    (v2/release-world! w)))

(deftest a-reader-walking-a-stream-frees-what-it-passed
  ;; production retention; the verify registry holds a link until its handle's
  ;; T19, so there a chain unwinds one link per collection
  (let [w (v2/world) n 300]
    (binding [v2/*world* w]
      (let [s (v2/stream)
            first-row (weak-row (v2/position s))
            seen (atom 0)
            reader (task (loop [p (v2/position s) sum 0]
                           (if-let [[v nx] (await p)] (do (swap! seen inc) (recur nx (+ sum v))) sum)))]
        (dotimes [i n] (v2/append! s i))
        (is (wait-until #(= n @seen)))
        (is (collected? first-row) "the parked reader holds only its position")
        (v2/close! s)
        (is (= (reduce + (range n)) (v2/value reader 5000 ::timeout)))))
    (v2/release-world! w)))

;; ---------------------------------------------------------------------------
;; Forks: at most once per world

(deftest a-fork-finishes-a-pure-realization-in-both-worlds
  (checked
   (let [w (vworld) started (atom 0) finished (atom 0)]
     (binding [v2/*world* w]
       (let [xs (aseq [n 0] (swap! started inc) (v2/sleep 50) (swap! finished inc) [n (inc n)])
             reader (task (first (await xs)))
             _ (is (wait-until #(= 1 @started)))
             child (v2/fork! w)]
         (is (= 0 (v2/value reader 2000 ::timeout)))
         (is (= 0 (v2/value (v2/in-world child reader) 2000 ::timeout)))
         (is (= 1 @started) "the realization started once, before the fork")
         (is (= 2 @finished) "its run finished in each world (a timer re-arms in a fork)")
         (v2/release-world! child)))
     (v2/release-world! w))))

(deftest a-fork-restarts-a-realization-cut-by-the-fork
  (checked
   (let [w (vworld) started (atom 0) gate (promise)]
     (binding [v2/*world* w]
       (let [xs (aseq [n 0] (swap! started inc) [(v2/offload #(deref gate 2000 :late)) (inc n)])
             reader (task (first (await xs)))
             _ (is (wait-until #(= 1 @started)))
             child (v2/fork! w)
             in-child (promise)]
         ;; the child's first turn activates its dormant resources (§8.1)
         (v2/value-async (v2/in-world child reader) (fn [v _] (deliver in-child v)))
         (is (wait-until #(= 2 @started)) "V2: ::forked is not memoized; the child's reader restarts it")
         (deliver gate :value)
         (is (= :value (v2/value reader 2000 ::timeout)))
         (is (= :value (deref in-child 2000 ::timeout)))
         (v2/release-world! child)))
     (v2/release-world! w))))

(deftest forked-streams-diverge
  (checked
   (let [w (vworld)]
     (binding [v2/*world* w]
       (let [s (v2/stream)
             p (v2/position s)
             r (drain p)
             child (v2/fork! w)
             cs (v2/in-world child s)]
         (v2/append! s :parent)
         (v2/append! cs :child)
         (v2/close! s)
         (v2/close! cs)
         (is (= [:parent] (v2/value r 2000 ::timeout)))
         (is (= [:child] (v2/value (v2/in-world child r) 2000 ::timeout)))
         (is (= [:child] (v2/value (binding [v2/*world* child] (drain p)) 2000 ::timeout))
             "the parent's position names the child's own element in the child")
         (v2/release-world! child)))
     (v2/release-world! w))))
