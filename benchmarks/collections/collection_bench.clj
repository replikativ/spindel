(ns collection-bench
  (:refer-clojure :exclude [await])
  (:require [clojure.data.json :as json]
            [clojure.java.io :as io]
            [org.replikativ.foerster.core :as infer]
            [org.replikativ.foerster.dist :as dist]
            [org.replikativ.foerster.effects :as effects]
            [org.replikativ.foerster.measure :as measure]
            [org.replikativ.spindel.core :as sp]
            [org.replikativ.spindel.atom :as sa]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.executor :as executor]
            [org.replikativ.spindel.spin.cps :as cps]
            [is.simm.partial-cps.async :as async :refer [await]])
  (:import [com.sun.management ThreadMXBean]
           [java.lang.management ManagementFactory]
           [java.util.concurrent Executors ExecutorService ThreadFactory TimeUnit]))

(def ^ThreadMXBean allocation-bean (ManagementFactory/getThreadMXBean))
(def compilation-bean (ManagementFactory/getCompilationMXBean))
(def sink (volatile! nil))

(defn counters []
  {:thread-bytes (.getCurrentThreadAllocatedBytes allocation-bean)
   :total-bytes (.getTotalThreadAllocatedBytes allocation-bean)
   :jit-ms (.getTotalCompilationTime compilation-bean)})

(defn measured [f]
  (let [before (counters)
        start (System/nanoTime)
        value (f)
        elapsed (- (System/nanoTime) start)
        after (counters)]
    {:value value :ns elapsed
     :thread-bytes (- (:thread-bytes after) (:thread-bytes before))
     :total-bytes (- (:total-bytes after) (:total-bytes before))
     :jit-ms (- (:jit-ms after) (:jit-ms before))}))

(def forms
  {:mapv '(mapv (fn [x] (await (step x))) xs)
   :loop-vector '(loop [s (seq xs) out []]
                   (if s
                     (let [v (await (step (first s)))] (recur (next s) (conj out v)))
                     out))
   :doseq '(let [total (volatile! 0)]
             (doseq [x xs] (vswap! total + (long (await (step x)))))
             @total)
   :loop-sum '(loop [s (seq xs) total 0]
                (if s
                  (let [v (await (step (first s)))] (recur (next s) (+ total v)))
                  total))
   :reduce '(reduce (fn [total x] (+ total (await (step x)))) 0 xs)
   :pure-mapv '(mapv (fn [x] (unchecked-inc (long x))) xs)})

(defn lower [body]
  (binding [*ns* (the-ns 'collection-bench)]
    (cps/build-cps-fn (list body) async/breakpoints {'xs true 'step true})))

(defn compile-lowered [lowered]
  (binding [*ns* (the-ns 'collection-bench)]
    (eval (list 'fn ['xs 'step] lowered))))

(defn compile-task [body] (compile-lowered (lower body)))

(defn native-mapv [xs] (mapv (fn [x] (unchecked-inc (long x))) xs))
(defn native-persistent [xs]
  (loop [s (seq xs) out []]
    (if s (recur (next s) (conj out (unchecked-inc (long (first s))))) out)))
(defn native-doseq [xs]
  (let [total (volatile! 0)]
    (doseq [x xs] (vswap! total + (unchecked-inc (long x)))) @total))
(defn native-reduce [xs] (reduce (fn [total x] (+ total (unchecked-inc (long x)))) 0 xs))

(defn immediate-step [x] (fn [resolve _reject] (resolve (unchecked-inc (long x)))))

(defn synchronous-runner [factory xs]
  (let [out (volatile! ::not-delivered)
        yes #(vreset! out %)
        no (fn [error] (throw error))]
    (fn []
      (vreset! out ::not-delivered)
      ((factory xs immediate-step) yes no)
      (when (= ::not-delivered @out) (throw (ex-info "Unexpected suspension" {})))
      @out)))

(defn handoff-executor []
  (Executors/newSingleThreadExecutor
   (reify ThreadFactory
     (newThread [_ f]
       (doto (Thread. f "collection-bench-handoff") (.setDaemon true))))))

(defn deferred-runner [factory xs ^ExecutorService service]
  (let [step (fn [x]
               (fn [resolve reject]
                 (.execute service
                           ^Runnable
                           (fn []
                             (try
                               (async/with-trampoline (resolve (unchecked-inc (long x))))
                               (catch Throwable e (reject e)))))))]
    (fn []
      (let [result (promise)]
        ((factory xs step) #(deliver result [:ok %]) #(deliver result [:error %]))
        (let [[status value] (deref result 30000 [:timeout nil])]
          (case status
            :ok value
            :error (throw value)
            (throw (ex-info "Deferred task timed out" {}))))))))

(defn block [f iterations]
  (dissoc
   (measured (fn [] (dotimes [_ iterations] (vreset! sink (f)))))
   :value))

(defn median [xs] (nth (vec (sort xs)) (quot (count xs) 2)))

(defn benchmark [f {:keys [target-ms samples warm-max] :or {target-ms 30 samples 7 warm-max 40}}]
  (let [warm (loop [out [] iterations 1]
               (let [row (assoc (block f iterations) :iterations iterations)
                     out (conj out row)
                     tail (map #(/ (:ns %) (double (:iterations %))) (take-last 4 out))
                     next-iterations (max 1 (min 1000000 (* 8 iterations)
                                                (long (/ (* iterations target-ms 1.0e6)
                                                         (max 1 (:ns row))))))
                     stable? (and (>= (count out) 8)
                                  (> (reduce + (map :ns out)) 5.0e8)
                                  (zero? (reduce + (map :jit-ms (take-last 4 out))))
                                  (< (/ (- (apply max tail) (apply min tail))
                                        (double (median tail))) 0.10))]
                 (if (or stable? (>= (count out) warm-max))
                   {:blocks out :stable? stable? :iterations next-iterations}
                   (recur out next-iterations))))
        repetitions (:iterations warm)
        rows (mapv (fn [_] (block f repetitions)) (range samples))]
    {:repetitions repetitions :warm-stable? (:stable? warm)
     :warm-ms (/ (reduce + (map :ns (:blocks warm))) 1.0e6)
     :warm-blocks (mapv #(select-keys % [:iterations :ns :jit-ms]) (:blocks warm))
     :ns-per-op (mapv #(/ (:ns %) (double repetitions)) rows)
     :thread-bytes-per-op (mapv #(/ (:thread-bytes %) (double repetitions)) rows)
     :total-bytes-per-op (mapv #(/ (:total-bytes %) (double repetitions)) rows)
     :jit-ms (mapv :jit-ms rows)}))

(def bytecode-agent
  (try (Class/forName "bench.BytecodeAgent")
       (catch ClassNotFoundException _ nil)))

(defn agent-call [method]
  (when bytecode-agent
    (.invoke (.getMethod ^Class bytecode-agent method (make-array Class 0))
             nil (object-array 0))))

(defn counted-compile [lowered]
  (agent-call "reset")
  (let [row (dissoc (measured #(compile-lowered lowered)) :value)
        counts (some-> (agent-call "snapshot") vec)]
    (merge row (when counts {:classes (nth counts 0) :class-bytes (nth counts 1)
                            :max-class-filename (nth counts 2)}))))

(defn compile-case [kind n]
  (let [body
        (case kind
          :straight-await
          (let [vars (mapv #(symbol (str "v" %)) (range n))]
            (list 'let (vec (mapcat (fn [v i] [v (list 'await (list 'step i))]) vars (range n))) (last vars)))
          :nested-mapv
          (reduce (fn [body depth]
                    (let [x (symbol (str "x" depth))]
                      (list 'mapv (list 'fn [x] body) 'xs)))
                  '(await (step 1)) (range n))
          :doseq (:doseq forms)
          :mapv (:mapv forms))
        _ (dotimes [_ 2] (compile-task body))
        rows (mapv (fn [_]
                     (let [lowered (measured #(lower body))
                           compiled (counted-compile (:value lowered))]
                       {:lower (dissoc lowered :value)
                        :compile compiled})) (range 5))
        lowered (lower body)]
    {:kind kind :size n :rows rows
     :lowered-nodes (count (tree-seq coll? seq lowered))
     :classes (some->> rows (map #(get-in % [:compile :classes])) (remove nil?) seq median)
     :class-bytes (some->> rows (map #(get-in % [:compile :class-bytes])) (remove nil?) seq median)
     :max-class-filename (some->> rows (map #(get-in % [:compile :max-class-filename])) (remove nil?) seq (apply max))}))

(defn runtime-case [kind n]
  (let [xs (vec (range n))
        f (case kind
            :native-mapv #(native-mapv xs)
            :native-persistent #(native-persistent xs)
            :native-doseq #(native-doseq xs)
            :native-reduce #(native-reduce xs)
            (synchronous-runner (compile-task (get forms kind)) xs))
        expected (if (#{:native-mapv :native-persistent :mapv :loop-vector :pure-mapv} kind)
                   (mapv inc xs) (reduce + (map inc xs)))]
    (assert (= expected (f)) (str "Incorrect synchronous result: " kind))
    (merge {:kind kind :n n} (benchmark f {}))))

(defn deferred-case [kind n service]
  (let [f (deferred-runner (compile-task (get forms kind)) (vec (range n)) service)
        expected (if (#{:mapv :loop-vector} kind)
                   (mapv inc (range n)) (reduce + (map inc (range n))))]
    (assert (= expected (f)) (str "Incorrect deferred result: " kind))
    (merge {:kind kind :n n} (benchmark f {:target-ms 20 :warm-max 40}))))

(defn inference-model [kind]
  (let [step '(let [x (effects/sample (dist/flip 0.5) :id [:x i])]
                (swap! state conj x)
                (effects/observe (dist/flip (if x 0.8 0.2)) true :id [:y i])
                x)
        body (case kind
               :mapv (list 'let ['values (list 'mapv (list 'fn ['i] step) '(range k))]
                           '{:values values :state @state})
               :doseq (list 'do (list 'doseq ['i '(range k)] step) '{:values @state :state @state})
               :loop-vector
               (list 'loop ['i 0 'values []]
                     (list 'if '(< i k)
                           (list 'let ['v step] '(recur (inc i) (conj values v)))
                           '{:values values :state @state})))]
    (binding [*ns* (the-ns 'collection-bench)]
      (eval (list 'fn ['state 'k] (list 'cps/spin body))))))

(def inference-models (atom {}))

(defn cached-inference-model [kind]
  (or (get @inference-models kind)
      (let [model (inference-model kind)]
        (swap! inference-models assoc kind model)
        model)))

(defn inference-runner [model particles]
  (fn []
    (let [world (sp/create-execution-context :executor (executor/synchronous-executor))]
      (try
        (sp/with-context world
          (let [state (sa/atom [])
                result @(infer/smc-infer (model state 4) particles
                                        {:world-policy :fork :seed 29 :resample-threshold 1.01})
                values (mapv measure/get-value (measure/get-contexts result))]
            (assert (empty? @state) "Inference modified the caller")
            (assert (= 4 (count (:history result))))
            (assert (every? :resampled? (:history result)))
            (assert (every? #(and (= 4 (count (:values %))) (= (:values %) (:state %))) values))
            ;; Consume the result while avoiding retention of discarded worlds.
            (reduce + (map #(count (filter true? (:values %))) values))))
        (finally (context/close-context! world))))))

(defn inference-case [kind particles]
  (let [f (inference-runner (cached-inference-model kind) particles)]
    (f)
    (merge {:kind kind :particles particles :observations 4 :executor :inline}
           (benchmark f {:target-ms 50 :warm-max 40 :samples 5}))))

(defn environment []
  {:java (System/getProperty "java.version")
   :vm (System/getProperty "java.vm.name")
   :clojure (clojure-version)
   :heap-bytes (.maxMemory (Runtime/getRuntime))
   :processors (.availableProcessors (Runtime/getRuntime))
   :jvm-args (vec (.getInputArguments (ManagementFactory/getRuntimeMXBean)))
   :sources (into {} (for [path ["org/replikativ/spindel/spin/cps.cljc"
                                 "is/simm/partial_cps/ioc.clj"
                                 "org/replikativ/foerster/core.cljc"]]
                      [path (str (io/resource path))]))
   :allocation-supported? (.isThreadAllocatedMemorySupported allocation-bean)})

(defn run-worker [mode run-id output quick?]
  (assert bytecode-agent "Start measured workers with the bytecode agent")
  (.setThreadAllocatedMemoryEnabled allocation-bean true)
  (let [results (atom {:mode mode :run-id run-id :environment (environment)
                       :compile [] :runtime [] :deferred [] :inference []})
        record! (fn [section value]
                  (swap! results update section conj value)
                  (spit output (json/write-str @results))
                  (println (name section) (select-keys value [:kind :n :size :particles]))
                  (flush))]
    (doseq [[kind n] (if quick?
                      [[:straight-await 4] [:doseq 1] [:mapv 1]]
                      [[:straight-await 8] [:straight-await 32] [:straight-await 96]
                       [:nested-mapv 2] [:nested-mapv 4] [:nested-mapv 8]
                       [:doseq 1] [:mapv 1]])]
      (record! :compile (compile-case kind n)))
    (doseq [n (if quick? [16] [16 1024])
            kind [:native-mapv :native-persistent :native-doseq :native-reduce
                  :mapv :loop-vector :doseq :loop-sum :reduce :pure-mapv]]
      (record! :runtime (runtime-case kind n)))
    (let [service (handoff-executor)]
      (try
        (doseq [n (if quick? [16] [16 256]) kind [:mapv :loop-vector :doseq :loop-sum]]
          (record! :deferred (deferred-case kind n service)))
        (finally (.shutdownNow service) (.awaitTermination service 5 TimeUnit/SECONDS))))
    ;; Warm shared inference machinery and reuse compiled model factories. This
    ;; is separate from measured per-case warm-up, whose stability is recorded.
    (let [start (System/nanoTime)]
      (doseq [kind [:mapv :doseq :loop-vector]]
        (let [f (inference-runner (cached-inference-model kind) (if quick? 16 64))]
          (dotimes [_ (if quick? 4 32)] (f))))
      (swap! results assoc :inference-prewarm-ms (/ (- (System/nanoTime) start) 1.0e6)))
    (doseq [n (if quick? [16] [64 256]) kind [:mapv :doseq :loop-vector]]
      (record! :inference (inference-case kind n)))
    @results))

(defn -main [mode run-id output & [quick]]
  (try
    (run-worker mode run-id output (= quick "quick"))
    (shutdown-agents)
    (System/exit 0)
    (catch Throwable e
      (.printStackTrace e)
      (shutdown-agents)
      (System/exit 1))))
