(ns org.replikativ.spindel.engine-heap-probe
  "Node retained-heap probe. Compile with advanced optimization and run with
   node --expose-gc. SPINDEL_HEAP_BURSTS sets comma-separated burst sizes.
   This reports retained heap after collection, not total allocated bytes."
  (:require [clojure.string :as str]
            [org.replikativ.spindel.engine.impl.owned :as c :include-macros true]))

(defn- pause [] (js/Promise. (fn [resolve _] (js/setImmediate resolve))))

(defn- gc-turn []
  (.then (pause) (fn [_] ((aget js/globalThis "gc")) (pause))))

(defn- heap-used []
  ;; Node's result keys are an external ABI; Closure must not rename them.
  (let [bytes (aget (.memoryUsage js/process) "heapUsed")]
    (when-not (and (number? bytes) (js/Number.isFinite bytes))
      (throw (js/Error. "Invalid Node heap measurement")))
    bytes))

(defn- counts [rt]
  (let [state (c/snapshot rt)]
    (assoc (c/storage-stats rt)
           :entities (count (:entities state))
           :generation-history (count (get-in state [:global :generation-clock])))))

(defn- burst! [rt start n notify?]
  (dotimes [i n]
    (let [handle (c/cspin rt [:ephemeral (+ start i)] 42)]
      (c/observe! rt handle (fn [_]) #(throw %))
      (when notify? (c/notify-unreachable! rt handle)))))

(defn- wait-for [predicate remaining]
  (.then (gc-turn)
         (fn [_]
           (if (predicate) true
               (if (pos? remaining) (wait-for predicate (dec remaining)) false)))))

(defn- native-callback-world [retained complete?]
  (let [rt (c/runtime)
        start (fn [succeed! fail!]
                (swap! retained into [succeed! fail!])
                (fn []))
        handle (c/cspin rt :native (c/await-host start))]
    (c/observe! rt handle (fn [_]) (fn [_]))
    (if complete? ((nth @retained (- (count @retained) 2)) :done)
        (c/cancel-spin! rt handle))
    (js/WeakRef. rt)))

(defn- probe-callback-retention []
  (let [retained (atom [])
        worlds [(native-callback-world retained true) (native-callback-world retained false)]]
    (.then (wait-for #(and (= 4 (count @retained))
                           (every? (fn [weak] (nil? (.deref weak))) worlds)) 20)
           (fn [collected?]
             ;; Producers deliberately keep and call all stale capabilities.
             (doseq [callback @retained] (callback :late))
             (prn {:stage :stale-native-callbacks :callbacks (count @retained) :collected? collected?})
             (when-not collected? (throw (js/Error. "Stale callback retains its world")))))))

(defn -main [& _]
  (when-not (aget js/globalThis "gc")
    (throw (js/Error. "Run with node --expose-gc")))
  (let [holder (volatile! (c/runtime)) weak (js/WeakRef. @holder)
        sizes (mapv #(js/parseInt % 10)
                    (str/split (or (aget (.-env js/process) "SPINDEL_HEAP_BURSTS")
                                   "10000,10000,10000") #","))]
    (burst! @holder 0 1000 true)
    (-> (gc-turn)
        (.then (fn [_]
                 (let [base (heap-used)]
                   (reduce
                    (fn [previous n]
                      (.then previous
                             (fn [total]
                               (burst! @holder total n true)
                               (.then (gc-turn)
                                      (fn [_]
                                        (let [state (counts @holder)]
                                          (when-not (and (zero? (:entities state))
                                                         (zero? (:generation-history state))
                                                         (zero? (:pooled-references state)))
                                            (throw (ex-info "Reclamation left engine roots" state)))
                                          (prn (assoc state :stage :churn :updates (+ total n)
                                                      :heap-after-gc (heap-used)
                                                      :heap-growth (- (heap-used) base))))
                                        (+ total n))))))
                    (js/Promise.resolve 1000) sizes))))
        (.then (fn [total]
                 (burst! @holder total 100 false)
                 (.then (wait-for #(zero? (:entities (counts @holder))) 20)
                        (fn [cleaned?]
                          (prn (assoc (counts @holder) :stage :host-finalization :cleaned? cleaned?))
                          (when-not cleaned? (throw (js/Error. "Host finalization did not drain")))))))
        (.then (fn [_]
                 (let [ticket (c/ticket :waiting)
                       handle (c/cspin @holder :wanted (c/park ticket))]
                   (c/observe! @holder handle (fn [_]) #(throw %))
                   (c/notify-unreachable! @holder handle)
                   (prn (assoc (counts @holder) :stage :wanted-work))
                   (when-not (= [:parked] (mapv :status (vals (:runs (c/snapshot @holder)))))
                     (throw (js/Error. "Host collection cancelled wanted work")))
                   (vreset! holder nil))))
        (.then (fn [_] (wait-for #(nil? (.deref weak)) 20)))
        (.then (fn [collected?]
                 (prn {:stage :world-collection :collected? collected?})
                 (when-not collected? (throw (js/Error. "Runtime remains strongly reachable")))))
        (.then (fn [_] (probe-callback-retention)))
        (.catch (fn [error] (js/console.error error) (set! (.-exitCode js/process) 1))))))

(set! *main-cli-fn* -main)
