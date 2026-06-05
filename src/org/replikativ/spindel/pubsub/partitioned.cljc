(ns org.replikativ.spindel.pubsub.partitioned
  "Partitioned fan-out: N partitions with hash-based routing.

   Each partition is a mult with its own buffer config.
   A partition-fn extracts the routing key from each item.
   Items are routed to partition (bit-and (hash key) (dec n)).

   Use cases:
   - Streaming topologies with word→partition routing
   - Parallel processing with affinity-based routing
   - Replacing manual mailbox-per-task patterns

   Backpressure: When a partition's consumer is slow and its fixed-buffer
   fills up, the pump spin blocks. This backs up the entire source (same
   as Rama). Use dropping-buffer or sliding-buffer if independent partition
   throughput is needed."
  (:refer-clojure :exclude [await])
  (:require [is.simm.partial-cps.sequence :refer [PAsyncSeq anext]]
            [org.replikativ.spindel.pubsub.mult :as mult]
            [org.replikativ.spindel.pubsub.buffer :as buf]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.engine.core :as ec]
            [replikativ.logging :as log]
            #?(:clj [org.replikativ.spindel.spin.cps :refer [spin]])
            [org.replikativ.spindel.effects.await :refer [await]])
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]])))

;; =============================================================================
;; Internal: per-partition push-based async seq
;; =============================================================================

(defn- make-promise
  "Simple promise for coordination (same pattern as mult.cljc — see that
   ns for the cross-ctx-delivery rationale behind capturing ctx at
   await-spin construction and re-binding it around the watcher
   invocation)."
  []
  (let [state (atom {:delivered? false :value nil :watchers []})]
    {:state state
     :deliver! (fn [value]
                 (loop []
                   (let [s @state]
                     (if (:delivered? s)
                       value
                       (if (compare-and-set! state s {:delivered? true :value value :watchers []})
                         (do (doseq [w (:watchers s)]
                               (w value))
                             value)
                         (recur))))))
     :await-spin (fn []
                   (let [captured-ctx (try (ec/current-execution-context)
                                           (catch #?(:clj Throwable :cljs :default) _ nil))]
                     (spin-core/make-spin
                      (fn [resolve _reject]
                        (let [wrapped (if captured-ctx
                                        (fn [v]
                                          (binding [ec/*execution-context* captured-ctx]
                                            (resolve v)))
                                        resolve)]
                          (loop []
                            (let [s @state]
                              (if (:delivered? s)
                                (wrapped (:value s))
                                (when-not (compare-and-set! state s (update s :watchers conj wrapped))
                                  (recur))))))
                        spin-core/incomplete))))}))

(defn- deliver-promise! [p value]
  ((:deliver! p) value))

(defn- promise-spin [p]
  ((:await-spin p)))

(defrecord PartitionSource
           [;; atom of vector of items
            items-atom
     ;; atom of promise — signaled when items available
            waiter-atom
     ;; atom of boolean — closed?
            closed-atom])

(defn- create-partition-source []
  (->PartitionSource (atom [])
                     (atom (make-promise))
                     (atom false)))

(defn- push-to-source!
  "Push an item to a partition source. Signals waiting consumers."
  [^PartitionSource psrc item]
  (swap! (:items-atom psrc) conj item)
  (let [old-promise @(:waiter-atom psrc)]
    (reset! (:waiter-atom psrc) (make-promise))
    (deliver-promise! old-promise :item-available)))

(defn- close-source!
  "Close a partition source. Signals waiting consumers."
  [^PartitionSource psrc]
  (reset! (:closed-atom psrc) true)
  (let [old-promise @(:waiter-atom psrc)]
    (reset! (:waiter-atom psrc) (make-promise))
    (deliver-promise! old-promise :closed)))

(deftype PartitionSeq [psrc]
  PAsyncSeq
  (anext [this]
    (spin
     (loop []
       (cond
          ;; Items available
         (seq @(:items-atom psrc))
         (let [item (first @(:items-atom psrc))]
           (swap! (:items-atom psrc) (comp vec rest))
           [item this])

          ;; Closed with no items
         @(:closed-atom psrc)
         nil

          ;; Wait for notification.
          ;;
          ;; Check-act-recheck: capture the waiter promise BEFORE re-checking
          ;; items/closed. If a producer raced with the cond above and pushed
          ;; an item between our items-check and our waiter-atom read, the
          ;; producer would deliver the OLD promise (the one currently in
          ;; waiter-atom) and install a NEW one. Without the recheck we'd
          ;; capture the NEW (undelivered) promise after the producer
          ;; installed it, await it, and hang forever even though items is
          ;; non-empty.
          ;;
          ;; By capturing waiter first and re-checking items/closed before
          ;; awaiting, we either notice the new state and recur, or await
          ;; the same waiter the producer would deliver to — both safe.
         :else
         (let [waiter @(:waiter-atom psrc)]
           (if (or (seq @(:items-atom psrc))
                   @(:closed-atom psrc))
             (recur)
             (do (await (promise-spin waiter))
                 (recur)))))))))

;; =============================================================================
;; Partitioned Record
;; =============================================================================

(defrecord Partitioned
           [;; Number of partitions (power of 2)
            n
     ;; Vector of Mult instances, one per partition
            mults
     ;; Vector of PartitionSource, one per partition (internal sources for mults)
            sources
     ;; Function to extract routing key from item
            partition-fn
     ;; Pump spin (reads source, routes to partitions)
            pump-atom
     ;; Is the partitioned closed?
            closed-atom])

;; =============================================================================
;; Public API
;; =============================================================================

(defn partitioned
  "Create a partitioned fan-out from a source PAsyncSeq.

   n            — number of partitions (must be power of 2)
   source       — PAsyncSeq to consume
   partition-fn — (fn [item] routing-key), key is hashed for partition assignment
   :buf-fn      — (fn [partition-idx] buffer-or-nil) for per-partition buffer config
                  Defaults to (fixed-buffer 64).

   Returns a Partitioned record. The pump starts immediately."
  [n source partition-fn & {:keys [buf-fn]
                            :or {buf-fn (fn [_] (buf/fixed-buffer 64))}}]
  (assert (and (pos? n) (zero? (bit-and n (dec n))))
          "Number of partitions must be a power of 2")
  (let [mask (dec n)
        ;; Create N partition sources and mults
        sources (vec (repeatedly n create-partition-source))
        partition-seqs (mapv #(->PartitionSeq %) sources)
        mults (mapv mult/mult partition-seqs)
        closed-atom (atom false)
        pump-atom (atom nil)
        partitioned (->Partitioned n mults sources partition-fn pump-atom closed-atom)

        ;; Create pump spin that reads source and routes items
        pump (spin
              (loop [src source]
                (if-let [result (await (anext src))]
                  (let [[item rest-seq] result
                        key (partition-fn item)
                        idx (bit-and (hash key) mask)]
                    (push-to-source! (nth sources idx) item)
                    (recur rest-seq))
                   ;; Source exhausted — close all partition sources
                  (do
                    (reset! closed-atom true)
                    (doseq [psrc sources]
                      (close-source! psrc))))))]
    (reset! pump-atom pump)
    ;; Start pump via event system
    (let [ctx (ec/current-execution-context)]
      (ec/enqueue-event! {:type :spin-execution
                          :id (spin-core/spin-id pump)
                          :spin pump
                          :execution-context ctx
                          :resolve-fn (fn [_] nil)
                          :reject-fn (fn [e]
                                       (log/error :partitioned/pump-error {:error e}))}))
    partitioned))

(defn tap-partition
  "Subscribe to a specific partition. Returns a TapSeq (PAsyncSeq).

   partition-idx — which partition to consume (0-indexed)
   buffer        — override buffer for this tap (default: fixed-buffer 64)"
  ([partitioned partition-idx]
   (tap-partition partitioned partition-idx (buf/fixed-buffer 64)))
  ([partitioned partition-idx buffer]
   (assert (< partition-idx (:n partitioned))
           (str "Partition index " partition-idx " out of range [0," (:n partitioned) ")"))
   (mult/tap (nth (:mults partitioned) partition-idx) buffer true)))

(defn tap-all
  "Subscribe to all partitions. Returns a vector of TapSeqs."
  ([partitioned]
   (tap-all partitioned (buf/fixed-buffer 64)))
  ([partitioned buffer]
   (mapv #(mult/tap % buffer true) (:mults partitioned))))

(defn partition-post!
  "Post an item directly to a specific partition.
   Useful for the partition-by pattern where a consumer routes to another partition.
   Returns nil."
  [partitioned partition-idx item]
  (assert (< partition-idx (:n partitioned))
          (str "Partition index " partition-idx " out of range [0," (:n partitioned) ")"))
  (push-to-source! (nth (:sources partitioned) partition-idx) item)
  nil)

(defn close!
  "Close the partitioned fan-out. Closes all partition sources,
   which cascades to closing all taps."
  [partitioned]
  (reset! (:closed-atom partitioned) true)
  (doseq [psrc (:sources partitioned)]
    (close-source! psrc)))

(defn closed?
  "Returns true if the partitioned has been closed."
  [partitioned]
  @(:closed-atom partitioned))
