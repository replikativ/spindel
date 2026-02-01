(ns org.replikativ.spindel.sequence.combinators
  "Async sequence combinators and utilities"
  (:require [is.simm.partial-cps.sequence :refer [PAsyncSeq anext]]
            [org.replikativ.spindel.spin :as spin]
            [org.replikativ.spindel.sequence.core :as core]
            [org.replikativ.spindel.effects.reactive :refer [await]]
            [org.replikativ.spindel.log :as log]))

;; =============================================================================
;; Core Operations
;; =============================================================================

(defn first
  "Returns spin yielding first value of async sequence, or nil if empty.

  Example:
    (await (first pages))  ;=> first-page"
  [aseq]
  (spin/spin
    (when-let [[v _] (await (anext aseq))]
      v)))

(defn rest
  "Returns spin yielding rest of async sequence after first element.

  Returns nil if sequence is exhausted.

  Example:
    (await (rest pages))  ;=> rest-of-pages"
  [aseq]
  (spin/spin
    (when-let [[_ rest-seq] (await (anext aseq))]
      rest-seq)))

;; =============================================================================
;; Eager Reduction
;; =============================================================================

(defn reduce
  "Reduce async sequence eagerly, returns spin of final result.

  Consumes entire sequence, calling (rf acc value) for each element.
  Supports early termination via reduced.

  Example:
    (await (reduce conj [] pages))
    (await (reduce + 0 page-counts))"
  ([rf init aseq]
   (spin/spin
     (loop [acc init
            seq aseq]
       (if seq
         (do
           (log/trace! {:event :seq/reduce-anext :data {:seq-type (type seq)}})
           (let [pair (await (anext seq))]
             (if pair
               (let [value (clojure.core/first pair)
                     rest-seq (clojure.core/second pair)
                     acc' (rf acc value)]
                 (log/trace! {:event :seq/reduce-got
                              :data {:value value :has-rest (some? rest-seq)}})
                 (if (reduced? acc')
                   @acc'
                   (do
                     (log/trace! {:event :seq/reduce-recur :data {:rest-type (type rest-seq)}})
                     (recur acc' rest-seq))))
               (do
                 (log/trace! {:event :seq/reduce-end})
                 acc))))
         acc))))
  ([rf aseq]
   (reduce rf (rf) aseq)))

(defn into
  "Transduce async sequence into collection, returns spin of result.

  Example:
    (await (into [] (map count) pages))
    (await (into #{} pages))"
  ([to aseq]
   (reduce conj to aseq))
  ([to xform aseq]
   (spin/spin
     (let [rf (xform conj)]
       (await (reduce rf to aseq))))))

;; =============================================================================
;; Lazy Transduction (Deferred until we implement amb>)
;; =============================================================================

;; TODO: Implement lazy sequence with transducers
;; This requires proper state management similar to cps/sequence.cljc
;; but using runtime atom for fork-safety

(defn sequence
  "Transform async sequence with transducer, returns lazy async sequence.

  The transducer is applied lazily as elements are consumed.

  Example:
    (def page-counts (sequence (map count) pages))
    (await (reduce + 0 page-counts))

  TODO: Full implementation requires transducer state management"
  [xform aseq]
  (throw (ex-info "sequence not yet implemented - use reduce with xform for now"
                  {:xform xform :aseq aseq})))

(defn eduction
  "Alias for sequence (matches Clojure naming).

  TODO: Implement when sequence is implemented"
  [xform aseq]
  (sequence xform aseq))

;; =============================================================================
;; Simple Constructors
;; =============================================================================

(defn from-coll
  "Create async sequence from regular collection.

  Example:
    (def nums (from-coll [1 2 3 4 5]))
    (await (reduce + 0 nums))  ;=> 15"
  [coll]
  (when (seq coll)
    (reify PAsyncSeq
      (anext [_]
        (spin/spin
          (log/trace! {:event :seq/from-coll-emit
                       :data {:value (clojure.core/first coll)}})
          [(clojure.core/first coll)
           (from-coll (clojure.core/rest coll))])))))

(defn iterate-async
  "Create async sequence from iteration function.

  Function should return spin yielding map with:
    :value - current value
    :next-state - state for next iteration
    :done? - true if no more values

  Implemented using gen-aseq/yield to avoid nested spin-await edge cases.

  Example:
    (defn fetch-pages [api-fn]
      (iterate-async
        (fn [cursor]
          (spin/spin
            (let [{:keys [page next]} (await (api-fn cursor))]
              (if next
                {:value page :next-state next :done? false}
                {:value page :done? true}))))
        :start))"
  [f init-state]
  (core/gen-aseq
    (loop [state init-state]
      (let [{:keys [value next-state done?]} (await (f state))]
        (log/trace! {:event :seq/iterate-async-step
                     :data {:value value :done? done? :next-state next-state}})
        (core/yield value)
        (when-not done?
          (recur next-state))))))
