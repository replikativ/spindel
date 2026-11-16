(ns org.replikativ.spindel.v2.seq
  "Async sequences over v2 positions (C0). A position is a value: `(await p)`
   returns `[v next-position]`, or nil at the end. Every combinator is a pull
   sequence whose state is passed from element to element (no shared mutable
   state), so its elements are realized once per world and forks stay
   independent."
  (:refer-clojure :exclude [await amap take drop take-while concat merge reduce into dedupe partition-all])
  (:require [clojure.core :as cc]
            [org.replikativ.spindel.v2.core :as v2 :refer [aseq await await-any spin]])
  #?(:cljs (:require-macros [org.replikativ.spindel.v2.core :refer [aseq spin]])))

(defn from-coll
  "The elements of `coll` as a sequence."
  [coll]
  (aseq [s (seq coll)] (when s [(first s) (next s)])))

(defn amap
  "`(f v)` of each element."
  [f src]
  (aseq [p src] (when-let [[v nx] (await p)] [(f v) nx])))

(defn afilter
  "The elements for which `(pred v)` is truthy."
  [pred src]
  (aseq [p src]
    (loop [p p]
      (when-let [[v nx] (await p)]
        (if (pred v) [v nx] (recur nx))))))

(defn akeep
  "The non-nil values of `(f v)`."
  [f src]
  (aseq [p src]
    (loop [p p]
      (when-let [[v nx] (await p)]
        (let [x (f v)] (if (some? x) [x nx] (recur nx)))))))

(defn amapcat
  "The concatenation of the collections `(f v)`."
  [f src]
  (aseq [[buf p] [nil src]]
    (loop [buf buf p p]
      (if (seq buf)
        [(first buf) [(next buf) p]]
        (when-let [[v nx] (await p)]
          (recur (seq (f v)) nx))))))

(defn take
  "The first `n` elements."
  [n src]
  (aseq [[n p] [n src]]
    (when (pos? n)
      (when-let [[v nx] (await p)] [v [(dec n) nx]]))))

(defn drop
  "All but the first `n` elements."
  [n src]
  (aseq [[n p] [n src]]
    (loop [n n p p]
      (when-let [[v nx] (await p)]
        (if (pos? n) (recur (dec n) nx) [v [0 nx]])))))

(defn take-while
  "The elements up to the first for which `(pred v)` is falsy."
  [pred src]
  (aseq [p src]
    (when-let [[v nx] (await p)]
      (when (pred v) [v nx]))))

(defn partition-all
  "Vectors of `n` consecutive elements; the last may be shorter."
  [n src]
  (aseq [p src]
    (when p
      (loop [p p acc []]
        (if (= n (count acc))
          [acc p]
          (if-let [[v nx] (await p)]
            (recur nx (conj acc v))
            (when (seq acc) [acc nil])))))))

(defn dedupe
  "The elements that differ from their predecessor."
  [src]
  (aseq [[prev p] [::none src]]
    (loop [p p]
      (when-let [[v nx] (await p)]
        (if (= v prev) (recur nx) [v [v nx]])))))

(defn scan
  "The successive reductions `(f acc v)`, starting after `init`."
  [f init src]
  (aseq [[acc p] [init src]]
    (when-let [[v nx] (await p)]
      (let [acc (f acc v)] [acc [acc nx]]))))

(defn concat
  "The elements of each source in turn."
  [& srcs]
  (aseq [ps (seq srcs)]
    (loop [ps ps]
      (when ps
        (if-let [[v nx] (await (first ps))]
          [v (cons nx (next ps))]
          (recur (next ps)))))))

(defn- tagged
  "`[[i v] next]` per element of `src`, then `[[i ::end] nil]` once."
  [i src]
  (aseq [p src]
    (when p
      (if-let [[v nx] (await p)]
        [[i v] nx]
        [[i ::end] nil]))))

(defn merge
  "The elements of all sources in the order they become ready (by
   readiness, `await-any`); ends when every source has ended."
  [& srcs]
  (aseq [ps (vec (map-indexed tagged srcs))]
    (loop [ps ps]
      (let [live (vec (keep-indexed (fn [i p] (when p i)) ps))]
        (when (seq live)
          (let [[[i v] nx] (await-any (mapv ps live))]
            (if (= ::end v)
              (recur (assoc ps i nil))
              [v (assoc ps i nx)])))))))

(defn latest
  "Each read yields the newest element available: it waits for one, then
   skips over the elements that are already realized (a sliding window of
   one, for readers that only need the current state)."
  [src]
  (aseq [p src]
    (when p
      (when-let [[v nx] (await p)]
        (loop [v v nx nx]
          (if (v2/ready? nx)
            (if-let [[v2* nx2] (await nx)] (recur v2* nx2) [v nx])
            [v nx]))))))

(defn take-latest
  "Each read yields a vector of the newest available elements, at most `n`:
   it waits for one, then takes what is already realized (a sliding window
   of `n`)."
  [n src]
  (aseq [p src]
    (when p
      (when-let [[v nx] (await p)]
        (loop [acc [v] nx nx]
          (if (v2/ready? nx)
            (if-let [[v* nx*] (await nx)]
              (recur (let [acc (conj acc v*)] (if (> (count acc) n) (subvec acc 1) acc)) nx*)
              [acc nx])
            [acc nx]))))))

(defn reduce
  "A computation of reducing the elements of `src` with `f` from `init`."
  [f init src]
  (spin (loop [acc init p src]
          (if-let [[v nx] (await p)]
            (recur (f acc v) nx)
            acc))))

(defn into
  "A computation of `to` with every element of `src` added."
  [to src]
  (spin (loop [acc to p src]          ; persistent: a re-entered run resumes with it
          (if-let [[v nx] (await p)]
            (recur (conj acc v) nx)
            acc))))
