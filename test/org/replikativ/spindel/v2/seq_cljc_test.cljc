(ns org.replikativ.spindel.v2.seq-cljc-test
  "C0 async sequences on both platforms: pull sequences, streams,
   combinators and pub/sub."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is]]
            [org.replikativ.spindel.v2.core :as v2 :refer [task await aseq]]
            [org.replikativ.spindel.v2.seq :as as]
            [org.replikativ.spindel.v2.pubsub :as ps])
  #?(:cljs (:require-macros [org.replikativ.spindel.v2.core :refer [task aseq]])))

(def ^:dynamic *x* :root)
(v2/convey *x*)

(defn- now
  "The settled outcome of `h`. CLJS inline worlds without a time
   slice settle synchronously."
  [h]
  #?(:clj (try (v2/value h 2000 ::timeout) (catch Exception e [:err (ex-message e)]))
     :cljs (let [a (atom ::pending)]
             (v2/value-async h (fn [v err?] (reset! a (if err? [:err (ex-message v)] v))))
             @a)))

;; no time slice: an inline operation completes before it returns however
;; slow the host is (#363's default 5 ms slice can spill a slow turn, and a
;; synchronous read would see it pending)
(defn- in-world [f]
  (let [w (v2/world {:slice-ms nil})]
    (try (binding [v2/*world* w] (f)) (finally (v2/release-world! w)))))

(deftest pull-sequences-realize-once
  (in-world
   #(let [calls (atom 0)
          xs (aseq [n 0] (swap! calls inc) (when (< n 3) [n (inc n)]))]
      (is (= [0 1 2] (now (as/into [] xs))))
      (is (= [0 1 2] (now (as/into [] xs))))
      (is (= 4 @calls)))))

(deftest errors-are-memoized
  (in-world
   #(let [xs (aseq [n 0] (if (= n 1) (throw (ex-info "boom" {})) [n (inc n)]))]
      (is (= [:err "boom"] (now (as/into [] xs))))
      (is (= 0 (first (now xs)))))))

(deftest creation-bindings-reach-the-realizer
  (in-world
   #(let [xs (binding [*x* :created] (aseq [n 0] (when (zero? n) [*x* 1])))]
      (is (= [:created] (now (as/into [] xs)))))))

(deftest streams-and-combinators
  (in-world
   #(let [s (v2/stream)
          p (v2/position s)
          evens (as/into [] (as/afilter even? (as/amap inc p)))]
      (dotimes [i 6] (v2/append! s i))
      (v2/close! s)
      (is (= [2 4 6] (now evens)))
      (is (= [[0 1] [2 3] [4 5]] (now (as/into [] (as/partition-all 2 p))))))))

(deftest a-task-reads-a-stream
  (in-world
   #(let [s (v2/stream)
          t (task (loop [p (v2/position s) acc []]
                    (if-let [[v nx] (await p)] (recur nx (conj acc v)) acc)))]
      (v2/append! s :a)
      (v2/append! s :b)
      (v2/close! s)
      (is (= [:a :b] (now t))))))

(deftest pub-sub
  (in-world
   #(let [bus (v2/stream)
          p (ps/pub (v2/position bus) :topic)
          a (now (ps/sub p :a))
          r (as/into [] (as/amap :v a))]
      (v2/append! bus {:topic :a :v 1})
      (v2/append! bus {:topic :b :v 2})
      (v2/append! bus {:topic :a :v 3})
      (v2/close! bus)
      (is (= [1 3] (now r))))))
