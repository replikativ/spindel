(ns org.replikativ.spindel.v2.incremental.combinators-test
  "The stateless combinators of `v2.incremental` (phase-d design §4.2),
   ported from `incremental/combinator_test.cljc`.

   Each output is the transformation of the input interval's endpoints
   under the parameters of the call: `:new` from the input's new value,
   `:old` from its old value, `:deltas` the output algebra's state-diff
   between them. So (Value) `:new` is a pure function of the input's `:new`
   and the parameters, and (Soundness) `:deltas` applied to `:old` gives
   `:new`. The old suite's cache cases change meaning: there is no cache, so
   two calls never share state, and the no-change answer is computed, not
   short-circuited."
  #?(:clj
     (:require [clojure.test :refer [deftest is testing]]
               [clojure.test.check.clojure-test :refer [defspec]]
               [clojure.test.check.generators :as gen]
               [clojure.test.check.properties :as prop]
               [org.replikativ.spindel.incremental.algebra :as a]
               [org.replikativ.spindel.incremental.interval :as iv]
               [org.replikativ.spindel.incremental.sequence-algebra :as sa]
               [org.replikativ.spindel.v2.incremental :as ic])
     :cljs
     (:require [cljs.test :refer-macros [deftest is testing]]
               [clojure.test.check.clojure-test :refer-macros [defspec]]
               [clojure.test.check.generators :as gen]
               [clojure.test.check.properties :as prop :include-macros true]
               [org.replikativ.spindel.incremental.algebra :as a]
               [org.replikativ.spindel.incremental.interval :as iv]
               [org.replikativ.spindel.incremental.sequence-algebra :as sa]
               [org.replikativ.spindel.v2.incremental :as ic])))

(defn- sound?
  "Whether the output's deltas take its :old to its :new."
  [algebra r]
  (= (iv/get-new r) (a/apply-deltas algebra (iv/get-old r) (iv/get-deltas r))))

;; =============================================================================
;; One per combinator
;; =============================================================================

(deftest imap-basics
  (let [r (ic/imap #(* 2 %) (iv/interval nil [1 2 3] nil))]
    (is (= [2 4 6] (iv/get-new r)))
    (is (= sa/sequence-algebra (:algebra r)))
    (is (nil? (iv/get-old r)) "no old input, no old output")
    (is (nil? (iv/get-deltas r)) "no old, no deltas")))

(deftest imap-state-diff-soundness
  (let [r (ic/imap inc (iv/interval [1 2 3] [1 2 3 4] nil))]
    (is (= [2 3 4] (iv/get-old r)))
    (is (= [2 3 4 5] (iv/get-new r)))
    (is (some? (iv/get-deltas r)))
    (is (sound? sa/sequence-algebra r))))

(deftest ifilter-basics
  (is (= [2 4] (iv/get-new (ic/ifilter even? (iv/interval nil [1 2 3 4] nil))))))

(deftest ireduce-basics
  (let [r (ic/ireduce + 0 (iv/interval nil [1 2 3 4] nil))]
    (is (= 10 (iv/get-new r)))
    (is (= a/scalar-algebra (:algebra r)))))

(deftest ireduce-scalar-delta-soundness
  (let [r (ic/ireduce + 0 (iv/interval [1 2 3] [1 2 3 4] nil))]
    (is (= 6 (iv/get-old r)))
    (is (= 10 (iv/get-new r)))
    (is (sound? a/scalar-algebra r))))

(deftest plain-and-deltaable-inputs
  (testing "a plain value is an interval with no old"
    (let [r (ic/imap inc [1 2])]
      (is (= [2 3] (iv/get-new r)))
      (is (nil? (iv/get-old r)))))
  (testing "a typed interval (another combinator's output) is read by its endpoints"
    (let [r (ic/imap inc (ic/ifilter odd? (iv/interval [1 2] [1 2 3] nil)))]
      (is (= [2] (iv/get-old r)))
      (is (= [2 4] (iv/get-new r))))))

;; =============================================================================
;; No change: computed from the endpoints, not short-circuited
;; =============================================================================

(deftest unchanged-input-gives-an-unchanged-output
  (let [src (iv/interval [1 2 3 4] [1 2 3 4] [])]
    (doseq [[label algebra r] [["imap" sa/sequence-algebra (ic/imap inc src)]
                               ["ifilter" sa/sequence-algebra (ic/ifilter even? src)]
                               ["ireduce" a/scalar-algebra (ic/ireduce + 0 src)]
                               ["islice" sa/sequence-algebra (ic/islice {:start 0 :end 2} src)]]]
      (testing label
        (is (iv/no-change? r) "old = new and the empty delta")
        (is (sound? algebra r))))))

;; =============================================================================
;; No per-call-site state (the old cache, and its shared-instance bug, are gone)
;; =============================================================================

(deftest old-is-the-transformed-input-old
  (testing "the old suite's address-caching case: :old is the input's old
            transformed, here equal to the earlier call's :new because the
            parameters did not change"
    (let [f (fn [src] (ic/ifilter even? src))
          r1 (f (iv/interval nil [1 2 3] nil))
          r2 (f (iv/interval [1 2 3] [1 2 3 4] nil))]
      (is (= [2] (iv/get-new r1)))
      (is (= [2] (iv/get-old r2)))
      (is (= [2 4] (iv/get-new r2)))))
  (testing "two live instances of one call site share nothing"
    (let [f (fn [src] (ic/imap inc src))
          a1 (f (iv/interval nil [1 2] nil))
          b1 (f (iv/interval nil [10 20 30] nil))
          a2 (f (iv/interval [1 2] [1 2 3] nil))]
      (is (= [2 3] (iv/get-new a1)))
      (is (= [11 21 31] (iv/get-new b1)))
      (is (= [2 3] (iv/get-old a2)) "a2's :old is its own input's old, not b1's output"))))

;; =============================================================================
;; C1 (sol T9): a parameter changes while the source does not
;; =============================================================================

(deftest c1-a-captured-threshold-changes
  (let [src (iv/interval [1 2 3 4 5] [1 2 3 4 5] [])
        above (fn [t] (fn [x] (> x t)))
        r1 (ic/ifilter (above 2) src)
        r2 (ic/ifilter (above 4) src)]
    (is (= [3 4 5] (iv/get-new r1)))
    (is (= [5] (iv/get-new r2)))
    (is (= [5] (iv/get-old r2))
        ":old is the source's old filtered by the NEW threshold")
    (is (not= (iv/get-new r1) (iv/get-old r2))
        "so it is not the previous output: :old and :deltas are advisory when a parameter changes")
    (is (iv/no-change? r2) "the output even reports no change, though the visible list shrank")))

;; =============================================================================
;; Properties
;; =============================================================================

(def ^:private gen-int-seq (gen/vector gen/small-integer 0 10))

(defspec imap-equals-pure-mapv 100
  (prop/for-all [pre gen-int-seq post gen-int-seq]
                (let [r (ic/imap inc (iv/interval pre post nil))]
                  (and (= (mapv inc post) (iv/get-new r))
                       (= (mapv inc pre) (iv/get-old r))))))

(defspec ifilter-equals-pure-filterv 100
  (prop/for-all [pre gen-int-seq post gen-int-seq]
                (let [r (ic/ifilter even? (iv/interval pre post nil))]
                  (and (= (filterv even? post) (iv/get-new r))
                       (= (filterv even? pre) (iv/get-old r))))))

(defspec ireduce-equals-pure-reduce 100
  (prop/for-all [pre gen-int-seq post gen-int-seq]
                (let [r (ic/ireduce + 0 (iv/interval pre post nil))]
                  (and (= (reduce + 0 post) (iv/get-new r))
                       (= (reduce + 0 pre) (iv/get-old r))))))

(defspec imap-delta-soundness 100
  (prop/for-all [pre gen-int-seq post gen-int-seq]
                (sound? sa/sequence-algebra (ic/imap inc (iv/interval pre post nil)))))

(defspec ifilter-delta-soundness 100
  (prop/for-all [pre gen-int-seq post gen-int-seq]
                (sound? sa/sequence-algebra (ic/ifilter even? (iv/interval pre post nil)))))

(defspec ireduce-delta-soundness 100
  (prop/for-all [pre gen-int-seq post gen-int-seq]
                (sound? a/scalar-algebra (ic/ireduce + 0 (iv/interval pre post nil)))))

;; =============================================================================
;; Pipeline
;; =============================================================================

(deftest pipeline-filter-map-reduce
  (let [src (iv/interval [1 2 3] [1 2 3 4 5] nil)
        f (ic/ifilter even? src)
        m (ic/imap #(* 2 %) f)
        r (ic/ireduce + 0 m)]
    (is (= [2 4] (iv/get-new f)))
    (is (= [4 8] (iv/get-new m)))
    (is (= 12 (iv/get-new r)))
    (is (= [4] (iv/get-old m)))
    (is (= 4 (iv/get-old r)))
    (is (sound? a/scalar-algebra r))))
