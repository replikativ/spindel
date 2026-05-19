(ns org.replikativ.spindel.incremental.combinator-test
  "Tests for the rewritten typed-algebra combinators: `map*`, `filter*`,
   `reduce*`, `slice*`, `for-each*`.

   Strategy: every combinator must satisfy the same two invariants:

     (Value)    `:new` is a pure function of source `:new` and free
                vars, regardless of cache state.
     (Soundness) When `:deltas` is non-nil and non-empty, applying it
                  to `:old` via the output algebra recovers `:new`.

   These two together (plus the four monoid laws on the algebras
   themselves, already covered in algebra/sequence_algebra/scalar
   tests) cover the combinator surface. Shape-specific tests are
   gone — they checked an internal representation that changed."
  (:refer-clojure :exclude [filter map reduce])
  #?(:clj
     (:require [clojure.test :refer [deftest is testing]]
               [clojure.test.check.clojure-test :refer [defspec]]
               [clojure.test.check.generators :as gen]
               [clojure.test.check.properties :as prop]
               [org.replikativ.spindel.engine.context :as ctx]
               [org.replikativ.spindel.engine.core :as ec]
               [org.replikativ.spindel.incremental.algebra :as a]
               [org.replikativ.spindel.incremental.combinators :as ic]
               [org.replikativ.spindel.incremental.interval :as iv]
               [org.replikativ.spindel.incremental.sequence-algebra :as sa]
               [org.replikativ.spindel.test-helpers :as th])
     :cljs
     (:require [cljs.test :refer-macros [deftest is testing]])))

;; =============================================================================
;; Hand-written sanity tests — one per combinator
;; =============================================================================

#?(:clj
   (deftest map*-basics
     (testing "map* applies f and produces a sequence interval"
       (th/with-ctx [_ctx]
         (let [loc {:file "m1" :line 1 :column 0}
               r (ic/map* loc #(* 2 %) (iv/interval nil [1 2 3] nil))]
           (is (= [2 4 6] (iv/get-new r)))
           (is (= sa/sequence-algebra (:algebra r))))))))

#?(:clj
   (deftest map*-state-diff-soundness
     (testing "Map output delta is sound — applying it to :old gives :new"
       (th/with-ctx [_ctx]
         (let [loc {:file "m2" :line 1 :column 0}
               r1 (ic/map* loc inc (iv/interval nil [1 2 3] nil))
               r2 (ic/map* loc inc (iv/interval [1 2 3] [1 2 3 4] nil))]
           (is (= [2 3 4] (iv/get-new r1)))
           (is (= [2 3 4 5] (iv/get-new r2)))
           (let [delta (iv/get-deltas r2)]
             (is (some? delta) "second run should produce a delta")
             (is (= [2 3 4 5] (a/apply-deltas sa/sequence-algebra
                                              [2 3 4]
                                              delta)))))))))

#?(:clj
   (deftest filter*-basics
     (testing "filter* retains matching elements"
       (th/with-ctx [_ctx]
         (let [loc {:file "f1" :line 1 :column 0}
               r (ic/filter* loc even? (iv/interval nil [1 2 3 4] nil))]
           (is (= [2 4] (iv/get-new r))))))))

#?(:clj
   (deftest reduce*-basics
     (testing "reduce* folds and produces a scalar interval"
       (th/with-ctx [_ctx]
         (let [loc {:file "r1" :line 1 :column 0}
               r (ic/reduce* loc + 0 (iv/interval nil [1 2 3 4] nil))]
           (is (= 10 (iv/get-new r)))
           (is (= a/scalar-algebra (:algebra r))))))))

#?(:clj
   (deftest reduce*-scalar-delta-soundness
     (testing "reduce*'s scalar delta applies correctly"
       (th/with-ctx [_ctx]
         (let [loc {:file "r2" :line 1 :column 0}
               _ (ic/reduce* loc + 0 (iv/interval nil [1 2 3] nil))
               r2 (ic/reduce* loc + 0 (iv/interval [1 2 3] [1 2 3 4] nil))]
           (is (= 10 (iv/get-new r2)))
           (let [delta (iv/get-deltas r2)]
             (is (= 10 (a/apply-deltas a/scalar-algebra
                                       (iv/get-old r2) delta)))))))))

#?(:clj
   (deftest slice*-basics
     (testing "slice* projects a window"
       (th/with-ctx [_ctx]
         (let [loc {:file "s1" :line 1 :column 0}
               r (ic/slice* loc {:start 1 :end 3} (iv/interval nil [1 2 3 4 5] nil))]
           (is (= [2 3] (iv/get-new r))))))))

#?(:clj
   (deftest for-each*-memoises-by-key
     (testing "for-each* skips transform-fn for items whose key+value didn't change"
       (let [counter (atom 0)
             body (fn [item]
                    (swap! counter inc)
                    (assoc item :rendered true))]
         (th/with-ctx [_ctx]
           (let [loc {:file "fe1" :line 1 :column 0}
                 _ (ic/for-each* loc :id body
                                 (iv/interval nil
                                              [{:id 1 :v "a"} {:id 2 :v "b"}]
                                              nil))]
             (is (= 2 @counter))
             (reset! counter 0)
             (ic/for-each* loc :id body
                           (iv/interval [{:id 1 :v "a"} {:id 2 :v "b"}]
                                        [{:id 1 :v "a"} {:id 2 :v "b"} {:id 3 :v "c"}]
                                        nil))
             (is (= 1 @counter)
                 "transform should fire only for the new item (id 3)")))))))

;; =============================================================================
;; No-change short-circuit — all combinators must respect verified-no-change
;; =============================================================================

#?(:clj
   (deftest no-change-short-circuit
     (testing "Every combinator emits verified-no-change when source is verified-no-change"
       (th/with-ctx [_ctx]
         ;; Establish caches with a first call.
         (let [src1 (iv/interval nil [1 2 3 4] nil)
               loc-f {:file "nc-f" :line 1 :column 0}
               loc-m {:file "nc-m" :line 1 :column 0}
               loc-r {:file "nc-r" :line 1 :column 0}
               loc-s {:file "nc-s" :line 1 :column 0}
               loc-fe {:file "nc-fe" :line 1 :column 0}
               _ (ic/filter* loc-f even? src1)
               _ (ic/map* loc-m inc src1)
               _ (ic/reduce* loc-r + 0 src1)
               _ (ic/slice* loc-s {:start 0 :end 2} src1)
               _ (ic/for-each* loc-fe identity identity src1)]
           ;; Second call with verified-no-change source.
           (let [src-nc (iv/interval [1 2 3 4] [1 2 3 4] [])]
             (is (iv/no-change? (ic/filter* loc-f even? src-nc)))
             (is (iv/no-change? (ic/map* loc-m inc src-nc)))
             (is (iv/no-change? (ic/reduce* loc-r + 0 src-nc)))
             (is (iv/no-change? (ic/slice* loc-s {:start 0 :end 2} src-nc)))
             (is (iv/no-change? (ic/for-each* loc-fe identity identity src-nc)))))))))

;; =============================================================================
;; Address-based caching — same source-loc means same cache
;; =============================================================================

#?(:clj
   (deftest address-caching
     (testing "Two calls at the same source-loc share state"
       (th/with-ctx [_ctx]
         (let [loc {:file "ac" :line 1 :column 0}
               r1 (ic/filter* loc even? (iv/interval nil [1 2 3] nil))
               r2 (ic/filter* loc even? (iv/interval [1 2 3] [1 2 3 4] nil))]
           (is (= [2] (iv/get-new r1)))
           (is (= [2] (iv/get-old r2))
               "the second call's :old is the first call's :new")
           (is (= [2 4] (iv/get-new r2))))))))

;; =============================================================================
;; Property tests — value correctness across arbitrary delta sequences.
;;
;; These tests use the algebra protocol to construct typed intervals, so
;; they exercise the new combinators on the same shape downstream
;; consumers receive.
;; =============================================================================

#?(:clj
   (def ^:private gen-int-seq (gen/vector gen/small-integer 0 10)))

#?(:clj
   (defspec map*-equals-pure-mapv 100
     (prop/for-all [pre  gen-int-seq
                    post gen-int-seq]
                   (th/with-ctx [_ctx]
                     (let [loc {:file "mp" :line 1 :column 0}
                           _ (ic/map* loc inc (iv/interval nil pre nil))
                           r (ic/map* loc inc (iv/interval pre post nil))]
                       (= (mapv inc post) (iv/get-new r)))))))

#?(:clj
   (defspec filter*-equals-pure-filterv 100
     (prop/for-all [pre  gen-int-seq
                    post gen-int-seq]
                   (th/with-ctx [_ctx]
                     (let [loc {:file "fp" :line 1 :column 0}
                           _ (ic/filter* loc even? (iv/interval nil pre nil))
                           r (ic/filter* loc even? (iv/interval pre post nil))]
                       (= (filterv even? post) (iv/get-new r)))))))

#?(:clj
   (defspec reduce*-equals-pure-reduce 100
     (prop/for-all [pre  gen-int-seq
                    post gen-int-seq]
                   (th/with-ctx [_ctx]
                     (let [loc {:file "rp" :line 1 :column 0}
                           _ (ic/reduce* loc + 0 (iv/interval nil pre nil))
                           r (ic/reduce* loc + 0 (iv/interval pre post nil))]
                       (= (clojure.core/reduce + 0 post) (iv/get-new r)))))))

#?(:clj
   (defspec map*-delta-soundness 100
     (prop/for-all [pre  gen-int-seq
                    post gen-int-seq]
                   (th/with-ctx [_ctx]
                     (let [loc {:file "ms" :line 1 :column 0}
                           _ (ic/map* loc inc (iv/interval nil pre nil))
                           r (ic/map* loc inc (iv/interval pre post nil))
                           d (iv/get-deltas r)]
                       (or (nil? d)
                           (= (iv/get-new r)
                              (a/apply-deltas sa/sequence-algebra (iv/get-old r) d))))))))

#?(:clj
   (defspec filter*-delta-soundness 100
     (prop/for-all [pre  gen-int-seq
                    post gen-int-seq]
                   (th/with-ctx [_ctx]
                     (let [loc {:file "fs" :line 1 :column 0}
                           _ (ic/filter* loc even? (iv/interval nil pre nil))
                           r (ic/filter* loc even? (iv/interval pre post nil))
                           d (iv/get-deltas r)]
                       (or (nil? d)
                           (= (iv/get-new r)
                              (a/apply-deltas sa/sequence-algebra (iv/get-old r) d))))))))

#?(:clj
   (defspec for-each*-equals-pure-mapv 100
     (prop/for-all [pre  gen-int-seq
                    post gen-int-seq]
                   (th/with-ctx [_ctx]
                     (let [loc {:file "fep" :line 1 :column 0}
                           body (fn [n] (* 10 n))
                           _ (ic/for-each* loc identity body (iv/interval nil pre nil))
                           r (ic/for-each* loc identity body (iv/interval pre post nil))]
                       (= (mapv body post) (iv/get-new r)))))))

;; =============================================================================
;; Pipeline composition — chain combinators and verify value flow
;; =============================================================================

#?(:clj
   (deftest pipeline-filter-map-reduce
     (testing "Chained combinators compose: filter even → double → sum"
       (th/with-ctx [_ctx]
         (let [src (iv/interval nil [1 2 3 4 5] nil)
               f (ic/filter* {:file "p1" :line 1 :column 0} even? src)
               m (ic/map* {:file "p1" :line 2 :column 0} #(* 2 %) f)
               r (ic/reduce* {:file "p1" :line 3 :column 0} + 0 m)]
           (is (= [2 4] (iv/get-new f)))
           (is (= [4 8] (iv/get-new m)))
           (is (= 12 (iv/get-new r))))))))
