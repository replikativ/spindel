(ns org.replikativ.spindel.incremental.typed-combinators-test
  "Tests for `izip` (applicative product) and `iflat-map` (monadic
   flatten). Sanity tests verify the no-change short-circuit; property
   tests verify the functional contract — `:new` is always what the
   pure-function definition would produce."
  (:refer-clojure :exclude [zip])
  #?(:clj
     (:require [clojure.test :refer [deftest is testing]]
               [clojure.test.check.clojure-test :refer [defspec]]
               [clojure.test.check.generators :as gen]
               [clojure.test.check.properties :as prop]
               [org.replikativ.spindel.engine.core :as ec]
               [org.replikativ.spindel.incremental.algebra :as a]
               [org.replikativ.spindel.incremental.interval :as iv]
               [org.replikativ.spindel.incremental.sequence-algebra :as sa]
               [org.replikativ.spindel.incremental.typed-combinators :as tc]
               [org.replikativ.spindel.test-helpers :as th])
     :cljs
     (:require [cljs.test :refer-macros [deftest is testing]]
               [clojure.test.check.clojure-test :refer-macros [defspec]]
               [clojure.test.check.generators :as gen]
               [clojure.test.check.properties :as prop :include-macros true]
               [org.replikativ.spindel.engine.core :as ec]
               [org.replikativ.spindel.incremental.algebra :as a]
               [org.replikativ.spindel.incremental.interval :as iv]
               [org.replikativ.spindel.incremental.sequence-algebra :as sa]
               [org.replikativ.spindel.incremental.typed-combinators :as tc])))

;; =============================================================================
;; izip — applicative product of scalar intervals
;; =============================================================================

#?(:clj
   (deftest izip-basic-combination
     (testing "izip combines N scalar sources via f"
       (th/with-ctx [_ctx]
         (let [loc {:file "izip-1" :line 1 :column 0}
               s1 (iv/->Interval nil 5 nil)
               s2 (iv/->Interval nil 3 nil)
               r (tc/izip* loc + [s1 s2])]
           (is (= 8 (:new r))))))))

#?(:clj
   (deftest izip-no-change-short-circuit
     (testing "izip emits scalar empty deltas when all sources are no-change AND cached"
       (th/with-ctx [_ctx]
         (let [loc {:file "izip-nc" :line 1 :column 0}
               ;; Run #1 establishes cache.
               s1a (iv/->Interval nil 5 nil)
               s2a (iv/->Interval nil 3 nil)
               r1 (tc/izip* loc + [s1a s2a])
               ;; Run #2: both sources verified-no-change.
               s1b (iv/->Interval 5 5 [])
               s2b (iv/->Interval 3 3 [])
               r2 (tc/izip* loc + [s1b s2b])]
           (is (= 8 (:new r1)))
           (is (= 8 (:new r2)))
           (is (a/empty-deltas? a/scalar-algebra (:deltas r2))
               "second run with all-no-change sources should emit scalar empty"))))))

#?(:clj
   (deftest izip-real-change
     (testing "izip emits a scalar replace when the computed value differs"
       (th/with-ctx [_ctx]
         (let [loc {:file "izip-rc" :line 1 :column 0}
               _ (tc/izip* loc + [(iv/->Interval nil 1 nil) (iv/->Interval nil 2 nil)])
               r (tc/izip* loc + [(iv/->Interval 1 10 (a/scalar-replace 10))
                                  (iv/->Interval 2 20 (a/scalar-replace 20))])]
           (is (= 30 (:new r)))
           (is (= 3 (:old r)))
           (is (not (a/empty-deltas? a/scalar-algebra (:deltas r)))))))))

#?(:clj
   (deftest izip-value-equality-detects-no-change
     (testing "If sources claim change but f produces same value, output is verified no-change"
       (th/with-ctx [_ctx]
         (let [loc {:file "izip-eq" :line 1 :column 0}
               ;; Establish cache with sum = 5.
               _ (tc/izip* loc + [(iv/->Interval nil 2 nil) (iv/->Interval nil 3 nil)])
               ;; New inputs sum to 5 again (swap), with non-empty deltas.
               r (tc/izip* loc + [(iv/->Interval 2 4 (a/scalar-replace 4))
                                  (iv/->Interval 3 1 (a/scalar-replace 1))])]
           (is (= 5 (:new r)))
           (is (a/empty-deltas? a/scalar-algebra (:deltas r))
               "value-equal recomputation should emit verified no-change"))))))

;; =============================================================================
;; iflat-map — monadic flatten on sequences
;; =============================================================================

#?(:clj
   (deftest iflat-map-basic-concat
     (testing "iflat-map concatenates body results in source order"
       (th/with-ctx [_ctx]
         (let [loc {:file "fm-1" :line 1 :column 0}
               src (iv/->Interval nil [:a :b :c] nil)
               r   (tc/iflat-map* loc #(vector % %) src)]
           (is (= [:a :a :b :b :c :c] (:new r))))))))

#?(:clj
   (deftest iflat-map-empty-body-skips-element
     (testing "iflat-map with a body returning [] drops elements"
       (th/with-ctx [_ctx]
         (let [loc {:file "fm-2" :line 1 :column 0}
               src (iv/->Interval nil [1 2 3 4] nil)
               r   (tc/iflat-map* loc (fn [x] (if (even? x) [x] [])) src)]
           (is (= [2 4] (:new r))))))))

#?(:clj
   (deftest iflat-map-no-change-short-circuit
     (testing "iflat-map short-circuits when source verifies no-change"
       (th/with-ctx [_ctx]
         (let [loc {:file "fm-nc" :line 1 :column 0}
               body #(vector % %)
               ;; First run: builds cache.
               _ (tc/iflat-map* loc body (iv/->Interval nil [:a :b :c] nil))
               ;; Second run: source verified no-change.
               r (tc/iflat-map* loc body (iv/->Interval [:a :b :c] [:a :b :c] []))]
           (is (= [:a :a :b :b :c :c] (:new r)))
           (is (a/empty-deltas? sa/sequence-algebra (:deltas r))
               "no-change source should produce sequence-algebra empty deltas"))))))

#?(:clj
   (deftest iflat-map-state-diff-on-insert
     (testing "iflat-map emits a sound sequence diff via state-diff on a new element"
       (th/with-ctx [_ctx]
         (let [loc {:file "fm-sd" :line 1 :column 0}
               body #(vector % %)
               _ (tc/iflat-map* loc body (iv/->Interval nil [:a :b] nil))
               r (tc/iflat-map* loc body (iv/->Interval [:a :b]
                                                        [:a :x :b]
                                                        [{:delta :add :value :x}]))]
           (is (= [:a :a :x :x :b :b] (:new r)))
           (let [delta (:deltas r)]
             (is (some? delta) "should produce a real diff via state-diff")
             ;; The state-diff applied to prev-new must yield the new value.
             (is (= [:a :a :x :x :b :b]
                    (a/apply-deltas sa/sequence-algebra
                                    [:a :a :b :b]
                                    delta)))))))))

;; =============================================================================
;; Property tests — the functional contract
;; =============================================================================

#?(:clj
   (defspec izip-equals-pure-application 100
     ;; :new of izip equals (apply f news) for any sources
     (prop/for-all [vals (gen/vector (gen/vector gen/small-integer 1 5) 1 4)]
                   (th/with-ctx [_ctx]
                     (let [loc {:file "prop" :line 1 :column 0}
               ;; Each "source" is a sequence of (Interval) snapshots in
               ;; time order; we just test the final snapshot.
                           sources (mapv (fn [v] (iv/->Interval nil (last v) nil)) vals)
                           news (mapv last vals)
                           r (tc/izip* loc + sources)]
                       (= (apply + news) (:new r)))))))

#?(:clj
   (defspec iflat-map-equals-mapcat 100
     ;; :new of iflat-map equals (into [] (mapcat body) source)
     (prop/for-all [src (gen/vector gen/small-integer 0 10)]
                   (th/with-ctx [_ctx]
                     (let [loc {:file "fm-prop" :line 1 :column 0}
                           body (fn [x] [x x])
                           r (tc/iflat-map* loc body (iv/->Interval nil src nil))]
                       (= (into [] (mapcat body) src) (:new r)))))))

#?(:clj
   (defspec iflat-map-delta-soundness 100
     ;; If iflat-map emits non-nil deltas, they are sound:
     ;; apply(prev, deltas) = new
     (prop/for-all [pre  (gen/vector gen/small-integer 0 8)
                    post (gen/vector gen/small-integer 0 8)]
                   (th/with-ctx [_ctx]
                     (let [loc {:file "fm-sound" :line 1 :column 0}
                           body (fn [x] [x])  ; identity-shape; one-in, one-out
                           _ (tc/iflat-map* loc body (iv/->Interval nil pre nil))
                           r (tc/iflat-map* loc body (iv/->Interval pre post nil))
                           d (:deltas r)]
                       (or (nil? d)
                           (= (:new r) (a/apply-deltas sa/sequence-algebra
                                                       (:old r)
                                                       d))))))))
