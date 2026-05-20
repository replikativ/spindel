(ns org.replikativ.spindel.incremental.typed-combinators-test
  "Tests for `izip` (applicative product) and `iflat-map` (monadic
   flatten). Sanity tests verify the no-change short-circuit; property
   tests verify the functional contract — `:new` is always what the
   pure-function definition would produce.

   House-style demonstrator: every interval read goes through
   `iv/get-new` / `iv/get-old` / `iv/get-deltas`. Output assertions
   use the algebra identity (`a/empty-deltas? a/scalar-algebra …`,
   `a/empty-deltas? sa/sequence-algebra …`).

   Input intervals built by `iv/->Interval` use the *legacy* empty-
   deltas value `[]` because the Interval deftype's `no-change?`
   predicate only recognises `[]` (typed-interval-maps with an
   `:algebra` key use algebra identities; deftypes don't)."
  (:refer-clojure :exclude [zip])
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.test.check.clojure-test :refer [defspec]]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [org.replikativ.spindel.incremental.algebra :as a]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.incremental.sequence-algebra :as sa]
            [org.replikativ.spindel.incremental.typed-combinators :as tc]
            [org.replikativ.spindel.test-helpers :as th]))

;; =============================================================================
;; izip — applicative product of scalar intervals
;; =============================================================================

(deftest izip-basic-combination
  (testing "izip combines N scalar sources via f"
    (th/with-ctx [_ctx]
      (let [loc {:file "izip-1" :line 1 :column 0}
            s1 (iv/->Interval nil 5 nil)
            s2 (iv/->Interval nil 3 nil)
            r (tc/izip* loc + [s1 s2])]
        (is (= 8 (iv/get-new r)))))))

(deftest izip-no-change-short-circuit
  (testing "izip emits scalar empty deltas when all sources are no-change AND cached"
    (th/with-ctx [_ctx]
      (let [loc {:file "izip-nc" :line 1 :column 0}
            ;; Run #1 establishes cache.
            s1a (iv/->Interval nil 5 nil)
            s2a (iv/->Interval nil 3 nil)
            r1 (tc/izip* loc + [s1a s2a])
            ;; Run #2: both sources verified-no-change. Legacy Interval
            ;; uses `[]` for empty-deltas; the OUTPUT assertion below
            ;; checks the algebra-typed empty.
            s1b (iv/->Interval 5 5 [])
            s2b (iv/->Interval 3 3 [])
            r2 (tc/izip* loc + [s1b s2b])]
        (is (= 8 (iv/get-new r1)))
        (is (= 8 (iv/get-new r2)))
        (is (a/empty-deltas? a/scalar-algebra (iv/get-deltas r2))
            "second run with all-no-change sources should emit scalar empty")))))

(deftest izip-real-change
  (testing "izip emits a scalar replace when the computed value differs"
    (th/with-ctx [_ctx]
      (let [loc {:file "izip-rc" :line 1 :column 0}
            _ (tc/izip* loc + [(iv/->Interval nil 1 nil) (iv/->Interval nil 2 nil)])
            r (tc/izip* loc + [(iv/->Interval 1 10 (a/scalar-replace 10))
                               (iv/->Interval 2 20 (a/scalar-replace 20))])]
        (is (= 30 (iv/get-new r)))
        (is (= 3 (iv/get-old r)))
        (is (not (a/empty-deltas? a/scalar-algebra (iv/get-deltas r))))))))

(deftest izip-value-equality-detects-no-change
  (testing "If sources claim change but f produces same value, output is verified no-change"
    (th/with-ctx [_ctx]
      (let [loc {:file "izip-eq" :line 1 :column 0}
            ;; Establish cache with sum = 5.
            _ (tc/izip* loc + [(iv/->Interval nil 2 nil) (iv/->Interval nil 3 nil)])
            ;; New inputs sum to 5 again (swap), with non-empty deltas.
            r (tc/izip* loc + [(iv/->Interval 2 4 (a/scalar-replace 4))
                               (iv/->Interval 3 1 (a/scalar-replace 1))])]
        (is (= 5 (iv/get-new r)))
        (is (a/empty-deltas? a/scalar-algebra (iv/get-deltas r))
            "value-equal recomputation should emit verified no-change")))))

;; =============================================================================
;; iflat-map — monadic flatten on sequences
;; =============================================================================

(deftest iflat-map-basic-concat
  (testing "iflat-map concatenates body results in source order"
    (th/with-ctx [_ctx]
      (let [loc {:file "fm-1" :line 1 :column 0}
            src (iv/->Interval nil [:a :b :c] nil)
            r   (tc/iflat-map* loc #(vector % %) src)]
        (is (= [:a :a :b :b :c :c] (iv/get-new r)))))))

(deftest iflat-map-empty-body-skips-element
  (testing "iflat-map with a body returning [] drops elements"
    (th/with-ctx [_ctx]
      (let [loc {:file "fm-2" :line 1 :column 0}
            src (iv/->Interval nil [1 2 3 4] nil)
            r   (tc/iflat-map* loc (fn [x] (if (even? x) [x] [])) src)]
        (is (= [2 4] (iv/get-new r)))))))

(deftest iflat-map-no-change-short-circuit
  (testing "iflat-map short-circuits when source verifies no-change"
    (th/with-ctx [_ctx]
      (let [loc {:file "fm-nc" :line 1 :column 0}
            body #(vector % %)
            src-val [:a :b :c]
            ;; First run: builds cache.
            _ (tc/iflat-map* loc body (iv/->Interval nil src-val nil))
            ;; Second run: source verified no-change. Legacy Interval
            ;; uses `[]` for empty-deltas; the OUTPUT assertion below
            ;; checks the typed sequence-algebra empty.
            r (tc/iflat-map* loc body (iv/->Interval src-val src-val []))]
        (is (= [:a :a :b :b :c :c] (iv/get-new r)))
        (is (a/empty-deltas? sa/sequence-algebra (iv/get-deltas r))
            "no-change source should produce sequence-algebra empty deltas")))))

(deftest iflat-map-state-diff-on-insert
  (testing "iflat-map emits a sound sequence diff via state-diff on a new element"
    (th/with-ctx [_ctx]
      (let [loc {:file "fm-sd" :line 1 :column 0}
            body #(vector % %)
            _ (tc/iflat-map* loc body (iv/->Interval nil [:a :b] nil))
            ;; Source delta vocabulary on this line is the deltaable-
            ;; collection input edge — that's still the raw {:delta …}
            ;; shape. iflat-map's OUTPUT is the typed seq-diff, which
            ;; is what we then exercise via apply-deltas below.
            r (tc/iflat-map* loc body (iv/->Interval [:a :b]
                                                     [:a :x :b]
                                                     [{:delta :add :value :x}]))]
        (is (= [:a :a :x :x :b :b] (iv/get-new r)))
        (let [delta (iv/get-deltas r)]
          (is (some? delta) "should produce a real diff via state-diff")
          ;; The state-diff applied to prev-new must yield the new value.
          (is (= [:a :a :x :x :b :b]
                 (a/apply-deltas sa/sequence-algebra
                                 [:a :a :b :b]
                                 delta))))))))

;; =============================================================================
;; Property tests — the functional contract
;; =============================================================================

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
                    (= (apply + news) (iv/get-new r))))))

(defspec iflat-map-equals-mapcat 100
  ;; :new of iflat-map equals (into [] (mapcat body) source)
  (prop/for-all [src (gen/vector gen/small-integer 0 10)]
                (th/with-ctx [_ctx]
                  (let [loc {:file "fm-prop" :line 1 :column 0}
                        body (fn [x] [x x])
                        r (tc/iflat-map* loc body (iv/->Interval nil src nil))]
                    (= (into [] (mapcat body) src) (iv/get-new r))))))

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
                        d (iv/get-deltas r)]
                    (or (nil? d)
                        (= (iv/get-new r) (a/apply-deltas sa/sequence-algebra
                                                          (iv/get-old r)
                                                          d)))))))
