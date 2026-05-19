(ns org.replikativ.spindel.incremental.slice-test
  "Tests for the rewritten `slice*` combinator on the typed delta
   algebra. Same invariant strategy as `combinator-test`: check that
   `:new` is exactly `(subvec source [start, end))` and that any
   non-nil delta is sound. Old shape-specific assertions are removed
   — they were checking the legacy `{:delta :add/:remove}` vocabulary
   that no longer exists. Property tests pin value correctness
   across arbitrary source/window pairs."
  (:refer-clojure :exclude [filter map reduce])
  #?(:clj
     (:require [clojure.test :refer [deftest is testing]]
               [clojure.test.check.clojure-test :refer [defspec]]
               [clojure.test.check.generators :as gen]
               [clojure.test.check.properties :as prop]
               [org.replikativ.spindel.incremental.algebra :as a]
               [org.replikativ.spindel.incremental.combinators :as ic]
               [org.replikativ.spindel.incremental.interval :as iv]
               [org.replikativ.spindel.incremental.sequence-algebra :as sa]
               [org.replikativ.spindel.test-helpers :as th])
     :cljs
     (:require [cljs.test :refer-macros [deftest is testing]])))

(defn- subvec-safe [v start end]
  (let [len (count v) s (max 0 (min start len)) e (max s (min end len))]
    (if (= s e) [] (subvec v s e))))

(def ^:private slice-loc {:file "slice-test" :line 1 :column 0})

;; =============================================================================
;; Basic projection
;; =============================================================================

#?(:clj
   (deftest slice-projection
     (testing "slice* projects a window of the source"
       (th/with-ctx [_ctx]
         (let [src (iv/interval nil [1 2 3 4 5] nil)]
           (is (= [3 4] (iv/get-new (ic/slice* slice-loc {:start 2 :end 4} src))))
           (is (= [] (iv/get-new (ic/slice* slice-loc {:start 0 :end 0} src))))
           (is (= [1 2 3 4 5] (iv/get-new (ic/slice* slice-loc {:start 0 :end 10} src)))))))))

#?(:clj
   (deftest slice-bounds-clamping
     (testing "Out-of-range bounds are clamped, not exceptions"
       (th/with-ctx [_ctx]
         (let [src (iv/interval nil [1 2 3] nil)]
           (is (= [1 2 3] (iv/get-new (ic/slice* slice-loc {:start -5 :end 100} src))))
           (is (= [] (iv/get-new (ic/slice* slice-loc {:start 100 :end 200} src))))
           (is (= [] (iv/get-new (ic/slice* slice-loc {:start 5 :end 2} src))))
           ;; Empty source.
           (is (= [] (iv/get-new (ic/slice* slice-loc {:start 0 :end 10}
                                            (iv/interval nil [] nil))))))))))

;; =============================================================================
;; Window changes
;; =============================================================================

#?(:clj
   (deftest slice-window-changes
     (testing "Changing the window updates the slice"
       (th/with-ctx [_ctx]
         (let [loc {:file "win" :line 1 :column 0}
               r1 (ic/slice* loc {:start 0 :end 3} (iv/interval nil [1 2 3 4 5] nil))
               r2 (ic/slice* loc {:start 1 :end 4} (iv/interval [1 2 3 4 5] [1 2 3 4 5] []))]
           (is (= [1 2 3] (iv/get-new r1)))
           (is (= [2 3 4] (iv/get-new r2))))))))

;; =============================================================================
;; Source changes
;; =============================================================================

#?(:clj
   (deftest slice-source-changes
     (testing "Source changes propagate through the slice"
       (th/with-ctx [_ctx]
         (let [loc {:file "src-change" :line 1 :column 0}
               win {:start 0 :end 3}
               r1 (ic/slice* loc win (iv/interval nil [1 2 3 4] nil))
               r2 (ic/slice* loc win (iv/interval [1 2 3 4] [1 2 3 4 5] nil))]
           (is (= [1 2 3] (iv/get-new r1)))
           (is (= [1 2 3] (iv/get-new r2))
               "Appending past the window is invisible")
           (let [r3 (ic/slice* loc win (iv/interval [1 2 3 4 5] [10 2 3 4 5] nil))]
             (is (= [10 2 3] (iv/get-new r3))
                 "Changes within the window are reflected")))))))

;; =============================================================================
;; Delta soundness
;; =============================================================================

#?(:clj
   (deftest slice-delta-soundness
     (testing "When slice* emits non-nil deltas, they are sound"
       (th/with-ctx [_ctx]
         (let [loc {:file "sd" :line 1 :column 0}
               win {:start 1 :end 4}
               _ (ic/slice* loc win (iv/interval nil [1 2 3 4 5 6] nil))
               r2 (ic/slice* loc win (iv/interval [1 2 3 4 5 6] [1 9 3 4 5 6] nil))
               d (iv/get-deltas r2)]
           (when d
             (is (= (iv/get-new r2)
                    (a/apply-deltas sa/sequence-algebra (iv/get-old r2) d)))))))))

;; =============================================================================
;; No-change short-circuit
;; =============================================================================

#?(:clj
   (deftest slice-no-change
     (testing "Verified-no-change source + unchanged window emits verified-no-change"
       (th/with-ctx [_ctx]
         (let [loc {:file "nc" :line 1 :column 0}
               win {:start 0 :end 3}
               _ (ic/slice* loc win (iv/interval nil [1 2 3 4 5] nil))
               r (ic/slice* loc win (iv/interval [1 2 3 4 5] [1 2 3 4 5] []))]
           (is (iv/no-change? r)))))))

;; =============================================================================
;; Property tests
;; =============================================================================

#?(:clj
   (def ^:private gen-window-pair
     (gen/let [start (gen/choose 0 10)
               end (gen/large-integer* {:min start :max (+ start 10)})]
       {:start start :end end})))

#?(:clj
   (defspec slice*-equals-subvec 100
     (prop/for-all [src (gen/vector gen/small-integer 0 15)
                    w gen-window-pair]
                   (th/with-ctx [_ctx]
                     (let [loc {:file "sp" :line 1 :column 0}
                           r (ic/slice* loc w (iv/interval nil src nil))]
                       (= (subvec-safe src (:start w) (:end w))
                          (iv/get-new r)))))))

#?(:clj
   (defspec slice*-source-change-correctness 100
     (prop/for-all [pre (gen/vector gen/small-integer 0 10)
                    post (gen/vector gen/small-integer 0 10)
                    w gen-window-pair]
                   (th/with-ctx [_ctx]
                     (let [loc {:file "scc" :line 1 :column 0}
                           _ (ic/slice* loc w (iv/interval nil pre nil))
                           r (ic/slice* loc w (iv/interval pre post nil))]
                       (= (subvec-safe post (:start w) (:end w))
                          (iv/get-new r)))))))

#?(:clj
   (defspec slice*-delta-soundness 100
     (prop/for-all [pre (gen/vector gen/small-integer 0 10)
                    post (gen/vector gen/small-integer 0 10)
                    w gen-window-pair]
                   (th/with-ctx [_ctx]
                     (let [loc {:file "sds" :line 1 :column 0}
                           _ (ic/slice* loc w (iv/interval nil pre nil))
                           r (ic/slice* loc w (iv/interval pre post nil))
                           d (iv/get-deltas r)]
                       (or (nil? d)
                           (= (iv/get-new r)
                              (a/apply-deltas sa/sequence-algebra (iv/get-old r) d))))))))
