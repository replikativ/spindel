(ns org.replikativ.spindel.v2.incremental.slice-test
  "`islice` of `v2.incremental` (phase-d design §4.2), ported from
   `incremental/slice_test.cljc`: `:new` is the input's new value sliced by
   the window's new value, `:old` the input's old value sliced by the
   window's old value, and any delta is sound. A plain window map is its own
   old value; a window interval without an old value gives no `:old`."
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

(defn- subvec-safe [v start end]
  (let [len (count v) s (max 0 (min start len)) e (max s (min end len))]
    (if (= s e) [] (subvec v s e))))

(defn- sound? [r]
  (= (iv/get-new r) (a/apply-deltas sa/sequence-algebra (iv/get-old r) (iv/get-deltas r))))

;; =============================================================================
;; Projection and clamping
;; =============================================================================

(deftest slice-projection
  (let [src (iv/interval nil [1 2 3 4 5] nil)]
    (is (= [3 4] (iv/get-new (ic/islice {:start 2 :end 4} src))))
    (is (= [] (iv/get-new (ic/islice {:start 0 :end 0} src))))
    (is (= [1 2 3 4 5] (iv/get-new (ic/islice {:start 0 :end 10} src))))
    (is (= sa/sequence-algebra (:algebra (ic/islice {:start 0 :end 1} src))))))

(deftest slice-bounds-clamping
  (let [src (iv/interval nil [1 2 3] nil)]
    (is (= [1 2 3] (iv/get-new (ic/islice {:start -5 :end 100} src))))
    (is (= [] (iv/get-new (ic/islice {:start 100 :end 200} src))))
    (is (= [] (iv/get-new (ic/islice {:start 5 :end 2} src))))
    (is (= [] (iv/get-new (ic/islice {:start 0 :end 10} (iv/interval nil [] nil)))))))

;; =============================================================================
;; Window changes
;; =============================================================================

(deftest slice-window-changes
  (testing "a window interval: old slice by the old window, new slice by the new one"
    (let [r (ic/islice (iv/interval {:start 0 :end 3} {:start 1 :end 4} nil)
                       (iv/interval [1 2 3 4 5] [1 2 3 4 5] []))]
      (is (= [1 2 3] (iv/get-old r)))
      (is (= [2 3 4] (iv/get-new r)))
      (is (sound? r))))
  (testing "a plain window that changes between calls is a parameter change:
            each output's :old uses the window of its own call"
    (let [src (iv/interval [1 2 3 4 5] [1 2 3 4 5] [])
          r1 (ic/islice {:start 0 :end 3} src)
          r2 (ic/islice {:start 1 :end 4} src)]
      (is (= [1 2 3] (iv/get-new r1)))
      (is (= [2 3 4] (iv/get-new r2)))
      (is (= [2 3 4] (iv/get-old r2)) "not r1's output")))
  (testing "a window interval with no old value gives no :old"
    (let [r (ic/islice (iv/interval nil {:start 0 :end 2} nil) (iv/interval [1 2 3] [1 2 3] []))]
      (is (= [1 2] (iv/get-new r)))
      (is (nil? (iv/get-old r)))
      (is (nil? (iv/get-deltas r))))))

;; =============================================================================
;; Source changes
;; =============================================================================

(deftest slice-source-changes
  (let [win {:start 0 :end 3}
        r1 (ic/islice win (iv/interval nil [1 2 3 4] nil))
        r2 (ic/islice win (iv/interval [1 2 3 4] [1 2 3 4 5] nil))
        r3 (ic/islice win (iv/interval [1 2 3 4 5] [10 2 3 4 5] nil))]
    (is (= [1 2 3] (iv/get-new r1)))
    (is (= [1 2 3] (iv/get-new r2)) "appending past the window is invisible")
    (is (iv/no-change? r2))
    (is (= [10 2 3] (iv/get-new r3)) "changes within the window are reflected")
    (is (sound? r3))))

(deftest slice-delta-soundness
  (is (sound? (ic/islice {:start 1 :end 4} (iv/interval [1 2 3 4 5 6] [1 9 3 4 5 6] nil)))))

;; =============================================================================
;; Properties
;; =============================================================================

(def ^:private gen-window
  (gen/let [start (gen/choose 0 10)
            end (gen/large-integer* {:min start :max (+ start 10)})]
    {:start start :end end}))

(defspec islice-equals-subvec 100
  (prop/for-all [src (gen/vector gen/small-integer 0 15) w gen-window]
                (= (subvec-safe src (:start w) (:end w))
                   (iv/get-new (ic/islice w (iv/interval nil src nil))))))

(defspec islice-source-change-correctness 100
  (prop/for-all [pre (gen/vector gen/small-integer 0 10)
                 post (gen/vector gen/small-integer 0 10)
                 w gen-window]
                (let [r (ic/islice w (iv/interval pre post nil))]
                  (and (= (subvec-safe post (:start w) (:end w)) (iv/get-new r))
                       (= (subvec-safe pre (:start w) (:end w)) (iv/get-old r))))))

(defspec islice-delta-soundness 100
  (prop/for-all [pre (gen/vector gen/small-integer 0 10)
                 post (gen/vector gen/small-integer 0 10)
                 w0 gen-window
                 w1 gen-window]
                (sound? (ic/islice (iv/interval w0 w1 nil) (iv/interval pre post nil)))))
