(ns org.replikativ.spindel.v2.creation-key-test
  "§5.2 creation keys: a computation's body-created sources are keyed by
   site and per-run ordinal; a run re-entered after a breakpoint restores the
   ordinals of the creations it keeps and readopts the later ones by key."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [org.replikativ.spindel.v2.core :as v2 :refer [spin track]]
            #?(:clj [org.replikativ.spindel.v2.port.helpers :refer [checked-fixture]])))

;; no time slice: an inline operation completes before it returns however
;; slow the host is (#363's default 5 ms slice can spill a slow turn, and a
;; synchronous read would see it pending)
(use-fixtures :each
  #?(:clj checked-fixture
     :cljs (fn [f] (let [w (v2/world {:slice-ms nil})]
                     (try (binding [v2/*world* w] (f)) (finally (v2/release-world! w)))))))

(defn- now
  "The settled value of `h`. CLJS inline worlds without a time
   slice settle synchronously."
  [h]
  #?(:clj (v2/value h 1000 ::timeout)
     :cljs (let [a (atom ::pending)]
             (v2/value-async h (fn [v _err?] (reset! a v)))
             @a)))

(defn- values [hs] (mapv now hs))

(deftest a-source-created-after-a-re-entered-breakpoint-keeps-its-own-key
  ;; Body sources use site -1, so their keys are negative. Two creations before
  ;; the track give the kept prefix an ordinal above 0, which the restored
  ;; count for site -1 must continue from.
  (let [top (v2/signal 0)
        mid (v2/signal 0)
        c (spin (track top)
                (let [a (v2/signal :a) b (v2/signal :b)]
                  (track mid)
                  [a b (v2/signal :x)]))
        stop (v2/observe! c (fn [_ _]))]
    (try
      (let [[_ _ x] (now c)]
        (v2/write! x :written)
        (v2/write! mid 1)              ; re-enters at the track of mid, keeps a and b
        (is (= [:a :b :written] (values (now c)))
            "re-entry readopts the third source, not the second")
        (v2/write! top 1)              ; runs again from the start, readopting all three
        (is (= [:a :b :written] (values (now c)))
            "a later full run still finds the third source by its key"))
      (finally (stop)))))
