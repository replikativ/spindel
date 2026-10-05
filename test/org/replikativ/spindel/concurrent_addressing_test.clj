(ns org.replikativ.spindel.concurrent-addressing-test
  "Spins built on several threads at once, off the drain (an embedder's
   worker threads): every one gets its own id and completes."
  (:refer-clojure :exclude [await])
  (:require [clojure.test :refer [deftest is]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.engine.addressing :as a]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.test-helpers :refer [with-ctx]])
  (:import [java.util.concurrent CountDownLatch]))

(defn- build-at-once
  "Build one spin per thread on `threads` threads released together; the
   spins, in thread order."
  [ctx threads make]
  (let [latch (CountDownLatch. 1)
        fs (doall (for [_ (range threads)]
                    (future (binding [ec/*execution-context* ctx]
                              (.await latch)
                              (make)))))]
    (.countDown latch)
    (mapv deref fs)))

(deftest spins-built-at-once-get-distinct-ids
  (with-ctx [ctx]
    (dotimes [_ 50]
      (let [spins (build-at-once ctx 8 #(spin 1))]
        (is (= 8 (count (set (map spin-core/spin-id spins)))))))))

(deftest spins-spawned-at-once-all-complete
  ;; the shape that lost completions: worker threads each create a deferred
  ;; another thread delivers at once, and spawn a spin awaiting it
  (with-ctx [ctx]
    (let [n 200
          ps (vec (repeatedly n promise))
          ws (doall (for [i (range n)]
                      (future
                        (binding [ec/*execution-context* ctx]
                          (let [d (sync/deferred)]
                            (future (binding [ec/*execution-context* ctx] (sync/deliver! d i)))
                            (sync/spawn! (spin (inc (await d)))
                                         {:on-success #(deliver (ps i) %)
                                          :on-error #(deliver (ps i) [:error %])}))))))]
      (run! deref ws)
      (is (= (mapv inc (range n)) (mapv #(deref % 5000 ::lost) ps))))))

(deftest a-fork-mints-from-the-cursors-it-inherits
  ;; the fork copies :chain-heads on its first local seed; cursors the parent
  ;; seeds afterwards are read through from the parent, and minting must hash
  ;; from them (not from nil, which gave two spins one id)
  (let [parent (ctx/create-execution-context)
        child (ctx/fork-context parent)]
    (try
      (a/seed-body-chain-head! child :already-local)
      (a/seed-body-chain-head! parent :b)
      (a/seed-body-chain-head! parent :c)
      (let [mint (fn [sid]
                   (binding [ec/*spin-id* sid]
                     (let [head (a/get-chain-head child)]
                       [(keyword (str "spin-" (a/chain-hash [:same-site] head)))
                        (a/next-address! child "spin" [:same-site])])))
            [expected-b b] (mint :b)
            [expected-c c] (mint :c)]
        (is (= expected-b b))
        (is (= expected-c c))
        (is (not= b c)))
      (finally (ctx/stop-context! parent)))))
