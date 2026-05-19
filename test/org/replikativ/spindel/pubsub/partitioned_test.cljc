(ns org.replikativ.spindel.pubsub.partitioned-test
  "Tests for partitioned pub-sub implementation."
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer [deftest is testing] :include-macros true])
            [org.replikativ.spindel.pubsub.partitioned :as pp]
            [org.replikativ.spindel.pubsub.buffer :as buf]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.spin.sync :as sync]
            [is.simm.partial-cps.sequence :refer [PAsyncSeq anext]]
            #?(:clj [org.replikativ.spindel.spin.cps :refer [spin]])
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.test-helpers :as th])
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]]
                            [org.replikativ.spindel.test-helpers :refer [async with-ctx]])))

;; =============================================================================
;; Helper: Simple vector-based async sequence
;; =============================================================================

(deftype VectorSeq [items-atom idx]
  PAsyncSeq
  (anext [_]
    (spin
     (let [items @items-atom]
       (when (< idx (count items))
         [(nth items idx) (VectorSeq. items-atom (inc idx))])))))

(defn vec->aseq [v]
  (VectorSeq. (atom v) 0))

;; =============================================================================
;; Tests
;; =============================================================================

(deftest test-partitioned-basic-routing
  (testing "Items are routed to correct partitions by hash"
    (th/async done
              (th/with-ctx [_ctx]
                (let [source (vec->aseq [{:word "hello"} {:word "world"} {:word "hello"} {:word "foo"}])
                      p (pp/partitioned 2 source :word
                                        :buf-fn (fn [_] (buf/fixed-buffer 16)))
              ;; Track items per partition
                      results (atom {0 [] 1 []})
                      taps-done (atom 0)
                      check-done! (fn []
                                    (when (= 2 @taps-done)
                              ;; All items should be accounted for
                                      (let [all-items (concat (get @results 0) (get @results 1))]
                                        (is (= 4 (count all-items)))
                                ;; Each "hello" goes to the same partition
                                        (let [hello-partition (bit-and (hash "hello") 1)]
                                          (is (= 2 (count (filter #(= "hello" (:word %))
                                                                  (get @results hello-partition))))))
                                        (done))))]
          ;; Tap both partitions
                  (doseq [i (range 2)]
                    (let [tap (pp/tap-partition p i)]
                      (th/run-spin!
                       (spin
                        (loop [s tap]
                          (if-let [[item rest-seq] (await (anext s))]
                            (do
                              (swap! results update i conj item)
                              (recur rest-seq))
                            (do
                              (swap! taps-done inc)
                              (check-done!)))))
                       (fn [_] nil)
                       (fn [e] (is false (str "Error: " e)) (done))))))))))

(deftest test-partitioned-power-of-2-assertion
  (testing "Partitioned requires power-of-2 partition count"
    (is (thrown? #?(:clj AssertionError :cljs js/Error)
                 (let [source (vec->aseq [])]
                   (pp/partitioned 3 source identity))))))

(deftest test-partition-post-direct
  (testing "partition-post! pushes items directly to partition sources"
    (th/async done
              (th/with-ctx [_ctx]
                (let [;; Create partitioned with a dummy source (never used)
                      dummy (sync/mailbox)
                      p (pp/partitioned 2 dummy :word
                                        :buf-fn (fn [_] (buf/fixed-buffer 16)))
                      results (atom [])
                      tap (pp/tap-partition p 0)]

          ;; Consumer on partition 0
                  (th/run-spin!
                   (spin
                    (loop [s tap count 0]
                      (if-let [[item rest-seq] (await (anext s))]
                        (do
                          (swap! results conj item)
                          (if (>= (inc count) 3)
                            @results
                            (recur rest-seq (inc count))))
                        @results)))
                   (fn [result]
                     (is (= 3 (count result)))
                     (is (every? #(= "test" (:word %)) result))
                     (done))
                   (fn [e] (is false (str "Error: " e)) (done)))

          ;; Post directly to partition 0
                  (pp/partition-post! p 0 {:word "test"})
                  (pp/partition-post! p 0 {:word "test"})
                  (pp/partition-post! p 0 {:word "test"})
          ;; Close after posting
                  (pp/close! p))))))

(deftest test-partitioned-close-cascades
  (testing "Closing partitioned cascades to all taps"
    (th/async done
              (th/with-ctx [_ctx]
                (let [dummy (sync/mailbox)
                      p (pp/partitioned 2 dummy identity
                                        :buf-fn (fn [_] (buf/fixed-buffer 16)))
                      tap0 (pp/tap-partition p 0)
                      tap1 (pp/tap-partition p 1)
                      taps-closed (atom 0)]
          ;; Start consumers that detect close
                  (doseq [tap [tap0 tap1]]
                    (th/run-spin!
                     (spin
                      (loop [s tap]
                        (if-let [[_item rest-seq] (await (anext s))]
                          (recur rest-seq)
                    ;; nil = closed
                          (swap! taps-closed inc))))
                     (fn [_]
                       (when (= 2 @taps-closed)
                         (is true "Both taps closed")
                         (done)))
                     (fn [e] (is false (str "Error: " e)) (done))))

          ;; Close immediately
                  (pp/close! p))))))

(deftest test-tap-all
  (testing "tap-all returns taps for all partitions"
    (th/async done
              (th/with-ctx [_ctx]
                (let [dummy (sync/mailbox)
                      p (pp/partitioned 4 dummy identity
                                        :buf-fn (fn [_] (buf/fixed-buffer 16)))
                      taps (pp/tap-all p)]
                  (is (= 4 (count taps)))
                  (pp/close! p)
                  (done))))))
