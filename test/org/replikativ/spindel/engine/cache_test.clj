(ns org.replikativ.spindel.engine.cache-test
  "Tests for content-addressed caching"
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [org.replikativ.spindel.engine.cache :as cache]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.track :refer [track]]))

;; =============================================================================
;; Test Fixtures
;; =============================================================================

(defn clear-cache-fixture [f]
  "Clear global cache before each test"
  (cache/clear!)
  (f))

(use-fixtures :each clear-cache-fixture)

;; =============================================================================
;; Basic Cache Infrastructure Tests
;; =============================================================================

(deftest test-cache-initially-empty
  (testing "Global cache starts empty"
    (is (= 0 (:total-entries (cache/stats))))))

(deftest test-compute-deps-identity-deterministic
  (testing "Same generations produce same hash"
    (let [sig-gens {:sig-1 5 :sig-2 12}
          spin-hashes {:spin-a #uuid "00000000-0000-0000-0000-000000000001"}
          h1 (cache/compute-deps-identity sig-gens spin-hashes nil)
          h2 (cache/compute-deps-identity sig-gens spin-hashes nil)]
      (is (= h1 h2))
      (is (uuid? h1)))))

(deftest test-compute-deps-identity-different
  (testing "Different generations produce different hashes"
    (let [h1 (cache/compute-deps-identity {:sig-1 5} {} nil)
          h2 (cache/compute-deps-identity {:sig-1 6} {} nil)]
      (is (not= h1 h2)))))

(deftest test-cache-store-and-lookup
  (testing "Can store and retrieve from cache"
    (let [spin-id :test-spin
          deps-hash (cache/compute-deps-identity {:sig-1 5} {} nil)
          result {:status :ok :value 100 :completed? true}]

      ;; Store
      (cache/store! spin-id deps-hash nil result)

      ;; Lookup
      (is (= result (cache/lookup spin-id deps-hash nil)))

      ;; Stats
      (is (= 1 (:total-entries (cache/stats)))))))

;; =============================================================================
;; Spin Execution with Caching Tests
;; =============================================================================

(deftest test-spin-without-dependencies-no-cache
  (testing "Spin without dependencies doesn't use global cache"
    (let [ctx (ctx/create-execution-context)
          executed (atom 0)]

      (binding [ec/*execution-context* ctx]
        (let [my-spin (spin
                        (do
                          (swap! executed inc)
                          42))]

          ;; First execution
          (is (= 42 @my-spin))
          (is (= 1 @executed))

          ;; Second execution (local cache hit, not global)
          (is (= 42 @my-spin))
          (is (= 1 @executed)) ; Should not re-execute

          ;; Global cache should still be empty (no dependencies)
          (is (= 0 (:total-entries (cache/stats)))))))))

(deftest test-spin-with-signal-dependency-uses-cache
  (testing "Spin with signal dependency stores in global cache"
    (let [ctx (ctx/create-execution-context)
          executed (atom 0)]

      (binding [ec/*execution-context* ctx]
        (let [sig (sig/signal 42)
              my-spin (spin
                        (let [{:keys [new]} (track sig)]
                          (swap! executed inc)
                          (+ new 1)))]

          ;; First execution
          (is (= 43 @my-spin))
          (is (= 1 @executed))

          ;; Cache should have one entry now
          (is (= 1 (:total-entries (cache/stats))))

          ;; Second execution with SAME signal value uses LOCAL cache
          (is (= 43 @my-spin))
          (is (= 1 @executed)) ; Should not re-execute

          ;; Still just one global cache entry
          (is (= 1 (:total-entries (cache/stats)))))))))

(deftest test-different-signal-values-different-cache-entries
  (testing "Different signal values create different cache entries"
    (let [ctx (ctx/create-execution-context)]

      (binding [ec/*execution-context* ctx]
        (let [sig-1 (sig/signal 42)
              executed-1 (atom 0)
              spin-1 (spin
                       (let [{:keys [new]} (track sig-1)]
                         (swap! executed-1 inc)
                         (+ new 1)))]

          ;; First spin execution with sig=42
          (is (= 43 @spin-1))
          (is (= 1 @executed-1))
          (is (= 1 (:total-entries (cache/stats))))

          ;; Create second spin with DIFFERENT signal value
          (let [sig-2 (sig/signal 99)
                executed-2 (atom 0)
                spin-2 (spin
                         (let [{:keys [new]} (track sig-2)]
                           (swap! executed-2 inc)
                           (+ new 1)))]

            ;; Second spin execution with sig=99
            (is (= 100 @spin-2))
            (is (= 1 @executed-2))

            ;; Should have TWO cache entries now (different signal values)
            (is (= 2 (:total-entries (cache/stats))))))))))

;; =============================================================================
;; Cache Isolation and Reuse Tests
;; =============================================================================

(deftest test-cache-per-spin-id-isolation
  (testing "Different spin instances have separate cache entries (per-spin-id isolation)"
    (let [ctx (ctx/create-execution-context)
          executed-1 (atom 0)
          executed-2 (atom 0)]

      (binding [ec/*execution-context* ctx]
        (let [sig (sig/signal 42)]
        ;; Create first spin that depends on signal
        (let [spin-1 (spin
                       (let [{:keys [new]} (track sig)]
                         (swap! executed-1 inc)
                         (* new 2)))]

          ;; Execute first spin
          (is (= 84 @spin-1))
          (is (= 1 @executed-1))
          (is (= 1 (:total-entries (cache/stats)))))

        ;; Create DIFFERENT spin with SAME dependencies
        ;; Cache key includes spin-id, so different spins have separate entries
        (let [spin-2 (spin
                       (let [{:keys [new]} (track sig)]
                         (swap! executed-2 inc)
                         (* new 2)))]

          ;; Execute second spin - has different spin-id, so separate cache entry
          (is (= 84 @spin-2))

          ;; spin-2 has different spin-id, so it WILL execute (not a cache hit)
          (is (= 1 @executed-2) "Different spin-id means separate cache entry")

          ;; Two cache entries now (one per spin-id)
          (is (= 2 (:total-entries (cache/stats))))))))))

(deftest test-same-spin-same-deps-uses-cache
  (testing "Same spin instance with same dependencies uses cache"
    (let [ctx (ctx/create-execution-context)
          executed (atom 0)]

      (binding [ec/*execution-context* ctx]
        (let [sig (sig/signal 10)]
        (let [my-spin (spin
                        (let [{:keys [new]} (track sig)]
                          (swap! executed inc)
                          (* new 2)))]

          ;; First execution
          (is (= 20 @my-spin))
          (is (= 1 @executed))
          (is (= 1 (:total-entries (cache/stats))))

          ;; Second execution - same spin, same deps, uses LOCAL cache
          (is (= 20 @my-spin))
          (is (= 1 @executed) "Should use local cache, not re-execute")

          ;; Still one global cache entry
          (is (= 1 (:total-entries (cache/stats))))))))))

;; =============================================================================
;; Cache Debugging Helpers Tests
;; =============================================================================

(deftest test-cache-for-spin
  (testing "Can retrieve all cache entries for a specific spin"
    (let [spin-id :test-spin
          deps-hash-1 (cache/compute-deps-identity {:sig-1 42} {} nil)
          deps-hash-2 (cache/compute-deps-identity {:sig-1 99} {} nil)
          result-1 {:status :ok :value 100}
          result-2 {:status :ok :value 200}]

      (cache/store! spin-id deps-hash-1 nil result-1)
      (cache/store! spin-id deps-hash-2 nil result-2)

      (let [entries (cache/cache-for-spin spin-id)]
        (is (= 2 (count entries)))
        (is (= result-1 (get entries deps-hash-1)))
        (is (= result-2 (get entries deps-hash-2)))))))

(deftest test-cache-evict
  (testing "Can evict specific cache entry"
    (let [spin-id :test-spin
          deps-hash (cache/compute-deps-identity {:sig-1 42} {} nil)
          result {:status :ok :value 100}]

      (cache/store! spin-id deps-hash nil result)
      (is (= 1 (:total-entries (cache/stats))))

      ;; Evict
      (is (true? (cache/evict! spin-id deps-hash nil)))
      (is (= 0 (:total-entries (cache/stats))))

      ;; Evicting again returns false
      (is (false? (cache/evict! spin-id deps-hash nil))))))
