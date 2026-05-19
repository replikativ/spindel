(ns org.replikativ.spindel.pubsub.buffer-test
  "Tests for pub/sub buffer implementations."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.pubsub.buffer :as buf]))

;; =============================================================================
;; Fixed Buffer Tests
;; =============================================================================

(deftest test-fixed-buffer-basic
  (testing "fixed buffer stores and retrieves items FIFO"
    (let [b (buf/fixed-buffer 3)]
      (is (= 0 (count b)))
      (is (not (buf/full? b)))

      (buf/add! b :a)
      (is (= 1 (count b)))

      (buf/add! b :b)
      (buf/add! b :c)
      (is (= 3 (count b)))
      (is (buf/full? b))

      ;; FIFO order
      (is (= :a (buf/remove! b)))
      (is (= :b (buf/remove! b)))
      (is (= :c (buf/remove! b)))
      (is (= 0 (count b))))))

(deftest test-fixed-buffer-full
  (testing "fixed buffer reports full correctly"
    (let [b (buf/fixed-buffer 2)]
      (is (not (buf/full? b)))
      (buf/add! b :a)
      (is (not (buf/full? b)))
      (buf/add! b :b)
      (is (buf/full? b)))))

(deftest test-fixed-buffer-is-blocking
  (testing "fixed buffer is not unblocking"
    (let [b (buf/fixed-buffer 10)]
      (is (not (buf/unblocking? b))))))

;; =============================================================================
;; Dropping Buffer Tests
;; =============================================================================

(deftest test-dropping-buffer-basic
  (testing "dropping buffer drops new items when full"
    (let [b (buf/dropping-buffer 2)]
      (buf/add! b :a)
      (buf/add! b :b)
      (buf/add! b :c)  ; Should be dropped

      (is (= 2 (count b)))
      (is (= :a (buf/remove! b)))
      (is (= :b (buf/remove! b)))
      (is (nil? (buf/remove! b))))))

(deftest test-dropping-buffer-never-full
  (testing "dropping buffer never reports full"
    (let [b (buf/dropping-buffer 2)]
      (is (not (buf/full? b)))
      (buf/add! b :a)
      (buf/add! b :b)
      (is (not (buf/full? b)))  ; Still not full
      (buf/add! b :c)
      (is (not (buf/full? b))))))

(deftest test-dropping-buffer-is-unblocking
  (testing "dropping buffer is unblocking"
    (let [b (buf/dropping-buffer 10)]
      (is (buf/unblocking? b)))))

;; =============================================================================
;; Sliding Buffer Tests
;; =============================================================================

(deftest test-sliding-buffer-basic
  (testing "sliding buffer slides out oldest items when full"
    (let [b (buf/sliding-buffer 2)]
      (buf/add! b :a)
      (buf/add! b :b)
      (buf/add! b :c)  ; Should push out :a

      (is (= 2 (count b)))
      (is (= :b (buf/remove! b)))
      (is (= :c (buf/remove! b)))
      (is (nil? (buf/remove! b))))))

(deftest test-sliding-buffer-never-full
  (testing "sliding buffer never reports full"
    (let [b (buf/sliding-buffer 2)]
      (is (not (buf/full? b)))
      (buf/add! b :a)
      (buf/add! b :b)
      (is (not (buf/full? b)))  ; Still not full
      (buf/add! b :c)
      (is (not (buf/full? b))))))

(deftest test-sliding-buffer-is-unblocking
  (testing "sliding buffer is unblocking"
    (let [b (buf/sliding-buffer 10)]
      (is (buf/unblocking? b)))))

(deftest test-sliding-buffer-sliding-behavior
  (testing "sliding buffer maintains newest items"
    (let [b (buf/sliding-buffer 3)]
      ;; Add 5 items to a buffer of size 3
      (doseq [x (range 5)]
        (buf/add! b x))

      ;; Should have [2, 3, 4] - the newest 3
      (is (= 3 (count b)))
      (is (= 2 (buf/remove! b)))
      (is (= 3 (buf/remove! b)))
      (is (= 4 (buf/remove! b))))))

;; =============================================================================
;; Buffer Empty Tests
;; =============================================================================

(deftest test-buffer-empty?
  (testing "buffer-empty? works correctly"
    (let [b (buf/fixed-buffer 3)]
      (is (buf/buffer-empty? b))
      (buf/add! b :a)
      (is (not (buf/buffer-empty? b)))
      (buf/remove! b)
      (is (buf/buffer-empty? b)))))
