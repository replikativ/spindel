(ns org.replikativ.spindel.engine.node-protocols-test
  "Unit tests for node protocols and node type implementations."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.nodes :as nodes]))

;; =============================================================================
;; SignalNode Tests
;; =============================================================================

(deftest test-signal-node-creation
  (testing "SignalNode creation and PNode protocol"
    (let [node (nodes/->signal-node 42 nil [] false #{})]
      (is (= :signal (nodes/node-type node)))
      (is (= 42 (nodes/get-value node)))
      (is (= #{} (nodes/get-observers node))))))

(deftest test-signal-node-with-delta-tracking
  (testing "SignalNode with delta tracking enabled"
    (let [node (nodes/->signal-node [1 2 3]
                                  [1 2]
                                  [{:op :conj :value 3}]
                                  true
                                  #{})]
      (is (= :signal (nodes/node-type node)))
      (is (= [1 2 3] (nodes/get-value node)))
      (is (= [1 2] (:old-snapshot node)))
      (is (= [{:op :conj :value 3}] (:deltas node)))
      (is (true? (:deltaable? node))))))

(deftest test-signal-node-observers
  (testing "SignalNode observer management (PObservable)"
    (let [node (nodes/->signal-node 42 nil [] false #{})
          node' (nodes/add-observer node :spin-1)]

      (is (= #{:spin-1} (nodes/get-observers node')))
      (is (= #{} (nodes/get-observers node))  ; Original unchanged (immutability)

      (let [node'' (nodes/add-observer node' :spin-2)]
        (is (= #{:spin-1 :spin-2} (nodes/get-observers node'')))

        (let [node''' (nodes/remove-observer node'' :spin-1)]
          (is (= #{:spin-2} (nodes/get-observers node''')))))))))

(deftest test-signal-node-no-dependencies
  (testing "SignalNode has no dependencies (PDependent)"
    (let [node (nodes/->signal-node 42 nil [] false #{})]
      (is (false? (nodes/has-deps? node)))
      (is (= {:signals #{} :spins #{}} (nodes/get-deps node)))

      ;; set-deps is a no-op for signals
      (let [node' (nodes/set-deps node {:signals #{:sig-1} :spins #{:spin-1}})]
        (is (= {:signals #{} :spins #{}} (nodes/get-deps node')))))))

(deftest test-signal-node-always-clean
  (testing "SignalNode is always clean (PCacheable)"
    (let [node (nodes/->signal-node 42 nil [] false #{})]
      (is (false? (nodes/dirty? node)))
      (is (true? (nodes/clean? node)))

      ;; mark-dirty is a no-op for signals
      (let [node' (nodes/mark-dirty node)]
        (is (false? (nodes/dirty? node')))
        (is (true? (nodes/clean? node'))))

      ;; mark-clean is a no-op for signals
      (let [node' (nodes/mark-clean node)]
        (is (false? (nodes/dirty? node')))
        (is (true? (nodes/clean? node')))))))

;; =============================================================================
;; SpinNode Tests
;; =============================================================================

(deftest test-spin-node-creation
  (testing "SpinNode creation and PNode protocol"
    (let [result {:status :ok :value 42}
          node (nodes/->spin-node result :clean false false #{} {} nil #{})]
      (is (= :spin (nodes/node-type node)))
      (is (= result (nodes/get-value node)))
      (is (= #{} (nodes/get-observers node))))))

(deftest test-spin-node-observers
  (testing "SpinNode observer management (PObservable)"
    (let [node (nodes/->spin-node nil :clean false false #{} {} nil #{})
          node' (nodes/add-observer node :spin-2)]

      (is (= #{:spin-2} (nodes/get-observers node')))
      (is (= #{} (nodes/get-observers node))  ; Original unchanged (immutability)

      (let [node'' (nodes/add-observer node' :spin-3)]
        (is (= #{:spin-2 :spin-3} (nodes/get-observers node'')))

        (let [node''' (nodes/remove-observer node'' :spin-2)]
          (is (= #{:spin-3} (nodes/get-observers node''')))))))))

(deftest test-spin-node-dependencies
  (testing "SpinNode dependency management (PDependent)"
    (let [node (nodes/->spin-node nil :clean false false #{} {} nil #{})
          deps {:signals #{:sig-1} :spins #{:spin-0}}
          node' (nodes/set-deps node deps)]

      (is (true? (nodes/has-deps? node')))
      (is (= deps (nodes/get-deps node'))))))

(deftest test-spin-node-no-dependencies
  (testing "SpinNode with no dependencies"
    (let [node (nodes/->spin-node nil :clean false false #{} {} nil #{})]
      (is (false? (nodes/has-deps? node)))
      (is (= {:signals #{} :spins #{}} (nodes/get-deps node))))))

(deftest test-spin-node-caching
  (testing "SpinNode dirty/clean state (PCacheable)"
    (let [node (nodes/->spin-node nil :clean false false #{} {} nil #{})
          dirty-node (nodes/mark-dirty node)]

      (is (true? (nodes/clean? node)))
      (is (false? (nodes/dirty? node)))

      (is (true? (nodes/dirty? dirty-node)))
      (is (false? (nodes/clean? dirty-node)))

      (let [clean-node (nodes/mark-clean dirty-node)]
        (is (true? (nodes/clean? clean-node)))
        (is (false? (nodes/dirty? clean-node)))))))

(deftest test-spin-node-initially-clean
  (testing "SpinNode created with :clean status"
    (let [node (nodes/->spin-node nil :clean false false #{} {} nil #{})]
      (is (true? (nodes/clean? node)))
      (is (false? (nodes/dirty? node))))))

(deftest test-spin-node-initially-dirty
  (testing "SpinNode created with :dirty status"
    (let [node (nodes/->spin-node nil :dirty false false #{} {} nil #{})]
      (is (false? (nodes/clean? node)))
      (is (true? (nodes/dirty? node))))))

;; =============================================================================
;; Protocol Immutability Tests
;; =============================================================================

(deftest test-protocol-methods-are-pure
  (testing "All protocol methods return new nodes, don't mutate"
    (let [sig-node (nodes/->signal-node 42 nil [] false #{})
          spin-node (nodes/->spin-node nil :clean false false #{} {} nil #{})]

      ;; add-observer doesn't mutate
      (let [sig-node' (nodes/add-observer sig-node :spin-1)]
        (is (= #{} (nodes/get-observers sig-node)))
        (is (= #{:spin-1} (nodes/get-observers sig-node'))))

      (let [spin-node' (nodes/add-observer spin-node :spin-2)]
        (is (= #{} (nodes/get-observers spin-node)))
        (is (= #{:spin-2} (nodes/get-observers spin-node'))))

      ;; mark-dirty doesn't mutate
      (let [spin-node' (nodes/mark-dirty spin-node)]
        (is (true? (nodes/clean? spin-node)))
        (is (true? (nodes/dirty? spin-node'))))

      ;; set-deps doesn't mutate
      (let [deps {:signals #{:sig-1} :spins #{}}
            spin-node' (nodes/set-deps spin-node deps)]
        (is (= {:signals #{} :spins #{}} (nodes/get-deps spin-node)))
        (is (= deps (nodes/get-deps spin-node')))))))

;; =============================================================================
;; Constructor Function Tests
;; =============================================================================

(deftest test-signal-node-constructor-defaults
  (testing "->signal-node with default observers"
    (let [node (nodes/->signal-node 42 nil [] false)]
      (is (= #{} (nodes/get-observers node))))))

(deftest test-signal-node-constructor-with-observers
  (testing "->signal-node with explicit observers"
    (let [node (nodes/->signal-node 42 nil [] false #{:spin-1 :spin-2})]
      (is (= #{:spin-1 :spin-2} (nodes/get-observers node))))))
