(ns org.replikativ.spindel.runtime.node-protocols-test
  "Unit tests for node protocols and node type implementations."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.runtime.node-protocols :as np]
            [org.replikativ.spindel.runtime.node-types :as nt]))

;; =============================================================================
;; SignalNode Tests
;; =============================================================================

(deftest test-signal-node-creation
  (testing "SignalNode creation and PNode protocol"
    (let [node (nt/->signal-node 42 nil [] false #{})]
      (is (= :signal (np/node-type node)))
      (is (= 42 (np/get-value node)))
      (is (= #{} (np/get-observers node))))))

(deftest test-signal-node-with-delta-tracking
  (testing "SignalNode with delta tracking enabled"
    (let [node (nt/->signal-node [1 2 3]
                                  [1 2]
                                  [{:op :conj :value 3}]
                                  true
                                  #{})]
      (is (= :signal (np/node-type node)))
      (is (= [1 2 3] (np/get-value node)))
      (is (= [1 2] (:old-snapshot node)))
      (is (= [{:op :conj :value 3}] (:deltas node)))
      (is (true? (:deltaable? node))))))

(deftest test-signal-node-observers
  (testing "SignalNode observer management (PObservable)"
    (let [node (nt/->signal-node 42 nil [] false #{})
          node' (np/add-observer node :spin-1)]

      (is (= #{:spin-1} (np/get-observers node')))
      (is (= #{} (np/get-observers node))  ; Original unchanged (immutability)

      (let [node'' (np/add-observer node' :spin-2)]
        (is (= #{:spin-1 :spin-2} (np/get-observers node'')))

        (let [node''' (np/remove-observer node'' :spin-1)]
          (is (= #{:spin-2} (np/get-observers node''')))))))))

(deftest test-signal-node-no-dependencies
  (testing "SignalNode has no dependencies (PDependent)"
    (let [node (nt/->signal-node 42 nil [] false #{})]
      (is (false? (np/has-deps? node)))
      (is (= {:signals #{} :spins #{}} (np/get-deps node)))
      (is (nil? (np/get-deps-hash node)))
      (is (= {:signal-generations {} :spin-hashes {}} (np/get-deps-values node)))

      ;; set-deps is a no-op for signals
      (let [node' (np/set-deps node {:signals #{:sig-1} :spins #{:spin-1}})]
        (is (= {:signals #{} :spins #{}} (np/get-deps node'))))

      ;; set-deps-hash is a no-op for signals
      (let [node' (np/set-deps-hash node #uuid "550e8400-e29b-41d4-a716-446655440000")]
        (is (nil? (np/get-deps-hash node')))))))

(deftest test-signal-node-always-clean
  (testing "SignalNode is always clean (PCacheable)"
    (let [node (nt/->signal-node 42 nil [] false #{})]
      (is (false? (np/dirty? node)))
      (is (true? (np/clean? node)))

      ;; mark-dirty is a no-op for signals
      (let [node' (np/mark-dirty node)]
        (is (false? (np/dirty? node')))
        (is (true? (np/clean? node'))))

      ;; mark-clean is a no-op for signals
      (let [node' (np/mark-clean node)]
        (is (false? (np/dirty? node')))
        (is (true? (np/clean? node')))))))

;; =============================================================================
;; SpinNode Tests
;; =============================================================================

(deftest test-spin-node-creation
  (testing "SpinNode creation and PNode protocol"
    (let [result {:status :ok :value 42}
          node (nt/->spin-node result :clean false false #{} {} nil {} nil #{})]
      (is (= :spin (np/node-type node)))
      (is (= result (np/get-value node)))
      (is (= #{} (np/get-observers node))))))

(deftest test-spin-node-observers
  (testing "SpinNode observer management (PObservable)"
    (let [node (nt/->spin-node nil :clean false false #{} {} nil {} nil #{})
          node' (np/add-observer node :spin-2)]

      (is (= #{:spin-2} (np/get-observers node')))
      (is (= #{} (np/get-observers node))  ; Original unchanged (immutability)

      (let [node'' (np/add-observer node' :spin-3)]
        (is (= #{:spin-2 :spin-3} (np/get-observers node'')))

        (let [node''' (np/remove-observer node'' :spin-2)]
          (is (= #{:spin-3} (np/get-observers node''')))))))))

(deftest test-spin-node-dependencies
  (testing "SpinNode dependency management (PDependent)"
    (let [node (nt/->spin-node nil :clean false false #{} {} nil {} nil #{})
          deps {:signals #{:sig-1} :spins #{:spin-0}}
          node' (np/set-deps node deps)]

      (is (true? (np/has-deps? node')))
      (is (= deps (np/get-deps node')))

      ;; Test deps-hash
      (let [hash #uuid "550e8400-e29b-41d4-a716-446655440000"
            node'' (np/set-deps-hash node' hash)]
        (is (= hash (np/get-deps-hash node'')))

        ;; Test deps-values (now stores generations/hashes, not full values)
        (let [deps-vals {:signal-generations {:sig-1 5} :spin-hashes {:spin-0 #uuid "550e8400-e29b-41d4-a716-446655440000"}}
              node''' (assoc node'' :deps-values deps-vals)]
          (is (= deps-vals (np/get-deps-values node'''))))))))

(deftest test-spin-node-no-dependencies
  (testing "SpinNode with no dependencies"
    (let [node (nt/->spin-node nil :clean false false #{} {} nil {} nil #{})]
      (is (false? (np/has-deps? node)))
      (is (= {:signals #{} :spins #{}} (np/get-deps node)))
      (is (nil? (np/get-deps-hash node)))
      (is (= {:signal-generations {} :spin-hashes {}} (np/get-deps-values node))))))

(deftest test-spin-node-caching
  (testing "SpinNode dirty/clean state (PCacheable)"
    (let [node (nt/->spin-node nil :clean false false #{} {} nil {} nil #{})
          dirty-node (np/mark-dirty node)]

      (is (true? (np/clean? node)))
      (is (false? (np/dirty? node)))

      (is (true? (np/dirty? dirty-node)))
      (is (false? (np/clean? dirty-node)))

      (let [clean-node (np/mark-clean dirty-node)]
        (is (true? (np/clean? clean-node)))
        (is (false? (np/dirty? clean-node)))))))

(deftest test-spin-node-initially-clean
  (testing "SpinNode created with :clean status"
    (let [node (nt/->spin-node nil :clean false false #{} {} nil {} nil #{})]
      (is (true? (np/clean? node)))
      (is (false? (np/dirty? node))))))

(deftest test-spin-node-initially-dirty
  (testing "SpinNode created with :dirty status"
    (let [node (nt/->spin-node nil :dirty false false #{} {} nil {} nil #{})]
      (is (false? (np/clean? node)))
      (is (true? (np/dirty? node))))))

;; =============================================================================
;; Protocol Immutability Tests
;; =============================================================================

(deftest test-protocol-methods-are-pure
  (testing "All protocol methods return new nodes, don't mutate"
    (let [sig-node (nt/->signal-node 42 nil [] false #{})
          spin-node (nt/->spin-node nil :clean false false #{} {} nil {} nil #{})]

      ;; add-observer doesn't mutate
      (let [sig-node' (np/add-observer sig-node :spin-1)]
        (is (= #{} (np/get-observers sig-node)))
        (is (= #{:spin-1} (np/get-observers sig-node'))))

      (let [spin-node' (np/add-observer spin-node :spin-2)]
        (is (= #{} (np/get-observers spin-node)))
        (is (= #{:spin-2} (np/get-observers spin-node'))))

      ;; mark-dirty doesn't mutate
      (let [spin-node' (np/mark-dirty spin-node)]
        (is (true? (np/clean? spin-node)))
        (is (true? (np/dirty? spin-node'))))

      ;; set-deps doesn't mutate
      (let [deps {:signals #{:sig-1} :spins #{}}
            spin-node' (np/set-deps spin-node deps)]
        (is (= {:signals #{} :spins #{}} (np/get-deps spin-node)))
        (is (= deps (np/get-deps spin-node')))))))

;; =============================================================================
;; Constructor Function Tests
;; =============================================================================

(deftest test-signal-node-constructor-defaults
  (testing "->signal-node with default observers"
    (let [node (nt/->signal-node 42 nil [] false)]
      (is (= #{} (np/get-observers node))))))

(deftest test-signal-node-constructor-with-observers
  (testing "->signal-node with explicit observers"
    (let [node (nt/->signal-node 42 nil [] false #{:spin-1 :spin-2})]
      (is (= #{:spin-1 :spin-2} (np/get-observers node))))))
