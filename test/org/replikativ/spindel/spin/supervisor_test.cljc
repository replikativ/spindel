(ns org.replikativ.spindel.spin.supervisor-test
  "Tests for supervisor spin implementation."
  (:require #?(:clj [clojure.test :refer [deftest is testing use-fixtures]]
               :cljs [cljs.test :refer [deftest is testing] :include-macros true])
            [org.replikativ.spindel.spin.supervisor :as sup]
            [org.replikativ.spindel.spin.sync :as sync :refer [spawn!]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            #?(:clj [org.replikativ.spindel.spin.cps :refer [spin]])
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.test-helpers :as th])
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]]
                            [cljs.test :refer [use-fixtures]]
                            [org.replikativ.spindel.test-helpers :refer [async with-ctx]])))

;; =============================================================================
;; Test Fixtures
;; =============================================================================

(defn with-execution-context [f]
  (let [c (ctx/create-execution-context)]
    (try
      (binding [ec/*execution-context* c]
        (f))
      (finally
        (ctx/stop-context! c)))))

(use-fixtures :each with-execution-context)

;; =============================================================================
;; Tests
;; =============================================================================

(deftest test-supervisor-spawns-children
  (testing "Supervisor starts all children"
    (th/async done
      (th/with-ctx [_ctx]
        (let [started (atom #{})
              children-done (atom 0)
              sup-spin (sup/supervisor
                         [{:id :child-1
                           :start (fn []
                                    (spin
                                      (swap! started conj :child-1)
                                      (swap! children-done inc)))}
                          {:id :child-2
                           :start (fn []
                                    (spin
                                      (swap! started conj :child-2)
                                      (swap! children-done inc)))}]
                         {:strategy :one-for-one
                          :max-restarts 3})]
          (spawn! sup-spin)
          ;; Wait for children to complete
          (simple/await-drain-complete! (ec/current-execution-context) :timeout-ms 5000)
          #?(:clj (Thread/sleep 100))  ;; Small delay for async completion
          (is (contains? @started :child-1))
          (is (contains? @started :child-2))
          (done))))))

(deftest test-supervisor-one-for-one-restart
  (testing "Supervisor restarts failed child with :one-for-one strategy"
    (th/async done
      (th/with-ctx [_ctx]
        (let [attempt-count (atom 0)
              success-result (atom nil)
              sup-spin (sup/supervisor
                         [{:id :flaky
                           :start (fn []
                                    (spin
                                      (let [n (swap! attempt-count inc)]
                                        (if (< n 3)
                                          (throw (ex-info "Flaky failure" {:attempt n}))
                                          (reset! success-result n)))))}]
                         {:strategy :one-for-one
                          :max-restarts 5
                          :window-ms 60000})]
          (spawn! sup-spin)
          ;; Wait for restarts to complete
          (simple/await-drain-complete! (ec/current-execution-context) :timeout-ms 5000)
          #?(:clj (Thread/sleep 500))  ;; Allow restart cycles
          (is (>= @attempt-count 3) "Should have attempted at least 3 times")
          (done))))))

(deftest test-supervisor-max-restarts-exceeded
  (testing "Supervisor calls on-fatal when max restarts exceeded"
    (th/async done
      (th/with-ctx [_ctx]
        (let [fatal-called (atom false)
              sup-spin (sup/supervisor
                         [{:id :always-fail
                           :start (fn []
                                    (spin (throw (ex-info "Always fails" {}))))}]
                         {:strategy :one-for-one
                          :max-restarts 2
                          :window-ms 60000
                          :on-fatal (fn [_e]
                                      (reset! fatal-called true))})]
          (spawn! sup-spin)
          ;; Wait for all restarts to exhaust
          (simple/await-drain-complete! (ec/current-execution-context) :timeout-ms 5000)
          #?(:clj (Thread/sleep 1000))  ;; Allow restart cycles + fatal
          (is @fatal-called "on-fatal should have been called")
          (done))))))
