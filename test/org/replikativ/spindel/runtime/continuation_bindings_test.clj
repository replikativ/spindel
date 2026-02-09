(ns org.replikativ.spindel.runtime.continuation-bindings-test
  "Integration tests for continuation capture/restore of dynamic bindings."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.runtime.core :as rtc]
            [org.replikativ.spindel.runtime.context :as ctx]
            [org.replikativ.spindel.runtime.impl.simple :as simple]
            [org.replikativ.spindel.spin.core :as spin]))

(deftest continuation-captures-bindings-test
  (testing "continuation-add! automatically captures bindings"
    (binding [rtc/*execution-context* (ctx/create-execution-context)
              rtc/*spin-id* :test-spin
              rtc/*worker-id* :test-worker
              rtc/*yield-handler* (fn [v _] v)]

      ;; Add a continuation
      (let [cont {:id :test-cont
                  :resolve-fn (fn [v] v)
                  :reject-fn (fn [e] e)}]

        (rtc/continuation-add! :test-spin cont)

        ;; Retrieve the continuation from runtime state
        ;; Continuations are stored at [:continuations spin-id cont-id]
        (let [all-conts (rtc/get-state [:continuations :test-spin])
              stored-cont (first (vals all-conts))]

          ;; Should have :bindings field
          (is (contains? stored-cont :bindings)
              "Continuation should have :bindings field")

          ;; Should have captured all bound vars (except *execution-context*)
          (let [bindings (:bindings stored-cont)]
            (is (nil? (get bindings #'rtc/*execution-context*))
                "Should NOT capture *execution-context* (avoids circular refs)")
            (is (= :test-spin (get bindings #'rtc/*spin-id*))
                "Should capture *spin-id*")
            (is (= :test-worker (get bindings #'rtc/*worker-id*))
                "Should capture *worker-id*")
            (is (fn? (get bindings #'rtc/*yield-handler*))
                "Should capture *yield-handler*")))))))

(deftest continuation-restores-bindings-test
  (testing "resume-continuation! automatically restores bindings"
    (let [ctx (ctx/create-execution-context)
          result-atom (atom nil)]

      (binding [rtc/*execution-context* ctx
                rtc/*spin-id* :outer-spin]

        ;; Create continuation with specific bindings
        (binding [rtc/*yield-handler* (fn [v _] (* 2 v))]
          (let [cont {:id :test-cont
                      :resolve-fn (fn [v] (reset! result-atom v))
                      :on-resume (fn [_rt] :resume-value)}]

            (rtc/continuation-add! :outer-spin cont)))

        ;; Now resume in a DIFFERENT binding context
        (binding [rtc/*execution-context* ctx
                  rtc/*spin-id* :different-spin
                  rtc/*yield-handler* nil]  ; Unbound

          (let [all-conts (rtc/get-state [:continuations :outer-spin])
                stored-cont (first (vals all-conts))
                captured-handler (atom nil)]

            ;; Resume continuation - should restore original bindings
            (simple/resume-continuation! ctx :outer-spin stored-cont
              (fn [value]
                ;; Inside resume-fn, bindings should be restored
                (reset! captured-handler rtc/*yield-handler*)
                :resumed))

            ;; Should have restored the yield-handler
            (is (fn? @captured-handler)
                "Should have restored *yield-handler* during resume")

            ;; Test that the restored handler works
            (when @captured-handler
              (is (= 10 (@captured-handler 5 nil))
                  "Restored *yield-handler* should work correctly"))))))))

(deftest continuation-bindings-cross-thread-test
  (testing "bindings work across thread boundaries"
    (let [ctx (ctx/create-execution-context)
          result-promise (promise)
          handler-promise (promise)]

      (binding [rtc/*execution-context* ctx
                rtc/*spin-id* :main-spin
                rtc/*yield-handler* (fn [v _] (str "handled: " v))]

        ;; Capture continuation on main thread
        (let [cont {:id :cross-thread-cont
                    :resolve-fn (fn [v] (deliver result-promise v))
                    :on-resume (fn [_rt] :thread-value)}]

          (rtc/continuation-add! :main-spin cont)))

      ;; Resume on a different thread (simulating async completion)
      (future
        (binding [rtc/*execution-context* ctx]
          (let [all-conts (rtc/get-state [:continuations :main-spin])
                stored-cont (first (vals all-conts))]
            (simple/resume-continuation! ctx :main-spin stored-cont
              (fn [value]
                ;; Capture the restored yield-handler
                (deliver handler-promise rtc/*yield-handler*)
                :done)))))

      ;; Wait for async completion
      (let [handler (deref handler-promise 1000 :timeout)]
        (is (fn? handler)
            "Should restore *yield-handler* even across threads")

        (when (fn? handler)
          (is (= "handled: test" (handler "test" nil))
              "Restored handler should work correctly"))))))

(deftest continuation-bindings-nil-safe-test
  (testing "handles continuations without :bindings field (backwards compat)"
    (let [ctx (ctx/create-execution-context)
          result-atom (atom nil)]

      (binding [rtc/*execution-context* ctx]
        ;; Manually create continuation WITHOUT :bindings field
        ;; Continuations are stored at [:continuations spin-id cont-id]
        (rtc/swap-state! [:continuations :compat-spin]
          (constantly {:old-cont {:id :old-cont
                                  :event-key nil
                                  :resolve-fn (fn [v] (reset! result-atom v))
                                  :on-resume (fn [_rt] :old-value)
                                  :order 1}}))

        ;; Resume should handle missing :bindings gracefully
        (let [all-conts (rtc/get-state [:continuations :compat-spin])
              cont (first (vals all-conts))]
          (is (nil? (:bindings cont))
              "Test setup: continuation should not have :bindings")

          (simple/resume-continuation! ctx :compat-spin cont
            (fn [value]
              ;; Call the continuation's resolve-fn with the value from :on-resume
              ((:resolve-fn cont) value)
              :resumed))

          (is (= :old-value @result-atom)
              "Should successfully resume continuation without :bindings"))))))
