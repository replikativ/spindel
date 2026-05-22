(ns org.replikativ.spindel.engine.continuation-bindings-test
  "Integration tests for continuation capture/restore of dynamic bindings."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.spin.core :as spin]
            [org.replikativ.spindel.test-helpers :as th]))

(deftest continuation-captures-bindings-test
  (testing "continuation-add! automatically captures bindings"
    (th/with-ctx [ctx]
      (binding [ec/*spin-id* :test-spin
                ec/*external-await-cancel-token* :test-token
                ec/*yield-handler* (fn [v _] v)]

        ;; Add a continuation
        (let [cont {:id :test-cont
                    :kind :await-once
                    :resolve-fn (fn [v] v)
                    :reject-fn (fn [e] e)}]

          (ec/continuation-add! :test-spin cont)

          ;; Retrieve the continuation from runtime state
          ;; Await conts are stored at [:await-conts spin-id cont-id]
          (let [all-conts (ec/get-state [:await-conts :test-spin])
                stored-cont (first (vals all-conts))]

            ;; Should have :bindings field
            (is (contains? stored-cont :bindings)
                "Continuation should have :bindings field")

            ;; Should have captured all bound vars (except *execution-context*)
            (let [bindings (:bindings stored-cont)]
              (is (nil? (get bindings #'ec/*execution-context*))
                  "Should NOT capture *execution-context* (avoids circular refs)")
              (is (= :test-spin (get bindings #'ec/*spin-id*))
                  "Should capture *spin-id*")
              (is (= :test-token (get bindings #'ec/*external-await-cancel-token*))
                  "Should capture *external-await-cancel-token*")
              (is (fn? (get bindings #'ec/*yield-handler*))
                  "Should capture *yield-handler*"))))))))

(deftest continuation-restores-bindings-test
  (testing "resume-continuation! automatically restores bindings"
    (let [result-atom (atom nil)]
      (th/with-ctx [ctx]
        (binding [ec/*spin-id* :outer-spin]

          ;; Create continuation with specific bindings
          (binding [ec/*yield-handler* (fn [v _] (* 2 v))]
            (let [cont {:id :test-cont
                        :kind :await-once
                        :resolve-fn (fn [v] (reset! result-atom v))
                        :on-resume (fn [_rt] :resume-value)}]

              (ec/continuation-add! :outer-spin cont)))

          ;; Now resume in a DIFFERENT binding context
          (binding [ec/*spin-id* :different-spin
                    ec/*yield-handler* nil]  ; Unbound

            (let [all-conts (ec/get-state [:await-conts :outer-spin])
                  stored-cont (first (vals all-conts))
                  captured-handler (atom nil)]

              ;; Resume continuation - should restore original bindings
              (simple/resume-continuation! ctx :outer-spin stored-cont
                                           (fn [value]
                  ;; Inside resume-fn, bindings should be restored
                                             (reset! captured-handler ec/*yield-handler*)
                                             :resumed))

              ;; Should have restored the yield-handler
              (is (fn? @captured-handler)
                  "Should have restored *yield-handler* during resume")

              ;; Test that the restored handler works
              (when @captured-handler
                (is (= 10 (@captured-handler 5 nil))
                    "Restored *yield-handler* should work correctly")))))))))

(deftest continuation-bindings-cross-thread-test
  (testing "bindings work across thread boundaries"
    (let [result-promise (promise)
          handler-promise (promise)]
      (th/with-ctx [ctx]
        (binding [ec/*spin-id* :main-spin
                  ec/*yield-handler* (fn [v _] (str "handled: " v))]

          ;; Capture continuation on main thread
          (let [cont {:id :cross-thread-cont
                      :kind :await-once
                      :resolve-fn (fn [v] (deliver result-promise v))
                      :on-resume (fn [_rt] :thread-value)}]

            (ec/continuation-add! :main-spin cont)))

        ;; Resume on a different thread (simulating async completion)
        (future
          (binding [ec/*execution-context* ctx]
            (let [all-conts (ec/get-state [:await-conts :main-spin])
                  stored-cont (first (vals all-conts))]
              (simple/resume-continuation! ctx :main-spin stored-cont
                                           (fn [value]
                  ;; Capture the restored yield-handler
                                             (deliver handler-promise ec/*yield-handler*)
                                             :done)))))

        ;; Wait for async completion
        (let [handler (deref handler-promise 1000 :timeout)]
          (is (fn? handler)
              "Should restore *yield-handler* even across threads")

          (when (fn? handler)
            (is (= "handled: test" (handler "test" nil))
                "Restored handler should work correctly")))))))

(deftest continuation-bindings-nil-safe-test
  (testing "handles continuations without :bindings field (backwards compat)"
    (let [result-atom (atom nil)]
      (th/with-ctx [ctx]
        ;; Manually create continuation WITHOUT :bindings field
        ;; Await conts are stored at [:await-conts spin-id cont-id]
        (ec/swap-state! [:await-conts :compat-spin]
                        (constantly {:old-cont {:id :old-cont
                                                :kind :await-once
                                                :event-key nil
                                                :resolve-fn (fn [v] (reset! result-atom v))
                                                :on-resume (fn [_rt] :old-value)
                                                :order 1}}))

        ;; Resume should handle missing :bindings gracefully
        (let [all-conts (ec/get-state [:await-conts :compat-spin])
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
