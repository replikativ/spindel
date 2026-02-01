(ns org.replikativ.spindel.state.atom-test
  "Tests for fork-safe runtime atoms with ExecutionContext"
  #?(:clj
     (:require [clojure.test :refer [deftest is testing]]
               [org.replikativ.spindel.state.atom :as ratom]
               [org.replikativ.spindel.runtime.context :as ctx]
               [org.replikativ.spindel.runtime.core :as rtc]
               [org.replikativ.spindel.runtime.scheduler :as sched]
               [org.replikativ.spindel.runtime.state-backend :as backend]
               [org.replikativ.spindel.spin.cps :refer [spin]]
               [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]])
     :cljs
     (:require [cljs.test :refer-macros [deftest is testing]]
               [org.replikativ.spindel.state.atom :as ratom]
               [org.replikativ.spindel.runtime.context :as ctx]
               [org.replikativ.spindel.runtime.core :as rtc]
               [org.replikativ.spindel.runtime.state-backend :as backend]
               [org.replikativ.spindel.spin.cps :refer [spin]]
               [org.replikativ.spindel.test-helpers :refer [async with-ctx run-spin!]]))
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]])))

;; =============================================================================
;; Cross-platform basic atom tests (async pattern)
;; =============================================================================

(deftest test-atom-basic-operations
  (testing "Runtime atoms support basic atom operations"
    (async done
      (with-ctx [ctx]
        (let [my-atom (ratom/create-atom [])]

          ;; deref
          (is (= [] @my-atom))

          ;; swap!
          (is (= [1] (swap! my-atom conj 1)))
          (is (= [1] @my-atom))

          ;; reset!
          (is (= [2 3] (reset! my-atom [2 3])))
          (is (= [2 3] @my-atom))

          ;; swap! with multiple args
          (is (= [2 3 4 5] (swap! my-atom conj 4 5)))
          (is (= [2 3 4 5] @my-atom))
          (done))))))

(deftest test-atom-metadata
  (testing "Runtime atoms support metadata"
    (async done
      (with-ctx [ctx]
        (let [my-atom (ratom/create-atom [] :meta {:doc "Test atom"})]
          (is (= {:doc "Test atom"} (meta my-atom)))
          (done))))))

(deftest test-atom-state-location
  (testing "Atom state is stored in [:atoms] and accessible via backend protocol"
    (async done
      (with-ctx [ctx]
        (let [my-atom (ratom/create-atom [1 2 3] :meta {:doc "Test"})
              ;; Check runtime structure via backend protocol
              atom-id (.-id my-atom)
              atom-state (backend/backend-read (:backend ctx) [:atoms atom-id])]

          (is (some? atom-state))
          (is (= [1 2 3] (:value atom-state)))
          (is (= {:doc "Test"} (:meta atom-state)))
          (is (map? (:watchers atom-state)))
          (done))))))

(deftest test-atom-in-spin-context
  (testing "Runtime atoms can be created in spin context using (atom)"
    (async done
      (with-ctx [_ctx]
        (let [result-spin (spin
                           (let [cache (ratom/atom [])]
                             (swap! cache conj 1)
                             (swap! cache conj 2)
                             @cache))]
          (run-spin! result-spin
                     (fn [result]
                       (is (= [1 2] result))
                       (done))
                     (fn [err]
                       (is false (str "Spin failed: " err))
                       (done))))))))

;; =============================================================================
;; CLJ-only tests: require Thread/sleep, context forking, backend type checks
;; =============================================================================

#?(:clj
   (deftest test-atom-watchers
     (testing "Runtime atoms support watchers"
       (let [exec-ctx (ctx/create-execution-context :executor (sched/default-executor))]
         (binding [rtc/*execution-context* exec-ctx]
           (let [my-atom (ratom/create-atom 0)
                 watch-calls (atom [])]

             ;; Add watcher
             (add-watch my-atom :test-watcher
               (fn [k _ref old new]
                 (swap! watch-calls conj {:key k :old old :new new})))

             ;; Modify atom - watcher should fire
             (swap! my-atom inc)

             ;; Give watcher a moment to fire
             (Thread/sleep 10)

             (is (= 1 (count @watch-calls)))
             (is (= {:key :test-watcher :old 0 :new 1} (first @watch-calls)))

             ;; Remove watcher
             (remove-watch my-atom :test-watcher)

             ;; Modify again - watcher should not fire
             (swap! my-atom inc)
             (Thread/sleep 10)

             (is (= 1 (count @watch-calls)))))))))

#?(:clj
   (deftest test-atom-forking
     (testing "Runtime atoms fork correctly with ExecutionContext"
       (let [exec-ctx (ctx/create-execution-context :executor (sched/default-executor))]
         (binding [rtc/*execution-context* exec-ctx]
           (let [my-atom (ratom/create-atom [1 2 3])]

             ;; Original has [1 2 3]
             (is (= [1 2 3] @my-atom))

             ;; Fork the execution context
             (let [forked-ctx (ctx/fork-context exec-ctx)
                   atom-id (.-id my-atom)
                   forked-atom (ratom/->RuntimeAtom atom-id)]

               ;; Forked atom has same initial value (reads from parent backend)
               (binding [rtc/*execution-context* forked-ctx]
                 (is (= [1 2 3] @forked-atom))

                 ;; Modify forked atom
                 (swap! forked-atom conj 4)

                 ;; Forked atom changed
                 (is (= [1 2 3 4] @forked-atom)))

               ;; Original atom unchanged (rebind to original context)
               (is (= [1 2 3] @my-atom))

               ;; Modify original atom
               (swap! my-atom conj 5)

               ;; Original changed
               (is (= [1 2 3 5] @my-atom))

               ;; Forked unchanged (copy-on-write)
               (binding [rtc/*execution-context* forked-ctx]
                 (is (= [1 2 3 4] @forked-atom))))))))))

#?(:clj
   (deftest test-atom-execution-context
     (testing "Runtime atoms work with ExecutionContext (not old runtime structure)"
       (let [exec-ctx (ctx/create-execution-context :executor (sched/default-executor))]

         ;; Verify ExecutionContext structure
         (is (some? (:backend exec-ctx)))
         (is (= :atom (backend/backend-type (:backend exec-ctx))))

         ;; Create atom with ExecutionContext
         (binding [rtc/*execution-context* exec-ctx]
           (let [my-atom (ratom/create-atom 42)]
             (is (= 42 @my-atom))

             ;; Verify watcher was installed on backend
             ;; (This implicitly tests that install-atom-watcher! worked)
             (let [watch-calls (atom [])
                   atom-id (.-id my-atom)]

               ;; Add watcher to runtime atom
               (add-watch my-atom :test-watcher
                 (fn [k _ref old new]
                   (swap! watch-calls conj {:key k :old old :new new})))

               ;; Modify atom
               (swap! my-atom inc)

               ;; Give watcher a moment
               (Thread/sleep 10)

               ;; Watcher should have fired
               (is (= 1 (count @watch-calls)))
               (is (= 42 (:old (first @watch-calls))))
               (is (= 43 (:new (first @watch-calls)))))))))))

#?(:clj
   (deftest test-atom-backend-abstraction
     (testing "Atom watcher installation delegates to backend protocol"
       (let [exec-ctx (ctx/create-execution-context :executor (sched/default-executor))]

         ;; Create multiple atoms - watcher should be installed once per backend (idempotent)
         (binding [rtc/*execution-context* exec-ctx]
           (let [atom1 (ratom/create-atom 1)
                 atom2 (ratom/create-atom 2)
                 atom3 (ratom/create-atom 3)]

             ;; All atoms should work
             (is (= 1 @atom1))
             (is (= 2 @atom2))
             (is (= 3 @atom3))

             ;; Watchers should work for all atoms
             (let [watch-calls-1 (atom [])
                   watch-calls-2 (atom [])
                   watch-calls-3 (atom [])]

               (add-watch atom1 :w1 (fn [k _ref old new] (swap! watch-calls-1 conj {:k k :old old :new new})))
               (add-watch atom2 :w2 (fn [k _ref old new] (swap! watch-calls-2 conj {:k k :old old :new new})))
               (add-watch atom3 :w3 (fn [k _ref old new] (swap! watch-calls-3 conj {:k k :old old :new new})))

               (swap! atom1 inc)
               (swap! atom2 inc)
               (swap! atom3 inc)

               (Thread/sleep 10)

               (is (= 1 (count @watch-calls-1)))
               (is (= 1 (count @watch-calls-2)))
               (is (= 1 (count @watch-calls-3))))))))))
