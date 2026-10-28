(ns org.replikativ.spindel.spin.abort-observer-test
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.nodes :as nodes]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.signal :as sig]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.test-helpers
             :refer [async with-ctx run-spin! await-engine-idle!]])
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]])))

(deftest abort-invalidates-reactive-observer
  (testing "an aborted dependency invalidates its observer's cached success"
    (async done
           (with-ctx [ctx]
             (let [source (sig/signal :ready)
                   child (spin (:new (track source)))
                   runs (atom 0)
                   caught (atom [])
                   observer (spin
                             (swap! runs inc)
                             (try
                               (await child)
                               (catch #?(:clj Throwable :cljs :default) e
                                 (swap! caught conj e)
                                 (throw e))))
                   child-id (spin-core/spin-id child)
                   observer-id (spin-core/spin-id observer)
                   initial (atom nil)
                   subsequent (atom nil)
                   err (ex-info "upstream aborted" {:type ::upstream-failure})]
               (run-spin! observer
                          #(reset! initial [:ok %])
                          #(reset! initial [:error %]))
               (await-engine-idle!
                ctx
                (fn []
                  (is (= [:ok :ready] @initial))
                  (is (= 1 @runs))
                  (is (contains? (nodes/get-observers (ec/get-state [:nodes child-id]))
                                 observer-id))
                  (is (seq (ec/get-state [:subscriptions [:spin/complete child-id] observer-id]))
                      "cache-result! skips dirtying observers with completion subscriptions")
                  ;; Exercise abortion itself, before the caller publishes a completion
                  ;; event: that separate delivery must not hide a stale observer cache.
                  (spin-core/abort-spin-chain! child-id err)
                  (is (nodes/dirty? (ec/get-state [:nodes observer-id])))
                  (is (false? (ec/get-state [:nodes observer-id :completed?])))
                  (run-spin! observer
                             #(reset! subsequent [:ok %])
                             #(reset! subsequent [:error %]))
                  (await-engine-idle!
                   ctx
                   (fn []
                     (is (= 2 @runs) "the dirty observer re-executes on its next invocation")
                     (is (= [err] @caught) "await's rejection continuation reaches the observer's catch")
                     (is (= [:error err] @subsequent) "the caller receives the original upstream error")
                     (done))))))))))
