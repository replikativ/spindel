(ns org.replikativ.spindel.v2.cleanup-operation-test
  "Real shared operation state, runnable on native Babashka without engine/JVM."
  (:require [clojure.test :refer [deftest is testing]]
            [org.replikativ.spindel.v2.cleanup :as cleanup]))

(defn- operation [register]
  (cleanup/operation :world (cleanup/resource :world :owner [:owner] register (fn [f] (f)))))

(deftest shared-one-shot-close-and-observer-withdrawal
  (let [calls (atom 0) complete (atom nil) detach (atom 0) seen (atom [])
        op (operation (fn [cb] (swap! calls inc) (reset! complete cb)
                        #(swap! detach inc)))
        withdraw (cleanup/subscribe! op #(swap! seen conj [:withdrawn %]))]
    (cleanup/subscribe! op #(swap! seen conj [:kept %]))
    (withdraw)
    (withdraw)
    (is (= {:phase :pending :subscribers 1} (cleanup/status op)))
    (is (= 0 @detach) "withdrawal cannot detach/cancel the physical close")
    (@complete :closed)
    (@complete :duplicate)
    (cleanup/subscribe! op #(swap! seen conj [:late %]))
    (is (= 1 @calls))
    (is (= 1 @detach))
    (is (= [[:kept [:closed false]] [:late [:closed false]]] @seen))
    (is (= {:phase :settled :subscribers 0 :outcome [:closed false]} (cleanup/status op)))))

(deftest first-terminal-wins-during-registration
  (doseq [mode [:throw :complete-then-throw :synchronous-late-detach]]
    (testing (str mode)
      (let [error (ex-info "registration failed" {:mode mode})
            detach (atom 0) seen (atom [])
            op (operation (fn [cb]
                            (if (= mode :throw)
                              (throw error)
                              (do (cb :closed) (cb :duplicate true)
                                  (if (= mode :complete-then-throw)
                                    (throw error)
                                    #(swap! detach inc))))))]
        (cleanup/subscribe! op #(swap! seen conj %))
        (is (= [(if (= mode :throw) [error true] [:closed false])] @seen))
        (is (= (if (= mode :synchronous-late-detach) 1 0) @detach))
        (is (= 0 (:subscribers (cleanup/status op))))))))

(deftest subscriber-and-detach-exceptions-do-not-rewrite-outcome
  (let [complete (atom nil) seen (atom [])
        op (operation (fn [cb] (reset! complete cb)
                        #(throw (ex-info "detach failed" {}))))]
    (cleanup/subscribe! op (fn [_] (throw (ex-info "subscriber failed" {}))))
    (cleanup/subscribe! op #(swap! seen conj %))
    (@complete :closed)
    (is (= [[:closed false]] @seen))
    (is (= [:closed false] (:outcome (cleanup/status op))))))

(deftest physical-callback-keeps-only-settled-operation-state
  (let [complete (atom nil) payload (Object.)
        op (operation (fn [cb] (reset! complete cb) (fn [] payload)))]
    (cleanup/subscribe! op (fn [_] payload))
    (@complete :closed)
    ;; A held physical callback references this atom, rather than the Resource,
    ;; registration closure, subscribers, detach control, or engine/world rows.
    (is (= {:phase :settled :outcome [:closed false]} @(.-state op)))))
