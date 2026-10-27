(ns org.replikativ.spindel.pubsub.mult-untap-race-test
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            #?(:clj [is.simm.partial-cps.async :as pcps-async])
            [is.simm.partial-cps.sequence :as aseq]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.executor :as ex]
            [org.replikativ.spindel.pubsub.buffer :as buf]
            [org.replikativ.spindel.pubsub.mult :as mult]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.test-helpers :as th :refer [async with-ctx run-spin!]]))

(defn- finite-mailbox [mailbox]
  (reify aseq/PAsyncSeq
    (anext [this]
      (spin
        (let [[item _] (await (aseq/anext mailbox))]
          (when-not (= ::end item) [item this]))))))

(deftest blocking-buffer-untap-before-waiter-capture
  (async done
    (with-redefs [th/create-test-context
                  #(ctx/create-execution-context :executor (ex/synchronous-executor))]
      (with-ctx [world]
        (let [mailbox (sync/create-mailbox world)
              m (mult/mult (finite-mailbox mailbox))
              fixed (buf/fixed-buffer 1)
              close! (atom nil)
              forced? (atom false)
              ;; Protocol calls can bypass with-redefs, so put the hook
              ;; on a buffer that delegates storage to a real fixed buffer.
              buffer (reify
                       buf/PBuffer
                       (full? [_]
                         (let [full (buf/full? fixed)]
                           (when (and full (compare-and-set! forced? false true))
                             (@close!))
                           full))
                       (add! [this item] (buf/add! fixed item) this)
                       (remove! [_] (buf/remove! fixed))
                       (close-buf! [_] (buf/close-buf! fixed))
                       #?@(:clj [clojure.lang.Counted (count [_] (count fixed))]
                           :cljs [ICounted (-count [_] (count fixed))]))
              tap (mult/tap m buffer)
              remaining (buf/sliding-buffer 4)
              _ (mult/tap m remaining)
              result (atom ::pending)]
          (reset! close! #(mult/untap m tap))
          (mult/start! m)
          (sync/post! mailbox :first)
          ;; Return the first full? observation AFTER untap has replaced
          ;; and delivered the space waiter. The next capture sees a new,
          ;; undelivered promise while the closed buffer remains full.
          (sync/post! mailbox :second)
          (sync/post! mailbox ::end)
          (run-spin! (spin (await (mult/mult-pump m))) #(reset! result [:ok %])
                     #(reset! result [:error %]))
          (is @forced?)
          (is (= [:ok nil] @result) "untap cannot strand the producer")
          (is (= 2 (count remaining)) "remaining taps receive both items")
          (is (= 1 (count buffer)) "no delivery into the closed buffer"))))
    (done)))

#?(:clj
   (deftest fixed-buffer-concurrent-untap-2000
     (let [outcomes
           (frequencies
            (for [_ (range 2000)]
              (let [world (ctx/create-execution-context)]
                (try
                  (binding [ec/*execution-context* world]
                    (let [mailbox (sync/create-mailbox world)
                          m (mult/mult (finite-mailbox mailbox))
                          buffer (buf/fixed-buffer 1)
                          tap (mult/tap m buffer)
                          tap-state (val (first @(:taps-atom m)))
                          remaining (buf/sliding-buffer 4)
                          _ (mult/tap m remaining)
                          filled (promise)
                          completed (promise)
                          gate (java.util.concurrent.CountDownLatch. 1)]
                      (add-watch (:item-available-atom @tap-state) ::filled
                                 (fn [_ _ _ _] (deliver filled true)))
                      (mult/start! m)
                      (run-spin! (spin (await (mult/mult-pump m)))
                                 #(deliver completed [:ok %])
                                 #(deliver completed [:error %]))
                      (sync/post! mailbox :first)
                      (if (= ::timeout (deref filled 2000 ::timeout))
                        ::fill-timeout
                        (let [producer (future
                                         (.await gate)
                                         (binding [pcps-async/*in-trampoline* false]
                                           (sync/post! mailbox :second)
                                           (sync/post! mailbox ::end)))
                              untapper (future
                                         (.await gate)
                                         (binding [pcps-async/*in-trampoline* false]
                                           (mult/untap m tap)))]
                          (.countDown gate)
                          (try
                            (let [posted (deref producer 2000 ::timeout)
                                  untapped (deref untapper 2000 ::timeout)
                                  result (deref completed 2000 ::timeout)]
                              (if (or (= ::timeout posted) (= ::timeout untapped))
                                ::worker-timeout
                                [result [(buf/remove! remaining) (buf/remove! remaining)]
                                 (count buffer)]))
                            (finally
                              (future-cancel producer)
                              (future-cancel untapper)))))))
                  (finally (ctx/close-context! world))))))]
       (is (= {[[:ok nil] [:first :second] 1] 2000} outcomes)
           (str "2000 fixed-buffer races, completion / remaining / closed buffer: " outcomes)))))

(deftest rendezvous-untap-before-waiter-capture
  (async done
    (with-redefs [th/create-test-context
                  #(ctx/create-execution-context :executor (ex/synchronous-executor))]
      (with-ctx [world]
        (let [mailbox (sync/create-mailbox world)
              m (mult/mult (finite-mailbox mailbox))
              tap (mult/tap m)
              tap-state (val (first @(:taps-atom m)))
              remaining (buf/sliding-buffer 4)
              _ (mult/tap m remaining)
              forced? (atom false)
              result (atom ::pending)]
          ;; Publishing the slot precedes capture of the space waiter.
          (add-watch tap-state ::untap
                     (fn [_ _ _ state]
                       (when (and (contains? state :rendezvous-item)
                                  (compare-and-set! forced? false true))
                         (mult/untap m tap))))
          (mult/start! m)
          (sync/post! mailbox :item)
          (sync/post! mailbox ::end)
          (run-spin! (spin (await (mult/mult-pump m))) #(reset! result [:ok %])
                     #(reset! result [:error %]))
          (is @forced?)
          (is (= [:ok nil] @result) "closed rendezvous cannot strand the producer")
          (is (= 1 (count remaining)))
          (is (not (contains? @tap-state :rendezvous-item)) "closed slot is cleared"))))
    (done)))

(deftest consumer-untap-before-waiter-capture
  (async done
    (with-redefs [th/create-test-context
                  #(ctx/create-execution-context :executor (ex/synchronous-executor))]
      (with-ctx [world]
        (let [mailbox (sync/create-mailbox world)
              m (mult/mult mailbox)
              close! (atom nil)
              forced? (atom false)
              ;; The first empty-buffer check returns after untap has
              ;; rotated the item waiter. anext must recheck closure.
              buffer (reify
                       buf/PBuffer
                       (full? [_] false)
                       (add! [this _] this)
                       (remove! [_] nil)
                       (close-buf! [_])
                       #?@(:clj [clojure.lang.Counted
                                 (count [_]
                                   (when (compare-and-set! forced? false true) (@close!))
                                   0)]
                           :cljs [ICounted
                                  (-count [_]
                                    (when (compare-and-set! forced? false true) (@close!))
                                    0)]))
              tap (mult/tap m buffer)
              result (atom ::pending)]
          (reset! close! #(mult/untap m tap))
          (run-spin! (aseq/anext tap) #(reset! result [:ok %])
                     #(reset! result [:error %]))
          (is @forced?)
          (is (= [:ok nil] @result) "consumer observes closure after capturing the new waiter"))))
    (done)))

(deftest untap-after-producer-waiter-registration
  (async done
    (with-redefs [th/create-test-context
                  #(ctx/create-execution-context :executor (ex/synchronous-executor))]
      (doseq [buffer [(buf/fixed-buffer 1) nil]]
        (with-ctx [world]
          (let [mailbox (sync/create-mailbox world)
                m (mult/mult (finite-mailbox mailbox))
                tap (mult/tap m buffer)
                tap-state (val (first @(:taps-atom m)))
                result (atom ::pending)
                forced? (atom false)]
            (mult/start! m)
            (when buffer (sync/post! mailbox :first))
            (add-watch (:state @(:space-available-atom @tap-state)) ::untap
                       (fn [_ _ _ state]
                         (when (and (seq (:watchers state))
                                    (compare-and-set! forced? false true))
                           (mult/untap m tap))))
            (sync/post! mailbox :item)
            (sync/post! mailbox ::end)
            (run-spin! (spin (await (mult/mult-pump m))) #(reset! result [:ok %])
                       #(reset! result [:error %]))
            (is @forced?)
            (is (= [:ok nil] @result) "close delivers the captured waiter")))))
    (done)))
