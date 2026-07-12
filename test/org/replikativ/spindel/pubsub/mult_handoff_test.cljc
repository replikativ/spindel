(ns org.replikativ.spindel.pubsub.mult-handoff-test
  "Regression tests for the resume-as-event mult handoff (#27 Phase B):
  the pubsub coordination promises now deliver each watcher through its
  own ctx's drain as a `:cont-resume` event instead of running it on the
  deliverer's stack.

  1. untap from a FOREIGN thread under producer load: the untap's
     close-tap! signalling no longer executes engine continuations on
     the user thread — it only enqueues. Remaining taps must receive
     every item, and the pump must not jam.
  2. a consumer that throws mid-tap rejects loudly (spawn! :on-error)
     while the pump keeps delivering to the other taps — the original
     room-bus wedge scenario, now via the event path."
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer [deftest is testing] :include-macros true])
            [org.replikativ.spindel.pubsub.mult :as mult]
            [org.replikativ.spindel.pubsub.buffer :as buf]
            [org.replikativ.spindel.engine.fault :as fault]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.sync :as sync]
            [is.simm.partial-cps.sequence :refer [anext]]
            #?(:clj [org.replikativ.spindel.spin.cps :refer [spin]])
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.test-helpers :as th])
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]]
                            [org.replikativ.spindel.test-helpers :refer [with-ctx async]])))

#?(:clj
   (defn- poll-until
     [pred timeout-ms]
     (let [deadline (+ (System/currentTimeMillis) timeout-ms)]
       (loop []
         (cond
           (pred) true
           (>= (System/currentTimeMillis) deadline) false
           :else (do (Thread/sleep 10) (recur)))))))

#?(:clj
   (deftest untap-from-foreign-thread-under-load
     (testing "untap on a raw user thread mid-flood: remaining taps get every
             item, nothing jams, no engine continuation ran on that thread"
       (th/with-ctx [ctx]
         (let [mbx (sync/create-mailbox ctx)
               m (mult/mult mbx)
               n 50
               t1 (mult/tap m (buf/fixed-buffer (* 2 n)))
               t2 (mult/tap m (buf/fixed-buffer (* 2 n)))
               t3 (mult/tap m (buf/fixed-buffer (* 2 n)))
               seen1 (atom [])
               seen2 (atom [])
               consume! (fn [tap-seq seen stop-at]
                          (sync/spawn!
                           (spin
                            (loop [s tap-seq]
                              (when-let [[item rest-seq] (await (anext s))]
                                (swap! seen conj item)
                                (when (< (count @seen) stop-at)
                                  (recur rest-seq)))))))]
           (consume! t1 seen1 n)
           (consume! t2 seen2 n)
           ;; t3 gets NO consumer — its buffer absorbs items until the
           ;; foreign-thread untap removes it mid-flood.
           (let [producer (future
                            (dotimes [i n]
                              (sync/post! mbx i)
                              (when (= i 10)
                                ;; raw user thread, mid-load
                                @(future (mult/untap m t3)))))]
             @producer
             (is (poll-until #(= n (count @seen1)) 5000)
                 "tap 1 received all items")
             (is (poll-until #(= n (count @seen2)) 5000)
                 "tap 2 received all items")
             (is (= (vec (range n)) @seen1) "tap 1 in order")
             (is (= (vec (range n)) @seen2) "tap 2 in order")))))))

#?(:clj
   (deftest consumer-throw-mid-tap-rejects-and-pump-continues
     (testing "a tap consumer throwing on a poison item rejects loudly while
             the pump keeps delivering to the other tap (room-bus scenario)"
       (let [orig (fault/current-fault-reporter)]
         (fault/set-fault-reporter! (fn [_ _] nil)) ;; quiet expected fault
         (try
           (th/with-ctx [ctx]
             (let [mbx (sync/create-mailbox ctx)
                   m (mult/mult mbx)
                   ta (mult/tap m (buf/fixed-buffer 100))
                   tb (mult/tap m (buf/fixed-buffer 100))
                   seen-b (atom [])
                   errs (atom [])
                   consumer-a (spin
                               (loop [s ta]
                                 (when-let [[item rest-seq] (await (anext s))]
                                   (when (= item :boom)
                                     (throw (ex-info "poison" {})))
                                   (recur rest-seq))))]
               (sync/spawn! consumer-a
                            {:on-error (fn [e] (swap! errs conj e))})
               (sync/spawn!
                (spin
                 (loop [s tb]
                   (when-let [[item rest-seq] (await (anext s))]
                     (swap! seen-b conj item)
                     (when (< (count @seen-b) 4)
                       (recur rest-seq))))))
               (sync/post! mbx :a)
               (sync/post! mbx :boom)
               (sync/post! mbx :c)
               (sync/post! mbx :d)
               (is (poll-until #(seq @errs) 4000)
                   "consumer A rejected loudly (spawn! :on-error)")
               (is (= "poison" (ex-message (first @errs))))
               (is (poll-until #(= [:a :boom :c :d] @seen-b) 5000)
                   "tap B received every item — the pump survived A's crash")))
           (finally (fault/set-fault-reporter! orig)))))))
