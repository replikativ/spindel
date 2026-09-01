(ns org.replikativ.spindel.work-test
  (:refer-clojure :exclude [await])
  (:require [is.simm.partial-cps.sequence :refer [anext]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.test-helpers :as h]
            [org.replikativ.spindel.work :as work]
            #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing async]])))

(defn- collect-events [event-stream n]
  (spin
   (loop [source event-stream events []]
     (if (= n (count events))
       events
       (let [[event rest-source] (await (anext source))]
         (recur rest-source (conj events event)))))))

(defn- event-shape [event]
  (select-keys event [:work/event :work/id :work/disposition :work/reason
                      :work/result]))

(deftest latest-quiesces-before-starting-replacement
  (h/async-test [ctx done]
                (let [gates {:a (sync/deferred) :b (sync/deferred)}
                      entered-a (sync/deferred)
                      admission (work/work-admission
                                 {:strategy :latest}
                                 (fn [value]
                                   (work/task
                                    (when (= :a value)
                                      (sync/deliver! entered-a true))
                                    (await (get gates value)))))
                      collected (collect-events (work/events admission) 6)]
                  (h/run-spin!
                   collected
                   (fn [events]
                     (is (= [{:work/event :work/accepted
                              :work/id :a
                              :work/disposition :started}
                             {:work/event :work/started :work/id :a}
                             {:work/event :work/accepted
                              :work/id :b
                              :work/disposition :pending-supersession}
                             {:work/event :work/superseded :work/id :a}
                             {:work/event :work/started :work/id :b}
                             {:work/event :work/completed
                              :work/id :b
                              :work/result :b-done}]
                            (mapv event-shape events)))
                     (is (= 0 (:work/active (work/snapshot admission))))
                     (done))
                   (fn [error]
                     (is false (str error))
                     (done)))
                  (h/run-spin!
                   (spin
                    (await entered-a)
                    (work/submit! admission :b :b)
                    (sync/deliver! (:b gates) :b-done))
                   (fn [_] nil)
                   (fn [error]
                     (is false (str error))
                     (done)))
                  (work/submit! admission :a :a))))

(deftest serial-is-fifo-and-exposes-capacity
  (h/async-test [ctx done]
                (let [gates {:a (sync/deferred) :b (sync/deferred)}
                      admission (work/work-admission
                                 {:strategy :serial :capacity 1}
                                 (fn [value] (work/task (await (get gates value)))))
                      collected (collect-events (work/events admission) 8)]
                  (h/run-spin!
                   collected
                   (fn [events]
                     (is (= [[:work/accepted :a :started]
                             [:work/started :a nil]
                             [:work/accepted :b :queued]
                             [:work/rejected :c nil]
                             [:work/completed :a nil]
                             [:work/started :b nil]
                             [:work/completed :b nil]
                             [:work/controller-closed nil nil]]
                            (mapv (juxt :work/event :work/id :work/disposition) events)))
                     (is (= :capacity (:work/reason (nth events 3))))
                     (done))
                   (fn [error]
                     (is false (str error))
                     (done)))
                  (work/submit! admission :a :a)
                  (work/submit! admission :b :b)
                  (work/submit! admission :c :c)
                  (work/close! admission)
                  (sync/deliver! (:a gates) :a-done)
                  (sync/deliver! (:b gates) :b-done))))

(deftest busy-suppresses-while-active
  (h/async-test [ctx done]
                (let [gate (sync/deferred)
                      admission (work/work-admission
                                 {:strategy :busy}
                                 (fn [_] (work/task (await gate))))
                      collected (collect-events (work/events admission) 4)]
                  (h/run-spin!
                   collected
                   (fn [events]
                     (is (= [[:work/accepted :a]
                             [:work/started :a]
                             [:work/suppressed :b]
                             [:work/completed :a]]
                            (mapv (juxt :work/event :work/id) events)))
                     (is (= :busy (:work/reason (nth events 2))))
                     (done))
                   (fn [error]
                     (is false (str error))
                     (done)))
                  (work/submit! admission :a :a)
                  (work/submit! admission :b :b)
                  (sync/deliver! gate :done))))

(deftest parallel-bounds-active-work-and-queues-in-order
  (h/async-test [ctx done]
                (let [gates (into {} (map (fn [v] [v (sync/deferred)]) [:a :b :c]))
                      admission (work/work-admission
                                 {:strategy :parallel :concurrency 2 :capacity 1}
                                 (fn [value] (work/task (await (get gates value)))))
                      collected (collect-events (work/events admission) 11)]
                  (h/run-spin!
                   collected
                   (fn [events]
                     (is (= [[:work/accepted :a :started]
                             [:work/started :a nil]
                             [:work/accepted :b :started]
                             [:work/started :b nil]
                             [:work/accepted :c :queued]
                             [:work/rejected :d nil]]
                            (mapv (juxt :work/event :work/id :work/disposition)
                                  (take 6 events))))
                     (is (= #{[:work/completed :a]
                              [:work/completed :b]
                              [:work/started :c]
                              [:work/completed :c]}
                            (set (map (juxt :work/event :work/id)
                                      (subvec events 6 10)))))
                     (is (= :work/controller-closed (:work/event (last events))))
                     (done))
                   (fn [error]
                     (is false (str error))
                     (done)))
                  (doseq [v [:a :b :c :d]]
                    (work/submit! admission v v))
                  (work/close! admission)
                  (doseq [v [:a :b :c]]
                    (sync/deliver! (get gates v) (keyword (str (name v) "-done")))))))

(deftest cancel-unwinds-owned-children
  (h/async-test [ctx done]
                (let [gate (sync/deferred)
                      entered (sync/deferred)
                      cleaned? (atom false)
                      admission (work/work-admission
                                 {:strategy :serial}
                                 (fn [_]
                                   (work/task
                                    (try
                                      (sync/deliver! entered true)
                                      (await gate)
                                      (finally (reset! cleaned? true))))))
                      collected (collect-events (work/events admission) 4)]
                  (h/run-spin!
                   collected
                   (fn [events]
                     (is (= [:work/accepted :work/started :work/cancelled
                             :work/controller-cancelled]
                            (mapv :work/event events)))
                     (is @cleaned?)
                     (done))
                   (fn [error]
                     (is false (str error))
                     (done)))
                  (h/run-spin! (spin (await entered) (work/cancel! admission))
                               (fn [_] nil)
                               (fn [error]
                                 (is false (str error))
                                 (done)))
                  (work/submit! admission :a :a))))

(deftest construction-failure-is-data-and-controller-continues
  (h/async-test [ctx done]
                (let [admission (work/serial
                                 (fn [value]
                                   (if (= value :bad)
                                     :not-a-task
                                     (work/task :good-result))))
                      collected (collect-events (work/events admission) 6)]
                  (h/run-spin!
                   collected
                   (fn [events]
                     (is (= [[:work/accepted :bad]
                             [:work/failed :bad]
                             [:work/accepted :good]
                             [:work/started :good]
                             [:work/completed :good]
                             [:work/controller-closed nil]]
                            (mapv (juxt :work/event :work/id) events)))
                     (is (= :construction (:work/phase (second events))))
                     (done))
                   (fn [error]
                     (is false (str error))
                     (done)))
                  (work/submit! admission :bad :bad)
                  (work/submit! admission :good :good)
                  (work/close! admission))))

(deftest ids-are-unique-while-work-is-outstanding
  (h/async-test [ctx done]
                (let [gate (sync/deferred)
                      admission (work/serial (fn [_] (work/task (await gate))))
                      collected (collect-events (work/events admission) 5)
                      rejection (collect-events (work/events admission) 3)]
                  (h/run-spin!
                   collected
                   (fn [events]
                     (is (= [[:work/accepted :same]
                             [:work/started :same]]
                            (mapv (juxt :work/event :work/id) (take 2 events))))
                     (is (= #{[:work/rejected :same]
                              [:work/completed :same]}
                            (set (map (juxt :work/event :work/id)
                                      (subvec events 2 4)))))
                     (is (= :work/controller-closed (:work/event (last events))))
                     (is (= :duplicate-id
                            (:work/reason (some #(when (= :work/rejected
                                                          (:work/event %))
                                                   %)
                                                events))))
                     (done))
                   (fn [error]
                     (is false (str error))
                     (done)))
                  (h/run-spin! rejection
                               (fn [_] (sync/deliver! gate :done))
                               (fn [error]
                                 (is false (str error))
                                 (done)))
                  (work/submit! admission :same :first)
                  (work/submit! admission :same :second)
                  (work/close! admission))))

(deftest terminal-operations-are-idempotent-and-refuse-ingress
  (h/async-test [ctx done]
                (let [admission (work/busy (fn [value] (work/task value)))
                      collected (collect-events (work/events admission) 1)]
                  (work/close! admission)
                  (is (nil? (work/submit! admission :late :late)))
                  (work/close! admission)
                  (h/run-spin!
                   collected
                   (fn [events]
                     (is (= [:work/controller-closed] (mapv :work/event events)))
                     (is (:terminal? (work/snapshot admission)))
                     (work/cancel! admission)
                     (is (nil? (work/submit! admission :later :later)))
                     (done))
                   (fn [error]
                     (is false (str error))
                     (done))))))

(deftest ingress-is-explicitly-bounded-before-mailbox-retention
  (h/with-ctx [ctx]
    (let [admission (work/serial {:ingress-capacity 1}
                                 (fn [value] (work/task value)))]
      ;; Hold delivery so the first reservation cannot be dispatched while the
      ;; second submit checks the bound.
      (with-redefs [sync/post! (fn [_ _] nil)]
        (is (= :first (work/submit! admission :first :first)))
        (is (nil? (work/submit! admission :second :second)))
        (is (= 1 (:ingress (work/snapshot admission))))))))

(deftest event-taps-broadcast-without-competing
  (h/async-test [ctx done]
                (let [admission (work/serial (fn [value] (work/task value)))
                      tap-a (collect-events (work/events admission) 4)
                      tap-b (collect-events (work/events admission) 4)
                      results (atom [])
                      receive! (fn [events]
                                 (swap! results conj (mapv :work/event events))
                                 (when (= 2 (count @results))
                                   (is (= [[:work/accepted :work/started
                                            :work/completed :work/controller-closed]
                                           [:work/accepted :work/started
                                            :work/completed :work/controller-closed]]
                                          @results))
                                   (done)))
                      fail! (fn [error]
                              (is false (str error))
                              (done))]
                  (h/run-spin! tap-a receive! fail!)
                  (h/run-spin! tap-b receive! fail!)
                  (work/submit! admission :a :a)
                  (work/close! admission))))

(deftest controllers-create-private-spins-for-a-shared-task
  (h/async-test [ctx done]
                (let [gate (sync/deferred)
                      entered (sync/deferred)
                      entrants (atom 0)
                      shared-task (work/task
                                   (when (= 2 (swap! entrants inc))
                                     (sync/deliver! entered true))
                                   (await gate))
                      cancelled (work/serial (constantly shared-task))
                      completed (work/serial (constantly shared-task))
                      cancelled-events (collect-events (work/events cancelled) 4)
                      completed-events (collect-events (work/events completed) 4)
                      verification (spin
                                    (let [left (await cancelled-events)
                                          right (await completed-events)]
                                      [left right]))]
                  (h/run-spin!
                   verification
                   (fn [[left right]]
                     (is (= [:work/accepted :work/started :work/cancelled
                             :work/controller-cancelled]
                            (mapv :work/event left)))
                     (is (= [:work/accepted :work/started :work/completed
                             :work/controller-closed]
                            (mapv :work/event right)))
                     (is (= :shared-result (:work/result (nth right 2))))
                     (done))
                   (fn [error]
                     (is false (str error))
                     (done)))
                  (h/run-spin!
                   (spin
                    (await entered)
                    (work/cancel! cancelled)
                    (sync/deliver! gate :shared-result)
                    (work/close! completed))
                   (fn [_] nil)
                   (fn [error]
                     (is false (str error))
                     (done)))
                  (work/submit! cancelled :left :left)
                  (work/submit! completed :right :right))))

(deftest cancel-then-completion-observes-quiescence
  (h/async-test [ctx done]
                (let [gate (sync/deferred)
                      entered (sync/deferred)
                      cleaned? (atom false)
                      admission (work/serial
                                 (fn [_]
                                   (work/task
                                    (try
                                      (sync/deliver! entered true)
                                      (await gate)
                                      (finally (reset! cleaned? true))))))
                      finished (collect-events (work/events admission) 4)
                      verification (spin
                                    (let [events (await finished)
                                          state (await (work/completion admission))]
                                      {:events events :state state}))]
                  (h/run-spin! verification
                               (fn [{:keys [events state]}]
                                 (is (= [:work/accepted :work/started
                                         :work/cancelled
                                         :work/controller-cancelled]
                                        (mapv :work/event events)))
                                 (is @cleaned?)
                                 (is (:terminal? state))
                                 (is (zero? (:work/active state)))
                                 (is (:terminal? (work/snapshot admission)))
                                 (is (zero? (:work/active (work/snapshot admission))))
                                 (is (nil? (work/submit! admission :late :late)))
                                 (done))
                               (fn [error]
                                 (is false (str error))
                                 (done)))
                  (h/run-spin! (spin (await entered) (work/cancel! admission))
                               (fn [_] nil)
                               (fn [error]
                                 (is false (str error))
                                 (done)))
                  (work/submit! admission :owned :owned)
                  nil)))

#?(:clj
   (deftest inherited-controller-rejects-a-distinct-fork
     (h/with-ctx [parent]
       (let [admission (work/serial (fn [value] (work/task value)))
             fork (context/fork-context parent)]
         (try
           (is (thrown-with-msg?
                clojure.lang.ExceptionInfo
                #"outside its owning execution context"
                (binding [ec/*execution-context* fork]
                  (work/submit! admission :foreign :foreign))))
           (finally
             (context/stop-context! fork)
             (work/close! admission)))))))

#?(:clj
   (deftest completion-rechecks-affinity-when-awaited
     (h/with-ctx [parent]
       (let [admission (work/serial (fn [value] (work/task value)))
             completion (work/completion admission)
             fork (context/fork-context parent)
             rejected (atom nil)]
         (try
           (binding [ec/*execution-context* fork]
             (completion (fn [_] (is false "foreign completion resolved"))
                         #(reset! rejected %)))
           (is (= :foreign-context (:work/reason (ex-data @rejected))))
           (finally
             (context/stop-context! fork)
             (work/close! admission)))))))

#?(:clj
   (deftest submit-close-transition-is-linearizable-under-contention
     (dotimes [_ 10]
       (h/with-ctx [ctx]
         (let [admission (work/serial (fn [value] (work/task value)))
               start (promise)
               posted (atom [])]
           (with-redefs [sync/post! (fn [_ message]
                                      (swap! posted conj message)
                                      nil)]
             (let [submitter (future
                               @start
                               (binding [ec/*execution-context* ctx]
                                 (work/submit! admission :job :job)))
                   closer-a (future
                              @start
                              (binding [ec/*execution-context* ctx]
                                (work/close! admission)))
                   closer-b (future
                              @start
                              (binding [ec/*execution-context* ctx]
                                (work/close! admission)))]
               (deliver start true)
               @submitter
               @closer-a
               @closer-b
               (let [submit-count (count (filter #(= :submit (:work/op %))
                                                 @posted))
                     close-count (count (filter #(= :close (:work/op %))
                                                @posted))]
                 (is (= 1 close-count))
                 (is (= submit-count (:ingress (work/snapshot admission))))
                 (is (<= submit-count 1))
                 (is (nil? (work/submit! admission :late :late)))))))))))
