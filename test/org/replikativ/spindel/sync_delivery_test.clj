(ns org.replikativ.spindel.sync-delivery-test
  "Awaiting what is already there: a queued mailbox message or an assigned
   deferred resumes the body on its own trampoline (a loop over a backlog does
   not grow the stack), registers nothing that outlives the await, and keeps
   cancellation and mailbox order intact. A work controller whose runner dies
   fails its completion instead of hanging."
  (:require [clojure.test :refer [deftest is testing]]
            [is.simm.partial-cps.sequence :as aseq]
            [org.replikativ.spindel.core :as sp]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.fault :as fault]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.work :as work]))

;; Deep enough that ~20 frames per iteration overflow any default JVM stack.
(def ^:private n 20000)

(defn- wait-until
  "Poll `pred` until it is truthy or `ms` pass; its last value."
  [pred ms]
  (let [deadline (+ (System/currentTimeMillis) ms)]
    (loop []
      (let [v (pred)]
        (if (or v (> (System/currentTimeMillis) deadline))
          v
          (do (Thread/sleep 10) (recur)))))))

(defn- deref-spin
  "Run `s` to its result on a fresh thread; ::hung after `ms`, or the class of
   what it threw."
  [s ms]
  (let [p (promise)]
    (future (deliver p (try @s (catch Throwable t (class t)))))
    (deref p ms ::hung)))

(defn- queue-count [mb]
  (count (:queue @(.-state-atom ^org.replikativ.spindel.spin.sync.Mailbox mb))))

(defn- filled-mailbox
  "A mailbox of the current context holding 0..k-1, posted and drained."
  [k]
  (let [mb (sync/mailbox)]
    (dotimes [i k] (sync/post! mb i))
    (is (wait-until #(= k (queue-count mb)) 10000) "every post is queued")
    mb))

(deftest a-loop-over-a-queued-mailbox-does-not-grow-the-stack
  (binding [ec/*execution-context* (sp/create-execution-context)]
    (let [mb (filled-mailbox n)]
      (is (= (range n)
             (deref-spin (sp/spin (loop [i 0 acc []]
                                    (if (< i n) (recur (inc i) (conj acc (sp/await mb))) acc)))
                         30000))
          "every message, in post order"))))

(deftest a-loop-over-an-assigned-deferred-does-not-grow-the-stack
  (binding [ec/*execution-context* (sp/create-execution-context)]
    (let [d (sync/deferred)]
      (d 1)
      (is (= n (deref-spin (sp/spin (loop [i 0 acc 0]
                                      (if (< i n) (recur (inc i) (+ acc (sp/await d))) acc)))
                           30000))))))

(deftest a-loop-over-anext-of-a-queued-mailbox-does-not-grow-the-stack
  (binding [ec/*execution-context* (sp/create-execution-context)]
    (let [mb (filled-mailbox n)]
      (is (= (range n)
             (deref-spin (sp/spin (loop [i 0 acc [] s mb]
                                    (if (< i n)
                                      (let [[v more] (sp/await (aseq/anext s))]
                                        (recur (inc i) (conj acc v) more))
                                      acc)))
                         30000))
          "every message, in post order"))))

(deftest retiring-a-continuation-spares-a-newer-one-at-the-same-id
  (binding [ec/*execution-context* (sp/create-execution-context)]
    (let [sid :spin-retire-test
          cont {:id :external-await-x :kind :external-await :event-key [:external-await :x]
                :cancel-token :token-new :resolve-fn identity :reject-fn identity}]
      (ec/continuation-add! sid cont)
      (is (nil? (ec/continuation-remove! sid :external-await-x {:only-token :token-old}))
          "an older await's token does not remove the newer continuation")
      (is (some? (ec/get-state [:await-conts sid :external-await-x])))
      (is (some? (ec/continuation-remove! sid :external-await-x {:only-token :token-new})))
      (is (nil? (ec/get-state [:await-conts sid :external-await-x]))))))

(defn- parked-registrations
  "Run `body-spin` (which parks on a never-delivered deferred after its
   loop) and report what it left registered."
  [s]
  (sync/spawn! s)
  (wait-until #(= 1 (count (ec/get-state [:await-conts (spin-core/spin-id s)]))) 5000)
  {:await-conts (count (ec/get-state [:await-conts (spin-core/spin-id s)]))
   :cancelled-tokens (count (ec/get-state [:engine/cancelled-tokens]))})

(deftest synchronous-deliveries-leave-no-registrations-behind
  (testing "queued mailbox messages"
    (binding [ec/*execution-context* (sp/create-execution-context)]
      (let [mb (filled-mailbox 200)
            park (sync/deferred)]
        (is (= {:await-conts 1 :cancelled-tokens 0}
               (parked-registrations
                (sp/spin (loop [i 0] (if (< i 200) (do (sp/await mb) (recur (inc i))) (sp/await park))))))
            "only the parked await is registered"))))
  (testing "a thunk that resolves synchronously"
    (binding [ec/*execution-context* (sp/create-execution-context)]
      (let [park (sync/deferred)]
        (is (= {:await-conts 1 :cancelled-tokens 0}
               (parked-registrations
                (sp/spin (loop [i 0]
                           (if (< i 200) (do (sp/await (fn [r _] (r i))) (recur (inc i))) (sp/await park)))))))))))

(deftest cancelling-after-synchronous-takes-runs-finally-once
  (binding [ec/*execution-context* (sp/create-execution-context)]
    (let [mb (sync/mailbox)
          never (sync/deferred)
          seen (atom [])]
      (doseq [m [:a :b :stop]] (sync/post! mb m))
      (is (wait-until #(= 3 (queue-count mb)) 5000))
      (let [s (sp/spin (try (loop []
                              (let [m (sp/await mb)]
                                (swap! seen conj m)
                                (if (= m :stop) (sp/await never) (recur))))
                            (finally (swap! seen conj :finally))))]
        (sync/spawn! s {:on-error (fn [_] (swap! seen conj :on-error))})
        (is (wait-until #(= [:a :b :stop] @seen) 5000))
        (spin-core/cancel-spin! s)
        (wait-until #(some #{:on-error} @seen) 5000)
        (Thread/sleep 100)
        (is (= [:a :b :stop :finally :on-error] @seen))))))

(deftest cancelling-does-not-reenter-an-await-the-body-has-left
  (binding [ec/*execution-context* (sp/create-execution-context)]
    (let [mb (sync/mailbox)
          never (sync/deferred)
          seen (atom [])]
      (doseq [m [:a :stop]] (sync/post! mb m))
      (is (wait-until #(= 2 (queue-count mb)) 5000))
      (let [s (sp/spin (loop [k 0]
                         (when (< k 3)
                           (let [m (try (sp/await mb) (catch Exception _ :caught))]
                             (swap! seen conj m)
                             (when (= m :stop) (sp/await never))
                             (recur (inc k))))))]
        (sync/spawn! s {:on-error (fn [_] nil)})
        (is (wait-until #(= [:a :stop] @seen) 5000))
        (spin-core/cancel-spin! s)
        (Thread/sleep 300)
        (is (= [:a :stop] @seen) "no earlier catch ran again and the loop did not go on")))))

(deftest a-cancelled-consumer-takes-nothing
  (binding [ec/*execution-context* (sp/create-execution-context)]
    (let [mb (filled-mailbox 1)
          s (sp/spin (sp/await (sync/deferred)))]
      (sync/spawn! s {:on-error (fn [_] nil)})
      (spin-core/cancel-spin! s)
      (is (wait-until #(ec/spin-is-cancelled? (spin-core/spin-id s)) 5000))
      (is (identical? sync/nothing (sync/take-now! mb (spin-core/spin-id s))))
      (is (= 1 (queue-count mb)) "the message stays for another consumer"))))

(deftest a-fast-take-never-jumps-a-parked-waiter
  (binding [ec/*execution-context* (sp/create-execution-context)]
    (let [mb (sync/mailbox)
          first-taker (sp/spin (sp/await mb))
          got (promise)]
      (sync/spawn! first-taker {:on-success #(deliver got %)})
      (is (wait-until #(seq (:waiters @(.-state-atom ^org.replikativ.spindel.spin.sync.Mailbox mb))) 5000)
          "the first consumer is parked")
      (sync/post! mb :one)
      (sync/post! mb :two)
      (is (= :one (deref got 5000 ::hung)) "the parked consumer gets the first message")
      (is (= :two (deref-spin (sp/spin (sp/await mb)) 5000))))))

(deftest a-parallel-controller-drains-a-large-backlog
  (binding [ec/*execution-context* (sp/create-execution-context)]
    (let [k 500
          finished (atom 0)
          adm (work/parallel {:concurrency 6 :capacity k :ingress-capacity k}
                             (fn [i] (work/task (when (zero? (mod i 9)) (sp/await (sp/sleep 20)))
                                                (swap! finished inc))))]
      (dotimes [i k] (is (work/submit! adm i)))
      (work/close! adm)
      (let [result (deref-spin (sp/spin (sp/await (work/completion adm))) 60000)]
        (is (map? result))
        (is (= 0 (:work/active result)))
        (is (= k @finished))))))

(defn- with-faults
  "Call `f` with engine faults collected into the returned atom's vector."
  [f]
  (let [faults (atom [])
        previous (fault/current-fault-reporter)]
    (fault/set-fault-reporter! (fn [event data] (swap! faults conj [event data])))
    (try (f faults) (finally (fault/set-fault-reporter! previous)))))

(defn- failing-controller-completion
  "Submit to a parallel controller whose runner throws; the completion's
   outcome."
  []
  (binding [ec/*execution-context* (sp/create-execution-context)]
    (let [adm (work/parallel {:concurrency 2} (fn [_] (work/task :ok)))]
      (work/submit! adm 1)
      (deref-spin (sp/spin (try (sp/await (work/completion adm))
                                (catch Exception e (ex-data e))))
                  10000))))

(deftest a-failed-runner-rejects-its-completion
  (testing "the runner throws"
    (with-faults
      (fn [faults]
        (with-redefs-fn {#'work/handle-submit! (fn [& _] (throw (ex-info "runner bug" {})))}
          (fn []
            (is (= :controller-failed (:work/reason (failing-controller-completion))))
            (is (wait-until #(some (fn [[e d]] (and (= ::work/controller-fault e) (= :runner (:phase d))))
                                   @faults)
                            5000)
                "the failure is reported"))))))
  (testing "abort fails as well"
    (with-faults
      (fn [faults]
        (with-redefs-fn {#'work/handle-submit! (fn [& _] (throw (ex-info "runner bug" {})))
                         #'work/abort-controller! (fn [& _] (throw (ex-info "abort bug" {})))}
          (fn []
            (is (= :controller-failed (:work/reason (failing-controller-completion))))
            (is (some (fn [[e d]] (and (= ::work/controller-fault e) (= :abort (:phase d))))
                      @faults))))))))

(deftest a-fork-takes-from-its-own-copy-of-the-queue
  (let [root (sp/create-execution-context)
        mb (binding [ec/*execution-context* root] (filled-mailbox 50))
        fork (sp/fork-context root)]
    (binding [ec/*execution-context* fork]
      (is (= (range 50)
             (deref-spin (sp/spin (loop [i 0 acc []]
                                    (if (< i 50) (recur (inc i) (conj acc (sp/await mb))) acc)))
                         10000))
          "the fork drains its queue in order")
      (is (= 0 (queue-count mb))))
    (binding [ec/*execution-context* root]
      (is (= 50 (queue-count mb)) "the root's queue is untouched"))))
