(ns org.replikativ.spindel.engine.native-release-test
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.impl.owned :as owned]
            [org.replikativ.spindel.engine.lifecycle :as lifecycle]
            [org.replikativ.spindel.engine.owned-runtime-test :refer [verify-boundaries!]]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.effects.await :refer [await await-finalization]]
            [org.replikativ.spindel.spin.combinators :as combinators]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.spin.sync :as sync]))

(defn- ignore-result [_] nil)
(defn- runtime [] (owned/runtime {:audit? true :cps-exit? true}))
(defn- failure [f]
  (try (f) nil (catch #?(:clj Throwable :cljs :default) error error)))

(deftest idle-release-observers-replay-without-an-owned-join-dependency
  (let [rt (runtime) calls (atom [])
        completion (context/release-context! rt (ex-info "idle release" {}))]
    (is (= :released (:status (owned/snapshot rt))))
    (is (= :joined (get-in (owned/snapshot rt) [:release :phase])))
    (is (owned/join-ready? rt owned/w))
    (let [detach (lifecycle/observe! completion #(swap! calls conj %) #(throw %))]
      (detach)
      (detach))
    (is (= [nil] @calls))
    (is (identical? completion (context/release-context! rt :ignored)))
    (verify-boundaries! rt)))

(defn- controlled []
  (let [scheduled (atom nil) worker (atom nil) cancelled (atom [])]
    {:scheduled scheduled :worker worker :cancelled cancelled
     :transport {:schedule (fn [_ dispatch] (reset! scheduled dispatch) :timer-handle)
                 :submit (fn [task] (reset! worker task))
                 :cancel #(swap! cancelled conj %)}}))

(deftest release-revokes-a-queued-timer-worker-before-it-can-enter
  (let [driver (controlled)
        rt (owned/runtime {:audit? true :cps-exit? true :timer-transport (:transport driver)})
        values (atom []) errors (atom []) joined (atom []) reason (ex-info "release timer" {})]
    (binding [ec/*execution-context* rt]
      (let [sleep (combinators/sleep 100000 41)]
        (sleep #(swap! values conj %) #(swap! errors conj %))))
    (@(:scheduled driver))
    (let [completion (context/release-context! rt reason)]
      (lifecycle/observe! completion #(swap! joined conj %) #(throw %))
      (@(:worker driver))
      (@(:worker driver))
      (is (= [nil] @joined))
      (is (empty? @values))
      (is (= [reason] @errors))
      (is (= [:timer-handle] @(:cancelled driver)))
      (is (zero? (:timer-resources (owned/storage-stats rt)))))
    (verify-boundaries! rt)))

(deftest pending-observer-detach-and-self-join-refusal-preserve-cleanup
  (let [rt (runtime) holder (atom nil) rejected (atom nil) joined (atom [])]
    (binding [ec/*execution-context* rt]
      (let [pending (sync/deferred) ack (sync/deferred)
            target (spin (try (await pending)
                              (finally
                                (await-finalization
                                 (fn [succeed fail]
                                   (ack (fn [value]
                                          (reset! rejected
                                                  (failure #(lifecycle/observe! @holder ignore-result ignore-result)))
                                          (succeed (inc value)))
                                        fail))))))]
        (target ignore-result ignore-result)
        (let [completion (context/release-context! rt (ex-info "release protected wait" {}))]
          (reset! holder completion)
          (let [detach (lifecycle/observe! completion (fn [_] (swap! joined conj :detached)) #(throw %))]
            (detach)
            (detach))
          (lifecycle/observe! completion (fn [_] (swap! joined conj :joined)) #(throw %))
          (is (empty? @joined))
          (is (= :releasing (get-in (owned/snapshot rt) [:release :phase])))
          (ack 41)
          (is (= :self-release-join (:error (ex-data @rejected))))
          (is (= [:joined] @joined))
          (is (= :joined (get-in (owned/snapshot rt) [:release :phase]))))))
    (verify-boundaries! rt)))

(deftest raw-rejection-retains-physical-authority-until-its-real-return
  (let [rt (runtime) errors (atom []) physical (atom []) reason (ex-info "release raw take" {})]
    (binding [ec/*execution-context* rt]
      (let [mailbox (sync/mailbox)]
        (mailbox ignore-result
                 (fn [error]
                   (swap! errors conj error)
                   (swap! physical conj (owned/join-ready? rt owned/w))))
        (let [completion (context/release-context! rt reason) joined (atom [])]
          (lifecycle/observe! completion #(swap! joined conj %) #(throw %))
          (is (= [reason] @errors))
          (is (= [false] @physical))
          (is (= [nil] @joined))
          (is (failure #(mailbox ignore-result ignore-result))))))
    (verify-boundaries! rt)))

#?(:clj
   (deftest release-does-not-join-a-timer-installation-before-its-ordinary-return
     (let [entered (promise) leave (promise) cancelled (atom []) joined (atom [])
           driver {:schedule (fn [_ _]
                               (deliver entered true)
                               (when-not (= true (deref leave 5000 ::timeout))
                                 (throw (ex-info "Timer installation latch timed out" {})))
                               :late-handle)
                   :submit (fn [task] (task)) :cancel #(swap! cancelled conj %)}
           rt (owned/runtime {:audit? true :cps-exit? true :timer-transport driver})
           sleep (binding [ec/*execution-context* rt] (combinators/sleep 100000 41))
           installer (future (binding [ec/*execution-context* rt] (sleep ignore-result ignore-result)))]
       (try
         (is (= true (deref entered 5000 ::timeout)))
         (let [completion (context/release-context! rt (ex-info "release during install" {}))]
           (lifecycle/observe! completion #(swap! joined conj %) #(throw %))
           (is (empty? @joined))
           (is (not (owned/join-ready? rt owned/w))))
         (finally (deliver leave true)))
       (is (not= ::timeout (deref installer 5000 ::timeout)))
       (is (= [:late-handle] @cancelled))
       (is (= [nil] @joined))
       (verify-boundaries! rt))))

(deftest released-construction-refuses-before-any-token-or-cache-mutation
  (let [rt (runtime)]
    (context/release-context! rt)
    (let [before (owned/snapshot rt) stats (owned/storage-stats rt)
          trace-count (count (owned/audit-trace rt))]
      (is (failure #(binding [ec/*execution-context* rt] (spin :new-computation))))
      (is (failure #(owned/make-spin rt :new-raw-handle (fn [_ _] :never))))
      (is (failure #(owned/register-computation! rt #?(:clj (Object.) :cljs (js-obj)) :new-token-only)))
      (is (= before (owned/snapshot rt)))
      (is (= stats (owned/storage-stats rt)))
      (is (= trace-count (count (owned/audit-trace rt)))))
    (verify-boundaries! rt)))

(deftest joining-prunes-only-now-stale-accepted-producer-attempts-before-observers
  (doseq [kind [:deferred :mailbox]]
    (let [rt (runtime) cleanup (atom []) observed (atom []) errors (atom [])
          reason (ex-info "release with two accepted attempts" {:resource kind})]
      (binding [ec/*execution-context* rt]
        (let [pending (sync/deferred)
              ack (if (= :deferred kind) (sync/deferred) (sync/mailbox))
              target (spin (try (await pending)
                                (finally
                                  (let [value (await-finalization
                                               (fn [succeed fail] (ack succeed fail)))]
                                    (swap! cleanup conj (inc value))))))
              send! (if (= :deferred kind) sync/deliver! sync/post!)]
          (target ignore-result
                  (fn [error]
                    ;; This committed external notification runs with the
                    ;; drain busy, after the protected wait has registered.
                    (swap! errors conj error)
                    (let [completion (context/release-context! rt :ignored)]
                      (lifecycle/observe!
                       completion
                       (fn [_]
                         (let [state (owned/snapshot rt)]
                           (swap! observed conj [(:phase (:release state)) (empty? (:outside state))])))
                       #(throw %)))
                    (send! ack 1)
                    (send! ack {:stale :second-attempt})))
          (context/release-context! rt reason)
          (is (= [reason] @errors))
          (is (= [2] @cleanup))
          (is (= [[:joined true]] @observed))
          (is (empty? (:outside (owned/snapshot rt))))))
      (verify-boundaries! rt))))

#?(:clj
   (deftest last-raw-return-prunes-its-queued-packet-before-notifying-release
     (let [rt (runtime) entered (promise) leave (promise) observed (atom [])
           posted (atom false)
           mailbox (binding [ec/*execution-context* rt] (sync/mailbox))]
       (binding [ec/*execution-context* rt]
         (mailbox
          (fn [_]
            (deliver entered true)
            (when-not (= true (deref leave 5000 ::timeout))
              (throw (ex-info "Raw callback latch timed out" {})))
            ;; Release has retired this frame. Its exact named capability
            ;; permits this post, whose envelope is still queued at return.
            (sync/post! mailbox {:queued :after-release})
            (reset! posted true))
          #(throw %)))
       (let [worker (future (binding [ec/*execution-context* rt]
                              (sync/post! mailbox :enter)))]
         (try
           (is (= true (deref entered 5000 ::timeout)))
           (let [completion (context/release-context! rt (ex-info "release entered raw frame" {}))]
             (lifecycle/observe!
              completion
              (fn [_]
                (let [state (owned/snapshot rt)]
                  (swap! observed conj [(get-in state [:release :phase]) (empty? (:outside state))])))
              #(throw %))
             (is (empty? @observed))
             (is (not (owned/join-ready? rt owned/w))))
           (finally (deliver leave true)))
         (is (not= ::timeout (deref worker 5000 ::timeout))))
       (is @posted)
       ;; A ready observer post runs before the ordinary event lane. Retaining
       ;; the stale envelope until later dispatch would make this false.
       (is (= [[:joined true]] @observed))
       (is (empty? (:outside (owned/snapshot rt))))
       (verify-boundaries! rt))))
