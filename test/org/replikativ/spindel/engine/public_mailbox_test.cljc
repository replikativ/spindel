(ns org.replikativ.spindel.engine.public-mailbox-test
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [is.simm.partial-cps.sequence :as aseq]
            [is.simm.partial-cps.async :as pcps]
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.bindings :as bindings]
            [org.replikativ.spindel.engine.addressing :as address]
            [org.replikativ.spindel.engine.impl.owned :as owned]
            [org.replikativ.spindel.engine.owned-runtime-test :refer [verify-boundaries!]]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.await :refer [await await-finalization]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.signal :as signal]
            [org.replikativ.spindel.atom :as runtime-atom]
            [org.replikativ.spindel.incremental.interval :as iv]))

(defn- runtime [] (context/create-execution-context {:engine :owned :audit? true}))
(defn- observe! [s values] (s #(swap! values conj %) #(throw %)))
(defn- cancel! [rt s reason]
  (rtp/cancel-computation! rt s (spin-core/spin-id s) (spin-core/spin-body s) reason))
(defn- entity-id [mailbox] (:id (rtp/mailbox-payload mailbox)))

(deftest posting-is-nil-returning-and-each-message-has-one-reader
  (let [rt (runtime) values (atom [])]
    (binding [ec/*execution-context* rt]
      (let [mb (sync/mailbox)
            a (spin (await mb)) b (spin (await mb))]
        (observe! a values)
        (observe! b values)
        (is (nil? (mb :first)))
        (is (= [:first] @values))
        (is (nil? (sync/post! mb :second)))
        (is (= [:first :second] @values))
        (is (identical? sync/nothing (sync/take-now! mb nil)))))
    (verify-boundaries! rt)))

(deftest queued-messages-preserve-fifo-and-successful-payloads
  (let [rt (runtime) values (atom [])
        messages [nil false (ex-info "message data" {})
                  {:type spin-core/spin-cancelled :variant :error :payload false}]]
    (binding [ec/*execution-context* rt]
      (let [mb (sync/mailbox)
            reader (spin [(await mb) (await mb) (await mb) (await mb)])]
        (doseq [value messages] (mb value))
        (observe! reader values)
        (is (= [messages] @values))
        (is (identical? (nth messages 2) (nth (first @values) 2)))
        (is (identical? sync/nothing (sync/take-now! mb nil)))))
    (verify-boundaries! rt)))

(deftest immediate-take-distinguishes-empty-nil-and-false
  (let [rt (runtime)]
    (binding [ec/*execution-context* rt]
      (let [mb (sync/mailbox)]
        (is (identical? sync/nothing (sync/take-now! mb nil)))
        (mb nil) (mb false)
        (is (nil? (sync/take-now! mb nil)))
        (is (false? (sync/take-now! mb nil)))
        (is (identical? sync/nothing (sync/take-now! mb nil)))))
    (verify-boundaries! rt)))

(deftest a-mailbox-handle-does-not-select-a-different-runtime
  (let [left (runtime) right (runtime) mb (sync/create-mailbox left)
        before (owned/snapshot right)]
    (binding [ec/*execution-context* right]
      (is (= :unknown-mailbox
             (try (mb :wrong-world) nil
                  (catch #?(:clj Throwable :cljs :default) error (:error (ex-data error))))))
      (is (= :unknown-mailbox
             (try (sync/take-now! mb nil) nil
                  (catch #?(:clj Throwable :cljs :default) error (:error (ex-data error)))))))
    (is (= before (owned/snapshot right)))
    (verify-boundaries! left)
    (verify-boundaries! right)))

(deftest raw-consumers-and-spins-share-the-same-fifo
  (let [rt (runtime) values (atom [])]
    (binding [ec/*execution-context* rt]
      (let [mb (sync/mailbox) middle (spin [:spin (await mb)])]
        (mb #(swap! values conj [:first %]) #(throw %))
        (observe! middle values)
        (mb #(swap! values conj [:last %]) #(throw %))
        (doseq [v [1 2 3]] (mb v))
        (is (= [[:first 1] [:spin 2] [:last 3]] @values))
        (is (identical? sync/nothing (sync/take-now! mb nil)))))
    (verify-boundaries! rt)))

(deftest anext-is-callable-and-returns-the-same-mailbox
  (let [rt (runtime) values (atom [])]
    (binding [ec/*execution-context* rt]
      (let [mb (sync/mailbox) next (aseq/anext mb)
            reader (spin (await next))]
        (is (ifn? next))
        (is (satisfies? rtp/PMailboxNext next))
        (is (identical? mb (rtp/mailbox-next-target next)))
        (observe! reader values)
        (mb nil)
        (is (= [[nil mb]] @values))
        (mb false)
        (is (= :returned (next (fn [v] (is (= [false mb] v)) :returned) #(throw %))))
        (mb :applied)
        (is (= :applied (apply next [(fn [v] (is (= [:applied mb] v)) :applied) #(throw %)])))))
    (verify-boundaries! rt)))

(deftest raw-next-callbacks-have-physical-receipts-for-pending-and-buffered-input
  (doseq [buffered? [false true]]
    (let [rt (runtime) values (atom [])]
      (binding [ec/*execution-context* rt]
        (let [mb (sync/mailbox)]
          (when buffered? (mb 41))
          ((aseq/anext mb)
           (fn [value]
             (is (some #(and (= :mailbox-callback (:kind %)) (:physical? %))
                       (vals (:native (owned/snapshot rt)))))
             (swap! values conj value))
           #(throw %))
          (when-not buffered? (mb 41))
          (is (= [[41 mb]] @values))
          (is (empty? (:native (owned/snapshot rt))))))
      (verify-boundaries! rt))))

(deftest a-live-raw-callback-can-forward-to-another-live-mailbox
  (let [rt (runtime) values (atom [])]
    (binding [ec/*execution-context* rt]
      (let [source (sync/mailbox) target (sync/mailbox)]
        (source (fn [value]
                  (target (inc value))
                  (target #(swap! values conj %) #(throw %)))
                #(throw %))
        (source 41)
        (is (= [42] @values))
        (is (empty? (:native (owned/snapshot rt))))))
    (verify-boundaries! rt)))

(deftest live-mailbox-forwarding-does-not-grant-unrelated-cell-access
  (let [rt (runtime) refused (atom []) values (atom [])]
    (binding [ec/*execution-context* rt]
      (let [source (sync/mailbox) target (sync/mailbox)
            a (runtime-atom/atom 7) s (signal/signal 8) d (sync/deferred)]
        (source
         (fn [value]
           (doseq [[kind read-value] [[:atom #(deref a)]
                                      [:signal #(deref s)]
                                      [:deferred #(rtp/read-public-deferred rt d)]]]
             (try (read-value)
                  (catch #?(:clj Throwable :cljs :default) _
                    (swap! refused conj kind))))
           (target value)
           (target #(swap! values conj %) #(throw %)))
         #(throw %))
        (source 42)
        (is (= [:atom :signal :deferred] @refused))
        (is (= [42] @values))
        (is (= 7 @a))
        (is (= 8 @s))))
    (verify-boundaries! rt)))

(deftest callable-next-backlogs-reuse-their-existing-physical-frame
  (doseq [protected? [false true]]
    (let [rt (context/create-execution-context {:engine :owned :audit? false}) values (atom []) samples (atom [])]
      (binding [ec/*execution-context* rt]
        (let [mb (sync/mailbox)
              rf (completing (fn [sum value]
                               (when (zero? (mod value 1000))
                                 (swap! samples conj (count (:native (owned/snapshot rt)))))
                               (+ sum value)))
              operation (aseq/transduce (take 5000) rf 0 mb)]
          (dotimes [i 5000] (mb i))
          (if protected?
            (observe! (spin (await-finalization operation)) values)
            (binding [pcps/*in-trampoline* false]
              (operation #(swap! values conj %) #(throw %))))
          (is (= [12497500] @values))
          (is (= 5 (count @samples)))
          (is (every? #(= 1 %) @samples))
          (is (empty? (:native (owned/snapshot rt)))))))))

(deftest a-cancelled-reader-never-consumes-the-next-message
  (doseq [next? [false true]]
    (let [rt (runtime) cancelled (atom []) values (atom [])]
      (binding [ec/*execution-context* rt]
        (let [mb (sync/mailbox)
              first (spin (await (if next? (aseq/anext mb) mb)))
              second (spin (await mb)) reason (ex-info "withdraw consumer" {})]
          (first #(swap! cancelled conj [:ok %]) #(swap! cancelled conj [:error %]))
          (observe! second values)
          (cancel! rt first reason)
          (mb 42)
          (is (= [[:error reason]] @cancelled))
          (is (= [42] @values))
          (is (identical? sync/nothing (sync/take-now! mb nil)))))
      (verify-boundaries! rt))))

(deftest reactive-reentry-replaces-the-consumer-without-losing-messages
  (let [rt (runtime) values (atom [])]
    (binding [ec/*execution-context* rt]
      (let [trigger (signal/signal 0) mb (sync/mailbox)
            reader (spin [(iv/get-new (track trigger)) (await mb)])]
        (observe! reader values)
        (reset! trigger 1)
        (reset! trigger 2)
        (mb :only)
        (is (= [[2 :only]] @values))
        (is (identical? sync/nothing (sync/take-now! mb nil)))))
    (verify-boundaries! rt)))

(deftest a-throwing-raw-consumer-consumes-its-message-and-does-not-poison-the-queue
  (let [rt (runtime) values (atom []) failure (ex-info "consumer failed after entry" {})]
    (binding [ec/*execution-context* rt]
      (let [mb (sync/mailbox)]
        (mb (fn [_] (throw failure)) #(throw %))
        (mb #(swap! values conj %) #(throw %))
        (is (identical? failure (try (mb :poison) nil
                                     (catch #?(:clj Throwable :cljs :default) error error))))
        (mb :next)
        (is (= [:next] @values))
        (is (identical? sync/nothing (sync/take-now! mb nil)))))
    (verify-boundaries! rt)))

(deftest a-live-raw-callback-can-rearm-and-the-new-consumer-remains-owned
  (doseq [buffered? [false true]]
    (let [rt (runtime) shared (atom nil) owner-terminal (atom nil)
          entered (atom []) rejected (atom [])]
      (binding [ec/*execution-context* rt]
        (let [owner (spin (reset! shared (sync/mailbox))
                          (await-finalization (fn [succeed _] (reset! owner-terminal succeed))))]
          (owner (fn [_]) (fn [_]))
          (when buffered? (@shared :first) (@shared :second))
          (@shared (fn [first-value]
                     (swap! entered conj [:first first-value])
                     (@shared (fn [second-value]
                                (swap! entered conj [:second second-value]))
                              #(swap! rejected conj %)))
                   #(throw %))
          (when-not buffered? (@shared :first))
          (cancel! rt owner (ex-info "retire rearmed consumer" {}))
          (@owner-terminal :returned)
          (is (= (if buffered? [[:first :first] [:second :second]] [[:first :first]]) @entered))
          (is (= (if buffered? 0 1) (count @rejected)))
          (is (empty? (:native (owned/snapshot rt))))
          (is (empty? (:cleanup-cells (owned/snapshot rt))))))
      (verify-boundaries! rt))))

(deftest retired-cleanup-can-poll-its-owned-mailbox-without-registering-work
  (let [rt (runtime) values (atom []) taken (atom []) body (sync/create-deferred rt)]
    (binding [ec/*execution-context* rt]
      (let [task (spin
                  (let [mb (sync/mailbox)]
                    (mb nil)
                    (mb false)
                    (try (await body)
                         (finally
                           (swap! taken conj (sync/take-now! mb nil))
                           (swap! taken conj (sync/take-now! mb nil))))))
            reason (ex-info "cleanup polling" {})]
        (task #(swap! values conj [:ok %]) #(swap! values conj [:error %]))
        (cancel! rt task reason)
        (is (= [nil false] @taken))
        (is (= [[:error reason]] @values))
        (is (empty? (:native (owned/snapshot rt))))
        (is (empty? (:cleanup-cells (owned/snapshot rt))))))
    (verify-boundaries! rt)))

(deftest protected-mailbox-callback-transforms-the-message-before-terminal
  (doseq [queued? [false true]]
    (let [rt (runtime) values (atom []) entered (atom [])]
      (binding [ec/*execution-context* rt]
        (let [mb (sync/mailbox)
              task (spin
                    (await-finalization
                     (fn [succeed fail]
                       (mb (fn [v] (swap! entered conj v) (succeed (inc v))) fail))))]
          (when queued? (mb 41))
          (observe! task values)
          (when-not queued? (mb 41))
          (is (= [41] @entered))
          (is (= [42] @values))
          (is (empty? (:native (owned/snapshot rt))))))
      (verify-boundaries! rt))))

(deftest protected-mailbox-and-deferred-waits-compose-after-parent-cancellation
  (let [rt (runtime) values (atom []) steps (atom [])]
    (binding [ec/*execution-context* rt]
      (let [first (sync/mailbox) second (sync/deferred) third (sync/mailbox)
            task (spin
                  (let [state (signal/signal 7)]
                    (try
                      (await-finalization
                       (fn [succeed fail]
                         (first (fn [a]
                                  (swap! steps conj [:first a @state])
                                  (second (fn [b]
                                            (swap! steps conj [:second b @state])
                                            (third (fn [c]
                                                     (swap! steps conj [:third c @state])
                                                     (succeed (+ a b c)))
                                                   fail))
                                          fail))
                                fail)))
                      (finally (swap! steps conj [:finally @state])))))
            reason (ex-info "cancel composed resource wait" {})]
        (task #(swap! values conj [:ok %]) #(swap! values conj [:error %]))
        (cancel! rt task reason)
        (is (= [[:error reason]] @values))
        (first 10)
        (second 20)
        (is (= [[:first 10 7] [:second 20 7]] @steps))
        (third 12)
        (is (= [[:first 10 7] [:second 20 7] [:third 12 7] [:finally 7]] @steps))
        (is (= [[:error reason]] @values))
        (is (empty? (:native (owned/snapshot rt))))
        (is (empty? (:cleanup-cells (owned/snapshot rt))))))
    (verify-boundaries! rt)))

(deftest protected-terminal-detaches-the-other-consumer-without-eating-its-message
  (let [rt (runtime) values (atom []) entered (atom [])]
    (binding [ec/*execution-context* rt]
      (let [left (sync/mailbox) right (sync/mailbox)
            task (spin
                  (await-finalization
                   (fn [succeed fail]
                     (left (fn [v] (swap! entered conj :left) (succeed v)) fail)
                     (right (fn [v] (swap! entered conj :right) (succeed v)) fail))))]
        (observe! task values)
        (left 42)
        (right :remaining)
        (is (= [:left] @entered))
        (is (= [42] @values))
        (is (= :remaining (sync/take-now! right nil)))))
    (verify-boundaries! rt)))

(deftest a-protected-consumer-keeps-a-mailbox-after-its-other-owner-retires
  (let [rt (runtime) shared (atom nil) owner-terminal (atom nil) values (atom [])]
    (binding [ec/*execution-context* rt]
      (let [owner (spin (reset! shared (sync/mailbox))
                        (await-finalization (fn [succeed _] (reset! owner-terminal succeed))))]
        (owner (fn [_]) (fn [_]))
        (let [reader (spin (await-finalization
                            (fn [succeed fail] (@shared #(succeed (inc %)) fail))))]
          (observe! reader values)
          (cancel! rt owner (ex-info "retire mailbox owner" {}))
          (@owner-terminal :returned)
          (is (nil? (get-in (owned/snapshot rt) [:entities (entity-id @shared)])))
          (@shared 41)
          (is (= [42] @values))
          (is (empty? (:cleanup-cells (owned/snapshot rt)))))))
    (verify-boundaries! rt)))

#?(:clj
   (deftest a-post-survives-the-release-of-its-original-retained-owner-key
     (let [rt (runtime) shared (atom nil) values (atom []) entered (promise) leave (promise)]
       (binding [ec/*execution-context* rt]
         (let [trigger (signal/signal 0) gate (sync/deferred) driver (sync/deferred)
               owner (spin (let [mb (sync/mailbox)]
                             (reset! shared mb)
                             (track trigger)
                             :owner))]
           (owner (fn [_]) (fn [_]))
           (@shared :seed)
           (let [reader (spin
                         (await-finalization
                          (fn [succeed fail]
                            (@shared (fn [_]
                                       (gate (fn [_] (@shared succeed fail)) fail))
                                     fail))))]
             (observe! reader values)
             (reset! trigger 1)
             (@shared :first)
             (driver (fn [_]
                       (@shared (fn [v]
                                  (is (= :first v))
                                  (deliver entered true)
                                  @leave
                                  (@shared :returned))
                                #(throw %)))
                     #(throw %))
             (let [producer (future (driver :start))]
               (try
                 (is (= true (deref entered 10000 ::timeout)))
                 (cancel! rt owner (ex-info "retire newer resource owner" {}))
                 (finally (deliver leave true)))
               (is (not= ::timeout (deref producer 10000 ::timeout))))
             (is (empty? @values))
             (gate :continue)
             (is (= [:returned] @values))
             (is (empty? (:cleanup-cells (owned/snapshot rt)))))))
       (verify-boundaries! rt))))

(deftest pending-takes-use-the-current-resource-owner-at-physical-entry
  (doseq [raw? [false true]]
    (let [rt (runtime) shared (atom nil) values (atom []) receipts (atom [])]
      (binding [ec/*execution-context* rt]
        (let [trigger (signal/signal 0)
              owner (spin (let [mb (sync/mailbox)]
                            (reset! shared mb)
                            (track trigger)
                            :owner))
              capture! (fn [value]
                         (swap! receipts conj (mapv :owner (filter #(= :mailbox-callback (:kind %))
                                                                   (vals (:native (owned/snapshot rt))))))
                         value)]
          (owner (fn [_]) (fn [_]))
          (if raw?
            (@shared #(swap! values conj (capture! %)) #(throw %))
            (observe! (spin (capture! (await @shared))) values))
          (reset! trigger 1)
          (let [current-owner (get-in (owned/snapshot rt) [:entities (entity-id @shared) :owner])]
            (@shared 42)
            (is (= [42] @values))
            (is (= [[[owned/w current-owner]]] @receipts)))
          (cancel! rt owner (ex-info "dispose migrated source" {}))))
      (verify-boundaries! rt))))

(deftest a-pending-raw-rejection-keeps-the-exact-closing-owner-after-migration
  (let [rt (runtime) shared (atom nil) receipts (atom [])]
    (binding [ec/*execution-context* rt]
      (let [trigger (signal/signal 0)
            owner (spin (let [mb (sync/mailbox)]
                          (reset! shared mb)
                          (track trigger)
                          :owner))]
        (owner (fn [_]) (fn [_]))
        (@shared (fn [_] (is false "Closed source delivered input"))
                 (fn [_]
                   (swap! receipts conj (mapv :owner (filter #(= :mailbox-callback (:kind %))
                                                             (vals (:native (owned/snapshot rt))))))))
        (reset! trigger 1)
        (let [closing-owner (get-in (owned/snapshot rt) [:entities (entity-id @shared) :owner])]
          (cancel! rt owner (ex-info "close migrated source" {}))
          (is (= [[[owned/w closing-owner]]] @receipts)))
        (is (empty? (:native (owned/snapshot rt))))))
    (verify-boundaries! rt)))

(deftest retiring-a-mailbox-owner-rejects-ordinary-consumers
  (doseq [next? [false true]]
    (let [rt (runtime) shared (atom nil) owner-terminal (atom nil) outcomes (atom []) steps (atom [])]
      (binding [ec/*execution-context* rt]
        (let [owner (spin (reset! shared (sync/mailbox))
                          (await-finalization (fn [succeed _] (reset! owner-terminal succeed))))]
          (owner (fn [_]) (fn [_]))
          (let [consumer (spin (try (await (if next? (aseq/anext @shared) @shared))
                                    (finally (swap! steps conj :finally))))]
            (consumer #(swap! outcomes conj [:ok %]) #(swap! outcomes conj [:error %]))
            (cancel! rt owner (ex-info "source owner retires" {}))
            (@owner-terminal :returned)
            (is (= 1 (count @outcomes)))
            (is (= :error (ffirst @outcomes)))
            (is (= [:finally] @steps))
            (is (empty? (:native (owned/snapshot rt)))))))
      (verify-boundaries! rt))))

(deftest retiring-a-mailbox-owner-enters-the-raw-rejection-with-a-physical-receipt
  (let [rt (runtime) shared (atom nil) owner-terminal (atom nil) rejected (atom [])]
    (binding [ec/*execution-context* rt]
      (let [owner (spin (reset! shared (sync/mailbox))
                        (await-finalization (fn [succeed _] (reset! owner-terminal succeed))))]
        (owner (fn [_]) (fn [_]))
        (@shared (fn [_] (is false "Retired source delivered a message"))
                 (fn [error]
                   (let [receipts (filter #(= :mailbox-callback (:kind %))
                                          (vals (:native (owned/snapshot rt))))]
                     (is (= 1 (count receipts)))
                     (is (= :executing (:phase (first receipts))))
                     (is (= :error (:variant (first receipts))))
                     (is (true? (:physical? (first receipts)))))
                   (swap! rejected conj error)))
        (cancel! rt owner (ex-info "reject raw take" {}))
        (@owner-terminal :returned)
        (is (= 1 (count @rejected)))
        (is (empty? (:native (owned/snapshot rt))))
        (is (empty? (:cleanup-cells (owned/snapshot rt))))))
    (verify-boundaries! rt)))

(bindings/register-spin-scope-key! :mailbox-test/scope)

(deftest mailbox-delivery-restores-lexical-scope-without-changing-world
  (let [rt (runtime) mb (sync/create-mailbox rt) values (atom []) world (rtp/world-identity rt)
        task (binding [ec/*execution-context* (assoc rt :bindings {:mailbox-test/scope :consumer})]
               (spin
                (address/with-key :mailbox
                  (let [v (await (aseq/anext mb))]
                    [v (get-in (ec/current-execution-context) [:bindings :mailbox-test/scope])
                     (address/current-key (ec/current-execution-context))
                     (identical? world (rtp/world-identity (ec/current-execution-context)))]))))]
    (binding [ec/*execution-context* rt] (observe! task values))
    (binding [ec/*execution-context* (assoc rt :bindings {:mailbox-test/scope :producer})]
      (mb false)
      (is (= :producer (get-in (ec/current-execution-context) [:bindings :mailbox-test/scope]))))
    (is (= [[[false mb] :consumer :mailbox true]] @values))
    (verify-boundaries! rt)))

(deftest queued-mailbox-and-next-backlogs-stay-stack-safe
  (doseq [next? [false true]]
    (let [rt (context/create-execution-context {:engine :owned :audit? false}) values (atom [])]
      (binding [ec/*execution-context* rt]
        (let [mb (sync/mailbox)
              task (spin
                    (loop [i 0 sum 0]
                      (if (= i 5000)
                        sum
                        (let [value (await (if next? (aseq/anext mb) mb))]
                          (recur (inc i) (+ sum (if next? (first value) value)))))))]
          (dotimes [i 5000] (mb i))
          (observe! task values)
          (is (= [12497500] @values))
          (is (identical? sync/nothing (sync/take-now! mb nil))))))))

#?(:clj
   (deftest cancellation-and-posting-conserve-each-message-at-the-entry-boundary
     (doseq [next? [false true]]
       (let [rt (context/create-execution-context {:engine :owned :audit? false})]
         (binding [ec/*execution-context* rt]
           (dotimes [i 100]
             (let [mb (sync/mailbox) entered (atom []) outcomes (atom []) start (promise)
                   task (spin
                         (let [value (await (if next? (aseq/anext mb) mb))]
                           (swap! entered conj (if next? (first value) value))))]
               (task #(swap! outcomes conj [:ok %]) #(swap! outcomes conj [:error %]))
               (let [producer (future @start (mb i))
                     canceller (future @start (cancel! rt task (ex-info "cancel race" {})))]
                 (deliver start true)
                 (is (not= ::timeout (deref producer 10000 ::timeout)))
                 (is (not= ::timeout (deref canceller 10000 ::timeout)))
                 (let [remaining (sync/take-now! mb nil)
                       inputs (cond-> @entered (not (identical? sync/nothing remaining)) (conj remaining))]
                   (is (= [i] inputs) "Cancellation returns only a reservation that never entered"))
                 (is (= 1 (count @outcomes)))))))))))

#?(:clj
   (deftest raw-mailbox-callback-keeps-physical-evidence-through-owner-retirement
     (let [rt (runtime) shared (atom nil) owner-terminal (atom nil) values (atom [])
           neighbor (atom nil) refused (atom [])
           entered (promise) leave (promise) finished (atom []) reason (ex-info "retire raw source" {})]
       (binding [ec/*execution-context* rt]
         (let [owner (spin (reset! neighbor (signal/signal 7))
                           (reset! shared (sync/mailbox))
                           (await-finalization (fn [succeed _] (reset! owner-terminal succeed))))]
           (owner #(swap! values conj [:ok %]) #(swap! values conj [:error %]))
           (@shared (fn [v]
                      (deliver entered true)
                      @leave
                      (try (swap! refused conj (deref @neighbor))
                           (catch Throwable error (swap! refused conj (:error (ex-data error)))))
                      (swap! finished conj v))
                    #(throw %))
           (let [producer (future (@shared 42))]
             (try
               (is (= true (deref entered 10000 ::timeout)))
               (is (some #(= :mailbox-callback (:kind %)) (vals (:native (owned/snapshot rt)))))
               (cancel! rt owner reason)
               (@owner-terminal :returned)
               (is (= :error (:variant (rtp/computation-result rt owner (spin-core/spin-id owner)))))
               (is (some #(= :mailbox-callback (:kind %)) (vals (:native (owned/snapshot rt)))))
               (is (empty? @finished))
               (finally (deliver leave true)))
             (is (not= ::timeout (deref producer 10000 ::timeout)))
             (is (= [42] @finished))
             (is (= [:missing-cleanup-cell] @refused))
             (is (= [[:error reason]] @values))
             (is (empty? (:native (owned/snapshot rt))))
             (is (empty? (:cleanup-cells (owned/snapshot rt)))))))
       (verify-boundaries! rt))))

(deftest raw-root-mailbox-callback-does-not-invent-a-computation-run
  (let [rt (runtime) values (atom [])]
    (binding [ec/*execution-context* rt]
      (let [mb (sync/mailbox)]
        (mb (fn [v]
              (is (empty? (:runs (owned/snapshot rt))))
              (is (some #(= :mailbox-callback (:kind %)) (vals (:native (owned/snapshot rt)))))
              (swap! values conj v))
            #(throw %))
        (mb 42)
        (is (= [42] @values))
        (is (empty? (:native (owned/snapshot rt))))))
    (verify-boundaries! rt)))

#?(:clj
   (defn- next-without-a-stack-mailbox-reference [rt]
     (binding [ec/*execution-context* rt]
       (let [mb (sync/mailbox)]
         (dotimes [i 10] (mb i))
         {:holder (atom (aseq/anext mb)) :id (entity-id mb)}))))

#?(:clj
   (defn- mailbox-handles-without-a-retained-world []
     (let [rt (context/create-execution-context {:engine :owned :audit? false})
           mb (sync/create-mailbox rt)]
       {:world (java.lang.ref.WeakReference. rt) :mailbox mb :next (aseq/anext mb)})))

#?(:clj
   (deftest mailbox-next-retains-the-allocation-and-unreachable-buffers-are-reclaimed
     (let [rt (context/create-execution-context {:engine :owned :audit? false})
           {:keys [holder id]} (next-without-a-stack-mailbox-reference rt)]
       (dotimes [_ 5]
         (System/gc)
         (is (contains? (:entities (owned/snapshot rt)) id)))
       (reset! holder nil)
       (loop [remaining 100]
         (System/gc)
         (when (and (pos? remaining) (contains? (:entities (owned/snapshot rt)) id))
           (Thread/sleep 10)
           (recur (dec remaining))))
       (is (not (contains? (:entities (owned/snapshot rt)) id))))))

#?(:clj
   (deftest mailbox-and-next-handles-do-not-retain-a-world
     (let [{:keys [world mailbox next]} (mailbox-handles-without-a-retained-world)]
       (loop [remaining 100]
         (System/gc)
         (when (and (pos? remaining) (.get ^java.lang.ref.WeakReference world))
           (Thread/sleep 10)
           (recur (dec remaining))))
       (is (nil? (.get ^java.lang.ref.WeakReference world)))
       (is (identical? mailbox (rtp/mailbox-next-target next)))
       (java.lang.ref.Reference/reachabilityFence mailbox)
       (java.lang.ref.Reference/reachabilityFence next))))

#?(:clj
   (defn- mailbox-with-an-unconsumed-tail [rt]
     (binding [ec/*execution-context* rt]
       (let [mb (sync/mailbox) payload (Object.)]
         (mb payload)
         (mb :remaining)
         (is (identical? payload (sync/take-now! mb nil)))
         {:mailbox mb :payload (java.lang.ref.WeakReference. payload)}))))

#?(:clj
   (deftest consuming-a-message-releases-it-while-later-messages-stay-buffered
     (let [rt (context/create-execution-context {:engine :owned :audit? false})
           {:keys [mailbox payload]} (mailbox-with-an-unconsumed-tail rt)]
       (loop [remaining 100]
         (System/gc)
         (when (and (pos? remaining) (.get ^java.lang.ref.WeakReference payload))
           (Thread/sleep 10)
           (recur (dec remaining))))
       (is (nil? (.get ^java.lang.ref.WeakReference payload)))
       (binding [ec/*execution-context* rt]
         (is (= :remaining (sync/take-now! mailbox nil)))))))
