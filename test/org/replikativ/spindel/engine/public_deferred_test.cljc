(ns org.replikativ.spindel.engine.public-deferred-test
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.engine.context :as context]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.bindings :as bindings]
            [org.replikativ.spindel.engine.addressing :as address]
            [org.replikativ.spindel.engine.impl.owned :as owned]
            [org.replikativ.spindel.engine.owned-runtime-test :refer [verify-boundaries!]]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.await :refer [await await-finalization]]
            [org.replikativ.spindel.effects.track :refer [track]]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.signal :as signal]))

(defn- runtime [] (context/create-execution-context {:engine :owned :audit? true}))
(defn- entity-id [d] (:id (rtp/deferred-payload d)))
(defn- pending-count [rt d]
  (count (filter #(= [:entity owned/w (entity-id d)] (:debtor %))
                 (vals (:obligations (owned/snapshot rt))))))
(defn- observe! [s values] (s #(swap! values conj %) #(throw %)))
(defn- cancel! [rt s reason]
  (rtp/cancel-computation! rt s (spin-core/spin-id s) (spin-core/spin-body s) reason))

#?(:cljs
   (deftest cljs-core-await-keeps-managed-spin-dependency-and-cancellation
     (doseq [cancel? [false true]]
       (let [rt (runtime) values (atom []) errors (atom []) suffixes (atom [])
             reason (ex-info "cancel core await" {})]
         (binding [ec/*execution-context* rt]
           (let [d (sync/deferred)
                 child (spin (await d))
                 s (spin (let [value (cljs.core/await child)]
                           (swap! suffixes conj value)
                           value))]
             (s #(swap! values conj %) #(swap! errors conj %))
             (let [dependencies (filter #(= [:entity owned/w (spin-core/spin-id child)] (:debtor %))
                                        (vals (:obligations (owned/snapshot rt))))]
               (is (= 1 (count dependencies)))
               (is (= #{:run} (set (map (comp first :creditor) dependencies)))))
             (when cancel? (cancel! rt s reason))
             (d false)
             (is (= (if cancel? [] [false]) @values))
             (is (= (if cancel? [reason] []) @errors))
             (is (= (if cancel? [] [false]) @suffixes))
             (is (zero? (pending-count rt d)))))
         (verify-boundaries! rt)))))

(deftest deferred-single-assignment-preserves-nil-false-and-exception-values
  (doseq [value [nil false 42 (ex-info "successful data" {})
                 {:type spin-core/spin-cancelled :variant :error :payload false}
                 (owned/->Failure (ex-info "successful internal-shaped data" {}))]]
    (let [rt (runtime) values (atom [])]
      (binding [ec/*execution-context* rt]
        (let [d (sync/deferred) s (spin (await d))]
          (observe! s values)
          (is (empty? @values))
          (is (= 1 (pending-count rt d)))
          (is (true? (d value)))
          (is (false? (d :ignored)))
          (is (= 1 (count @values)))
          (is (identical? value (first @values)))
          (is (= :ok (:variant (rtp/computation-result rt s (spin-core/spin-id s)))))
          (is (= {:assigned? true :value value} (rtp/read-public-deferred rt d)))
          (is (zero? (pending-count rt d)))))
      (verify-boundaries! rt))))

(deftest unclaimed-assignment-and-callable-claim-have-distinct-ordering
  (let [rt (runtime) values (atom [])]
    (binding [ec/*execution-context* rt]
      (let [s (spin (let [d (sync/deferred)]
                      (is (= :first (sync/deliver! d :first)))
                      (is (true? (d :claimed-second)))
                      (is (false? (d :third)))
                      (await d)))]
        (observe! s values)
        (is (= [:first] @values)))
      (let [d (sync/deferred)]
        (is (= :assigned (sync/deliver! d :assigned)))
        (is (true? (d :too-late)) "Assignment alone did not claim callable delivery")
        (is (false? (d :later)))
        (is (= {:assigned? true :value :assigned} (rtp/read-public-deferred rt d)))))
    (verify-boundaries! rt)))

(deftest assigned-deferred-await-keeps-the-current-trampoline-stack-safe
  (let [rt (context/create-execution-context {:engine :owned :audit? false}) values (atom [])]
    (binding [ec/*execution-context* rt]
      (let [d (sync/deferred)
            s (spin (loop [i 0]
                      (if (< i 5000) (recur (+ i (await d))) i)))]
        (d 1)
        (observe! s values)
        (is (= [5000] @values))
        (is (zero? (pending-count rt d)))))))

(deftest actual-public-reactive-reentry-removes-obsolete-deferred-readers
  (let [rt (runtime) values (atom [])]
    (binding [ec/*execution-context* rt]
      (let [a (signal/signal 1) b (signal/signal 10) d (sync/deferred)
            child (spin (iv/get-new (track a)))
            parent (spin (let [x (await child) y (iv/get-new (track b)) z (await d)] [x y z]))]
        (observe! parent values)
        (is (= 1 (pending-count rt d)))
        (reset! b 20)
        (is (= 1 (pending-count rt d)))
        (reset! a 2)
        (is (= 1 (pending-count rt d)))
        (is (empty? @values))
        (d false)
        (is (= [[2 20 false]] @values))
        (is (zero? (pending-count rt d)))
        (reset! b 30)
        (is (= [[2 20 false] [2 30 false]] @values))))
    (verify-boundaries! rt)))

(deftest cancellation-detaches-reader-and-joins-protected-deferred-acknowledgement
  (let [rt (runtime) values (atom []) cleanup (atom [])]
    (binding [ec/*execution-context* rt]
      (let [d (sync/deferred) ack (sync/deferred)
            s (spin (let [state (signal/signal 7)]
                      (try (await d)
                           (finally
                             (swap! cleanup conj [:start @state])
                             (await-finalization ack)
                             (swap! cleanup conj [:returned @state])))))
            reason (ex-info "cancel exact reader" {})]
        (s #(swap! values conj [:ok %]) #(swap! values conj [:error %]))
        (cancel! rt s reason)
        (is (= [[:error reason]] @values))
        (is (= [[:start 7]] @cleanup))
        (is (zero? (pending-count rt d)))
        (d :late)
        (is (= [[:error reason]] @values))
        (is (= [[:start 7]] @cleanup))
        (ack nil)
        (is (= [[:start 7] [:returned 7]] @cleanup))
        (is (empty? (:cleanup-cells (owned/snapshot rt))))
        (is (empty? (:native (owned/snapshot rt))))))
    (verify-boundaries! rt)))

(deftest an-owned-deferred-acknowledgement-survives-logical-source-retirement
  (let [rt (runtime) ack-ref (atom nil) ready (atom nil) values (atom []) cleaned (atom [])]
    (binding [ec/*execution-context* rt]
      (let [s (spin (let [ack (sync/deferred)]
                      (reset! ack-ref ack)
                      (try (await-finalization (fn [r _] (reset! ready r)))
                           (finally (await-finalization ack) (swap! cleaned conj :done)))))
            reason (ex-info "owned cleanup source" {})]
        (s #(swap! values conj [:ok %]) #(swap! values conj [:error %]))
        (cancel! rt s reason)
        (is (= [[:error reason]] @values))
        (@ready :begin-cleanup)
        (is (empty? @cleaned))
        (is (nil? (get-in (owned/snapshot rt) [:entities (entity-id @ack-ref)])))
        (is (some? (try (rtp/read-public-deferred rt @ack-ref) nil
                        (catch #?(:clj Throwable :cljs :default) error error)))
            "External retained authority grants delivery, not ordinary observation")
        (@ack-ref false)
        (is (= [:done] @cleaned))
        (is (empty? (:cleanup-cells (owned/snapshot rt))))))
    (verify-boundaries! rt)))

(deftest direct-host-deferred-readers-share-assignment-and-leave-no-obligation
  (let [rt (runtime) values (atom [])]
    (binding [ec/*execution-context* rt]
      (let [d (sync/deferred)]
        (is (= spin-core/incomplete (d #(swap! values conj [:a %]) #(throw %))))
        (is (= spin-core/incomplete (d #(swap! values conj [:b %]) #(throw %))))
        (is (= 2 (pending-count rt d)))
        (d 9)
        (is (= #{[:a 9] [:b 9]} (set @values)))
        (is (zero? (pending-count rt d)))
        (is (= :inline (d (fn [v] (is (= 9 v)) :inline) #(throw %))))))
    (verify-boundaries! rt)))

(deftest protected-reader-retains-another-computations-deferred-allocation
  (let [rt (runtime) shared (atom nil) owner-gate (atom nil)
        owner-values (atom []) reader-values (atom [])]
    (binding [ec/*execution-context* rt]
      (let [owner (spin (let [d (sync/deferred)]
                          (reset! shared d)
                          (await-finalization (fn [r _] (reset! owner-gate r)))))
            reason (ex-info "owner retires" {})]
        (owner #(swap! owner-values conj [:ok %]) #(swap! owner-values conj [:error %]))
        (let [reader (spin (await-finalization @shared))]
          (observe! reader reader-values)
          (cancel! rt owner reason)
          (@owner-gate :finish-owner)
          (is (= [[:error reason]] @owner-values))
          (is (nil? (get-in (owned/snapshot rt) [:entities (entity-id @shared)])))
          (is (empty? @reader-values))
          (@shared 17)
          (is (= [17] @reader-values))
          (is (empty? (:cleanup-cells (owned/snapshot rt)))))))
    (verify-boundaries! rt)))

(deftest throwing-deferred-host-observers-do-not-strand-other-committed-deliveries
  (let [rt (runtime) called (atom []) failure (ex-info "host observer failed" {})]
    (binding [ec/*execution-context* rt]
      (let [d (sync/deferred)]
        (d (fn [v] (swap! called conj [:bad v]) (throw failure)) #(throw %))
        (d (fn [v] (swap! called conj [:good v])) #(throw %))
        (is (identical? failure (try (d :done) nil (catch #?(:clj Throwable :cljs :default) error error))))
        (is (= #{[:bad :done] [:good :done]} (set @called)))
        (is (zero? (pending-count rt d)))
        (is (false? (d :ignored)))
        (is (nil? (d (fn [_] nil) #(throw %))))
        (is (false? (d (fn [_] false) #(throw %))))))
    (verify-boundaries! rt)))

(deftest deferred-control-is-not-application-cell-state
  (let [rt (runtime)]
    (binding [ec/*execution-context* rt]
      (let [d (sync/deferred) id (entity-id d)
            ordinary (rtp/allocate-runtime-cell! rt 9 {:kind :deferred})]
        (is (some? (try (rtp/runtime-cell-value rt id) nil
                        (catch #?(:clj Throwable :cljs :default) error error))))
        (is (some? (try (rtp/swap-runtime-cell! rt d id (constantly :corrupted) nil) nil
                        (catch #?(:clj Throwable :cljs :default) error error))))
        (is (= :atom (get-in (owned/snapshot rt) [:entities (:id ordinary) :kind])))
        (is (= 9 (rtp/runtime-cell-value rt (:id ordinary))))
        (is (= {:assigned? false :value nil} (rtp/read-public-deferred rt d)))))
    (verify-boundaries! rt)))

#?(:clj
   (deftest concurrent-deferred-callers-have-one-claim-and-one-assignment
     (let [rt (context/create-execution-context {:engine :owned :audit? false}) values (atom [])]
       (binding [ec/*execution-context* rt]
         (let [d (sync/deferred) task (spin (await d))]
           (observe! task values)
           (let [workers (doall (for [value (range 16)] (future [value (d value)])))
                 results (mapv #(deref % 10000 ::timeout) workers)
                 winners (filterv #(and (vector? %) (second %)) results)]
             (is (not-any? #{::timeout} results))
             (is (= 1 (count winners)))
             (is (= [(ffirst winners)] @values))
             (is (= {:assigned? true :value (ffirst winners)} (rtp/read-public-deferred rt d)))
             (is (zero? (pending-count rt d)))))))))

(deftest reactive-ownership-migration-keeps-protected-deferred-aliases-consistent
  (let [rt (runtime) shared (atom nil) gates (atom []) owner-values (atom [])
        left (atom []) right (atom [])]
    (binding [ec/*execution-context* rt]
      (let [trigger (signal/signal 0)
            owner (spin (let [d (sync/deferred)]
                          (reset! shared d)
                          (track trigger)
                          (await-finalization (fn [r _] (swap! gates conj r)))))
            reason (ex-info "retire migrated owner" {})]
        (owner #(swap! owner-values conj [:ok %]) #(swap! owner-values conj [:error %]))
        (let [b (spin (await-finalization @shared))]
          (observe! b left)
          (reset! trigger 1)
          (let [c (spin (await-finalization @shared))]
            (observe! c right)
            (is (= 2 (count (:cleanup-cells (owned/snapshot rt)))))
            (cancel! rt owner reason)
            (is (nil? (get-in (owned/snapshot rt) [:entities (entity-id @shared)])))
            (@shared 31)
            (is (= [31] @left @right))
            (is (= [[:error reason]] @owner-values))
            (doseq [gate @gates] (gate :physical-return))
            (is (empty? (:cleanup-cells (owned/snapshot rt))))
            (is (empty? (:native (owned/snapshot rt))))))))
    (verify-boundaries! rt)))

#?(:clj
   (defn- deferred-allocation-without-a-stack-reference [rt]
     (let [d (sync/create-deferred rt)]
       {:holder (atom d) :id (entity-id d)})))

#?(:clj
   (defn- deferred-without-a-retained-world []
     (let [rt (context/create-execution-context {:engine :owned :audit? false})]
       {:world (java.lang.ref.WeakReference. rt) :deferred (sync/create-deferred rt)})))

#?(:clj
   (deftest deferred-host-anchor-retains-allocation-without-retaining-a-world
     (let [rt (context/create-execution-context {:engine :owned :audit? false})
           {:keys [holder id]} (deferred-allocation-without-a-stack-reference rt)]
       (dotimes [_ 5]
         (System/gc)
         (is (= {:assigned? false :value nil} (rtp/read-public-deferred rt @holder))))
       (reset! holder nil)
       (loop [remaining 100]
         (System/gc)
         (when (and (pos? remaining) (contains? (:entities (owned/snapshot rt)) id))
           (Thread/sleep 10)
           (recur (dec remaining))))
       (is (not (contains? (:entities (owned/snapshot rt)) id))))
     (let [{:keys [world deferred]} (deferred-without-a-retained-world)]
       (loop [remaining 100]
         (System/gc)
         (when (and (pos? remaining) (.get ^java.lang.ref.WeakReference world))
           (Thread/sleep 10)
           (recur (dec remaining))))
       (is (nil? (.get ^java.lang.ref.WeakReference world)))
       (is (satisfies? rtp/PDeferred deferred)))))

(bindings/register-spin-scope-key! :deferred-test/scope)

(deftest deferred-resumption-restores-lexical-scope-on-the-selected-world
  (let [rt (context/create-execution-context {:engine :owned :audit? true
                                              :bindings {:deferred-test/scope :base}})
        d (sync/create-deferred rt) values (atom []) world (rtp/world-identity rt)
        task (binding [ec/*execution-context* (assoc rt :bindings {:deferred-test/scope :construction})]
               (spin [(address/with-key :inside
                        (let [value (await d)]
                          [value (address/current-key (ec/current-execution-context))
                           (get-in (ec/current-execution-context) [:bindings :deferred-test/scope])
                           (identical? world (rtp/world-identity (ec/current-execution-context)))]))
                      (address/current-key (ec/current-execution-context))
                      (get-in (ec/current-execution-context) [:bindings :deferred-test/scope])]))]
    (binding [ec/*execution-context* (assoc rt :bindings {:deferred-test/scope :caller})]
      (observe! task values))
    (binding [ec/*execution-context* (assoc rt :bindings {:deferred-test/scope :producer})]
      (d 42)
      (is (= :producer (get-in (ec/current-execution-context) [:bindings :deferred-test/scope]))))
    (is (= [[[42 :inside :construction true] nil :construction]] @values))
    (verify-boundaries! rt)))

(deftest deferred-host-rejection-restores-the-observers-scope
  (let [rt (runtime) shared (atom nil) gate (atom nil) scopes (atom [])]
    (binding [ec/*execution-context* rt]
      (let [owner (spin (reset! shared (sync/deferred))
                        (await-finalization (fn [r _] (reset! gate r))))]
        (owner (fn [_]) (fn [_]))
        (binding [ec/*execution-context* (assoc rt :bindings {:deferred-test/scope :observer})]
          (@shared (fn [_] (is false "Unassigned Deferred succeeded"))
                   (fn [_]
                     (swap! scopes conj [(get-in (ec/current-execution-context) [:bindings :deferred-test/scope])
                                         (ec/same-world? rt (ec/current-execution-context))]))))
        (binding [ec/*execution-context* (assoc rt :bindings {:deferred-test/scope :canceller})]
          (cancel! rt owner (ex-info "owner cancelled" {}))
          (is (= :canceller (get-in (ec/current-execution-context) [:bindings :deferred-test/scope]))))
        (is (= [[:observer true]] @scopes))
        (@gate :physical-return)))
    (verify-boundaries! rt)))

(deftest protected-deferred-preserves-the-operation-continuation
  (let [rt (runtime) values (atom []) steps (atom [])]
    (binding [ec/*execution-context* rt]
      (let [d (sync/deferred)
            task (spin (await-finalization
                        (fn [succeed fail]
                          (d (fn [value]
                               (swap! steps conj :transform)
                               (succeed (inc value)))
                             fail))))]
        (observe! task values)
        (is (empty? @values))
        (d 41)
        (is (= [:transform] @steps))
        (is (= [42] @values))))
    (verify-boundaries! rt)))

;; These literal public observations independently test continuation semantics.
;; The symbolic operation participant still needs its own refinement coverage.
(defn- operation-runtime []
  (context/create-execution-context {:engine :owned :audit? false}))

(deftest protected-assigned-deferred-runs-the-callback-before-the-outer-continuation
  (let [rt (operation-runtime) steps (atom []) values (atom [])]
    (binding [ec/*execution-context* rt]
      (let [d (sync/deferred)
            task (spin
                  (let [value (await-finalization
                               (fn [succeed fail]
                                 (d (fn [value]
                                      (swap! steps conj :transform)
                                      (succeed (inc value))
                                      (swap! steps conj :callback-return))
                                    fail)
                                 (swap! steps conj :startup-return)))]
                    (swap! steps conj :outer)
                    value))]
        (d 41)
        (observe! task values)
        (is (= [42] @values))
        (is (= [:transform :callback-return :startup-return :outer] @steps))
        (is (empty? (:native (owned/snapshot rt))))))))

(deftest protected-operation-can-wait-again-without-completing-the-parent
  (let [rt (operation-runtime) steps (atom []) values (atom [])]
    (binding [ec/*execution-context* rt]
      (let [first (sync/deferred) second (sync/deferred)
            task (spin
                  (await-finalization
                   (fn [succeed fail]
                     (first (fn [a]
                              (swap! steps conj [:first a])
                              (second (fn [b]
                                        (swap! steps conj [:second b])
                                        (succeed (+ a b)))
                                      fail))
                            fail))))]
        (observe! task values)
        (first 19)
        (is (= [[:first 19]] @steps))
        (is (empty? @values))
        (second 23)
        (is (= [[:first 19] [:second 23]] @steps))
        (is (= [42] @values))
        (is (empty? (:native (owned/snapshot rt))))
        (is (empty? (:cleanup-cells (owned/snapshot rt))))))))

(deftest protected-operation-keeps-each-registration-on-the-same-source
  (let [rt (operation-runtime) entered (atom []) values (atom [])]
    (binding [ec/*execution-context* rt]
      (let [d (sync/deferred)
            task (spin
                  (await-finalization
                   (fn [succeed fail]
                     (d (fn [v] (swap! entered conj [:a v])) fail)
                     (d (fn [v]
                          (swap! entered conj [:b v])
                          (succeed @entered))
                        fail))))]
        (observe! task values)
        (d false)
        (is (= [[:a false] [:b false]] @entered))
        (is (= [[[:a false] [:b false]]] @values))
        (is (empty? (:native (owned/snapshot rt))))))))

(deftest protected-operation-keeps-independent-registrations-in-either-delivery-order
  (doseq [order [[:left :right] [:right :left]]]
    (let [rt (operation-runtime) entered (atom []) values (atom [])]
      (binding [ec/*execution-context* rt]
        (let [left (sync/deferred) right (sync/deferred)
              receive (fn [succeed side value]
                        (swap! entered conj [side value])
                        (when (= 2 (count @entered)) (succeed @entered)))
              task (spin
                    (await-finalization
                     (fn [succeed fail]
                       (left #(receive succeed :left %) fail)
                       (right #(receive succeed :right %) fail))))]
          (observe! task values)
          (({:left left :right right} (first order)) nil)
          (is (empty? @values))
          (({:left left :right right} (second order)) nil)
          (is (= (mapv #(vector % nil) order) @entered))
          (is (= [@entered] @values))
          (is (empty? (:native (owned/snapshot rt)))))))))

(deftest protected-terminal-invalidates-other-unclaimed-registrations
  (let [rt (operation-runtime) entered (atom []) values (atom [])]
    (binding [ec/*execution-context* rt]
      (let [left (sync/deferred) right (sync/deferred)
            task (spin
                  (await-finalization
                   (fn [succeed fail]
                     (left (fn [v] (swap! entered conj :left) (succeed v)) fail)
                     (right (fn [v] (swap! entered conj :right) (succeed v)) fail))))]
        (observe! task values)
        (left 42)
        (right :obsolete)
        (is (= [:left] @entered))
        (is (= [42] @values))
        (is (empty? (:native (owned/snapshot rt))))))))

(deftest protected-operation-callback-return-precedes-parent-resumption
  (let [rt (operation-runtime) steps (atom []) values (atom [])]
    (binding [ec/*execution-context* rt]
      (let [d (sync/deferred)
            task (spin
                  (let [value (await-finalization
                               (fn [succeed fail]
                                 (d (fn [v]
                                      (swap! steps conj :entered)
                                      (succeed v)
                                      (is (empty? @values))
                                      (swap! steps conj :returning))
                                    fail)))]
                    (swap! steps conj :outer)
                    value))]
        (observe! task values)
        (d 42)
        (is (= [:entered :returning :outer] @steps))
        (is (= [42] @values))))))

(deftest protected-delivery-during-startup-waits-for-startup-return
  (let [rt (operation-runtime) steps (atom []) values (atom [])]
    (binding [ec/*execution-context* rt]
      (let [d (sync/deferred)
            task (spin
                  (await-finalization
                   (fn [succeed fail]
                     (d (fn [v]
                          (swap! steps conj :callback)
                          (succeed (inc v)))
                        fail)
                     (d 41)
                     (is (empty? @values))
                     (is (empty? @steps))
                     (swap! steps conj :startup-return))))]
        (observe! task values)
        (is (= [:startup-return :callback] @steps))
        (is (= [42] @values))))))

(deftest protected-deferred-callback-values-do-not-encode-error-disposition
  (doseq [assigned? [false true]
          value [nil false (ex-info "callback data" {})
                 {:type spin-core/spin-cancelled :variant :error :payload false}]]
    (let [rt (operation-runtime) values (atom []) entered (atom 0)]
      (binding [ec/*execution-context* rt]
        (let [d (sync/deferred)
              task (spin
                    (await-finalization
                     (fn [succeed fail]
                       (d (fn [v] (swap! entered inc) (succeed [:wrapped v])) fail))))]
          (when assigned? (d value))
          (observe! task values)
          (when-not assigned? (d value))
          (is (= 1 @entered))
          (is (= 1 (count @values)))
          (is (= :wrapped (ffirst @values)))
          (is (identical? value (second (first @values)))))))))

(deftest cancelled-protected-operation-keeps-owned-state-through-sequential-waits
  (let [rt (operation-runtime) steps (atom []) values (atom [])]
    (binding [ec/*execution-context* rt]
      (let [first (sync/deferred) second (sync/deferred)
            task (spin
                  (let [state (signal/signal 7)]
                    (try
                      (await-finalization
                       (fn [succeed fail]
                         (first (fn [a]
                                  (swap! steps conj [:first a @state])
                                  (second (fn [b]
                                            (swap! steps conj [:second b @state])
                                            (succeed (+ a b)))
                                          fail))
                                fail)))
                      (finally (swap! steps conj [:finally @state])))))
            reason (ex-info "retire operation parent" {})]
        (task #(swap! values conj [:ok %]) #(swap! values conj [:error %]))
        (cancel! rt task reason)
        (is (= [[:error reason]] @values))
        (is (seq (:cleanup-cells (owned/snapshot rt))))
        (first 19)
        (is (= [[:first 19 7]] @steps))
        (is (seq (:cleanup-cells (owned/snapshot rt))))
        (second 23)
        (is (= [[:first 19 7] [:second 23 7] [:finally 7]] @steps))
        (is (= [[:error reason]] @values))
        (is (empty? (:native (owned/snapshot rt))))
        (is (empty? (:cleanup-cells (owned/snapshot rt))))))))

(deftest protected-callback-restores-its-lexical-context-in-the-selected-world
  (let [rt (operation-runtime) d (sync/create-deferred rt) values (atom [])
        world (rtp/world-identity rt)
        task (binding [ec/*execution-context* (assoc rt :bindings {:deferred-test/scope :operation})]
               (spin
                (address/with-key :protected
                  (await-finalization
                   (fn [succeed fail]
                     (d (fn [v]
                          (succeed [v
                                    (get-in (ec/current-execution-context) [:bindings :deferred-test/scope])
                                    (address/current-key (ec/current-execution-context))
                                    (identical? world (rtp/world-identity (ec/current-execution-context)))]))
                        fail))))))]
    (binding [ec/*execution-context* (assoc rt :bindings {:deferred-test/scope :observer})]
      (observe! task values))
    (binding [ec/*execution-context* (assoc rt :bindings {:deferred-test/scope :producer})]
      (d false)
      (is (= :producer (get-in (ec/current-execution-context) [:bindings :deferred-test/scope]))))
    (is (= [[false :operation :protected true]] @values))))

(deftest live-protected-callback-can-use-its-existing-signal-payload
  (let [rt (runtime) values (atom []) reads (atom [])]
    (binding [ec/*execution-context* rt]
      (let [d (sync/deferred)
            task (spin
                  (let [state (signal/signal 7)]
                    (await-finalization
                     (fn [succeed fail]
                       (d (fn [_]
                            (swap! reads conj @state)
                            (swap! state inc)
                            (succeed @state))
                          fail)))))]
        (observe! task values)
        (d :ready)
        (is (= [7] @reads))
        (is (= [8] @values))))
    (verify-boundaries! rt)))

(deftest live-protected-callback-can-read-an-acquired-deferred-after-its-owner-retires
  (let [rt (runtime) shared (atom nil) owner-terminal (atom nil) values (atom []) reads (atom [])]
    (binding [ec/*execution-context* rt]
      (let [owner (spin
                   (reset! shared (sync/deferred))
                   (await-finalization (fn [succeed _] (reset! owner-terminal succeed))))]
        (owner (fn [_]) (fn [_]))
        (let [reader (spin
                      (await-finalization
                       (fn [succeed fail]
                         (@shared (fn [v]
                                    (swap! reads conj (rtp/read-public-deferred (ec/current-execution-context) @shared))
                                    (succeed (inc v)))
                                  fail))))]
          (observe! reader values)
          (cancel! rt owner (ex-info "retire resource owner" {}))
          (@owner-terminal :returned)
          (is (nil? (get-in (owned/snapshot rt) [:entities (entity-id @shared)])))
          (@shared 41)
          (is (= [{:assigned? true :value 41}] @reads))
          (is (= [42] @values))
          (is (empty? (:cleanup-cells (owned/snapshot rt)))))))
    (verify-boundaries! rt)))

(deftest protected-callback-failure-rejects-the-operation-before-terminal
  (let [rt (runtime) values (atom []) failure (ex-info "operation callback failed" {})]
    (binding [ec/*execution-context* rt]
      (let [d (sync/deferred)
            task (spin (await-finalization
                        (fn [_ fail]
                          (d (fn [_] (throw failure)) fail))))]
        (task #(swap! values conj [:ok %]) #(swap! values conj [:error %]))
        (d 41)
        (is (= [[:error failure]] @values))
        (is (empty? (:native (owned/snapshot rt))))))
    (verify-boundaries! rt)))

(deftest returning-from-a-protected-callback-does-not-select-the-outer-result
  (let [rt (operation-runtime) values (atom []) terminal (atom nil) entered (atom [])]
    (binding [ec/*execution-context* rt]
      (let [d (sync/deferred)
            task (spin
                  (await-finalization
                   (fn [succeed fail]
                     (reset! terminal succeed)
                     (d (fn [v] (swap! entered conj v) :callback-return-value) fail))))]
        (observe! task values)
        (d 41)
        (is (= [41] @entered))
        (is (empty? @values))
        (is (= :waiting (:phase (first (vals (:native (owned/snapshot rt)))))))
        (@terminal 42)
        (is (= [42] @values))
        (@terminal :duplicate)
        (is (= [42] @values))
        (is (empty? (:native (owned/snapshot rt))))))))

(deftest late-protected-callback-errors-preserve-the-selected-result
  (doseq [startup? [true false]]
    (let [rt (runtime) values (atom []) failure (ex-info "after terminal" {})]
      (binding [ec/*execution-context* rt]
        (let [d (sync/deferred)
              task (spin
                    (await-finalization
                     (fn [succeed fail]
                       (let [finish (fn [v] (succeed v) (throw failure))]
                         (if startup? (finish 42) (d finish fail))))))
              error (try
                      (observe! task values)
                      (when-not startup? (d 42))
                      nil
                      (catch #?(:clj Throwable :cljs :default) error error))]
          (is (identical? failure error))
          (is (= [42] @values))
          (is (empty? (:native (owned/snapshot rt))))))
      (verify-boundaries! rt))))

(deftest cleanup-can-start-another-protected-operation-on-the-same-ticket
  (let [rt (operation-runtime) values (atom []) cleaned (atom [])]
    (binding [ec/*execution-context* rt]
      (let [body (sync/deferred) first (sync/deferred) second (sync/deferred)
            task (spin
                  (let [state (signal/signal 7)]
                    (try (await body)
                         (finally
                           (let [a (await-finalization
                                    (fn [succeed fail] (first #(succeed (inc %)) fail)))
                                 b (await-finalization
                                    (fn [succeed fail] (second #(succeed (inc %)) fail)))]
                             (swap! cleaned conj [a b @state]))))))
            reason (ex-info "sequential cleanup operations" {})]
        (task #(swap! values conj [:ok %]) #(swap! values conj [:error %]))
        (cancel! rt task reason)
        (first 19)
        (is (empty? @cleaned))
        (is (seq (:cleanup-cells (owned/snapshot rt))))
        (second 21)
        (is (= [[20 22 7]] @cleaned))
        (is (= [[:error reason]] @values))
        (is (empty? (:native (owned/snapshot rt))))))))

(deftest assigned-protected-callback-chain-releases-consumed-registrations
  (let [rt (operation-runtime) values (atom []) samples (atom []) entered (atom 0)]
    (binding [ec/*execution-context* rt]
      (let [d (sync/deferred)
            task (spin
                  (await-finalization
                   (fn [succeed fail]
                     (dotimes [i 5000]
                       (when (zero? (mod i 1000))
                         (swap! samples conj (owned/storage-stats rt)))
                       (d (fn [_] (swap! entered inc)) fail))
                     (swap! samples conj (owned/storage-stats rt))
                     (succeed @entered))))]
        (d :ready)
        (observe! task values)
        (is (= [5000] @values))
        (is (= 6 (count @samples)))
        (is (every? #(= 1 (:protected-operations %)) @samples))
        (is (every? #(<= (:operation-registrations %) 1) @samples))
        (is (every? #(<= (:operation-callback-references %) 2) @samples))
        (is (every? #(= 1 (:operation-frames %)) @samples))
        (is (= [0 0 0 0]
               ((juxt :protected-operations :operation-registrations :operation-frames :operation-callback-references)
                (owned/storage-stats rt))))))))

#?(:clj
   (defn- completed-operation-with-escaped-terminal []
     (let [rt (operation-runtime) terminal (atom nil) values (atom [])]
       (binding [ec/*execution-context* rt]
         (let [d (sync/deferred)
               task (spin
                     (await-finalization
                      (fn [succeed fail]
                        (reset! terminal succeed)
                        (d (fn [v] (succeed (inc v))) fail))))]
           (observe! task values)
           (d 41)
           (is (= [42] @values))))
       {:world (java.lang.ref.WeakReference. rt) :terminal @terminal})))

#?(:clj
   (deftest escaped-completed-operation-terminal-does-not-retain-its-world
     (let [{:keys [world terminal]} (completed-operation-with-escaped-terminal)]
       (loop [remaining 100]
         (System/gc)
         (when (and (pos? remaining) (.get ^java.lang.ref.WeakReference world))
           (Thread/sleep 10)
           (recur (dec remaining))))
       (is (nil? (.get ^java.lang.ref.WeakReference world)))
       (terminal :obsolete)
       (java.lang.ref.Reference/reachabilityFence terminal))))

#?(:clj
   (deftest protected-callback-terminal-does-not-release-a-physically-executing-frame
     (doseq [startup? [true false]]
       (let [rt (operation-runtime) values (atom []) steps (atom [])
             entered (promise) leave (promise) reason (ex-info "cancel physical callback" {})]
         (binding [ec/*execution-context* rt]
           (let [d (sync/deferred)
                 task (spin
                       (let [state (signal/signal 7)]
                         (try
                           (await-finalization
                            (fn [succeed fail]
                              (let [finish (fn [v]
                                             (succeed v)
                                             (deliver entered true)
                                             @leave
                                             (swap! steps conj [:callback @state]))]
                                (if startup? (finish 42) (d finish fail)))))
                           (finally (swap! steps conj [:finally @state])))))
                 start! #(task (fn [v] (swap! values conj [:ok v]))
                               (fn [e] (swap! values conj [:error e])))
                 worker (if startup?
                          (future (start!))
                          (do (start!) (future (d 42))))]
             (try
               (is (= true (deref entered 10000 ::timeout)))
               (is (empty? @values))
               (is (empty? @steps))
               (cancel! rt task reason)
               (is (= :error (:variant (rtp/computation-result rt task (spin-core/spin-id task)))))
               (is (identical? reason (:payload (rtp/computation-result rt task (spin-core/spin-id task)))))
               (is (seq (:cleanup-cells (owned/snapshot rt))))
               (is (empty? @steps))
               (finally (deliver leave true)))
             (is (not= ::timeout (deref worker 10000 ::timeout)))
             (is (= [[:callback 7] [:finally 7]] @steps))
             (is (= [[:error reason]] @values))
             (is (empty? (:native (owned/snapshot rt))))
             (is (empty? (:cleanup-cells (owned/snapshot rt))))))))))
