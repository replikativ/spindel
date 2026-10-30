(ns org.replikativ.spindel.engine.public-cancellation-test
  (:require #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])
            [org.replikativ.spindel.atom :as ratom]
            [org.replikativ.spindel.effects.await :refer [await await-finalization]]
            [org.replikativ.spindel.spin.cps :as cps]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.impl.owned :as owned #?@(:cljs [:include-macros true])]
            [org.replikativ.spindel.engine.owned-runtime-test :refer [verify-boundaries!]]
            [org.replikativ.spindel.spin.core :as spin]))

(defn- reason [label] (ex-info label {:type spin/spin-cancelled}))
(defn- result [rt target] (rtp/computation-result rt target (spin/spin-id target)))
(defn- cancel! [rt target value]
  (rtp/cancel-computation! rt target (spin/spin-id target) (spin/spin-body target) value))
(defn- observe! [rt target values]
  (binding [ec/*execution-context* rt]
    (target #(swap! values conj [:ok %]) #(swap! values conj [:error %]))))

(deftest cancellation-before-first-invocation-is-a-stable-public-outcome
  (let [rt (owned/runtime {:audit? true :cps-exit? true}) runs (atom 0) values (atom [])
        target (binding [ec/*execution-context* rt]
                 (spin/make-spin (fn [r _] (r (swap! runs inc))) :never {}))
        first (reason "first") second (reason "second")]
    (cancel! rt target first)
    (is (= {:variant :error :payload first :clean? true} (result rt target)))
    (is (= {:run nil :result (owned/->Failure first)}
           (get-in (owned/snapshot rt) [:entities :never :cancelled-completion])))
    (cancel! rt target second)
    (is (identical? first (:payload (result rt target))))
    (is (nil? (observe! rt target values)))
    (is (= [[:error first]] @values))
    (is (zero? @runs))
    #?(:clj (is (identical? first (try (binding [ec/*execution-context* rt] @target)
                                       nil (catch Throwable error error)))))
    (is (empty? (:native (owned/snapshot rt))))
    (verify-boundaries! rt)))

(deftest public-cancel-replaces-a-completed-cache-without-inventing-finalization
  (let [rt (owned/runtime {:audit? true :cps-exit? true}) values (atom [])
        target (binding [ec/*execution-context* rt]
                 (spin/make-spin (fn [r _] (r 42)) :completed {}))]
    (is (= 42 (observe! rt target values)))
    (binding [ec/*execution-context* rt] (spin/cancel-spin! target))
    (let [failure (:payload (result rt target))]
      (is (= spin/spin-cancelled (:type (ex-data failure))))
      (is (true? (:clean? (result rt target))))
      (is (nil? (observe! rt target values)))
      (is (= [[:ok 42] [:error failure]] @values)))
    (is (empty? (:native (owned/snapshot rt))))
    (verify-boundaries! rt)))

(deftest protected-cleanup-retains-the-first-reason-and-a-fresh-entry-wins
  (let [rt (owned/runtime {:audit? true :cps-exit? true}) values (atom []) trace (atom [])
        late (atom nil) cleanup (atom nil)
        first (reason "first") second (reason "second")
        target
        (binding [ec/*execution-context* rt]
          (let [child (spin/make-spin
                       (fn [r j] (owned/await-host-effect! (fn [resolve _] (reset! late resolve) nil) r j))
                       :child {})]
            (cps/spin
             (let [cell (ratom/atom 41)]
               (try
                 (await child)
                 (catch #?(:clj Throwable :cljs :default) error
                   (swap! trace conj [:reason error])
                   (throw error))
                 (finally
                   (swap! trace conj [:finally @cell])
                   (await-finalization (fn [resolve _] (reset! cleanup resolve)))
                   (swap! cell inc)
                   (swap! trace conj [:returned @cell])))))))
        id (spin/spin-id target)]
    (is (= spin/incomplete (observe! rt target values)))
    (cancel! rt target first)
    (is (= [[:error first]] @values))
    (is (= [[:reason first] [:finally 41]] @trace))
    (is (identical? first (:payload (result rt target))))
    (is (false? (owned/join-ready? rt [id 1])))
    (let [before (:native (owned/snapshot rt))]
      (cancel! rt target second)
      (is (= before (:native (owned/snapshot rt))) "Repeated cancel cannot replace or advance the protected wait"))
    (let [replacement (binding [ec/*execution-context* rt]
                        (spin/make-spin (fn [r _] (r :fresh)) id {'version 2}))
          fresh-values (atom [])]
      (is (= :fresh (observe! rt replacement fresh-values)))
      (is (= [[:ok :fresh]] @fresh-values))
      (is (nil? (get-in (owned/snapshot rt) [:entities id :cancelled-completion])))
      (@late :obsolete)
      (is (= :fresh (:payload (result rt replacement))))
      (@cleanup :closed)
      (is (= [[:reason first] [:finally 41] [:returned 42]] @trace))
      (is (= {:variant :ok :payload :fresh :clean? true} (result rt replacement))))
    (is (owned/join-ready? rt [id 1]))
    (is (empty? (:cleanup-cells (owned/snapshot rt))))
    (verify-boundaries! rt)))

(deftest cancellation-does-not-revoke-already-committed-host-deliveries
  (let [rt (owned/runtime {:audit? true :cps-exit? true}) settle (atom nil) calls (atom [])
        second-state (atom nil)
        target (binding [ec/*execution-context* rt]
                 (spin/make-spin
                  (fn [r j] (owned/await-host-effect! (fn [resolve _] (reset! settle resolve) nil) r j))
                  :committed {}))]
    (let [callback (fn [label]
                     (fn [value]
                       (let [delivered (swap! calls conj [label value])]
                         (if (= 1 (count delivered))
                           (spin/cancel-spin! target)
                           (reset! second-state (:variant (result rt target)))))))]
      (binding [ec/*execution-context* rt]
        (target (callback :first) #(throw %))
        (target (callback :second) #(throw %))))
    (@settle 42)
    (is (= #{[:first 42] [:second 42]} (set @calls)))
    (is (= 2 (count @calls)))
    (is (= :error @second-state) "The second committed success survives the first callback's cancel")
    (is (= :error (:variant (result rt target))))
    (verify-boundaries! rt)))

(deftest dropped-public-target-cannot-invalidate-a-new-live-incarnation
  (let [rt (owned/runtime {:audit? true :cps-exit? true}) values (atom [])
        old (binding [ec/*execution-context* rt]
              (spin/make-spin (fn [r _] (r 1)) :reused {'value 1}))]
    (observe! rt old values)
    (owned/release-idle! rt)
    (let [current (binding [ec/*execution-context* rt]
                    (spin/make-spin (fn [r _] (r 2)) :reused {'value 2}))]
      (observe! rt current values)
      (let [before (owned/snapshot-family rt)]
        (doseq [operation [(fn [] (rtp/register-computation! rt old :reused (spin/spin-body old)))
                           (fn [] (observe! rt old values))
                           (fn [] (cancel! rt old (reason "unavailable")))]]
          (is (= :idle-cache-released
                 (try (operation) nil
                      (catch #?(:clj Exception :cljs :default) error (:error (ex-data error))))))
          (is (= before (owned/snapshot-family rt)))))
      (is (= {:variant :ok :payload 2 :clean? true} (result rt current))))
    (verify-boundaries! rt)))

(deftest cancellation-shaped-user-errors-do-not-install-an-explicit-fence
  (let [rt (owned/runtime {:audit? true :cps-exit? true}) values (atom [])
        ordinary (reason "ordinary rejection")
        target (binding [ec/*execution-context* rt]
                 (spin/make-spin (fn [_ j] (j ordinary)) :ordinary {}))]
    (is (nil? (observe! rt target values)))
    (is (= [[:error ordinary]] @values))
    (is (nil? (get-in (owned/snapshot rt) [:entities :ordinary :cancelled-completion])))
    (verify-boundaries! rt)))

#?(:clj
   (deftest cancellation-commits-before-the-running-physical-body-returns
     (let [rt (owned/runtime {:audit? true :cps-exit? true}) entered (promise) release (promise)
           finally-count (atom 0) values (atom [])
           target (binding [ec/*execution-context* rt]
                    (spin/make-spin
                     (fn [r _]
                       (try
                         (deliver entered true)
                         (when-not (= true (deref release 5000 ::timeout))
                           (throw (ex-info "Physical body test timed out" {})))
                         (r :late-success)
                         (finally (swap! finally-count inc))))
                     :physical {}))
           first (reason "physical cancellation")
           worker (future (observe! rt target values))]
       (try
         (is (= true (deref entered 5000 ::timeout)))
         (cancel! rt target first)
         (is (identical? first (:payload (result rt target))))
         (is (zero? @finally-count))
         (is (false? (owned/join-ready? rt [:physical 1])))
         (finally (deliver release true)))
       (is (not= ::timeout (deref worker 5000 ::timeout)))
       (is (= 1 @finally-count))
       (is (= [[:error first]] @values))
       (is (identical? first (:payload (result rt target))))
       (is (owned/join-ready? rt [:physical 1]))
       (verify-boundaries! rt))))

(deftest cancellation-drops-an-obsolete-target-publication-before-delivery
  (let [rt (owned/runtime {:audit? true :cps-exit? true}) holder (atom nil) values (atom [])
        first (reason "before delivery")
        target (binding [ec/*execution-context* rt]
                 (spin/make-spin
                  (fn [r _]
                    ;; Completion queues a publication. The public cancel
                    ;; happens on this slice before the drain can process it.
                    (r :obsolete)
                    (cancel! rt @holder first))
                  :queued {'holder holder}))]
    (reset! holder target)
    (observe! rt target values)
    (is (= [[:error first]] @values))
    (is (= {:variant :error :payload first :clean? true} (result rt target)))
    (verify-boundaries! rt)))

(deftest armed-parent-and-host-receive-the-exact-reason-without-fencing-the-parent
  (let [rt (owned/runtime {:audit? true :cps-exit? true}) first (reason "child cancellation")
        parent-values (atom []) child-values (atom [])
        [child parent]
        (binding [ec/*execution-context* rt]
          (let [child (spin/make-spin
                       (fn [r j] (owned/await-host-effect! (fn [_ _]) r j)) :awaited {})]
            [child (cps/spin
                    (try (await child)
                         (catch #?(:clj Throwable :cljs :default) error [:caught error])))]))]
    (observe! rt parent parent-values)
    (observe! rt child child-values)
    (cancel! rt child first)
    (is (= [[:error first]] @child-values))
    (is (= [[:ok [:caught first]]] @parent-values))
    (is (nil? (get-in (owned/snapshot rt) [:entities (spin/spin-id parent) :cancelled-completion])))
    (verify-boundaries! rt)))
