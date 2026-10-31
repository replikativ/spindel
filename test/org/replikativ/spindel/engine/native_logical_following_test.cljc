(ns org.replikativ.spindel.engine.native-logical-following-test
  (:refer-clojure :exclude [await])
  (:require #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.impl.owned :as c #?@(:cljs [:include-macros true])]
            [org.replikativ.spindel.engine.lifetime :as lifetime]
            [org.replikativ.spindel.engine.lifecycle :as lifecycle]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.owned-runtime-test :refer [verify-boundaries!]]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.cps :refer [spin]]))

(defn- ignore-result [_])
(defn- world-id [rt] (let [state (c/snapshot rt)] (or (:id state) (second (:root state)))))
(defn- publish [rt]
  (rtp/fork-owned-world! rt {:world-id [:w 1] :owner (lifetime/root-scope rt)
                             :mode :following :systems #{}}))
(defn- run-obligations [rt run]
  (into {} (filter (fn [[_ row]] (= [:run (world-id rt) run] (:creditor row)))
                   (:obligations (c/snapshot rt)))))
(defn- release! [rt]
  (let [values (atom []) errors (atom [])]
    (lifecycle/observe! (rtp/request-world-release! rt :finished)
                        #(swap! values conj %) #(swap! errors conj %))
    (is (= [nil] @values))
    (is (empty? @errors))
    (doseq [[_ state] (c/snapshot-family rt)]
      (is (= :released (:status state)))
      (is (empty? (:native state)))
      (is (empty? (:cleanup-cells state))))
    (is (empty? (get-in (c/snapshot rt) [:global :custody :claims])))
    (is (empty? (get-in (c/snapshot rt) [:global :custody :by-holder])))))

(deftest armed-computation-await-follows-source-without-replaying-prefix
  (let [rt (c/runtime {:audit? true :cps-exit? true}) gate (c/ticket :worker)
        prefixes (atom []) suffixes (atom []) finalizers (atom []) values (atom []) errors (atom [])
        worker (c/cspin rt :worker
                        (swap! prefixes conj :worker)
                        (try (c/park gate)
                             (finally (swap! finalizers conj (world-id ec/*execution-context*)))))
        waiter (c/cspin rt :waiter
                        (swap! prefixes conj :waiter)
                        (let [value (c/await worker)]
                          (swap! suffixes conj [(world-id ec/*execution-context*) value])
                          value))]
    (c/observe! rt waiter #(swap! values conj %) #(swap! errors conj %))
    (let [{child :context} (publish rt)
          source-worker-run (first (for [[run row] (:runs (c/snapshot rt)) :when (= :worker (:spin row))] run))
          source-before (get-in (c/snapshot rt) [:runs source-worker-run])
          copied (c/snapshot child)
          obligations (vals (run-obligations child [:waiter 1]))]
      (is (= {:worker 1 :waiter 1} (frequencies @prefixes)))
      (is (= :parked (:status source-before)))
      (is (some? source-worker-run))
      (doseq [run [source-worker-run [:waiter 1]]]
        (is (= :inherited (get-in copied [:runs run :status])))
        (is (not (contains? (get-in copied [:runs run]) :cps-entered?))))
      (is (= [:armed] (mapv :slot obligations)))
      (is (= [[:entity (world-id rt) :worker]] (mapv :debtor obligations)))
      (is (= #{[:bundle (world-id child) #{:worker}]} (:fdeps (c/snapshot rt))))
      (is (not-any? :join-bundle (:queue (c/snapshot rt))))
      (verify-boundaries! rt)
      (c/drain! rt)
      (is (some #(and (= :bundle (first %)) (= (world-id child) (second %)))
                (:fdeps (c/snapshot rt))))
      (is (= source-before (get-in (c/snapshot rt) [:runs source-worker-run])))
      (c/resume-ticket! rt (c/pending-ticket rt gate) 42)
      (is (= [42] @values))
      (is (= #{[(world-id rt) 42] [(world-id child) 42]} (set @suffixes)))
      (is (= 2 (count @suffixes)))
      (is (= {:worker 1 :waiter 1} (frequencies @prefixes)))
      (is (= [(world-id rt)] @finalizers))
      ;; This active dormant copy still supports its completed allocation
      ;; owner; an actual later entity-owner release cancels it without entry.
      (is (= :inherited (get-in (c/snapshot child) [:runs source-worker-run :status])))
      (is (= 42 (get-in (c/snapshot child) [:entities :waiter :result])))
      (is (empty? @errors))
      (release! rt)
      (is (= [:finished] @errors))
      (is (= [(world-id rt)] @finalizers))
      (verify-boundaries! rt))))

(deftest inherited-cancellation-before-and-after-drain-has-no-finally
  (doseq [drained? [false true]]
    (let [rt (c/runtime {:audit? true :cps-exit? true}) gate (c/ticket :worker)
          finalizers (atom []) suffixes (atom [])
          worker (c/cspin rt :worker (c/park gate))
          waiter (c/cspin rt :waiter
                          (try
                            (let [value (c/await worker)]
                              (swap! suffixes conj [(world-id ec/*execution-context*) value]))
                            (finally (swap! finalizers conj (world-id ec/*execution-context*)))))]
      (c/observe! rt waiter ignore-result ignore-result)
      (let [{child :context} (publish rt)]
        (when drained? (c/drain! rt))
        (c/cancel-spin! child waiter)
        (is (empty? @finalizers))
        (is (empty? (run-obligations child [:waiter 1])))
        (is (empty? (:native (c/snapshot child))))
        (is (empty? (:cleanup-cells (c/snapshot child))))
        (is (c/join-ready? child [:waiter 1]))
        (verify-boundaries! rt)
        (c/resume-ticket! rt (c/pending-ticket rt gate) :source)
        (is (= [[(world-id rt) :source]] @suffixes))
        (is (= [(world-id rt)] @finalizers))
        (release! rt)
        (is (= [(world-id rt)] @finalizers))
        (verify-boundaries! rt)))))

(deftest consumed-track-keeps-following-the-source-and-preserves-descendant-scopes
  (let [rt (c/runtime {:audit? true :cps-exit? true}) source (c/signal rt :source 3)
        gate (c/ticket :waiter) after (c/ticket :after-track) prefixes (atom 0) observations (atom [])
        intervals (atom [])
        task (c/cspin rt :waiter
                      (swap! prefixes inc)
                      (let [outer (lifetime/open-scope! rt :outer)
                            inner (lifetime/open-scope! rt :inner outer)]
                        (binding [ec/*owner-scope* inner]
                          (c/signal rt :nested-cell :retained)))
                      (let [interval (c/track source) value (iv/get-new interval)]
                        (swap! intervals conj [(world-id ec/*execution-context*) (iv/get-old interval) value])
                        (swap! observations conj [(world-id ec/*execution-context*) value])
                        (c/park gate)
                        (c/park after)))]
    (c/observe! rt task ignore-result ignore-result)
    (let [{child :context} (publish rt) copied (c/snapshot child)
          obligations (vals (run-obligations child [:waiter 1]))]
      (is (= #{:track :await-once} (set (map :kind obligations))))
      (is (= [:consumed] (mapv :slot (filter #(= :track (:kind %)) obligations))))
      (is (= [:waiter 1] (get-in copied [:scopes [:scope :id 0] :parent])))
      (is (= [:scope :id 0] (get-in copied [:scopes [:scope :id 1] :parent])))
      (is (= [:scope :id 1] (get-in copied [:entities :nested-cell :owner])))
      (is (= :inherited (get-in copied [:entities :nested-cell :origin])))
      (is (= :retained (get-in copied [:entities :nested-cell :result])))
      (is (not (contains? (:entities copied) :source)))
      (c/drain! rt)
      ;; A consumed inherited track is inert until an armed child slot activates it.
      (c/set-signal! rt source 7)
      (is (= :inherited (get-in (c/snapshot child) [:runs [:waiter 1] :status])))
      (is (= [[(world-id rt) 3] [(world-id rt) 7]] @observations))
      (c/resume-ticket! child (c/pending-ticket child gate) :activated)
      (c/set-signal! rt source 9)
      (is (= 1 @prefixes))
      (is (= #{[(world-id rt) 3] [(world-id rt) 7] [(world-id rt) 9] [(world-id child) 9]}
             (set @observations)))
      (is (= 4 (count @observations)))
      (is (some #{[(world-id child) 3 9]} @intervals))
      (is (= :open (get-in (c/snapshot child) [:scopes [:scope :id 1] :status])))
      (verify-boundaries! rt)
      (release! rt)
      (verify-boundaries! rt))))

(deftest admitted-bundle-does-not-outlive-disposal-or-its-debtor
  (doseq [operation [:discard-child :cancel-source :release-root]]
    (let [rt (c/runtime {:audit? true :cps-exit? true}) gate (c/ticket :worker)
          finalizers (atom []) suffixes (atom [])
          worker (c/cspin rt :worker (c/park gate))
          waiter (c/cspin rt :waiter
                          (try
                            (c/await worker)
                            (swap! suffixes conj (world-id ec/*execution-context*))
                            (finally (swap! finalizers conj (world-id ec/*execution-context*)))))]
      (c/observe! rt waiter ignore-result ignore-result)
      (let [{child :context bearer :capability} (publish rt)]
        (is (= #{[:bundle (world-id child) #{:worker}]} (:fdeps (c/snapshot rt))))
        (is (not-any? :join-bundle (:queue (c/snapshot rt))))
        (case operation
          :discard-child
          (let [values (atom []) errors (atom [])]
            (lifecycle/observe!
             (rtp/discard-owned-world! rt bearer (lifetime/root-scope rt)
                                       {:operation-id :discard-pending})
             #(swap! values conj %) #(swap! errors conj %))
            (is (= [nil] @values))
            (is (empty? @errors))
            (is (= :released (:status (c/snapshot child))))
            (is (empty? @finalizers))
            (is (= :parked (get-in (c/snapshot rt) [:runs [:waiter 1] :status]))))
          :cancel-source
          (do
            (c/cancel-spin! rt waiter)
            ;; A real foreign cancellation delivery activates the child
            ;; continuation before it enters finally; direct child retirement
            ;; above deliberately has a different no-entry contract.
            (is (= [(world-id rt) (world-id child)] @finalizers))
            (is (empty? (run-obligations child [:waiter 1])))
            (is (c/join-ready? child [:waiter 1])))
          :release-root
          (do
            (release! rt)
            (is (= [(world-id rt)] @finalizers))))
        (is (empty? @suffixes))
        (is (empty? (:fdeps (c/snapshot rt))))
        (is (empty? (:native (c/snapshot child))))
        (is (empty? (:cleanup-cells (c/snapshot child))))
        (verify-boundaries! rt)
        (when-not (= :release-root operation) (release! rt))
        (is (= (if (= :cancel-source operation)
                 [(world-id rt) (world-id child)] [(world-id rt)]) @finalizers))
        (verify-boundaries! rt)))))

(deftest public-spin-await-uses-the-copied-logical-obligation
  (let [rt (c/runtime {:audit? true :cps-exit? true}) gate (c/ticket :public-worker)
        prefixes (atom 0) suffixes (atom []) values (atom []) errors (atom [])]
    (binding [ec/*execution-context* rt]
      (let [worker (spin-core/make-spin
                    (fn [resolve reject] (c/park-effect! gate resolve reject))
                    :public-worker {'gate gate})
            waiter (spin (swap! prefixes inc)
                         (let [value (await worker)]
                           (swap! suffixes conj [(world-id ec/*execution-context*) value])
                           value))
            id (spin-core/spin-id waiter)]
        (waiter #(swap! values conj %) #(swap! errors conj %))
        (let [{child :context} (publish rt)]
          (is (= :inherited (get-in (c/snapshot child) [:runs [id 1] :status])))
          (is (= [:armed] (mapv :slot (vals (run-obligations child [id 1])))))
          (c/drain! rt)
          (c/resume-ticket! rt (c/pending-ticket rt gate) :public-result)
          (is (= 1 @prefixes))
          (is (= [:public-result] @values))
          (is (empty? @errors))
          (is (= #{[(world-id rt) :public-result] [(world-id child) :public-result]}
                 (set @suffixes)))
          (is (= 2 (count @suffixes)))
          (is (= :public-result (get-in (c/snapshot child) [:entities id :result])))
          (verify-boundaries! rt)
          (release! rt)
          (verify-boundaries! rt))))))

(deftest following-a-dormant-world-does-not-copy-its-inherited-runs
  (let [rt (c/runtime {:audit? true :cps-exit? true}) gate (c/ticket :dormant)
        entries (atom 0) task (c/cspin rt :dormant (swap! entries inc) (c/park gate))]
    (c/observe! rt task ignore-result ignore-result)
    (let [{child :context} (publish rt)
          {grandchild :context} (rtp/fork-owned-world! child {:world-id [:w 2] :owner (lifetime/root-scope child)
                                                              :mode :following :systems #{}})]
      (is (= :inherited (get-in (c/snapshot child) [:runs [:dormant 1] :status])))
      (is (empty? (:runs (c/snapshot grandchild))))
      (is (= 1 @entries))
      (verify-boundaries! rt)
      (release! rt)
      (is (= 1 @entries))
      (is (zero? (:following-worlds (c/storage-stats rt))))
      (verify-boundaries! rt))))

(deftest foreign-await-touches-the-debtor-world-only
  (let [rt (c/runtime {:audit? true :cps-exit? true}) source (c/signal rt :value 7)
        worker (c/cspin rt :observed-worker (iv/get-new (c/track source)))
        values (atom []) errors (atom [])]
    ;; A standing source observer keeps this completed reactive basis live.
    ;; Completed Runs are not selected by T19's parked-copy rule.
    (c/observe! rt worker ignore-result #(swap! errors conj %))
    (let [{child :context} (publish rt)
          waiter (c/cspin child :new-waiter (c/await worker))]
      (is (empty? (:runs (c/snapshot child))))
      (c/observe! child waiter #(swap! values conj %) #(swap! errors conj %))
      (is (= [7] @values))
      (is (empty? @errors))
      (let [handles (for [[_ handle] (:handles (c/snapshot rt))]
                      handle)
            worker-handles (filter #(= :observed-worker (:spin %)) handles)]
        (is (= 1 (count worker-handles)))
        (is (= #{(world-id rt)} (:touched (first worker-handles)))))
      (verify-boundaries! rt)
      (release! rt)
      (verify-boundaries! rt))))

(deftest activation-converts-the-whole-inherited-bundle-before-sync
  (let [rt (c/runtime {:audit? true :cps-exit? true})
        s1 (c/signal rt :first-source 1) s2 (c/signal rt :second-source 2)
        gate (c/ticket :activate) after (c/ticket :remain-live)
        task (c/cspin rt :two-tracks
                      (c/track s1)
                      (c/track s2)
                      (c/park gate)
                      (c/park after))]
    (c/observe! rt task ignore-result ignore-result)
    (let [{child :context} (publish rt)
          tracks (for [[o ob] (:obligations (c/snapshot child)) :when (= :track (:kind ob))]
                   [(nth (:debtor ob) 2) (world-id child) o])]
      (is (= #{[:bundle (world-id child) #{:first-source :second-source}]} (:fdeps (c/snapshot rt))))
      (c/resume-ticket! child (c/pending-ticket child gate) :activate)
      (is (= (set tracks) (:fdeps (c/snapshot rt))))
      (is (empty? (:releasing (c/snapshot rt))))
      (is (not-any? :fdep-ended (:queue (c/snapshot rt))))
      (verify-boundaries! rt)
      (release! rt)
      (verify-boundaries! rt))))

(deftest sealed-inherited-followers-cannot-enter-from-late-values-or-cancellation
  (doseq [completion? [true false]]
    (let [rt (c/runtime {:audit? true :cps-exit? true}) worker-gate (c/ticket :foreign-worker)
          cleanup-gate (c/ticket :cleanup-blocker) cleanup-ack (atom nil)
          suffixes (atom []) values (atom []) errors (atom [])
          worker (c/cspin rt :foreign-worker (c/park worker-gate))
          waiter (c/cspin rt :inherited-waiter
                          (let [value (c/await worker)]
                            (swap! suffixes conj [(world-id ec/*execution-context*) value])))]
      (c/observe! rt waiter ignore-result ignore-result)
      (let [{child :context bearer :capability} (publish rt)
            blocker (c/cspin child :cleanup-blocker
                             (try (c/park cleanup-gate)
                                  (finally (c/await-finalization (fn [resolve _] (reset! cleanup-ack resolve))))))]
        (c/observe! child blocker ignore-result ignore-result)
        (let [receipt (rtp/discard-owned-world! rt bearer (lifetime/root-scope rt)
                                                {:operation-id :sealed-inherited})]
          (lifecycle/observe! receipt #(swap! values conj %) #(swap! errors conj %))
          (is (= :sealed (:status (c/snapshot child))))
          (is (fn? @cleanup-ack))
          (is (empty? @values))
          (if completion?
            (c/resume-ticket! rt (c/pending-ticket rt worker-gate) :source-value)
            (c/cancel-spin! rt worker))
          (let [state (c/snapshot child)]
            (is (= :inherited (get-in state [:runs [:inherited-waiter 1] :status])))
            (is (not (contains? (get-in state [:runs [:inherited-waiter 1]]) :cps-entered?)))
            (is (not-any? #(= (world-id child) (first %)) @suffixes))
            (is (empty? @values))
            (if completion?
              (do (is (seq (:outside state)))
                  (is (some #(= :foreign-worker (get-in % [:event :completion])) (:outside state))))
              (do (is (seq (:queue state)))
                  (is (some :cancelled (:queue state)))
                  (is (pos? (:following-held (c/storage-stats rt)))))))
          (verify-boundaries! rt)
          (when completion?
            ;; Both omission and a false empty projection must fail the strict
            ;; all-world comparison while the sealed outside extent is real.
            (let [trace (vec (c/audit-trace rt)) index (dec (count trace))
                  child-id (world-id child)]
              (doseq [edit [#(dissoc % :outside) #(assoc % :outside [])]]
                (let [corrupted (update-in trace [index 2 child-id] edit)]
                  (with-redefs [c/audit-trace (constantly corrupted)]
                    (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
                                          #"Boundary mismatch" (verify-boundaries! rt))))))))
          ;; Physical cleanup keeps its own admitted callback lane. It must
          ;; progress even though B's ordinary logical queue is blocked.
          (@cleanup-ack :return)
          (is (= [nil] @values))
          (is (empty? @errors))
          (is (= :released (:status (c/snapshot child))))
          (is (zero? (:following-held (c/storage-stats rt))))
          (is (zero? (:following-outside (c/storage-stats rt))))
          (is (not-any? #(= (world-id child) (first %)) @suffixes))
          (verify-boundaries! rt)
          (release! rt)
          (verify-boundaries! rt))))))

(deftest queued-source-value-does-not-reenter-a-cancelling-foreign-track
  (let [rt (c/runtime {:audit? true :cps-exit? true})
        source (c/signal rt :source 1)
        gate (c/ticket :activate) after (c/ticket :after)
        observations (atom [])
        task (c/cspin rt :waiter
                      (let [value (iv/get-new (c/track source))]
                        (swap! observations conj [(world-id ec/*execution-context*) value]))
                      (c/park gate)
                      (c/park after))
        trigger (c/cspin rt :trigger :ready)]
    (c/observe! rt task ignore-result ignore-result)
    (let [{child :context bearer :capability} (publish rt)
          child-root (lifetime/root-scope child)
          self-cap (rtp/transfer-owned-world! rt bearer (lifetime/root-scope rt)
                                              child child-root {:operation-id :self-custody})]
      (c/resume-ticket! child (c/pending-ticket child gate) :activate)
      (try
        (let [before (get-in (c/snapshot child) [:runs [:waiter 1]])]
        ;; Both operations happen in a real host callback with nested draining
        ;; held. The value is queued before T34 cancels its foreign observer.
          (c/observe! rt trigger
                      (fn [_]
                        (c/set-signal! rt source 2)
                        (rtp/request-world-release! rt :source-release))
                      #(is false (str %)))
          (is (= [[(world-id rt) 1]] @observations))
          (is (= :released (:status (c/snapshot rt))))
          (is (= :live (:status (c/snapshot child))))
          (is (= (:status before) (get-in (c/snapshot child) [:runs [:waiter 1] :status])))
          (is (empty? (filter #(= :track (:kind %)) (vals (:obligations (c/snapshot child))))))
          (verify-boundaries! rt))
        (finally
          (lifecycle/observe! (rtp/discard-owned-world! child self-cap child-root {:operation-id :finish-child})
                              ignore-result #(is false (str %)))))
      (is (= :released (:status (c/snapshot child))))
      (verify-boundaries! rt))))

#?(:clj
   (deftest local-completion-stays-local-after-the-last-following-bucket-is-pruned
     (let [rt (c/runtime {:audit? true :cps-exit? true}) source (c/signal rt :source 1)
           gate (c/ticket :activate) after (c/ticket :after) observations (atom [])
           worker (c/cspin rt :worker (iv/get-new (c/track source)))
           waiter (c/cspin rt :waiter
                           (let [value (c/await worker)]
                             (swap! observations conj [(world-id ec/*execution-context*) value]))
                           (c/park gate)
                           (c/park after))]
       (c/observe! rt waiter ignore-result ignore-result)
       (let [{child :context} (publish rt)
             dispatch-var (ns-resolve 'org.replikativ.spindel.engine.impl.owned 'next-dispatch!)
             dispatch @dispatch-var intercepted (atom nil)]
         (c/resume-ticket! child (c/pending-ticket child gate) :activate)
         (try
           ;; Select the legal interval between committed completion and its
           ;; dequeue. Only public cancellation mutates the actual engine.
           (with-redefs-fn
             {dispatch-var
              (fn [runtime borrowed]
                (when (and (nil? @intercepted)
                           (some #(and (= :worker (:completion %)) (= 2 (:value %))
                                       (= (world-id rt) (:debtor-world %)))
                                 (:queue (c/snapshot rt))))
                  (reset! intercepted :entered)
                  (c/cancel-spin! rt worker)
                  (reset! intercepted {:source (c/snapshot rt) :child (c/snapshot child)}))
                (dispatch runtime borrowed))}
             #(c/set-signal! rt source 2))
           (is (map? @intercepted))
           (is (empty? (:fdeps (:source @intercepted))))
           (is (some :cancelled (:queue (:child @intercepted))))
           (is (= [[(world-id rt) 1]] @observations))
           (is (= :parked (get-in (c/snapshot child) [:runs [:waiter 1] :status])))
           (verify-boundaries! rt)
           (finally (release! rt)))
         (verify-boundaries! rt)))))

(deftest queued-source-evidence-is-copied-once-without-entering-a-consumed-follower
  (let [rt (c/runtime {:audit? true :cps-exit? true}) source (c/signal rt :queued-source 1)
        gate (c/ticket :evidence-gate) observations (atom []) forked (atom nil)
        copied-at-publication (atom nil)
        task (c/cspin rt :evidence-waiter
                      (let [value (iv/get-new (c/track source))]
                        (swap! observations conj [(world-id ec/*execution-context*) value])
                        (c/park gate)))
        trigger (c/cspin rt :publication-trigger :ready)]
    (c/observe! rt task ignore-result ignore-result)
    ;; A host callback runs outside any ordinary slice, inside the existing
    ;; drain. Its nested write queues a fact; nested drain cannot consume it.
    (c/observe! rt trigger
                (fn [_]
                  (c/set-signal! rt source 2)
                  (let [result (publish rt)]
                    (reset! forked result)
                    (reset! copied-at-publication (c/snapshot (:context result)))))
                #(is false (str %)))
    (let [child (:context @forked) copied @copied-at-publication
          facts (filter #(= :queued-source (:completion %)) (:queue copied))]
      (is (some? child))
      (is (= 1 (count facts)))
      (is (= 2 (:value (first facts))))
      (is (= 1 (:seq (first facts))))
      (is (= :inherited (get-in copied [:runs [:evidence-waiter 1] :status])))
      (is (= :inherited (get-in (c/snapshot child) [:runs [:evidence-waiter 1] :status])))
      (is (= [[(world-id rt) 1] [(world-id rt) 2]] @observations))
      (verify-boundaries! rt)
      (release! rt)
      (verify-boundaries! rt))))
