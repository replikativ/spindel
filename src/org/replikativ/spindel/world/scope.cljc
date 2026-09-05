(ns org.replikativ.spindel.world.scope
  "Process-local affine ownership for a finite family of canonical worlds.

   A WorldScope is algorithm-neutral. SMC particles, MCTS nodes, simulations,
   and other bounded searches may fork worlds through it. The scope owns every
   ForkHandle, tracks live contexts and in-flight fork construction, and
   consumes settlement authority only after quiescence.

   Live handles never cross a durable boundary. descriptors is the portable
   audit projection retained after successful cleanup."
  (:require [is.simm.partial-cps.async :as pcps-async]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.yggdrasil :as ygg]
            [replikativ.logging :as log]))

(declare maybe-complete-quiescence!)

(defn create
  "Create a finite world-ownership scope from optional purpose and fork-opts.
   Lifecycle keys are scope-owned and override values in fork-opts."
  [{:keys [purpose fork-opts]
    :or {purpose :simulation fork-opts {}}}]
  (atom {:id (random-uuid)
         :status :open
         :purpose purpose
         :fork-opts fork-opts
         :handles []
         :pending-forks 0
         :activities {}
         :cancel-requested? false
         :cleanup-started? false
         :quiescent? false
         :quiescence-readers []
         :cleanup (atom {:status :pending :readers []})}))

(defn descriptors [scope]
  (let [{:keys [descriptors handles]} @scope]
    (or descriptors (mapv ygg/fork-descriptor handles))))

(defn- scope-error [scope type message]
  (ex-info message
           {:type type
            :scope/id (:id @scope)
            :scope/status (:status @scope)}))

(defn- claim-fork! [scope]
  (loop []
    (let [state @scope]
      (cond
        (or (not= :open (:status state)) (:quiescent? state))
        (scope-error scope ::scope-consumed
                     "Cannot fork through a consumed world scope")

        (:cancel-requested? state)
        (scope-error scope ::scope-cancelled
                     "Cannot fork through a cancelled world scope")

        (compare-and-set! scope state (update state :pending-forks inc))
        nil

        :else (recur)))))

(defn- invoke-once! [operation resolve reject]
  (let [delivered? (atom false)
        deliver! (fn [callback value]
                   (when (compare-and-set! delivered? false true)
                     (callback value)))]
    (try
      (if (fn? operation)
        (operation #(deliver! resolve %) #(deliver! reject %))
        (deliver! resolve operation))
      (catch #?(:clj Throwable :cljs :default) error
        ;; Exceptions before delivery reject the operation. Exceptions from a
        ;; claimed continuation belong to its executor/error boundary.
        (if @delivered? (throw error) (deliver! reject error))))))

(defn fork!
  "Fork source-context into a frozen canonical child owned by scope.

   Resolves a non-settleable world reference containing :child-ctx and a
   portable :descriptor. The affine ForkHandle remains private to scope."
  [scope source-context resolve reject]
  (if-let [claim-error (claim-fork! scope)]
    (reject claim-error)
    (let [{:keys [id purpose fork-opts]} @scope
          settled? (atom false)
          finish! (fn [update-state callback value]
                    (when (compare-and-set! settled? false true)
                      (swap! scope update-state)
                      (try
                        (binding [ec/*execution-context* source-context]
                          (callback value))
                        (finally (maybe-complete-quiescence! scope)))))
          opts (-> fork-opts
                   (assoc :mode :frozen :purpose purpose :owner id :sync? false))]
      (letfn [(succeed! [handle]
                (finish! (fn [state]
                           (-> state
                               (update :handles conj handle)
                               (update :pending-forks dec)))
                         resolve {:child-ctx (:child-ctx handle)
                                  :descriptor (ygg/fork-descriptor handle)}))
              (fail! [error]
                (finish! #(update % :pending-forks dec) reject error))]
        (binding [ec/*execution-context* source-context
                  pcps-async/*in-trampoline* false]
          (try
            (let [operation (ygg/fork! opts)]
              (if (fn? operation)
                (operation succeed! fail!)
                (succeed! operation)))
            (catch #?(:clj Throwable :cljs :default) error
              ;; A successful callback owns its continuation exception. Do not
              ;; reinterpret it as a second rejection and silently swallow it.
              (if @settled? (throw error) (fail! error)))))))))

(defn discard!
  "Discard all owned worlds newest first. Returns a shared CPS operation."
  [scope]
  (fn [resolve reject]
    (let [cleanup (:cleanup @scope)
          immediate (volatile! nil)]
      (loop []
        (let [state @cleanup]
          (when (and (= :failed (:status state))
                     (= :open (:status @scope))
                     (not (compare-and-set!
                           cleanup state {:status :pending :readers []})))
            (recur))))
      (swap! cleanup
             (fn [state]
               (if (= :pending (:status state))
                 (update state :readers conj {:resolve resolve :reject reject})
                 (do (vreset! immediate state) state))))
      (when-let [{:keys [status value error]} @immediate]
        (if (= :done status) (resolve value) (reject error)))
      (letfn [(complete! [status payload]
                (let [readers (volatile! [])]
                  (swap! cleanup
                         (fn [state]
                           (if (= :pending (:status state))
                             (do
                               (vreset! readers (:readers state))
                               (cond-> {:status status :readers []}
                                 (= status :done) (assoc :value payload)
                                 (= status :failed) (assoc :error payload)))
                             state)))
                  (let [callback-error (volatile! nil)]
                    (doseq [{:keys [resolve reject]} @readers]
                      (try
                        ((if (= status :done) resolve reject) payload)
                        (catch #?(:clj Throwable :cljs :default) error
                          (when-not @callback-error
                            (vreset! callback-error error)))))
                    (when-let [error @callback-error]
                      (throw error)))))
              (fail! [handle error]
                (swap! scope assoc
                       :status (if (ygg/open-fork? handle) :open :failed)
                       :error error)
                (complete! :failed error))
              (step [handles]
                (if-let [handle (first handles)]
                  (if (ygg/open-fork? handle)
                    (binding [ec/*execution-context* (:parent-ctx handle)
                              pcps-async/*in-trampoline* false]
                      (invoke-once!
                       (ygg/discard-fork! handle {:sync? false})
                       (fn [_] (step (next handles)))
                       (fn [error] (fail! handle error))))
                    (step (next handles)))
                  (do
                    (swap! scope
                           (fn [state]
                             (-> state
                                 (assoc :status :discarded
                                        :descriptors
                                        (mapv ygg/fork-descriptor
                                              (:handles state))
                                        :handles [])
                                 (dissoc :client))))
                    (complete! :done nil))))
              (claim! []
                (let [state @scope]
                  (case (:status state)
                    :open
                    (if (or (pos? (:pending-forks state))
                            (seq (:activities state)))
                      (complete!
                       :failed
                       (scope-error scope ::scope-busy
                                    "Cannot discard a world scope while forks are in flight"))
                      (if (compare-and-set! scope state
                                            (assoc state :status :discarding))
                        (step (reverse (:handles state)))
                        (recur)))
                    :discarded (complete! :done nil)
                    :failed (complete! :failed (:error state))
                    :discarding nil
                    nil)))]
        (when-not @immediate (claim!))))))

(defn await-quiescence [scope]
  (fn [resolve _reject]
    (let [immediate? (volatile! false)]
      (swap! scope
             (fn [state]
               (if (or (:quiescent? state)
                       (and (empty? (:activities state))
                            (zero? (:pending-forks state))))
                 (do (vreset! immediate? true)
                     (assoc state :quiescent? true))
                 (update state :quiescence-readers conj resolve))))
      (when @immediate? (resolve nil)))))

(defn discard-when-quiescent! [scope]
  (fn [resolve reject]
    ((await-quiescence scope)
     (fn [_] (invoke-once! (discard! scope) resolve reject))
     reject)))

(defn begin-activity!
  "Acquire a process-local activity lease. New work is rejected after
   cancellation or once quiescence has been published."
  ([scope kind] (begin-activity! scope kind nil))
  ([scope kind value]
   (let [activity-id (random-uuid)
         error* (volatile! nil)]
     (swap! scope
            (fn [state]
              (cond
                (not= :open (:status state))
                (do (vreset! error* (scope-error scope ::scope-consumed
                                                 "Cannot enter a consumed world scope"))
                    state)

                (or (:cancel-requested? state) (:quiescent? state))
                (do (vreset! error* (scope-error scope ::scope-cancelled
                                                 "Cannot enter a closed world scope"))
                    state)

                :else
                (assoc-in state [:activities activity-id]
                          {:kind kind :value value}))))
     (if-let [error @error*] (throw error) activity-id))))

(defn activity-values
  "Return process-local activity values of kind."
  [scope kind]
  (->> (:activities @scope)
       vals
       (keep #(when (= kind (:kind %)) (:value %)))
       vec))

(defn exchange-activity!
  "Atomically retire activity-id and admit replacement activity specs.

   Each spec is {:id optional-id :kind keyword :value process-local-value}.
   Returns {:admitted? boolean :activity-ids [...]} so generated IDs remain
   releasable. Cancellation rejects non-empty replacements."
  [scope activity-id activity-specs]
  (let [specs (mapv #(update % :id (fn [id] (or id (random-uuid))))
                    activity-specs)
        ids (mapv :id specs)
        result* (volatile! nil)
        error* (volatile! nil)]
    (swap! scope
           (fn [state]
             (let [remaining (dissoc (:activities state) activity-id)
                   duplicate-ids? (not= (count ids) (count (set ids)))
                   collisions (seq (filter #(contains? remaining %) ids))]
               (cond
                 (not (contains? (:activities state) activity-id))
                 (do (vreset! error* (scope-error scope ::unknown-activity
                                                  "World-scope activity is not live"))
                     state)

                 (or duplicate-ids? collisions)
                 (do (vreset! error* (scope-error scope ::activity-id-collision
                                                  "Replacement activity IDs must be unique"))
                     state)

                 :else
                 (let [admit? (or (empty? specs)
                                  (not (:cancel-requested? state)))
                       replacements
                       (if admit?
                         (into {}
                               (map (fn [{:keys [id kind value]}]
                                      [id {:kind kind :value value}]))
                               specs)
                         {})]
                   (vreset! result* {:admitted? admit?
                                     :activity-ids (if admit? ids [])})
                   (assoc state :activities (merge remaining replacements)))))))
    (when-let [error @error*] (throw error))
    (maybe-complete-quiescence! scope)
    @result*))

(defn end-activity! [scope activity-id]
  (swap! scope update :activities dissoc activity-id)
  (maybe-complete-quiescence! scope)
  nil)

(defn- maybe-clean-cancelled! [scope]
  (loop []
    (let [state @scope]
      (when (and (:cancel-requested? state)
                 (empty? (:activities state))
                 (zero? (:pending-forks state))
                 (not (:cleanup-started? state)))
        (if (compare-and-set! scope state (assoc state :cleanup-started? true))
          (invoke-once!
           (discard! scope)
           (constantly nil)
           (fn [error]
             (log/error :world-scope/cleanup-failed
                        {:scope/id (:id state) :error error})))
          (recur))))))

(defn maybe-complete-quiescence! [scope]
  (let [readers (volatile! [])]
    (swap! scope
           (fn [state]
             (if (and (empty? (:activities state))
                      (zero? (:pending-forks state)))
               (do (vreset! readers (:quiescence-readers state))
                   (assoc state :quiescent? true :quiescence-readers []))
               state)))
    (doseq [reader @readers] (reader nil))
    (maybe-clean-cancelled! scope)))

(defn request-cancel!
  "Request cleanup after client-owned computation cancellation and quiescence."
  [scope]
  (let [state (swap! scope assoc :cancel-requested? true)]
    (maybe-clean-cancelled! scope)
    state))
