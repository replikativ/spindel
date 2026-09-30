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
            [org.replikativ.spindel.engine.executor :as executor]
            [org.replikativ.spindel.yggdrasil :as ygg]
            [replikativ.logging :as log]))

(declare maybe-complete-quiescence!)

(defprotocol PResourceAuthority
  "What a scope asks when its worlds may spend something that must not be
   duplicated by forking: money, tokens, device memory. A fork copies state;
   it must MOVE authority. The ledger behind an authority is not a member of
   any forked world. Every method returns a value or a CPS operation
   `(fn [resolve reject])`."
  (grant! [authority source-context child-context grant]
    "Move `grant` from the source world's wallet into a new wallet of the
     child. Reject when the source cannot afford it; the fork then fails and
     the child is discarded.")
  (return! [authority context]
    "Move what is left in the world's wallet back to where it was granted
     from. Called once, before the world is discarded. A world without a
     wallet is a no-op.")
  (escrow! [authority context key]
    "Move what is left in the world's wallet into an escrow named `key`: a
     savepoint of the world is leaving the process, and the authority it could
     spend must leave the world with it, or it exists twice.")
  (claim! [authority key context]
    "Move the escrow named `key` into a new wallet of `context`. Reject when
     there is no such escrow: it was claimed already.")
  (balance [authority context]
    "What is left in the world's wallet, {resource amount}; nil when it has
     none. A value or a CPS operation, like the others; `copy!` asks it to
     split a world's budget between its copies."))

(defn- transition!
  "Commit a pure [next-state result] transition; expose only its winning result."
  [state-atom f]
  (loop []
    (let [before @state-atom
          [after result] (f before)]
      (if (compare-and-set! state-atom before after)
        result
        (recur)))))

(defn create
  "Create a finite world-ownership scope from optional purpose, fork-opts and
   a PResourceAuthority. Lifecycle keys are scope-owned and override values in
   fork-opts."
  [{:keys [purpose fork-opts authority retain-released?]
    :or {purpose :simulation fork-opts {} retain-released? true}}]
  (atom {:id (random-uuid)
         :status :open
         :purpose purpose
         :fork-opts fork-opts
         :authority authority
         ;; Descriptors of worlds released early are part of the audit
         ;; projection. A search that releases without bound (a Markov chain)
         ;; turns this off.
         :retain-released? retain-released?
         :returned #{}
         ;; {n handle} in the order the worlds joined, and {fork-id n}: a
         ;; world is found and removed in O(log n), however many there are
         :handles (sorted-map)
         :handle-index {}
         :next-handle 0
         :pending-forks 0
         :activities {}
         :cancel-requested? false
         :cleanup-started? false
         :quiescent? false
         :quiescence-readers []}))

(defn- fork-id-of [handle] (:fork-id (:child-ctx handle)))

(defn- add-handle
  "`state` owning `handle`, newest; or at position `n` (a world given back to
  the place it held)."
  ([state handle] (add-handle state handle (:next-handle state 0)))
  ([state handle n]
   (-> state
       (assoc-in [:handles n] handle)
       (assoc-in [:handle-index (fork-id-of handle)] n)
       (update :next-handle (fnil max 0) (inc n)))))

(defn- handle-position [state fork-id] (get (:handle-index state) fork-id))

(defn- handle-of [state fork-id]
  (some->> (handle-position state fork-id) (get (:handles state))))

(defn- remove-handle [state handle]
  (let [fork-id (fork-id-of handle)]
    (-> state
        (update :handles dissoc (handle-position state fork-id))
        (update :handle-index dissoc fork-id))))

(defn ^:no-doc set-handles
  "`state` owning exactly `handles`, in order (tests)."
  [state handles]
  (reduce add-handle (assoc state :handles (sorted-map) :handle-index {} :next-handle 0) handles))

(defn handles
  "The handles of the worlds `state` (a scope's value) owns, oldest first."
  [state]
  (vec (vals (:handles state))))

(defn- live-descriptors
  "Descriptors of the scope's copied worlds, then of its worlds."
  [{:keys [copied-worlds handles]}]
  (-> []
      (into (keep (fn [[member fork-id]] (ygg/copied-descriptor member fork-id))) copied-worlds)
      (into (map ygg/fork-descriptor) (vals handles))))

(defn descriptors
  "The portable audit projection: every world the scope forked or copied,
   released ones first."
  [scope]
  (let [{:keys [descriptors released] :as state} @scope]
    (or descriptors
        (into (vec released) (live-descriptors state)))))

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

(defn- returning!
  "Run `operation` after the scope's authority took back what is left in
   `context`'s wallet, once per world: a discard that fails is retried, the
   return before it is not. No authority: just run it."
  [scope context operation reject]
  (let [{:keys [authority returned]} @scope
        fork-id (:fork-id context)]
    (if (and authority (not (contains? returned fork-id)))
      (invoke-once! (try (return! authority context)
                         (catch #?(:clj Throwable :cljs :default) error
                           (fn [_ reject-return] (reject-return error))))
                    (fn [_]
                      (swap! scope update :returned conj fork-id)
                      (operation))
                    reject)
      (operation))))

(defn fork!
  "Fork source-context into a frozen canonical child owned by scope.

   `opts` may carry `:fork-opts`, merged over the scope's for this fork (e.g.
   `:snapshots` to pin systems), and `:grant`: what the scope's
   PResourceAuthority moves from the source world's wallet to the child's. A grant the source cannot afford
   fails the fork and discards the child. With an authority and no grant the
   child has no wallet.

   Resolves a non-settleable world reference containing :child-ctx and a
   portable :descriptor. The affine ForkHandle remains private to scope."
  ([scope source-context resolve reject]
   (fork! scope source-context nil resolve reject))
  ([scope source-context {:keys [grant] extra-fork-opts :fork-opts} resolve reject]
   (if-let [claim-error (claim-fork! scope)]
     (reject claim-error)
     (let [{:keys [id purpose fork-opts authority]} @scope
           settled? (atom false)
           finish! (fn [update-state callback value]
                     (when (compare-and-set! settled? false true)
                       (swap! scope update-state)
                       (try
                         (binding [ec/*execution-context* source-context]
                           (callback value))
                         (finally (maybe-complete-quiescence! scope)))))
           opts (-> (merge fork-opts extra-fork-opts)
                    (assoc :mode :frozen :purpose purpose :owner id :sync? false))]
       (letfn [(admit! [handle]
                 (finish! (fn [state]
                            (-> state
                                (add-handle handle)
                                (update :pending-forks dec)))
                          resolve {:child-ctx (:child-ctx handle)
                                   :descriptor (ygg/fork-descriptor handle)}))
               (succeed! [handle]
                 (if (and authority (some? grant))
                  ;; The fork is not a world of this scope until it is funded.
                   (invoke-once!
                    (try (grant! authority source-context (:child-ctx handle) grant)
                         (catch #?(:clj Throwable :cljs :default) error
                           (fn [_ reject-grant] (reject-grant error))))
                    (fn [_] (admit! handle))
                    (fn [grant-error]
                      (binding [ec/*execution-context* (:parent-ctx handle)
                                pcps-async/*in-trampoline* false]
                        (invoke-once! (ygg/discard-fork! handle {:sync? false})
                                      (fn [_] (fail! grant-error))
                                      (fn [discard-error]
                                        (log/error :world-scope/unfunded-fork-leaked
                                                   {:scope/id id :error discard-error})
                                        (fail! grant-error))))))
                   (admit! handle)))
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
               (if @settled? (throw error) (fail! error))))))))))

(defn- discard-opts
  "A copy family settles synchronously; other worlds discard asynchronously."
  [handle]
  (if (:family handle) {} {:sync? false}))

(defn- copied-world-discarded? [{:keys [context member]}]
  (= :discarded (get-in (ygg/copy-family member) [:members (:fork-id context) :settled])))

(defn- return-copied!
  "Give back what the copied worlds whose last copy is gone have left, newest
   first: their copies returned into them before."
  [scope done fail]
  (if-let [entry (last (filter copied-world-discarded? (:copied @scope)))]
    (returning! scope (:context entry)
                (fn []
                  (swap! scope (fn [state]
                                 (-> state
                                     (update :copied (fn [cs] (vec (remove #(identical? entry %) cs))))
                                     (update :returned disj (:fork-id (:context entry))))))
                  (return-copied! scope done fail))
                fail)
    (done)))

(defn- settle-now
  "The value of an authority operation that settles before it returns, as a
   copy must: it is synchronous."
  [operation]
  (let [outcome (volatile! nil)]
    (invoke-once! operation #(vreset! outcome [:ok %]) #(vreset! outcome [:error %]))
    (case (first @outcome)
      :ok (second @outcome)
      :error (throw (second @outcome))
      (throw (ex-info "A resource authority must settle synchronously to fund copies"
                      {:type ::asynchronous-authority})))))

(defn- authority-op [f]
  (try (f)
       (catch #?(:clj Throwable :cljs :default) error
         (fn [_ reject] (reject error)))))

(defn- share
  "One of `k` even shares of `resources`: integer amounts rounded down."
  [resources k]
  (into {} (map (fn [[r amount]]
                  [r (if (integer? amount) (quot amount k) (/ amount k))]))
        resources))

(defn copy!
  "Copy the scope's world `context` into `k` alternatives that settle at most
   once (`ygg/copy-fork!`): the world becomes a copied world that never runs
   again, and its copies are the scope's worlds in its place.

   With an authority, each copy is funded from the copied world's wallet —
   `:grants`, one per copy, `:grant` for every copy, or `:split? true` for an
   even share of what the world has left (integer amounts rounded down; the
   rest stays with the copied world) — so copying never multiplies a budget. A grant the world cannot afford fails the copy: the
   grants made are returned, the copies discarded, and the world stays as it
   was. Discarded copies give back what they have left into the copied
   world, and the copied world, after its last copy, to where it was granted
   from. `:fork-opts` are merged over the scope's.

   Resolves [{:child-ctx :descriptor}], one per copy. JVM / synchronous only."
  ([scope context k resolve reject] (copy! scope context k nil resolve reject))
  ([scope context k {:keys [grant grants split?] extra-fork-opts :fork-opts} resolve reject]
   (let [fork-id (:fork-id context)
         authority (:authority @scope)
         grants (try
                  (or grants
                      (when (some? grant) (vec (repeat k grant)))
                      (when (and split? authority)
                        (when-let [left (settle-now (authority-op #(balance authority context)))]
                          (vec (repeat k (share left k))))))
                  (catch #?(:clj Throwable :cljs :default) error
                    {::error error}))
         claimed
         (transition!
          scope
          (fn [state]
            (let [handle (handle-of state fork-id)]
              (cond
                (::error grants)
                [state {:error (::error grants)}]

                (or (not= :open (:status state)) (:quiescent? state))
                [state {:error (scope-error scope ::scope-consumed
                                            "Cannot copy in a consumed world scope")}]

                (:cancel-requested? state)
                [state {:error (scope-error scope ::scope-cancelled
                                            "Cannot copy in a cancelled world scope")}]

                (nil? handle)
                [state {:error (scope-error scope ::unknown-world
                                            "World is not owned by this scope")}]

                (and grants (not= k (count grants)))
                [state {:error (ex-info "copy! needs one grant per copy"
                                        {:type ::grant-count :k k :grants (count grants)})}]

                :else
                [(-> state
                     (remove-handle handle)
                     (update :pending-forks inc))
                 {:handle handle
                  :position (handle-position state fork-id)}]))))]
     (if-let [error (:error claimed)]
       (reject error)
       (let [{:keys [id purpose fork-opts authority]} @scope
             handle (:handle claimed)
             fund! (fn [copies]
                     (let [funded (volatile! [])]
                       (try
                         (doseq [[c g] (map vector copies grants)]
                           (settle-now (authority-op #(grant! authority context (:child-ctx c) g)))
                           (vswap! funded conj c))
                         (catch #?(:clj Throwable :cljs :default) error
                           (doseq [c (rseq @funded)]
                             (try (settle-now (authority-op #(return! authority (:child-ctx c))))
                                  (catch #?(:clj Throwable :cljs :default) return-error
                                    (log/error :world-scope/unreturned-copy-grant
                                               {:scope/id id :error return-error}))))
                           (throw error)))))
             outcome
             (try
               {:copies (ygg/copy-fork!
                         handle k
                         (cond-> (-> (merge fork-opts extra-fork-opts)
                                     (assoc :mode :frozen :purpose purpose :owner id :sync? true))
                           (and authority grants) (assoc :admit fund!)))}
               (catch #?(:clj Throwable :cljs :default) error
                 {:error error}))]
         (swap! scope
                (fn [state]
                  (-> (if-let [copies (:copies outcome)]
                        (-> (reduce add-handle state copies)
                            (update :copied (fnil conj []) {:context context :member (first copies)})
                            (update :copied-worlds (fnil conj []) [(first copies) fork-id]))
                        ;; the world stays the scope's, where it was: the
                        ;; scope discards its worlds newest first
                        (add-handle state handle (:position claimed)))
                      (update :pending-forks dec))))
         (try
           (binding [ec/*execution-context* context]
             (if-let [copies (:copies outcome)]
               (resolve (mapv (fn [c] {:child-ctx (:child-ctx c)
                                       :descriptor (ygg/fork-descriptor c)})
                              copies))
               (reject (:error outcome))))
           (finally (maybe-complete-quiescence! scope))))))))

(def ^:private hop-depth
  "Worlds `discard!` walks on one stack before continuing on a fresh one."
  200)

(defn discard!
  "Discard all owned worlds newest first. Returns a shared CPS operation."
  [scope]
  (fn [resolve reject]
    (let [reader {:resolve resolve :reject reject}
          {:keys [handles immediate]}
          (transition!
           scope
           (fn [state]
             (case (:status state)
               :open
               (if (or (pos? (:pending-forks state))
                       (seq (:activities state)))
                 [state
                  {:immediate
                   {:status :failed
                    :error
                    (ex-info
                     "Cannot discard a world scope while forks are in flight"
                     {:type ::scope-busy
                      :scope/id (:id state)
                      :scope/status (:status state)})}}]
                 [(assoc state
                         :status :discarding
                         :discard-readers [reader])
                  {:handles (reverse (vals (:handles state)))}])

               :discarding
               [(update state :discard-readers (fnil conj []) reader) {}]

               :discarded
               [state {:immediate {:status :done :value nil}}]

               :failed
               [state {:immediate {:status :failed :error (:error state)}}]

               [state {:immediate
                       {:status :failed
                        :error
                        (ex-info
                         "Cannot discard a consumed world scope"
                         {:type ::scope-consumed
                          :scope/id (:id state)
                          :scope/status (:status state)})}}])))
          notify!
          (fn [readers status payload]
            (let [callback-error (volatile! nil)]
              (doseq [{:keys [resolve reject]} readers]
                (try
                  ((if (= status :done) resolve reject) payload)
                  (catch #?(:clj Throwable :cljs :default) error
                    (when-not @callback-error
                      (vreset! callback-error error)))))
              (when-let [error @callback-error]
                (throw error))))
          complete!
          (fn [status payload update-state]
            (let [readers
                  (transition!
                   scope
                   (fn [state]
                     (if (= :discarding (:status state))
                       [(-> (update-state state)
                            (dissoc :discard-readers))
                        (:discard-readers state)]
                       [state []])))]
              (notify! readers status payload)))]
      (when-let [{:keys [status value error]} immediate]
        (if (= :done status) (resolve value) (reject error)))
      (when handles
        (letfn [(fail! [handle error]
                  (complete!
                   :failed error
                   #(assoc %
                           :status (if (ygg/open-fork? handle) :open :failed)
                           :error error)))
                (step [remaining depth]
                  ;; A discard usually completes inline, so each continues
                  ;; the next from inside its own callback: ~20 frames per
                  ;; world, and a scope of ~650 worlds overflowed the stack —
                  ;; the overflow then failed `fail!` too and the discard
                  ;; never resolved (#71). Every `hop-depth` worlds the walk
                  ;; continues from a fresh task on the world's executor
                  ;; instead; inline if that executor refuses the task.
                  (let [remaining (drop-while (complement ygg/open-fork?) remaining)]
                    (if-let [handle (first remaining)]
                      (returning!
                       scope (:child-ctx handle)
                       (fn []
                         (binding [ec/*execution-context* (:parent-ctx handle)
                                   pcps-async/*in-trampoline* false]
                           (invoke-once!
                            (ygg/discard-fork! handle (discard-opts handle))
                            (fn [_]
                              (if (< depth hop-depth)
                                (step (next remaining) (inc depth))
                                (let [continue! #(step (next remaining) 0)]
                                  (try
                                    (executor/execute! (:executor (:parent-ctx handle)) continue!)
                                    (catch #?(:clj Throwable :cljs :default) _
                                      (continue!))))))
                            (fn [error] (fail! handle error)))))
                       (fn [error] (fail! handle error)))
                      (return-copied!
                       scope
                       (fn []
                         (let [descriptors
                               (into (vec (:released @scope)) (live-descriptors @scope))]
                           (complete!
                            :done nil
                            #(-> %
                                 (assoc :status :discarded
                                        :descriptors descriptors
                                        :handles (sorted-map)
                                        :handle-index {})
                                 (dissoc :client :error)))))
                       (fn [error]
                         (complete! :failed error
                                    #(assoc % :status :open :error error)))))))]
          (step handles 0))))))

(defn release!
  "Discard ONE owned world before the scope ends, so a long search need not
   hold every world it ever forked. `context` is the world's context; it must
   hold no activity lease (its computation is terminal). The release counts as
   an in-flight fork operation: the scope is neither quiescent nor discardable
   until it settles. The world's descriptor stays in `descriptors`.

   Returns a CPS operation resolving nil."
  [scope context]
  (fn [resolve reject]
    (let [fork-id (:fork-id context)
          result
          (transition!
           scope
           (fn [state]
             (let [handle (handle-of state fork-id)]
               (cond
                 (not= :open (:status state))
                 [state {:error (scope-error scope ::scope-consumed
                                             "Cannot release from a consumed world scope")}]

                 (nil? handle)
                 [state {:error (scope-error scope ::unknown-world
                                             "World is not owned by this scope")}]

                 (contains? (:activities state) fork-id)
                 [state {:error (scope-error scope ::world-busy
                                             "Cannot release a world that holds an activity lease")}]

                 :else
                 [(-> state
                      (remove-handle handle)
                      (update :pending-forks inc))
                  {:handle handle}]))))
          settle! (fn [handle released? callback value]
                    (swap! scope (fn [state]
                                   (cond-> (update state :pending-forks dec)
                                     released?
                                     (update :returned disj (:fork-id (:child-ctx handle)))
                                     (and released? (:retain-released? state))
                                     (update :released (fnil conj [])
                                             (ygg/fork-descriptor handle))
                                     ;; still owned: the scope's discard retries it
                                     (not released?)
                                     (add-handle handle))))
                    (try (callback value)
                         (finally (maybe-complete-quiescence! scope))))]
      (if-let [error (:error result)]
        (reject error)
        (let [handle (:handle result)]
          (returning!
           scope (:child-ctx handle)
           (fn []
             (binding [ec/*execution-context* (:parent-ctx handle)
                       pcps-async/*in-trampoline* false]
               (invoke-once!
                (ygg/discard-fork! handle (discard-opts handle))
                (fn [_]
                  (return-copied! scope
                                  #(settle! handle true resolve nil)
                                  ;; the world is gone; a copied world not
                                  ;; returned yet is retried by `discard!`
                                  #(settle! handle true reject %)))
                (fn [error] (settle! handle false reject error)))))
           (fn [error] (settle! handle false reject error))))))))

(defn await-quiescence [scope]
  (fn [resolve _reject]
    (let [immediate?
          (transition! scope
                       (fn [state]
                         (if (or (:quiescent? state)
                                 (and (empty? (:activities state))
                                      (zero? (:pending-forks state))))
                           [(assoc state :quiescent? true) true]
                           [(update state :quiescence-readers conj resolve)
                            false])))]
      (when immediate? (resolve nil)))))

(defn discard-when-quiescent! [scope]
  (fn [resolve reject]
    ((await-quiescence scope)
     (fn [_] (invoke-once! (discard! scope) resolve reject))
     reject)))

(defn begin-activity!
  "Acquire a process-local activity lease. New work is rejected after
   cancellation or once quiescence has been published. A caller that must
   release the lease from elsewhere (a terminal callback that knows only its
   world) supplies activity-id; it must not be live."
  ([scope kind] (begin-activity! scope kind nil))
  ([scope kind value] (begin-activity! scope kind value (random-uuid)))
  ([scope kind value activity-id]
   (let [error (transition! scope
                            (fn [state]
                              (cond
                                (contains? (:activities state) activity-id)
                                [state (scope-error scope ::activity-id-collision
                                                    "World-scope activity ID is already live")]

                                (not= :open (:status state))
                                [state (scope-error scope ::scope-consumed
                                                    "Cannot enter a consumed world scope")]

                                (or (:cancel-requested? state) (:quiescent? state))
                                [state (scope-error scope ::scope-cancelled
                                                    "Cannot enter a closed world scope")]

                                :else
                                [(assoc-in state [:activities activity-id]
                                           {:kind kind :value value}) nil])))]
     (if error (throw error) activity-id))))

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
        result (transition! scope
                            (fn [state]
                              (let [remaining (dissoc (:activities state) activity-id)
                                    duplicate-ids? (not= (count ids) (count (set ids)))
                                    collisions (seq (filter #(contains? remaining %) ids))]
                                (cond
                                  (not (contains? (:activities state) activity-id))
                                  [state {:error (scope-error scope ::unknown-activity
                                                              "World-scope activity is not live")}]

                                  (or duplicate-ids? collisions)
                                  [state {:error (scope-error scope ::activity-id-collision
                                                              "Replacement activity IDs must be unique")}]

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
                                    [(assoc state :activities (merge remaining replacements))
                                     {:admitted? admit?
                                      :activity-ids (if admit? ids [])}])))))]
    (when-let [error (:error result)] (throw error))
    (maybe-complete-quiescence! scope)
    result))

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
  (let [readers (transition! scope
                             (fn [state]
                               (if (and (empty? (:activities state))
                                        (zero? (:pending-forks state)))
                                 [(assoc state :quiescent? true :quiescence-readers [])
                                  (:quiescence-readers state)]
                                 [state []])))]
    (try
      (let [callback-error (volatile! nil)]
        (doseq [reader readers]
          (try
            (reader nil)
            (catch #?(:clj Throwable :cljs :default) error
              (when-not @callback-error
                (vreset! callback-error error)))))
        (when-let [error @callback-error]
          (throw error)))
      (finally
        (maybe-clean-cancelled! scope)))))

(defn request-cancel!
  "Request cleanup after client-owned computation cancellation and quiescence."
  [scope]
  (let [state (swap! scope assoc :cancel-requested? true)]
    (maybe-clean-cancelled! scope)
    state))
