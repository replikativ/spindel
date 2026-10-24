(ns org.replikativ.spindel.trace
  "Traces of savepoints, and replay.

  A *trace* is what a computation did at its savepoints: for every site the
  value it was resumed with, a note, and an *anchor* (a fork of the savepoint
  taken before it was resumed, i.e. the world as it was at the site).

    {:trace/entries {address {:site :path :seq :payload :value :note :savepoint}}
     :trace/order   [address ...]        ; program order
     :trace/result  r | :trace/error e
     :trace/world   the world the computation ended in
     :trace/session the session owning every world above}

  A *policy* decides a site: `(policy sp old-entry)` returns
  `{:value v :note n}`, or a CPS operation `(fn [resolve reject])` resolving
  that. `sp` is pending in the world that is about to continue, so a policy
  that scores (a log-weight, a reward, a budget) writes to
  `(:savepoint/world sp)`; the write lands on top of what that world had
  accumulated before the site. `old-entry` is the entry of the same address in
  the trace being replayed, or nil.

  `run` executes a computation under a policy. `replay` executes it again from
  one address under another policy, reusing everything upstream of it. The
  operations of a trace-based inference interface (generate, update,
  regenerate, assess, propose) are policies; see docs/savepoints.md.

  The trace under construction is world state, so it forks with its world."
  (:refer-clojure :exclude [update])
  (:require [org.replikativ.spindel.effects.savepoint :as sp]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.quiescence :as quiescence]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.keyed :as keyed]
            [org.replikativ.spindel.world.scope :as world-scope]))

(def ^:private empty-trace
  {:trace/entries {} :trace/order []})

(defn payload-policy
  "Resume every site with its own payload: the computation as written."
  [sp _old-entry]
  {:value (:savepoint/payload sp)})

(defn keep-policy
  "Resume a site with the value it had in the replayed trace, else decide it
  with `policy`."
  [policy]
  (fn [sp old-entry]
    (if old-entry
      (select-keys old-entry [:value :note])
      (policy sp old-entry))))

(defn constrained-policy
  "Resume the addresses of `constraints` ({address value}) with those values
  and decide every other site with `policy`."
  [constraints policy]
  (fn [sp old-entry]
    (let [address (:savepoint/address sp)]
      (if (contains? constraints address)
        {:value (get constraints address)}
        (policy sp old-entry)))))

(defn- invoke!
  "Call `make-operation` and deliver its value-or-CPS result. It is a thunk so
  that a policy which throws rejects the run, like one which rejects."
  [make-operation resolve reject]
  (try
    (let [operation (make-operation)]
      (if (fn? operation)
        (operation resolve reject)
        (resolve operation)))
    (catch #?(:clj Throwable :cljs :default) error
      (reject error))))

(defn record!
  "Add a decided site to the trace under construction. An address reached
  twice in one computation is an error: two sites named alike (an `:id`
  reused in a loop) would otherwise share one entry, and a replay or a
  constraint could not tell them apart. An entry records the spin that
  reached the site (`:spin`, its id).

  `update` (a map, from `update`) marks an update: the trace already holds
  the computation's entries, and a site its re-run reaches again replaces
  its entry in place (program order is kept). It is still an error to reach
  an address twice in the update itself (`:recorded`, an atom of a set), or
  one held by a spin the update does not re-run (`:movable`, the spin ids
  whose entries it may rewrite): that would be two sites named alike."
  ([world sp decision anchor] (record! world sp decision anchor nil))
  ([world sp decision anchor {:keys [recorded movable] :as update}]
   (rtp/swap-state!
    world [:savepoint/trace]
    (fn [trace]
      (let [trace (or trace empty-trace)
            address (:savepoint/address sp)
            present (get-in trace [:trace/entries address])
            spin-id (:spin-id (::sp/k sp))]
        (when (if update
                (or (contains? @recorded address)
                    (and present
                         (not= spin-id (:spin present))
                         (not (contains? movable (:spin present)))))
                present)
          (throw (ex-info "Duplicate site address in one computation"
                          {:type ::duplicate-address
                           :address address
                           :site (:savepoint/site sp)})))
        (-> (cond-> trace (not present) (clojure.core/update :trace/order conj address))
            (assoc-in [:trace/entries address]
                      {:site (:savepoint/site sp)
                       :path (:savepoint/path sp)
                       :seq (:savepoint/seq sp)
                       :payload (:savepoint/payload sp)
                       :value (:value decision)
                       :note (:note decision)
                       :spin spin-id
                       :savepoint anchor})))))
   (when update (swap! recorded conj (:savepoint/address sp)))))

(defn- decide-site!
  "Decide `sp` with the run's policy, record it with `anchor`, and resume it —
  or, when `until` holds for it, leave it pending and hand it to `park!`.
  `done!` (optional) is called once the site is resumed, parked or failed —
  an update counts a site in flight while its policy decides."
  [sp anchor {:keys [live until park! fail! update done!] :or {done! (fn [])}}]
  (let [{:keys [policy old]} @live]
    (if-not policy
      (try (fail! sp (ex-info "The run has delivered" {:type ::delivered}))
           (finally (done!)))
      (invoke! #(policy sp (get-in old [:trace/entries (:savepoint/address sp)]))
               (fn [decision]
                 (try
                   (record! (:savepoint/world sp) sp decision anchor update)
                   (if (and until (until sp))
                     (park! sp (:value decision))
                     (sp/resume sp (:value decision)))
                   (catch #?(:clj Throwable :cljs :default) error
                     (fail! sp error))
                   (finally (done!))))
               (fn [error]
                 (try (fail! sp error) (finally (done!))))))))

(defn- handlers-of
  "The handlers of one run: decide every site, deliver the end once.
  Returns {:table handler-table :fail! (fn [sp error])}.

  The table is world state, and every fork snapshots it: an anchor holds it
  for as long as a trace refers to the anchor. So the run's callbacks, policy
  and replayed trace sit in `live`, which delivery clears, instead of in the
  closures themselves; otherwise every anchor would keep them, and through
  them the caller's state, alive."
  [{:keys [policy old anchor? until] :or {anchor? (constantly true)}} session resolve reject]
  (let [live (volatile! {:resolve resolve :reject reject :policy policy :old old})
        delivered? (atom false)
        once! (fn [k value]
                (when (compare-and-set! delivered? false true)
                  (let [callback (get @live k)]
                    (vreset! live nil)
                    (callback value))))
        fail! (fn [sp error]
                ;; Report the error BEFORE abandoning: the abandon unwinds on
                ;; the executor and reaches `abandoned-site`, whose handler
                ;; rejects with the cancellation — first come, first
                ;; delivered, so it could win the race and hide the error.
                (once! :reject error)
                (try (sp/abandon sp) (catch #?(:clj Throwable :cljs :default) _ nil)))
        trace-of (fn [world]
                   (assoc (or (rtp/get-state world [:savepoint/trace]) empty-trace)
                          :trace/world world
                          :trace/session session))
        finish (fn [k]
                 (fn [event]
                   (once! :resolve (assoc (trace-of (:savepoint/world event))
                                          k (:savepoint/payload event)))))
        park! (fn [sp value]
                (once! :resolve (assoc (trace-of (:savepoint/world sp))
                                       :trace/pending sp
                                       :trace/pending-value value)))
        site-opts {:live live :until until :park! park! :fail! fail!}]
    {:fail! fail!
     :site-opts site-opts
     :table
     {sp/any-site
      (fn [sp]
        (if (anchor? sp)
          (invoke! #(sp/fork sp)
                   #(decide-site! sp % site-opts)
                   #(fail! sp %))
          (decide-site! sp nil site-opts)))
      sp/result-site (finish :trace/result)
      sp/error-site (finish :trace/error)
      ;; Abandoned from outside (the session closed, or someone else's
      ;; handler gave this world up): there is no trace to deliver.
      sp/abandoned-site (fn [event] (once! :reject (:savepoint/payload event)))}}))

(defn run
  "Run `task` (a spin) in `session`'s root world under `policy`.

  Options:
    :anchor? (fn [sp]) whether to keep the state at a site (default: always);
             a site without an anchor cannot be replayed from
    :until   (fn [sp]) a site at which to stop: it is decided and recorded,
             but not resumed, and the operation resolves the trace so far
             with `:trace/pending` (the savepoint, still pending) and
             `:trace/pending-value` (the decided value). Whoever resumes it
             installs its own handlers on its world first
             (`effects.savepoint/install-handlers!`): the run's have
             delivered.

  Returns a CPS operation resolving the trace. A computation that throws
  resolves a trace with `:trace/error`; the operation rejects only when the
  policy or the machinery fails."
  ([session task policy] (run session task policy nil))
  ([session task policy opts]
   (fn [resolve reject]
     (let [[resolve reject] (sp/in-callers-world resolve reject)]
       (try
         (sp/install-handlers! (:root session)
                               (:table (handlers-of (assoc opts :policy policy)
                                                    session resolve reject)))
         (sp/start! session task)
         (catch #?(:clj Throwable :cljs :default) error
           (reject error)))))))

(defn replay
  "Run the computation of `trace` again from `address` under `policy`.

  The world at `address` is forked from its anchor, so everything upstream is
  reused as it was: values, world state, and the entries of the trace. Sites
  downstream reach `policy` with their entry in `trace` when their address
  still exists; entries that are not reached again are absent from the
  result. `trace` is not changed. Options as for `run`, and `:seed`, the
  replaying world's random seed (default: derived from the anchor's world and
  how often it was forked, which depends on the order concurrent replays of
  one anchor fork it).

  Returns a CPS operation resolving the new trace."
  ([trace address policy] (replay trace address policy nil))
  ([trace address policy opts]
   (fn [resolve reject]
     (let [[resolve reject] (sp/in-callers-world resolve reject)
           anchor (get-in trace [:trace/entries address :savepoint])]
       (if-not (and anchor (sp/pending? anchor))
         (reject (ex-info "Trace holds no pending anchor at address"
                          {:type ::no-anchor :address address}))
         (let [{:keys [table fail! site-opts]}
               (handlers-of (assoc opts :policy policy :old trace)
                            (:trace/session trace) resolve reject)]
           (invoke! #(sp/fork anchor (cond-> {:handlers table}
                                       (:seed opts) (assoc :seed (:seed opts))))
                    (fn [fork]
                      ;; Downstream spins the old run computed and this one
                      ;; reaches again unchanged are adopted, not re-run.
                      (when-let [source (:trace/world trace)]
                        (rtp/swap-state! (:savepoint/world fork) [:engine/reuse-source]
                                         (constantly source)))
                      ;; The anchor already is the state at this site.
                      (decide-site! fork anchor site-opts))
                    reject)))))))

(defn- subtree
  "The spin ids of `ids` and every spin they created, transitively, in
  `world`."
  [world ids]
  (loop [todo (vec ids) seen #{}]
    (if-let [id (peek todo)]
      (if (contains? seen id)
        (recur (pop todo) seen)
        (recur (into (pop todo) (rtp/get-state world [:nodes id :created-spins]))
               (conj seen id)))
      seen)))

(defn- settle-update
  "The trace of the updated world `world` (a fork of `source`): `trace`'s
  entries as the update rewrote them in place, without the entries it no
  longer reaches (deaths) — those of spins under the re-run ones that are
  gone, and those of spins that ran again but did not reach them — and
  without anchors downstream of the first rewritten entry (they are forks of
  the world before the update; a replay from one would bring the old values
  back)."
  [trace world source session spin-ids recorded]
  (let [t (or (rtp/get-state world [:savepoint/trace]) empty-trace)
        before (subtree source spin-ids)
        after (subtree world spin-ids)
        gone (into #{} (remove after) before)
        ran (into #{} (filter #(not= (rtp/get-state world [:nodes % :run-gen])
                                     (rtp/get-state source [:nodes % :run-gen])))
                  after)
        dead (into #{} (keep (fn [[address entry]]
                               (let [owner (:spin entry)]
                                 (when (or (contains? gone owner)
                                           (and (contains? ran owner)
                                                (not (contains? recorded address))))
                                   address))))
                   (:trace/entries t))
        order (into [] (remove dead) (:trace/order t))
        first-changed (first (keep-indexed (fn [i a] (when (contains? recorded a) i)) order))
        stale (if first-changed (set (subvec order first-changed)) #{})
        entries (reduce-kv (fn [m address entry]
                             (cond (contains? dead address) m
                                   (contains? stale address) (assoc m address (assoc entry :savepoint nil))
                                   :else (assoc m address entry)))
                           {} (:trace/entries t))
        root (some-> (rtp/get-state world [:savepoint/task]) spin-core/spin-id)
        result (when root (rtp/current-result world root))]
    (cond-> (assoc t
                   :trace/entries entries
                   :trace/order order
                   :trace/world world
                   :trace/session session
                   :trace/updated (vec recorded))
      true (dissoc :trace/result :trace/error :trace/pending :trace/pending-value)
      (= :ok (:variant result)) (assoc :trace/result (:payload result))
      (= :error (:variant result)) (assoc :trace/error (:payload result)))))

(defn update
  "Re-run the spins `spin-ids` of the computation `trace` recorded, under
  `policy`, in a fork of the world the trace ended in — and nothing else.

  The incremental counterpart of `replay`: where a replay runs the program
  again from an anchor (everything downstream of the site), an update runs
  only the given spins (`spin.keyed` children: one key of a keyed loop) and
  whatever their new results reach — a keyed spin patches its slot, a spin
  awaiting it resumes. Their sites reach `policy` with their entry in
  `trace`; a site reached again replaces its entry in place, a site reached
  for the first time is added, and the entries the update no longer reaches
  are removed (under the re-run spins: of spins that are gone, and of spins
  that ran again without reaching them). Sites take no anchors (an update
  needs none), and entries after the first rewritten one lose theirs.

  The update is done when the fork is quiescent (`engine.quiescence`), a
  site counted in flight while its policy decides: the consequences of a
  change may stop anywhere, so the root re-completing cannot mark it. A
  computation that throws resolves a trace with `:trace/error`, as `run`
  does; the operation rejects when the policy or the machinery fails, or
  the session closes while the update runs. Options: `:seed`, the fork's
  random seed (default: derived from `trace`'s world and the fork, so every
  update draws afresh); `:spin-of` (fn [world spin-id]) finds a spin to
  re-run (default `keyed/spin-of`).

  Returns a CPS operation resolving the updated trace (`:trace/updated`, the
  addresses the update decided). `trace` is not changed."
  ([trace spin-ids policy] (update trace spin-ids policy nil))
  ([trace spin-ids policy {:keys [seed spin-of]}]
   (fn [resolve reject]
     (let [[resolve reject] (sp/in-callers-world resolve reject)
           session (:trace/session trace)
           source (:trace/world trace)
           spin-of (or spin-of keyed/spin-of)
           delivered? (atom false)
           deliver! (fn [f v] (when (compare-and-set! delivered? false true) (f v)))]
       (if-not (and session source)
         (reject (ex-info "The trace has no world to update" {:type ::no-world}))
         (world-scope/fork!
          (:scope session) source
          (fn [{world :child-ctx}]
            (let [scope (:scope session)
                  active? (atom false)
                  ;; give the fork back: its lease first, or the release
                  ;; waits for an end that never comes (it never terminates)
                  give-back! (fn []
                               (when (compare-and-set! active? true false)
                                 (world-scope/end-activity! scope (:fork-id world))))
                  failed! (fn [error]
                            (give-back!)
                            (sp/release-world! session world)
                            (deliver! reject error))]
              (try
                (let [recorded (atom #{})
                      abandoned (atom nil)
                      live (volatile! {:policy policy :old trace})
                      fail! (fn [sp-or-nil error]
                              (failed! error)
                              (when sp-or-nil
                                (try (sp/abandon sp-or-nil) (catch #?(:clj Throwable :cljs :default) _ nil))))
                      site-opts {:live live :fail! fail!
                                 :update {:recorded recorded
                                          :movable (subtree source spin-ids)}}
                      spins (mapv (fn [id]
                                    (or (spin-of world id)
                                        (throw (ex-info "No spin to re-run" {:type ::no-spin :spin-id id}))))
                                  spin-ids)]
                  (world-scope/begin-activity! scope :savepoint/world world (:fork-id world))
                  (reset! active? true)
                  (rtp/swap-state! world [:savepoint/seed]
                                   (constantly (or seed (sp/derive-seed (sp/seed source)
                                                                        [::update (:fork-id world)] 0))))
                  ;; the update's table replaces the inherited one: a site
                  ;; handler of the session would otherwise take precedence
                  (rtp/swap-state!
                   world [:savepoint/handlers]
                   (constantly
                    {sp/any-site (fn [s]
                                   (let [w (:savepoint/world s)]
                                     (quiescence/begin! w)
                                     (decide-site! s nil (assoc site-opts :done! #(quiescence/end! w)))))
                     ;; the root's end was delivered when the trace was made;
                     ;; the world keeps that end marker, so these do not fire
                     sp/result-site (fn [_] nil)
                     sp/error-site (fn [_] nil)
                     sp/abandoned-site (fn [event] (reset! abandoned (:savepoint/payload event)))}))
                  (binding [ec/*execution-context* world]
                    (doseq [s spins]
                      ;; a computation that throws ends in the trace's
                      ;; :trace/error, as it does for `run`
                      ((keyed/rerun! s) (fn [_] nil) (fn [_] nil))))
                  (quiescence/on-quiescent
                   world
                   (fn []
                     (vreset! live nil)
                     (try
                       (cond
                         (some-> session :closing? deref)
                         (failed! (ex-info "The session closed during the update" {:type ::session-closing}))

                         @abandoned
                         (failed! @abandoned)

                         :else
                         (let [t (settle-update trace world source session spin-ids @recorded)]
                           (give-back!)
                           (deliver! resolve t)))
                       (catch #?(:clj Throwable :cljs :default) error
                         (failed! error))))))
                (catch #?(:clj Throwable :cljs :default) error
                  (failed! error)))))
          reject))))))

(defn earliest
  "The first address of `trace`, in program order, that is in `addresses`."
  [trace addresses]
  (let [wanted (set addresses)]
    (first (filter wanted (:trace/order trace)))))

(defn by-path
  "{path address} of the sites of `trace`: how a readable path
  (`addressing/with-scope`, `:id`) finds the address a site ran under."
  [trace]
  (into {} (map (fn [[address entry]] [(:path entry) address])) (:trace/entries trace)))

(defn anchor-id
  "The identity of an anchor: its world and address. Two traces that share an
  upstream entry share its anchor."
  [anchor]
  [(:fork-id (:savepoint/world anchor)) (:savepoint/address anchor)])

(defn release!
  "Give back the worlds of `trace` that `retained` (another trace, or nil) does
  not share: its anchors are abandoned, the world it ended in is released.
  After a replay: release the loser against the winner. `trace` must not be
  read through its worlds afterwards."
  ([trace] (release! trace nil))
  ([trace retained]
   (let [shared (into #{} (keep (comp #(some-> % anchor-id) :savepoint))
                      (vals (:trace/entries retained)))]
     (doseq [{anchor :savepoint} (vals (:trace/entries trace))
             :when (and anchor
                        (not (contains? shared (anchor-id anchor)))
                        (sp/pending? anchor))]
       (try (sp/abandon anchor)
            (catch #?(:clj Throwable :cljs :default) _ nil)))
     ;; a partial trace (`:until`) holds its pending savepoint too
     (when-let [pending (:trace/pending trace)]
       (when (and (not= (:fork-id (:savepoint/world pending))
                        (some-> retained :trace/pending :savepoint/world :fork-id))
                  (sp/pending? pending))
         (try (sp/abandon pending)
              (catch #?(:clj Throwable :cljs :default) _ nil))))
     (when-let [world (:trace/world trace)]
       (when (and (:fork-id world)
                  (not= (:fork-id world) (:fork-id (:trace/world retained))))
         (sp/release-world! (:trace/session trace) world)))
     nil)))
