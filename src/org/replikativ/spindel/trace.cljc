(ns org.replikativ.spindel.trace
  "Traces of savepoints, and replay.

  A *trace* is what a computation did at its savepoints: for every site the
  value it was resumed with, a note, and an *anchor* (a fork of the savepoint
  taken before it was resumed, i.e. the world as it was at the site).

    {:trace/entries {address {:site :seq :payload :value :note :savepoint}}
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
  (:require [org.replikativ.spindel.effects.savepoint :as sp]
            [org.replikativ.spindel.engine.protocols :as rtp]))

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

(defn- record! [world sp decision anchor]
  (rtp/swap-state!
   world [:savepoint/trace]
   (fn [trace]
     (let [address (:savepoint/address sp)]
       (-> (or trace empty-trace)
           (update :trace/order conj address)
           (assoc-in [:trace/entries address]
                     {:site (:savepoint/site sp)
                      :seq (:savepoint/seq sp)
                      :payload (:savepoint/payload sp)
                      :value (:value decision)
                      :note (:note decision)
                      :savepoint anchor}))))))

(defn- decide-site!
  "Decide `sp` with `policy`, record it with `anchor`, resume it."
  [sp anchor policy old fail!]
  (invoke! #(policy sp (get-in old [:trace/entries (:savepoint/address sp)]))
           (fn [decision]
             (try
               (record! (:savepoint/world sp) sp decision anchor)
               (sp/resume sp (:value decision))
               (catch #?(:clj Throwable :cljs :default) error
                 (fail! sp error))))
           #(fail! sp %)))

(defn- handlers-of
  "The handlers of one run: decide every site, deliver the end once.
  Returns {:table handler-table :fail! (fn [sp error])}."
  [{:keys [policy old anchor?] :or {anchor? (constantly true)}} session resolve reject]
  (let [delivered? (atom false)
        once! (fn [callback value]
                (when (compare-and-set! delivered? false true)
                  (callback value)))
        fail! (fn [sp error]
                (try (sp/abandon sp) (catch #?(:clj Throwable :cljs :default) _ nil))
                (once! reject error))
        finish (fn [k]
                 (fn [event]
                   (let [world (:savepoint/world event)]
                     (once! resolve
                            (assoc (or (rtp/get-state world [:savepoint/trace])
                                       empty-trace)
                                   k (:savepoint/payload event)
                                   :trace/world world
                                   :trace/session session)))))]
    {:fail! fail!
     :table
     {sp/any-site
      (fn [sp]
        (if (anchor? sp)
          (invoke! #(sp/fork sp)
                   #(decide-site! sp % policy old fail!)
                   #(fail! sp %))
          (decide-site! sp nil policy old fail!)))
      sp/result-site (finish :trace/result)
      sp/error-site (finish :trace/error)
      ;; Abandoned from outside (the session closed, or someone else's
      ;; handler gave this world up): there is no trace to deliver.
      sp/abandoned-site (fn [event] (once! reject (:savepoint/payload event)))}}))

(defn run
  "Run `task` (a spin) in `session`'s root world under `policy`.

  Options:
    :anchor? (fn [sp]) whether to keep the state at a site (default: always);
             a site without an anchor cannot be replayed from

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
  result. `trace` is not changed.

  Returns a CPS operation resolving the new trace."
  ([trace address policy] (replay trace address policy nil))
  ([trace address policy opts]
   (fn [resolve reject]
     (let [[resolve reject] (sp/in-callers-world resolve reject)
           anchor (get-in trace [:trace/entries address :savepoint])]
       (if-not (and anchor (sp/pending? anchor))
         (reject (ex-info "Trace holds no pending anchor at address"
                          {:type ::no-anchor :address address}))
         (let [{:keys [table fail!]}
               (handlers-of (assoc opts :policy policy :old trace)
                            (:trace/session trace) resolve reject)]
           (invoke! #(sp/fork anchor {:handlers table})
                    ;; The anchor already is the state at this site.
                    #(decide-site! % anchor policy trace fail!)
                    reject)))))))

(defn earliest
  "The first address of `trace`, in program order, that is in `addresses`."
  [trace addresses]
  (let [wanted (set addresses)]
    (first (filter wanted (:trace/order trace)))))

(defn- anchor-id [anchor]
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
     (when-let [world (:trace/world trace)]
       (when (and (:fork-id world)
                  (not= (:fork-id world) (:fork-id (:trace/world retained))))
         (sp/release-world! (:trace/session trace) world)))
     nil)))
