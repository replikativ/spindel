(ns org.replikativ.spindel.v2.trace
  "Traces of savepoints, and replay, on engine v2.

  A *trace* is what a computation did at its savepoints: for every site the
  value it was resumed with, a note, and an *anchor*, the savepoint itself
  (a resumed publication keeps the world as it was at the site until it is
  disposed, §8.2 S9).

    {:trace/entries {address {:site :seq :payload :value :note :savepoint}}
     :trace/order   [address ...]        ; program order
     :trace/result  r | :trace/error e
     :trace/world   the world the computation ended in
     :trace/session the session owning every world above}

  A *policy* decides a site: `(policy sp old-entry)` returns
  `{:value v :note n}`, or a CPS operation `(fn [resolve reject])` resolving
  that. `sp` is pending in the world that is about to continue, so a policy
  that scores writes to `(:savepoint/world sp)`.

  `run` executes a computation under a policy; `replay` executes it again
  from one address under another policy, reusing everything upstream of it.
  On v2 an incremental update is a replay from the earliest changed address
  (choices live in tasks, which do not re-run).

  Operations return CPS operations `(fn [resolve reject])` that complete as
  host code (`savepoint/off-world`), never inside a world, so a driver may
  call into any world from its continuation. In a task body await one with
  `v2/external`."
  (:require [org.replikativ.spindel.v2.core :as v2]
            [org.replikativ.spindel.v2.savepoint :as sp]))

(def ^:private empty-trace {:trace/entries {} :trace/order []})

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
  "Calls `make-operation` and delivers its value-or-CPS result; a throw
  rejects."
  [make-operation resolve reject]
  (try
    (let [operation (make-operation)]
      (if (fn? operation)
        (operation resolve reject)
        (resolve operation)))
    (catch #?(:clj Throwable :cljs :default) error
      (reject error))))

(defn record!
  "Adds a decided site to the trace under construction in `w`. An address
  reached twice in one computation is an error: two sites named alike would
  share one entry."
  [w sp decision anchor]
  (v2/update-in-world!
   w [:savepoint/trace]
   (fn [trace]
     (let [trace (or trace empty-trace)
           address (:savepoint/address sp)]
       (when (get-in trace [:trace/entries address])
         (throw (ex-info "Duplicate site address in one computation"
                         {:type ::duplicate-address :address address :site (:savepoint/site sp)})))
       (-> trace
           (update :trace/order conj address)
           (assoc-in [:trace/entries address]
                     {:site (:savepoint/site sp)
                      :seq (:savepoint/seq sp)
                      :payload (:savepoint/payload sp)
                      :value (:value decision)
                      :note (:note decision)
                      :savepoint anchor}))))))

(defn- decide-site!
  "Decides `sp` with the run's policy, records it (with itself as anchor
  when `anchor?` holds), and resumes it, or leaves it pending and hands it
  to `park!` when `until` holds."
  [sp {:keys [live until park! fail! anchor?]}]
  (let [{:keys [policy old]} @live]
    (if-not policy
      (fail! sp (ex-info "The run has delivered" {:type ::delivered}))
      (invoke! #(policy sp (get-in old [:trace/entries (:savepoint/address sp)]))
               (fn [decision]
                 (try
                   (let [keep? (anchor? sp)]
                     (record! (:savepoint/world sp) sp decision (when keep? sp))
                     (if (and until (until sp))
                       (park! sp (:value decision))
                       (do (sp/resume sp (:value decision))
                           ;; no anchor: its basis is not needed
                           (when-not keep? (sp/dispose sp)))))
                   (catch #?(:clj Throwable :cljs :default) error
                     (fail! sp error))))
               (fn [error] (fail! sp error))))))

(defn- handlers-of
  "The handlers of one run: decide every site, deliver the end once. The
  run's callbacks, policy and replayed trace sit in `live`, cleared at
  delivery, so anchors (forks of world state) do not keep them alive."
  [{:keys [policy old anchor? until] :or {anchor? (constantly true)}} session resolve reject]
  (let [live (volatile! {:resolve resolve :reject reject :policy policy :old old})
        delivered? (atom false)
        once! (fn [k value]
                (when (compare-and-set! delivered? false true)
                  (let [callback (get @live k)]
                    (vreset! live nil)
                    (callback value))))
        fail! (fn [sp error]
                (once! :reject error)
                (try (when (sp/pending? sp) (sp/abandon sp)) (catch #?(:clj Throwable :cljs :default) _ nil)))
        trace-of (fn [w]
                   (assoc (or (v2/get-in-world w [:savepoint/trace]) empty-trace)
                          :trace/world w :trace/session session))
        finish (fn [k] (fn [event] (once! :resolve (assoc (trace-of (:savepoint/world event))
                                                          k (:savepoint/payload event)))))
        park! (fn [sp value]
                (once! :resolve (assoc (trace-of (:savepoint/world sp))
                                       :trace/pending sp :trace/pending-value value)))
        site-opts {:live live :until until :park! park! :fail! fail! :anchor? anchor?}]
    {:site-opts site-opts
     :table {:default (fn [sp] (decide-site! sp site-opts))
             sp/result-site (finish :trace/result)
             sp/error-site (finish :trace/error)
             sp/abandoned-site (fn [event] (once! :reject (:savepoint/payload event)))}}))

(defn run
  "Runs `(f)` (creating a task) in `session`'s root world under `policy`.
  Options: `:anchor?` (fn [sp]) whether to keep a site as an anchor (default
  always); `:until` (fn [sp]) a site at which to stop, decided and recorded
  but left pending (`:trace/pending`, `:trace/pending-value`).
  Returns a CPS operation resolving the trace; a computation that throws
  resolves one with `:trace/error`."
  ([session f policy] (run session f policy nil))
  ([session f policy opts]
   (fn [resolve reject]
     (let [resolve (sp/off-world resolve) reject (sp/off-world reject)]
       (try
         (sp/install-handlers! (:root session)
                               (:table (handlers-of (assoc opts :policy policy) session resolve reject)))
         (sp/start! session f)
         (catch #?(:clj Throwable :cljs :default) error
           (reject error)))))))

(defn replay
  "Runs the computation of `trace` again from `address` under `policy`: an
  instance of the anchor at `address` (everything upstream reused as it
  was), whose downstream sites reach `policy` with their entry in `trace`.
  `trace` is not changed. Options as for `run`, and `:seed`.
  Returns a CPS operation resolving the new trace."
  ([trace address policy] (replay trace address policy nil))
  ([trace address policy opts]
   (fn [resolve reject]
     (let [resolve (sp/off-world resolve) reject (sp/off-world reject)
           anchor (get-in trace [:trace/entries address :savepoint])]
       (if-not (and anchor (sp/anchor? anchor))
         (reject (ex-info "Trace holds no anchor at address" {:type ::no-anchor :address address}))
         (let [{:keys [table site-opts]}
               (handlers-of (assoc opts :policy policy :old trace) (:trace/session trace) resolve reject)]
           (invoke! #(sp/fork anchor (cond-> {:handlers table} (:seed opts) (assoc :seed (:seed opts))))
                    (fn [fork]
                      ;; the anchor's entry and everything before it are the
                      ;; fork's own trace already; this site is decided anew
                      (v2/update-in-world! (:savepoint/world fork) [:savepoint/trace]
                                           (fn [t] (let [t (or t empty-trace)]
                                                     (-> t
                                                         (update :trace/entries dissoc address)
                                                         (update :trace/order (fn [o] (vec (remove #{address} o))))))))
                      (decide-site! fork site-opts))
                    reject)))))))

(defn earliest
  "The first address of `trace`, in program order, that is in `addresses`."
  [trace addresses]
  (let [wanted (set addresses)]
    (first (filter wanted (:trace/order trace)))))

(defn anchor-id
  "The identity of an anchor. Two traces that share an upstream entry share
  its anchor."
  [anchor]
  [(::sp/pub anchor) (:savepoint/address anchor)])

(defn release!
  "Gives back what `trace` holds that `retained` (another trace, or nil)
  does not share: its anchors are disposed, the world it ended in is
  released. After a replay: release the loser against the winner."
  ([trace] (release! trace nil))
  ([trace retained]
   (let [shared (into #{} (keep (comp #(some-> % anchor-id) :savepoint))
                      (vals (:trace/entries retained)))]
     (doseq [{anchor :savepoint} (vals (:trace/entries trace))
             :when (and anchor (not (contains? shared (anchor-id anchor))))]
       (try (sp/dispose anchor) (catch #?(:clj Throwable :cljs :default) _ nil)))
     (when-let [pending (:trace/pending trace)]
       (when (and (not (identical? (:savepoint/world pending)
                                   (some-> retained :trace/pending :savepoint/world)))
                  (sp/pending? pending))
         (try (sp/abandon pending) (catch #?(:clj Throwable :cljs :default) _ nil))))
     (let [s (:trace/session trace) w (:trace/world trace)]
       (when (and s w (contains? @(:worlds s) w)
                  (not (identical? w (:trace/world retained))))
         (sp/release-world! s w)))
     nil)))
