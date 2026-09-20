(ns org.replikativ.spindel.effects.savepoint
  "savepoint effect - a checkpoint the program publishes to a handler.

  Every effect site drops a checkpoint the ENGINE continues, in one world.
  `(savepoint site payload)` offers the checkpoint to a HANDLER, which may
  continue it in this world, in any number of forked worlds, or not at all.
  See docs/savepoints.md.

  The algebra is three operations over a value:

    (resume sp v)   continue sp's world with the effect's value v
    (fork sp)       the same savepoint in a new world, as the world is NOW
    (abandon sp)    unwind the computation suspended at sp

  A savepoint is *pending* in its world until that world is resumed from it
  or abandons it; a pending savepoint may be forked any number of times and
  resumed at most once. The state at a site is therefore kept the way
  everything else is kept in Spindel: by forking. A handler that wants to
  come back to a site forks the savepoint BEFORE resuming it and holds the
  fork (an *anchor*: a world that is never run, only forked again).

  A `session` owns the worlds: one `world.scope`, an activity lease per live
  world, and the terminal callbacks. With no handler installed for a site the
  effect is the identity on `payload`."
  (:require [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.effects :as eff]
            [org.replikativ.spindel.engine.addressing :as addressing]
            [org.replikativ.spindel.engine.executor :as executor
             :refer [execute!]]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.world.scope :as world-scope]
            [org.replikativ.spindel.engine.hash :as h]
            [replikativ.logging :as log]
            [is.simm.partial-cps.async :as pcps-async]))

;; =============================================================================
;; Public API shim
;; =============================================================================

(defn savepoint
  "Publish a savepoint: `(savepoint site payload)` or
  `(savepoint site payload {:id address})`.

  `site` is portable data naming the kind of point, `payload` what the point
  offers its handler. Evaluates to whatever the handler resumes it with;
  `payload` when no handler is installed for `site`.

  Must only be called inside a spin; outside, this throws."
  [& _]
  (throw (ex-info "savepoint called outside of spin context (should be CPS-transformed)" {})))

(defn ^:no-doc savepoint-adapter [args]
  (let [[site payload opts] args]
    {:site site :payload payload :opts opts}))

;; =============================================================================
;; World state
;; =============================================================================
;;
;; [:savepoint/handlers] {site (fn [sp])}     inherited by forks, replaceable
;; [:savepoint/session]  Session               process-local owner
;; [:savepoint/pending]  {address entry}       continuations not yet consumed
;; [:savepoint/seq]      long                  program order
;; [:savepoint/seed]     portable              this world's random seed
;; [:savepoint/forks]    {address long}        fork index per site

(def any-site
  "Handler-table key matching every site that has no entry of its own."
  :savepoint/any)

(def result-site
  "Site of the terminal event of a computation that returned. Its payload is
  the result; it has no continuation."
  :savepoint/result)

(def error-site
  "Site of the terminal event of a computation that threw. Its payload is the
  error; it has no continuation."
  :savepoint/error)

(defn handlers [world]
  (or (rtp/get-state world [:savepoint/handlers]) {}))

(defn- handler-for [world site]
  (let [table (handlers world)]
    (or (get table site) (get table any-site))))

(defn install-handlers!
  "Merge `table` ({site handler}) into `world`'s handler table. A nil handler
  removes the entry."
  [world table]
  (rtp/swap-state! world [:savepoint/handlers]
                   (fn [current]
                     (reduce-kv (fn [m site f] (if f (assoc m site f) (dissoc m site)))
                                (or current {})
                                table))))

(defn seed
  "The random seed of `world`, or nil outside a session."
  [world]
  (rtp/get-state world [:savepoint/seed]))

(defn- attach [world entry]
  (assoc entry :savepoint/world world))

(defn pending
  "The savepoints pending in `world`, in program order."
  [world]
  (->> (vals (or (rtp/get-state world [:savepoint/pending]) {}))
       (remove ::claimed)
       (sort-by :savepoint/seq)
       (mapv #(attach world %))))

(defn pending?
  "True while `sp` may still be resumed, forked or abandoned."
  [sp]
  (let [entry (get (rtp/get-state (:savepoint/world sp) [:savepoint/pending])
                   (:savepoint/address sp))]
    (and (some? entry) (not (::claimed entry)))))

;; =============================================================================
;; Session: ownership of the worlds
;; =============================================================================

(defrecord Session [id scope lease root closing?])

(defn session [world]
  (rtp/get-state world [:savepoint/session]))

(defn- world-id [world]
  (or (:fork-id world) ::root))

(defn- cancellation-error []
  (ex-info "Savepoint world abandoned" {:type spin-core/spin-cancelled}))

(defn- cancellation-error? [error]
  (= spin-core/spin-cancelled (:type (ex-data error))))

(defn- dispatch-terminal!
  "Deliver a terminal event to the handler of the world it happened in."
  [world site payload]
  (when-let [handler (handler-for world site)]
    (handler {:savepoint/site site
              :savepoint/payload payload
              :savepoint/world world
              :savepoint/terminal? true})))

(defn- terminal!
  [session-value captured-world site payload]
  ;; The callbacks are closures of the ROOT start; a continuation resumed in a
  ;; forked world reaches them with that world bound.
  (let [world (or ec/*execution-context* captured-world)]
    (try
      (when-not (and (= error-site site) (cancellation-error? payload))
        (dispatch-terminal! world site payload))
      (finally
        (world-scope/end-activity! (:scope session-value) (world-id world))))))

(defn open!
  "Open a session rooted at `world`.

  Options:
    :handlers  {site (fn [sp])}, installed in `world` and inherited by forks
    :seed      portable root seed (default: a random uuid)
    :purpose   world-scope purpose (default :savepoint)
    :fork-opts options for every fork of the session (see `ygg/fork!`)

  Returns the Session. The caller must `close!` it."
  [world {:keys [handlers seed purpose fork-opts]
          :or {purpose :savepoint fork-opts {}}}]
  (when (session world)
    (throw (ex-info "World already belongs to a savepoint session"
                    {:type ::session-exists})))
  (let [scope (world-scope/create {:purpose purpose :fork-opts fork-opts})
        lease (world-scope/begin-activity! scope :savepoint/session)
        value (->Session (random-uuid) scope lease world (atom false))]
    (rtp/swap-state! world [:savepoint/session] (constantly value))
    (rtp/swap-state! world [:savepoint/seed] (constantly (or seed (random-uuid))))
    (install-handlers! world (or handlers {}))
    value))

(defn start!
  "Run `task` (a spin) in the session's root world. Its savepoints reach the
  world's handlers; its end reaches `result-site` or `error-site`."
  [session-value task]
  (let [world (:root session-value)
        scope (:scope session-value)
        spin-id (spin-core/spin-id task)]
    (world-scope/begin-activity! scope :savepoint/world world (world-id world))
    (rtp/swap-state! world [:savepoint/task] (constantly task))
    (ec/with-context world
      (try
        (ec/enqueue-event! {:type :spin-execution
                            :id spin-id
                            :spin task
                            :execution-context world
                            :callback-egress-policy :causal-follow
                            :resolve-fn (fn [value]
                                          (terminal! session-value world result-site value)
                                          value)
                            :reject-fn (fn [error]
                                         (terminal! session-value world error-site error))})
        (catch #?(:clj Throwable :cljs :default) error
          (spin-core/cancel-spin! task)
          (world-scope/end-activity! scope (world-id world))
          (throw error))))
    nil))

;; =============================================================================
;; The effect
;; =============================================================================

(declare abandon)

(defn- savepoint-handler-fn
  [_runtime args resolve reject]
  (let [{:keys [site payload opts spin-id source-loc]} args
        world ec/*execution-context*
        handler (handler-for world site)]
    (if-not handler
      ;; Law 1: no handler, no savepoint.
      (spin-core/resume resolve payload)
      (let [address (or (:id opts)
                        (addressing/site-address! world "sp" site source-loc))
            seq-no (dec (rtp/swap-state! world [:savepoint/seq] (fnil inc 0)))
            entry {:savepoint/site site
                   :savepoint/address address
                   :savepoint/seq seq-no
                   :savepoint/payload payload
                   ::k {:resolve resolve
                        :reject reject
                        :spin-id spin-id
                        :slice-state (simple/capture-slice-state world spin-id)}}]
        (when (get (rtp/get-state world [:savepoint/pending]) address)
          (throw (ex-info "Duplicate savepoint address"
                          {:type ::duplicate-address
                           :savepoint/site site
                           :savepoint/address address})))
        (rtp/swap-state! world [:savepoint/pending]
                         (fn [m] (assoc (or m {}) address entry)))
        (log/trace :savepoint/published {:site site :address address :seq seq-no})
        ;; Publish, THEN look at the session: `close!` raises the flag and
        ;; then scans for pending savepoints, so one of the two sees the other.
        (if (some-> (session world) :closing? deref)
          (try (abandon (attach world entry))
               (catch #?(:clj Throwable :cljs :default) error
                 (when-not (= ::not-pending (:type (ex-data error)))
                   (throw error))))
          (handler (attach world entry)))
        spin-core/incomplete))))

(def savepoint-handler
  (eff/async-effect savepoint-handler-fn))

(eff/register-effect-by-symbol!
 'org.replikativ.spindel.effects.savepoint/savepoint
 savepoint-handler
 'org.replikativ.spindel.effects.savepoint/savepoint-adapter)

;; =============================================================================
;; Operations
;; =============================================================================

(defn- claim!
  "Atomically consume `sp`'s pending entry; throws if it is not pending.

  The winner is read off the committed state: `swap-state!` may retry its
  function, and an overlay world cannot CAS a path it inherited."
  [sp operation]
  (let [world (:savepoint/world sp)
        address (:savepoint/address sp)
        token #?(:clj (Object.) :cljs (js-obj))
        committed (rtp/swap-state!
                   world [:savepoint/pending]
                   (fn [m]
                     (let [entry (get m address)]
                       (if (and entry (not (::claimed entry)))
                         (assoc m address (assoc entry ::claimed token))
                         m))))
        entry (get committed address)]
    (when-not (and entry (identical? token (::claimed entry)))
      (throw (ex-info "Savepoint is not pending in its world"
                      {:type ::not-pending
                       :operation operation
                       :savepoint/site (:savepoint/site sp)
                       :savepoint/address address})))
    (rtp/swap-state! world [:savepoint/pending] (fn [m] (dissoc m address)))
    entry))

(defn ^:no-doc continue-in-slice!
  "Invoke a continuation in the environment it suspended in (bindings,
  address frame, dependency tracking), with `world` bound."
  [world k cont value]
  (let [spin-id (:spin-id k)
        rctx (if (and spin-id (:slice-state k))
               (simple/restore-slice-state! world spin-id k)
               world)]
    (binding [ec/*execution-context* rctx
              ec/*spin-id* (or spin-id ec/*spin-id*)
              pcps-async/*in-trampoline* false]
      (spin-core/resume cont value))))

(defn resume
  "Continue the computation suspended at `sp`, in `sp`'s world, with `value`
  as the effect's value. Consumes `sp`. Returns nil; the continuation runs on
  the world's executor."
  [sp value]
  (let [world (:savepoint/world sp)
        k (::k (claim! sp :resume))]
    (execute! (:executor world)
              (fn [] (continue-in-slice! world k (:resolve k) value)))
    nil))

(defn abandon
  "Unwind the computation suspended at `sp` with a cancellation, so `finally`
  blocks run and its world becomes terminal. Consumes `sp`."
  [sp]
  (let [world (:savepoint/world sp)
        k (::k (claim! sp :abandon))
        reject! (fn [w] (continue-in-slice! w k (:reject k) (cancellation-error)))]
    (try
      (execute! (:executor world) #(reject! world))
      (catch #?(:clj Throwable :cljs :default) scheduling-error
        (log/warn :savepoint/abandon-schedule-failed
                  {:fork-id (:fork-id world) :error scheduling-error})
        (reject! (assoc world :executor (executor/synchronous-executor)))))
    nil))

(defn- derive-seed [parent-seed address index]
  (h/content-hash [:savepoint/seed parent-seed address index]))

(defn fork
  "The savepoint `sp` in a new world that starts as `sp`'s world is now.

  Options:
    :handlers {site handler} merged over the inherited handler table
    :seed     the child's random seed (default: derived from the parent's
              seed, the address and the fork index, so reruns agree)

  `sp` stays pending. Returns a CPS operation `(fn [resolve reject])`
  resolving the child savepoint."
  ([sp] (fork sp nil))
  ([sp {child-handlers :handlers child-seed :seed}]
   (fn [resolve reject]
     (let [world (:savepoint/world sp)
           address (:savepoint/address sp)
           session-value (session world)]
       (cond
         (nil? session-value)
         (reject (ex-info "Savepoint world has no session" {:type ::no-session}))

         (not (pending? sp))
         (reject (ex-info "Cannot fork a savepoint that is not pending"
                          {:type ::not-pending
                           :operation :fork
                           :savepoint/address address}))

         :else
         (let [scope (:scope session-value)
               index (dec (rtp/swap-state! world [:savepoint/forks address]
                                           (fnil inc 0)))]
           (world-scope/fork!
            scope world
            (fn [{:keys [child-ctx]}]
              (try
                (world-scope/begin-activity! scope :savepoint/world child-ctx
                                             (world-id child-ctx))
                (rtp/swap-state! child-ctx [:savepoint/seed]
                                 (constantly (or child-seed
                                                 (derive-seed (seed world) address index))))
                (rtp/swap-state! child-ctx [:savepoint/forks] (constantly {}))
                (when child-handlers
                  (install-handlers! child-ctx child-handlers))
                (resolve (attach child-ctx
                                 (get (rtp/get-state child-ctx [:savepoint/pending])
                                      address)))
                (catch #?(:clj Throwable :cljs :default) error
                  (reject error))))
            reject)))))))

(defn close!
  "End the session: cancel what still runs, abandon every pending savepoint,
  and discard the owned worlds once they are quiescent. Returns a CPS
  operation."
  [session-value]
  (let [scope (:scope session-value)]
    (fn [resolve reject]
      (try
        (reset! (:closing? session-value) true)
        (let [worlds (world-scope/activity-values scope :savepoint/world)]
          (world-scope/request-cancel! scope)
          (doseq [world worlds]
            (let [waiting (pending world)]
              (if (seq waiting)
                (doseq [sp waiting]
                  (try (abandon sp)
                       (catch #?(:clj Throwable :cljs :default) error
                         (when-not (= ::not-pending (:type (ex-data error)))
                           (log/error :savepoint/abandon-failed {:error error})))))
                (when-let [task (rtp/get-state world [:savepoint/task])]
                  (try
                    (binding [ec/*execution-context* world]
                      (spin-core/cancel-spin! task))
                    (catch #?(:clj Throwable :cljs :default) error
                      (log/error :savepoint/cancel-failed {:error error})))))))
          (world-scope/end-activity! scope (:lease session-value))
          ((world-scope/await-quiescence scope)
           (fn [_]
             ;; request-cancel! discards on quiescence; joining is idempotent.
             ((world-scope/discard! scope) resolve reject))
           reject))
        (catch #?(:clj Throwable :cljs :default) error
          (reject error))))))
