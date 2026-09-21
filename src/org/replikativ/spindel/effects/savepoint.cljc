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
  effect is the identity on `payload`.

  A handler is called INLINE: on the publishing thread, inside the effect,
  before the publishing slice has returned. It may call `resume`, `fork` and
  `abandon` there (they hop through the world's executor and are trampolined
  when that executor is synchronous) or hand the savepoint to someone else
  and return. A handler that throws before consuming the savepoint fails the
  computation with that error.

  What a fork of a pending savepoint shares with its source is the world's
  STATE. In-flight coordination is not state: a fork inherits no undrained
  engine events and no timers (see `engine.context/fork-context`), so a
  computation whose continuation waits on another spin of the same world must
  not be forked while that spin is in flight."
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
  `(savepoint site payload opts)` with

    :id     an explicit address, independent of the code's layout
    :resume a qualified symbol naming a function that continues the
            computation from here without the continuation: called with
            `:args` and then the value the savepoint is resumed with, it
            returns the spin to run. Makes the savepoint portable
            (`savepoint.portable/persist`).
    :args   portable arguments for :resume
    :state  the paths of world state :resume depends on

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
;; [:savepoint/pending]  {address entry}       continuations, or tombstones of
;;                                             consumed ones
;; [:savepoint/seq]      long                  program order
;; [:savepoint/seed]     portable              this world's random seed
;; [:savepoint/task]     Spin                  the computation `start!` ran
;; [:savepoint/ended]    token                 the world delivered its terminal
;;
;; Everything but :seq and :seed is process-local and is dropped by
;; `state-backend/serialize-backend`.

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

(def abandoned-site
  "Site of the terminal event of a computation that was abandoned or
  cancelled. Its payload is the cancellation; it has no continuation."
  :savepoint/abandoned)

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

(defn- live-entry
  "The pending entry of `address` in `world`, or nil when there is none or it
  was consumed."
  [world address]
  (let [entry (get (rtp/get-state world [:savepoint/pending]) address)]
    (when (and entry (not (::claimed entry))) entry)))

(defn pending?
  "True while `sp` may still be resumed, forked or abandoned."
  [sp]
  (some? (live-entry (:savepoint/world sp) (:savepoint/address sp))))

;; =============================================================================
;; Callbacks cross worlds
;; =============================================================================

(defn ^:no-doc in-callers-world
  "Wrap the callbacks of a CPS operation so they run in the world the
  operation was INVOKED from. The operations here complete on the thread and
  under the binding of some other world (a fork, the session root); a spin
  that awaits one would otherwise finish its body inside that world, where its
  own completion is not visible. Returns [resolve reject]."
  [resolve reject]
  (let [caller ec/*execution-context*
        wrap (fn [callback]
               (fn [value]
                 (binding [ec/*execution-context* caller
                           pcps-async/*in-trampoline* false]
                   (callback value))))]
    [(wrap resolve) (wrap reject)]))

;; =============================================================================
;; Session: ownership of the worlds
;; =============================================================================

(defrecord Session [id scope lease root closing? started? fork-indices release-on-end])

(defn session [world]
  (rtp/get-state world [:savepoint/session]))

(defn- world-id [world]
  (or (:fork-id world) ::root))

(defn spend-key
  "An identity for what is spent while continuing from `sp`: unique per world
  and site, and a world continues from a site once. A ledger that
  deduplicates by id needs it, or the second fork of one savepoint looks like
  a replay of the first and is not charged."
  [sp]
  [(world-id (:savepoint/world sp)) (:savepoint/address sp)])

(defn- cancellation-error []
  (ex-info "Savepoint world abandoned" {:type spin-core/spin-cancelled}))

(defn- cancellation-error? [error]
  (= spin-core/spin-cancelled (:type (ex-data error))))

(defn- dispatch-terminal!
  "Deliver a terminal event to the handler of the world it happened in. A
  terminal handler runs inside the computation's own completion callback, so
  a throw must not travel back into it as a second outcome."
  [world site payload]
  (when-let [handler (handler-for world site)]
    (try
      (handler {:savepoint/site site
                :savepoint/payload payload
                :savepoint/world world
                :savepoint/terminal? true})
      (catch #?(:clj Throwable :cljs :default) error
        (log/error :savepoint/terminal-handler-failed {:site site :error error})))))

(defn- release-now! [session-value world]
  ;; the fork indices of its sites are of no use once it is gone
  (let [id (world-id world)]
    (swap! (:fork-indices session-value)
           (fn [indices]
             (reduce dissoc indices (filter #(= id (first %)) (keys indices))))))
  ((world-scope/release! (:scope session-value) world)
   (constantly nil)
   (fn [error]
     (when-not (#{::world-scope/scope-consumed ::world-scope/unknown-world}
                (:type (ex-data error)))
       (log/warn :savepoint/release-failed {:fork-id (:fork-id world) :error error})))))

(defn release-world!
  "Give back one forked world of the session whose computation has ended or
  is ending (a world that ended at `result-site` or `error-site` is kept until
  someone is done reading it; an abandoned one is released by itself). May be
  called from the world's own terminal handler: the release then happens when
  the terminal is through. Fire and forget: a world that cannot be released is
  discarded when the session closes."
  [session-value world]
  (let [id (world-id world)
        scope (:scope session-value)]
    ;; Mark, THEN look at the lease: `terminal!` ends the lease and then reads
    ;; the mark, so one of the two releases it. A second release is refused
    ;; by the scope as an unknown world.
    (swap! (:release-on-end session-value) conj id)
    (when-not (contains? (:activities @scope) id)
      (swap! (:release-on-end session-value) disj id)
      (release-now! session-value world))
    nil))

(defn- ending-world
  "The world a terminal callback fired in. The callbacks are closures of the
  ROOT start; a continuation resumed in a forked world reaches them with that
  world bound. A completion that arrives with no world of this session bound
  can only be attributed to the root."
  [session-value]
  (let [ambient ec/*execution-context*]
    (if (and ambient (identical? session-value (session ambient)))
      ambient
      (do (log/warn :savepoint/terminal-without-world
                    {:session (:id session-value)
                     :ambient (some-> ambient :fork-id)})
          (:root session-value)))))

(defn- terminal!
  [session-value site payload]
  (let [world (ending-world session-value)
        token #?(:clj (Object.) :cljs (js-obj))
        first? (identical? token
                           (rtp/swap-state! world [:savepoint/ended]
                                            (fn [ended] (or ended token))))]
    (when first?
      (let [site (if (and (= error-site site) (cancellation-error? payload))
                   abandoned-site
                   site)]
        (try
          (dispatch-terminal! world site payload)
          (finally
            (world-scope/end-activity! (:scope session-value) (world-id world))
            ;; Nobody reads an abandoned world; give it back now, so a long
            ;; search does not hold every anchor it ever dropped.
            (when (and (:fork-id world)
                       (not @(:closing? session-value))
                       (or (= abandoned-site site)
                           (contains? @(:release-on-end session-value) (world-id world))))
              (swap! (:release-on-end session-value) disj (world-id world))
              (release-now! session-value world))))))))

(defn open!
  "Open a session rooted at `world`.

  Options:
    :handlers  {site (fn [sp])}, installed in `world` and inherited by forks
    :seed      portable root seed (default: a random uuid)
    :purpose   world-scope purpose (default :savepoint)
    :fork-opts options for every fork of the session (see `ygg/fork!`)
    :retain-released? keep the descriptors of worlds released before the
               session ends (default true; false for unbounded searches)
    :authority a `world.scope/PResourceAuthority`; forks then take a `:grant`
               and a world gives back what it has left when it is discarded

  Returns the Session. The caller must `close!` it."
  [world {:keys [handlers seed purpose fork-opts authority retain-released?]
          :or {purpose :savepoint fork-opts {} retain-released? true}}]
  (when (session world)
    (throw (ex-info "World already belongs to a savepoint session"
                    {:type ::session-exists})))
  (let [scope (world-scope/create {:purpose purpose :fork-opts fork-opts
                                   :authority authority
                                   :retain-released? retain-released?})
        lease (world-scope/begin-activity! scope :savepoint/session)
        value (->Session (random-uuid) scope lease world
                        (atom false) (atom false) (atom {}) (atom #{}))]
    (rtp/swap-state! world [:savepoint/session] (constantly value))
    (rtp/swap-state! world [:savepoint/seed] (constantly (or seed (random-uuid))))
    (install-handlers! world (or handlers {}))
    value))

(defn ^:no-doc start-in!
  "Run `task` in `world`, a world of the session, under a lease of its own.
  Its savepoints reach the world's handlers; its end reaches a terminal site."
  [session-value world task]
  (let [scope (:scope session-value)
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
                                          (terminal! session-value result-site value)
                                          value)
                            :reject-fn (fn [error]
                                         (terminal! session-value error-site error))})
        (catch #?(:clj Throwable :cljs :default) error
          (spin-core/cancel-spin! task)
          (world-scope/end-activity! scope (world-id world))
          (throw error))))
    nil))

(defn start!
  "Run `task` (a spin) in the session's root world. Its savepoints reach the
  world's handlers; its end reaches `result-site` or `error-site`."
  [session-value task]
  (when-not (compare-and-set! (:started? session-value) false true)
    (throw (ex-info "A savepoint session runs one computation"
                    {:type ::already-started})))
  (start-in! session-value (:root session-value) task))

;; =============================================================================
;; The effect
;; =============================================================================

(declare abandon claim!)

(defn handled?
  "Whether `world` has a handler for `site`."
  [world site]
  (some? (handler-for world site)))

(defn publish!
  "Publish a savepoint from inside another effect's handler: the body of the
  `savepoint` effect, for effects that ARE savepoints (`choose`, `factor`).
  `args` is {:site :payload :opts :spin-id :source-loc}; `resolve`/`reject`
  are the effect's continuations. Returns what the effect handler must return."
  [world args resolve reject]
  (let [{:keys [site payload opts spin-id source-loc]} args
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
                   ;; tier 2: how to continue without the continuation
                   :savepoint/portable (when (:resume opts)
                                         {:fn (:resume opts)
                                          :args (vec (:args opts))
                                          :state (vec (:state opts))})
                   ::k {:resolve resolve
                        :reject reject
                        :spin-id spin-id
                        :slice-state (simple/capture-slice-state world spin-id)}}]
        (when (live-entry world address)
          (throw (ex-info "Duplicate savepoint address"
                          {:type ::duplicate-address
                           :savepoint/site site
                           :savepoint/address address})))
        (rtp/swap-state! world [:savepoint/pending]
                         (fn [m] (assoc (or m {}) address entry)))
        (log/trace :savepoint/published {:site site :address address :seq seq-no})
        ;; Publish, THEN look at the session: `close!` raises the flag and
        ;; then scans for pending savepoints, so one of the two sees the other.
        (let [sp (attach world entry)]
          (if (some-> (session world) :closing? deref)
            (try (abandon sp)
                 (catch #?(:clj Throwable :cljs :default) error
                   (when-not (= ::not-pending (:type (ex-data error)))
                     (throw error))))
            (try
              (handler sp)
              (catch #?(:clj Throwable :cljs :default) error
                ;; Whoever consumed the savepoint owns the computation. If
                ;; nobody did, the computation fails here, once.
                (if (try (claim! sp :handler-failed) true
                         (catch #?(:clj Throwable :cljs :default) _ false))
                  (throw error)
                  (log/error :savepoint/handler-failed-after-consuming
                             {:site site :address address :error error})))))
          spin-core/incomplete)))))

(defn- savepoint-handler-fn
  [_runtime args resolve reject]
  (publish! ec/*execution-context* args resolve reject))

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
  "Atomically consume `sp`; throws if it is not pending. Returns nil.

  One swap replaces the entry by a tombstone, so there is no moment at which a
  savepoint is neither pending nor consumed. The winner is read off the
  committed state: `swap-state!` may retry its function, and an overlay world
  cannot CAS a path it inherited. The continuation itself travels in `sp`."
  [sp operation]
  (let [world (:savepoint/world sp)
        address (:savepoint/address sp)
        token #?(:clj (Object.) :cljs (js-obj))
        committed (rtp/swap-state!
                   world [:savepoint/pending]
                   (fn [m]
                     (let [entry (get m address)]
                       (if (and entry (not (::claimed entry)))
                         (assoc m address {::claimed token})
                         m))))]
    (when-not (identical? token (::claimed (get committed address)))
      (throw (ex-info "Savepoint is not pending in its world"
                      {:type ::not-pending
                       :operation operation
                       :savepoint/site (:savepoint/site sp)
                       :savepoint/address address})))
    nil))

;; A handler may resume inline, and the continuation then runs inside the
;; handler, inside the effect, to the next site, whose handler resumes inline
;; again: one stack frame set per site. So continuations are trampolined: the
;; outermost one on a thread drains the ones made beneath it.
;;
;; The same queue saves the executor hop. A resume made from a thread that is
;; already running this executor's savepoint work is queued on that thread and
;; runs when the current continuation returns. A driver that decides site
;; after site (a chain, a search) then runs on one thread instead of handing
;; every site to another one, which is most of its latency on a busy machine.
(def ^:private draining
  "Per thread: nil, or {:executor e :queue (volatile! PersistentQueue)}."
  #?(:clj (ThreadLocal.) :cljs (volatile! nil)))

(defn- current-drain []
  #?(:clj (.get ^ThreadLocal draining) :cljs @draining))

(def ^:private drain-batch
  "How many queued continuations one task runs before handing the rest back to
  the executor, so a long chain does not keep a pool thread to itself."
  256)

(defn- trampolined!
  "Run `thunk` as savepoint work of `executor` on this thread, then whatever it
  queued. A continuation that throws does not take the queued ones with it:
  they still run, and the first error is rethrown at the end."
  [executor thunk]
  (let [install! (fn [value]
                   #?(:clj (if (nil? value)
                             (.remove ^ThreadLocal draining)
                             (.set ^ThreadLocal draining value))
                      :cljs (vreset! draining value)))
        outer (current-drain)
        queue (volatile! #?(:clj clojure.lang.PersistentQueue/EMPTY
                            :cljs cljs.core/PersistentQueue.EMPTY))
        failure (volatile! nil)
        guarded (fn [f]
                  (try (f)
                       (catch #?(:clj Throwable :cljs :default) error
                         (when-not @failure (vreset! failure error)))))]
    (install! {:executor executor :queue queue})
    (try
      (guarded thunk)
      (loop [ran 0]
        (when-let [next-thunk (peek @queue)]
          (if (< ran drain-batch)
            (do (vswap! queue pop)
                (guarded next-thunk)
                (recur (inc ran)))
            ;; hand the tail back, in order
            (let [tail @queue]
              (vreset! queue (empty tail))
              (execute! executor
                        (fn [] (trampolined!
                                executor
                                ;; re-queue, so each one is guarded by itself
                                (fn [] (vswap! (:queue (current-drain)) into tail)))))))))
      (finally (install! outer)))
    (when-let [error @failure]
      (throw error))))

(defn- schedule!
  "Run `thunk` on `executor`: behind the current continuation when this thread
  is already doing that executor's savepoint work, as a new task otherwise."
  [executor thunk]
  (let [drain (current-drain)]
    (if (and drain (identical? executor (:executor drain)))
      (vswap! (:queue drain) conj thunk)
      (execute! executor (fn [] (trampolined! executor thunk))))))

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
        k (::k sp)]
    (when (some-> (session world) :closing? deref)
      (throw (ex-info "Cannot resume in a closing session"
                      {:type ::session-closing
                       :savepoint/address (:savepoint/address sp)})))
    (claim! sp :resume)
    (schedule! (:executor world)
               #(continue-in-slice! world k (:resolve k) value))
    nil))

(defn abandon
  "Unwind the computation suspended at `sp` with a cancellation, so `finally`
  blocks run and its world ends at `abandoned-site`. Consumes `sp`."
  [sp]
  (let [world (:savepoint/world sp)
        k (::k sp)
        _ (claim! sp :abandon)
        reject! (fn [w] (continue-in-slice! w k (:reject k) (cancellation-error)))]
    (try
      (schedule! (:executor world) #(reject! world))
      (catch #?(:clj Throwable :cljs :default) scheduling-error
        (log/warn :savepoint/abandon-schedule-failed
                  {:fork-id (:fork-id world) :error scheduling-error})
        (let [inline (executor/synchronous-executor)]
          (trampolined! inline #(reject! (assoc world :executor inline))))))
    nil))

(defn ^:no-doc derive-seed [parent-seed address index]
  (h/content-hash [:savepoint/seed parent-seed address index]))

(defn fork
  "The savepoint `sp` in a new world that starts as `sp`'s world is now.

  Options:
    :handlers {site handler} merged over the inherited handler table
    :seed     the child's random seed (default: derived from the parent's
              seed, the address and the fork index, so reruns agree)
    :grant    what the session's resource authority moves from this world's
              wallet to the child's; a grant this world cannot afford rejects
              the fork

  `sp` stays pending. Returns a CPS operation `(fn [resolve reject])`
  resolving the child savepoint."
  ([sp] (fork sp nil))
  ([sp {child-handlers :handlers child-seed :seed grant :grant}]
   (fn [resolve reject]
     (let [[resolve reject] (in-callers-world resolve reject)
           world (:savepoint/world sp)
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
               ;; Process-local, so that forking leaves its source untouched.
               index-key [(world-id world) address]
               index (dec (get (swap! (:fork-indices session-value)
                                      update index-key (fnil inc 0))
                               index-key))]
           (world-scope/fork!
            scope world {:grant grant}
            (fn [{:keys [child-ctx]}]
              ;; Decide inside the try, settle outside it: what the caller's
              ;; continuation throws is the caller's, not a failed fork.
              (let [outcome
                    (try
                      ;; The child is the world as it was when the fork read
                      ;; it. A resume or abandon that won in between leaves
                      ;; nothing to continue there; that fork never becomes a
                      ;; live world.
                      (if-let [entry (live-entry child-ctx address)]
                        (do
                          (world-scope/begin-activity! scope :savepoint/world child-ctx
                                                       (world-id child-ctx))
                          (rtp/swap-state! child-ctx [:savepoint/seed]
                                           (constantly (or child-seed
                                                           (derive-seed (seed world) address index))))
                          (when child-handlers
                            (install-handlers! child-ctx child-handlers))
                          {:ok (attach child-ctx entry)})
                        {:error (ex-info "Cannot fork a savepoint that is not pending"
                                         {:type ::not-pending
                                          :operation :fork
                                          :savepoint/address address})})
                      (catch #?(:clj Throwable :cljs :default) error
                        {:error error}))]
                (if (contains? outcome :ok)
                  (resolve (:ok outcome))
                  (do
                    ;; A world of the scope with nothing to run; it may hold a
                    ;; grant or a lease. Give both back.
                    (world-scope/end-activity! scope (world-id child-ctx))
                    (release-world! session-value child-ctx)
                    (reject (:error outcome))))))
            reject)))))))

(defn close!
  "End the session: cancel what still runs, abandon every pending savepoint,
  and discard the owned worlds once they are quiescent. Returns a CPS
  operation."
  [session-value]
  (let [scope (:scope session-value)]
    (fn [resolve reject]
      (try
        (let [[resolve reject] (in-callers-world resolve reject)]
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
           reject)))
        (catch #?(:clj Throwable :cljs :default) error
          (reject error))))))
