(ns org.replikativ.spindel.engine.core
  "Core runtime context and protocol facades.

	This namespace defines dynamic binding for the active runtime (*execution-context*) and
	thin facades that dispatch to runtime subprotocols in
	org.replikativ.spindel.engine.protocols. Concrete implementations live under
	org.replikativ.spindel.engine.impl.* (e.g., atoms, sequential, stm)."
  (:require [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.bindings :as bindings]
            #?(:clj [is.simm.partial-cps.ioc :as ioc])))

;; =============================================================================
;; Dynamic vars
;; =============================================================================
;;
;; Spindel intentionally minimises dynamic-var surface to keep the
;; programming model consistent across the JVM (per-thread bindings)
;; and ClojureScript (single global mutable `.-val` per Var). Each var
;; below has a clear lexical scope; values that live longer than a
;; single synchronous body are kept in execution-context state instead
;; (see e.g. `engine/addressing.cljc` for the chain-head cursor).
;;
;; The Invariant
;; -------------
;;   `*execution-context*` is the only *essential* dynamic var.
;;   Everything else is body-slice / call-stack scope and survives
;;   only as long as the lexical `binding` that pushed it. State that
;;   needs to outlive that scope lives in ctx state.

(def ^:dynamic *execution-context*
  "The active execution context. Bound by `with-context` / `binding`
  before invoking a spin's body or resuming a continuation.

  Holds all reactive state (signals, spin nodes, continuations,
  addressing cursor, etc.) via its state backend. Forks are O(1)
  overlay-backend copies of this record."
  nil)

(defn restore-scope
  "What `*execution-context*` is restored to when a continuation leaves a
  `binding` form that rebound it. `saved` is the context outside the form,
  `entered` the one the form bound, `current` the one the continuation fires
  in.

  A SCOPE form (`with-key`, `dom.addressing/with-parent-addr`) binds the same
  world with extra `:bindings`. The world is supplied from outside — whoever
  resumes a continuation binds the world to continue in, so the same
  continuation can be resumed in a fork or rerun elsewhere — so the world
  stays `current` and only the scope goes back: the `:bindings` are replaced,
  as `restore-slice-state!` replaces them. Restoring `saved` wholesale pulled
  a continuation resumed in a fork back into the world the form was entered
  in (#64).

  A form that SWITCHES worlds (binds a context over another backend: a
  restored snapshot, a fork, another runtime) returns to the world it left:
  `saved`."
  [saved current entered]
  (if (and saved current entered
           (identical? (:backend saved) (:backend entered)))
    (assoc current :bindings (:bindings saved))
    saved))

#?(:clj
   (ioc/register-binding-restorer! `*execution-context* `restore-scope))

(def ^:dynamic *spin-id*
  "The spin whose body is currently executing on this call stack.
  Bound by the engine at body entry, by the engine at resume sites,
  and by `effects/await.cljc` when invoking a child's body inline.

  Consumers always combine this with explicit ctx-state lookups
  (`get-state ctx [:nodes spin-id …]`), so a stale value points
  to an empty slot — no observable harm if it leaks across an
  async boundary, but the binders below cover every legitimate
  re-entry."
  nil)

(def ^:dynamic *yield-handler*
  "Yield handler for async-sequence generators (`gen-aseq`).
  Bound by `seq/core.cljc/with-yield` around the generator body;
  read by `effects/yield.cljc/yield-handler`. Scope is the whole
  generator body, including its asynchronous resumes (the seq
  machinery rebinds it on each resume via `restore-bindings`)."
  nil)

(def ^:dynamic *external-await-cancel-token*
  "Per-await cancellation token threaded from
  `effects/await.cljc::cancellable-external-pair` into a resource's
  await implementation when the resource consumes a waiter WITHOUT
  going through the wrapped resolve closure.

  Concretely: a `Deferred` invokes every closure in `:pending` on
  delivery, so the cancellation gate around the closure suffices to
  drop orphans. A `Mailbox` consumes exactly one waiter per post,
  so the consumed-but-orphaned waiter would swallow a message
  silently — instead, the Mailbox 2-arity reads this token at waiter
  registration and `post-inline!` skips waiters whose token is in
  `:engine/cancelled-tokens`.

  Lives in engine.core (rather than effects/await.cljc) to avoid
  a require cycle with `spin/sync.cljc`."
  nil)

(def ^:dynamic *callback-egress-policy*
  "Authority attached to callbacks created by the current host invocation.

  The default is world-local. Savepoint sessions and inference may bind
  `:causal-follow` when a continuation copied into a descendant is explicitly
  authorized to complete the coordinating callback. This authority is captured
  on the callback edge; interpreted code cannot grant it by rebinding a world."
  :isolated)

;; =============================================================================
;; CLJS Binding Registration
;; =============================================================================
;;
;; The engine schedules continuations across async boundaries (executor
;; setTimeouts on CLJS, executor submissions on JVM). At schedule time,
;; `engine/bindings.cljc/capture-bindings` snapshots the current values
;; of the registered vars; at fire time, `restore-bindings` re-establishes
;; them around the resume body.
;;
;; *execution-context* is deliberately NOT registered: it's bound
;; explicitly by event handlers when resuming continuations, and
;; capturing it here would create a circular reference (ctx → cont →
;; bindings → ctx) and risk StackOverflow.

#?(:cljs
   (do
     (bindings/register-var! #'*spin-id*)
     (bindings/register-var! #'*yield-handler*)
     (bindings/register-var! #'*external-await-cancel-token*)))

;; ExecutionContext binding macros
#?(:clj
   (defmacro with-context [ctx & body]
     `(binding [*execution-context* ~ctx]
        ~@body))
   :cljs
   (defn with-context [ctx f]
     (binding [*execution-context* ctx]
       (f))))

;; =============================================================================
;; Facades: dispatch to runtime protocols
;; =============================================================================

;; ----------------------------------------------------------------------------
;; Accessors
;; ----------------------------------------------------------------------------

;; -----------------------------------------------------------------------------
;; Home context: a stable record for weak references
;; -----------------------------------------------------------------------------
;;
;; Context records are values: every binding change (`assoc` of :bindings,
;; the per-body scope of every spin run, the drain's normalization) makes a
;; new, short-lived record over the same backend. A GC callback that must
;; reach a context (spin cleanup) can hold it only weakly — a strong
;; reference from a cleaner registry, a GC root, pins it — but a weak
;; reference to whatever record happened to be bound clears as soon as that
;; record is garbage, long before the context is. The callback then finds
;; nothing and silently does no cleanup (measured: 774 of 779 spin cleanups
;; in the jsdom fuzz suite were dropped this way).
;;
;; So each context (root, fork, restored snapshot) carries a :home cell
;; holding its creation record. Every record derived by `assoc` shares the
;; cell, so the home record stays reachable exactly as long as some record
;; of the context is — the right lifetime for a weak reference.

(declare home-context)

(defn ^:no-doc with-home
  "Stamp `ctx` with a fresh :home cell that holds the stamped record, and a
  fresh registry of its following forks (`register-following-fork!`)."
  [ctx]
  (let [cell (volatile! nil)
        ctx (assoc ctx
                   :home cell
                   :following-forks (atom []))]
    (vreset! cell ctx)
    ctx))

;; A FOLLOWING fork reads every path it has not written through from its
;; parent's live state, so a write in the parent is a write in the fork.
;; Engine decisions that are one world's to make — "the creator no longer
;; holds this child, detach it" — must not be written into state a
;; following fork still reads (`release-superseded-children!`). The parent
;; therefore keeps weak references to its following forks: a fork counts
;; while it is reachable, and stops counting once it is garbage.

;; On a JS runtime without WeakRef (pre-ES2021) a fork cannot be tracked
;; without pinning it for good. The registry then records a fork that holds
;; no reference at all and counts as reachable forever: once such a context
;; has had a following fork, superseded children are never detached there
;; (the pre-fix behaviour), but no fork is retained by the registry. Those
;; runtimes have no FinalizationRegistry either, so no spin is ever reaped
;; by GC on them anyway.
(defn- weak-ref [x]
  #?(:clj (java.lang.ref.WeakReference. x)
     :cljs (if (exists? js/WeakRef)
             (js/WeakRef. x)
             #js {:deref (constantly true)})))

(defn- weak-get [r]
  #?(:clj (.get ^java.lang.ref.WeakReference r)
     :cljs (.deref ^js r)))

(defn ^:no-doc register-following-fork!
  "Record `fork` (weakly) as a following fork of `parent`."
  [parent fork]
  (when-let [reg (:following-forks parent)]
    (let [r (weak-ref (home-context fork))]
      (swap! reg (fn [rs] (conj (filterv weak-get rs) r)))))
  fork)

(defn ^:no-doc following-forks?
  "Whether `ctx` has a following fork that is still reachable."
  [ctx]
  (boolean (when-let [reg (:following-forks ctx)]
             (some weak-get @reg))))

(defn ^:no-doc home-context
  "The home record of `ctx` (see `with-home`): stable for as long as the
  context is in use, so it is what a weak reference should point at. Falls
  back to `ctx` itself when it has no home or its home is over a different
  backend (a record re-pointed at a new backend without re-stamping)."
  [ctx]
  (let [h (some-> (:home ctx) deref)]
    (if (and h (identical? (:backend h) (:backend ctx)))
      h
      ctx)))

(defn current-execution-context
  "Return dynamically bound execution context.

	Throws if neither is bound.

	Returns: Runtime instance (AtomsRuntime, StmRuntime) or ExecutionContext."
  []
  (or *execution-context*
      (throw (ex-info "No execution context bound. Use with-context."
                      {:hint "Bind *execution-context* using with-context"}))))

(defn execution-context-bound?
  "Check if a runtime is currently bound.

	Returns true if *execution-context* is bound, false otherwise.

	Useful for cleanup callbacks that may run after test teardown."
  []
  (boolean *execution-context*))

;; ----------------------------------------------------------------------------
;; Graph operation helpers (dispatch to protocol when available)
;; ----------------------------------------------------------------------------

(defn ^:no-doc graph-commit-deps!
  "Commit tracked dependencies for spin-id using the bound runtime via PGraph."
  [spin-id]
  (let [ctx (current-execution-context)]
    (rtp/record-deps! ctx spin-id)))

(defn ^:no-doc graph-clear-deps!
  "Clear spin-id from graph using the bound runtime via PGraph."
  [spin-id]
  (let [ctx (current-execution-context)]
    (rtp/clear-deps! ctx spin-id)))

(defn ^:no-doc graph-ordered-observers
  "Return ordered observer spin-ids for a signal-id via PGraph."
  [signal-id]
  (let [ctx (current-execution-context)]
    (rtp/ordered-observers ctx signal-id)))

;; ----------------------------------------------------------------------------
;; Transient dependency tracking (PDepsTracking)
;; ----------------------------------------------------------------------------

(defn ^:no-doc deps-track-signal!
  "Record that the current spin observed signal-id during this turn."
  [spin-id signal-id]
  (let [ctx (current-execution-context)]
    (rtp/track-signal-dep! ctx spin-id signal-id)))

(defn ^:no-doc deps-track-spin!
  "Record that parent spin observed child spin during this turn."
  [parent-spin-id child-spin-id]
  (let [ctx (current-execution-context)]
    (rtp/track-spin-dep! ctx parent-spin-id child-spin-id)))

;; ----------------------------------------------------------------------------
;; Spin operation facades (PSpin protocol)
;; ----------------------------------------------------------------------------

(defn ^:no-doc spin-register! [spin-id spin-meta]
  (let [ctx (current-execution-context)]
    (rtp/register-spin! ctx spin-id spin-meta)))

(defn ^:no-doc spin-mark-dirty! [spin-id]
  (let [ctx (current-execution-context)]
    (rtp/mark-dirty! ctx spin-id)))

(defn ^:no-doc spin-cache-result!
  ([spin-id result]
   (let [ctx (current-execution-context)]
     (rtp/cache-result! ctx spin-id result)))
  ([spin-id result run]
   (let [ctx (current-execution-context)]
     (rtp/cache-result! ctx spin-id result run))))

(defn ^:no-doc spin-current-result [spin-id]
  (let [ctx (current-execution-context)]
    (rtp/current-result ctx spin-id)))

(defn ^:no-doc spin-result-clean?
  "Check if a spin's cached result is clean.
	Returns true if clean, false if dirty or uncached."
  [spin-id]
  (let [ctx (current-execution-context)]
    (rtp/clean? ctx spin-id)))

(defn ^:no-doc spin-result-dirty?
  "Check if a spin's cached result is dirty.
	Returns true if dirty, false if clean or uncached."
  [spin-id]
  (let [ctx (current-execution-context)]
    (rtp/dirty? ctx spin-id)))

(defn current-spin-id
  "Get the current spin ID from dynamic binding.
	Returns nil if called outside spin context."
  []
  *spin-id*)

(defn spin-is-cancelled?
  "Check if a spin has been cancelled.
	0-arity: Check current spin via *spin-id*
	1-arity: Check specific spin-id
	Returns false if spin not found or not cancelled."
  ([]
   (when-let [spin-id *spin-id*]
     (spin-is-cancelled? spin-id)))
  ([spin-id]
   (when spin-id
     (when-let [result (spin-current-result spin-id)]
       ;; Result is a Result record with :variant and :payload
       ;; Check for cancellation error type from lifecycle/cancel-spin!
       (and (= :error (:variant result))
            (let [error (:payload result)]
              (= :org.replikativ.spindel.spin.core/spin-cancelled
                 (:type (ex-data error)))))))))

;; ----------------------------------------------------------------------------
;; Continuation facades (PContinuation)
;; ----------------------------------------------------------------------------

(defn ^:no-doc continuation-add! [spin-id cont]
  (let [ctx (current-execution-context)
        ;; Auto-capture bindings when adding continuation
        captured-bindings (bindings/capture-bindings)
        cont-with-bindings (assoc cont :bindings captured-bindings)]
    (rtp/add-continuation! ctx spin-id cont-with-bindings)))

(defn ^:no-doc continuation-remove!
  ([spin-id cont-id]
   (let [ctx (current-execution-context)]
     (rtp/remove-continuation! ctx spin-id cont-id)))
  ([spin-id cont-id opts]
   (let [ctx (current-execution-context)]
     (rtp/remove-continuation! ctx spin-id cont-id opts))))

(defn ^:no-doc continuation-earliest [spin-id signal-id]
  (let [ctx (current-execution-context)]
    (rtp/earliest-continuation ctx spin-id signal-id)))

(defn ^:no-doc continuation-resume! [spin-id cont resume-fn]
  (let [ctx (current-execution-context)]
    (rtp/resume-continuation! ctx spin-id cont resume-fn)))

;; ----------------------------------------------------------------------------
;; Engine ingress facade (PEngine)
;; ----------------------------------------------------------------------------

;; Alias for ergonomics
(defn ^:no-doc enqueue-event!
  "Enqueue an event into the runtime engine.

  Uses current-execution-context from dynamic binding (*execution-context*).

  Events are processed by the engine's event handler, which dispatches based on :type.

  Example:
    (enqueue-event! {:type :deferred-delivery :deferred d :value 42})"
  [event]
  (let [ctx (current-execution-context)]
    (rtp/enqueue! ctx event)))

;; ----------------------------------------------------------------------------
;; General state management facades (PState)
;; ----------------------------------------------------------------------------

(defn swap-state!
  "Atomically update state at path using function f.

	Equivalent to: (swap! atom update-in path f)

	Automatically retries on conflict (like atom's swap!).
	Returns the new value at path.

	Example:
		(swap-state! [:signals sig-id]
			(fn [old-signal]
				(assoc old-signal :snapshot new-value)))"
  [path f]
  (let [ctx (current-execution-context)]
    (rtp/swap-state! ctx path f)))

(defn swap-state-args!
  "Atomically update state at path with function and args.

	Equivalent to: (apply swap! atom update-in path f args)

	Returns the new value at path.

	Example:
		(swap-state-args! [:state :atoms id :value] conj [item])"
  [path f & args]
  (let [ctx (current-execution-context)]
    (rtp/swap-state-args! ctx path f args)))

(defn get-state
  "Non-transactional read of state at path.

	For atomic read-modify-write, use swap-state! instead.

	Returns the value at path, or nil if path doesn't exist.

	Example:
		(get-state [:signals sig-id]) => {:snapshot 42 :deltas []}"
  [path]
  (let [ctx (current-execution-context)]
    (rtp/get-state ctx path)))

(defn get-state-in
  "Read `path` from the explicit execution context `ctx`.

  Most programs should use `get-state`, which follows the dynamic world. This
  arity exists for stable world references that must resolve against a context
  supplied by an embedding or continuation boundary."
  [ctx path]
  (rtp/get-state ctx path))

(defn notify-listeners!
  "Fire the watch/egress listeners registered for reference `ref` (id `id`) with the
   classic `(key ref old new)` watch arity. Listeners live at the fork-local path
   `[:listeners id]`, so this reads the BOUND context's set — a fork swap fires the
   fork's listeners (none, unless the fork added its own), never the parent's.

   MUST be called AFTER the value commit (swap-state!/cas-state!) returns — never
   inside the swap fn, which can CAS-retry and would double-fire. Exception-isolated
   so a misbehaving listener can't break the runtime. Shared by SignalRef and
   RuntimeAtom — the one watch mechanism for both context-backed reference types."
  [ref id old new]
  (doseq [[k f] (get-state [:listeners id])]
    (try
      (f k ref old new)
      (catch #?(:clj Throwable :cljs :default) e
        ;; Don't let a listener exception break the runtime (matches the old
        ;; atom-watcher dispatch behavior).
        #?(:clj (.printStackTrace ^Throwable e)
           :cljs (js/console.error "Listener error:" e)))))
  nil)

(defn cas-state!
  "Low-level compare-and-set for advanced CAS patterns.

	Most code should use swap-state! instead.

	Returns true if successful, false otherwise.

	Example (semaphore pattern):
		(loop []
			(let [old-state (get-state path)]
				(if (cas-state! path old-state new-state)
					:success
					(recur))))"
  [path old-val new-val]
  (let [ctx (current-execution-context)]
    (rtp/cas-state! ctx path old-val new-val)))

;; ----------------------------------------------------------------------------
;; Executor accessor
;; ----------------------------------------------------------------------------

(defn get-executor
  "Get the executor for a context (where spin functions actually run).

  Uses current-execution-context if no context provided. Returns an object
  implementing PExecutor (see engine.executor)."
  ([]
   (get-executor (current-execution-context)))
  ([ctx]
   (:executor ctx)))

;; =============================================================================
;; Event Handler Helpers
;; =============================================================================

(defn make-handler
  "Create an event handler function that auto-binds the execution context.

  Usage:
    (.addEventListener el \"click\" (make-handler ctx on-click))

  Args:
    ctx - ExecutionContext to bind
    handler-fn - Function that takes the event as argument

  Returns: Function that binds context before calling handler"
  [ctx handler-fn]
  (fn [event]
    (binding [*execution-context* ctx]
      (handler-fn event))))
