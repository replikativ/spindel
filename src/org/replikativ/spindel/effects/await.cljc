(ns org.replikativ.spindel.effects.await
  "await effect - suspend until spin or deferred completes.

  Supports:
  - Spin: awaits completion, tracks dependency
  - Deferred: async callback-based suspension
  - SignalRef: error (use track instead)"
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.engine.hash :as h]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.engine.effects :as eff]
            [org.replikativ.spindel.effects.track :as track]
            [replikativ.logging :as log]
            [is.simm.partial-cps.async :as pcps-async])
  #?(:clj (:import [org.replikativ.spindel.spin.core Spin])))

;; =============================================================================
;; Public API Shim
;; =============================================================================

(defn await
  "Suspend until value available from spin or deferred.

  Must only be called inside a spin; outside, this throws."
  [& _]
  (throw (ex-info "await called outside of spin context (should be CPS-transformed)" {})))

;; =============================================================================
;; Direct Handler Implementations
;; =============================================================================

(defn- await-spin-cont-id
  "Deterministic continuation ID for a parent's await of a child spin.

  The ID is derived from (parent-spin-id, awaited-spin-id, source-loc) so
  that when the parent body re-runs and re-awaits the same child at the
  same call site, `add-continuation!` overwrites the previous entry rather
  than accumulating stale duplicates. The source-loc disambiguates multiple
  await calls in the same parent body, and awaited-spin-id disambiguates
  iterations of a loop that await different children."
  [parent-spin-id awaited-spin-id source-loc]
  (keyword (str "await-cont-"
                (h/content-hash [parent-spin-id awaited-spin-id source-loc]))))

(defn- spin-await-cont-map
  "Build the continuation map for a parent awaiting a child Spin.

  Reactive children (PSpin) get :ephemeral-await? false so the continuation
  survives `clear-all-await-continuations!` between batches and re-fires
  whenever the child re-completes (e.g. its tracked signals change).

  Captures two per-spin snapshots so the resumed body slice resumes
  consistently with where it left off:

  - `:tracking-snap` — the parent's transient `:spin-tracking` entry at
    suspend time. On resume the engine restores it so the body's
    accumulated dep tracking continues from where it left off rather
    than restarting empty (which would cause record-deps! to spuriously
    remove deps that the pre-suspend body slice had registered).

  - `:chain-head-snap` — the parent's per-spin addressing chain-head at
    suspend time. On resume the engine restores it so any `(spin …)` or
    `(effect …)` forms in the post-resume body slice mint the SAME ids
    as on the first run. Under per-spin chain-head scoping
    (engine/addressing.cljc) the suspended spin's chain-head sits on
    its own node and is never disturbed by other spins running during
    the suspend interval — so this snapshot is per-parent-spin and
    cross-spin restoration cannot collide.

  Also stows the awaited Spin object itself under `:awaited-spin`:
  while the await is in flight (e.g. an asynchronous network
  round-trip via `chan->spin`), this is otherwise the *only* strong
  reference to the Spin. Without it, JS GC can collect the Spin
  between the body-suspend and the response, the finalizer fires
  `try-gc-cleanup-spin!`, sees an empty :observers set (await
  dependencies are tracked in `:await-dependents`, not in node
  observers), and full-cleanups the node. The subsequent response's
  `cache-result!` recreates the node, but a follow-up GC pass between
  cache-result and the :spin-completion event handler can delete it
  again — at which point `on-resume` reads `spin-current-result` and
  gets nil, producing the `No protocol method PResult.match` crash."
  [parent-spin-id awaited-spin awaited-spin-id resolve reject source-loc is-reactive-spin tracking-snap chain-head-snap]
  {:id (await-spin-cont-id parent-spin-id awaited-spin-id source-loc)
   :event-key [:spin/complete awaited-spin-id]
   :resolve-fn resolve
   :reject-fn reject
   :source-loc source-loc
   :ephemeral-await? (not is-reactive-spin)
   :tracking-snap tracking-snap
   :chain-head-snap chain-head-snap
   :awaited-spin awaited-spin
   :on-resume (fn [_rt]
                (let [res (ec/spin-current-result awaited-spin-id)]
                  (spin-core/match res identity identity)))})

(defn- await-spin
  "Direct await handler for Spin.

  Fast path: If spin already completed, resolve immediately from cache.
  Slow path: Register continuation and start child spin.

  NOTE: In rebuild mode, we SKIP the fast path to ensure child spin bodies execute
  (for side effects like nested spin creation and continuation registration)."
  [^Spin spin-ref spin-id source-loc resolve reject]
  (let [awaited-spin-id (spin-core/spin-id spin-ref)
        noop (fn [& _] nil)
        ctx (ec/current-execution-context)
        rebuild? (ctx/rebuild-mode? ctx)]

    ;; Track spin dependency
    (ec/deps-track-spin! spin-id awaited-spin-id)


    ;; Check if spin value available via protocol
    (let [cached (ec/spin-current-result awaited-spin-id)
          ;; CRITICAL: Disable fast path during batch mode to prevent glitches
          ;; UNLESS the spin has already been processed in this batch (cache is fresh)
          ;; Batch is now in context state, not dynamic binding
          batch (rtp/get-state ctx [:engine/current-batch])
          in-batch-mode? (some? batch)
          spin-processed? (when batch
                           (contains? @(:processed batch) awaited-spin-id))
          allow-fast-path? (and (some? cached)
                                (not rebuild?)
                                (not (simple/dirty? ctx awaited-spin-id))
                                (or (not in-batch-mode?)  ;; Not in batch - allow
                                    spin-processed?))]    ;; In batch but cache fresh - allow
      (cond
        ;; Fast path: Spin has result AND (not in batch OR spin already processed)
        allow-fast-path?
        (let [is-reactive-spin (satisfies? spin-core/PSpin spin-ref)]
          ;; Record await dependency even on fast-path so dirty propagation works.
          (simple/record-await-dependency! ctx spin-id awaited-spin-id)
          ;; Register a persistent :spin/complete subscription for reactive Spins.
          ;; Without this, the cached value resolves immediately but the parent
          ;; never gets notified when the child re-completes in a future batch
          ;; (its track-driven signals change, etc.) — the new value is computed
          ;; in the child but never propagates up through this await. The slow
          ;; path already does this; the fast path used to skip it because the
          ;; immediate resolve was treated as the only completion event.
          ;; Deterministic cont-id makes re-awaits idempotent: parent body
          ;; running multiple times overwrites instead of accumulating stale
          ;; continuations.
          (when is-reactive-spin
            (let [tracking-snap (rtp/get-state ctx [:spin-tracking spin-id])
                  chain-head-snap (when-let [a ec/*chain-head*] @a)]
              (ec/continuation-add!
                spin-id
                (spin-await-cont-map spin-id spin-ref awaited-spin-id resolve reject source-loc true
                                     tracking-snap chain-head-snap))))
          (spin-core/match cached
            #(spin-core/resume resolve %)
            #(spin-core/resume reject %)))

        ;; Rebuild mode: Execute child for side effects, then immediately resume with cached value
        ;; We need to execute child body (to create nested spins, register continuations)
        ;; but continue synchronously instead of suspending
        rebuild?
        (let [;; Re-apply the awaited spin's captured DOM scope, same as the
              ;; slow path below. Rebuild executes the child body for side
              ;; effects (registering child continuations etc.); those spins
              ;; need to see their own scope, not the parent's.
              spin-dom-scope (rtp/get-state ctx [:nodes awaited-spin-id :dom-scope])
              child-ctx (if (seq spin-dom-scope)
                          (update ctx :bindings merge spin-dom-scope)
                          ctx)]
          ;; Execute child spin for side effects with child's scope applied
          (binding [ec/*execution-context* child-ctx
                    ec/*spin-id* awaited-spin-id]
            (spin-ref noop noop))
          (log/debug :await/rebuild-child-executed {:parent-id spin-id :awaited-id awaited-spin-id})
          ;; Get cached result (should exist after child execution)
          (let [child-cached (ec/spin-current-result awaited-spin-id)]
            (if child-cached
              (spin-core/match child-cached
                #(spin-core/resume resolve %)
                #(spin-core/resume reject %))
              ;; No cache? Shouldn't happen in rebuild mode
              (spin-core/resume reject
                (ex-info "No cached result for child in rebuild mode"
                         {:parent-id spin-id :child-id awaited-spin-id})))))

        ;; Normal slow path: Start child, check if completed synchronously.
        ;;
        ;; Race fix: register the continuation BEFORE invoking the child.
        ;; The previous order (invoke → check completed? → register) had a
        ;; window between the check and the registration: if the child fired
        ;; asynchronously in that window, child-resolve enqueued a
        ;; :spin-completion event, drain processed it with no subscribers,
        ;; and the continuation we then registered would never fire — the
        ;; parent hung forever. Reproduced as a 4–7 % flake on cold JVMs in
        ;; test-gen-aseq-empty (and others using race / parallel).
        ;;
        ;; Registering first is safe because:
        ;; - synchronous completion still resumes the parent inline below
        ;;   (sync path bypasses the event queue, in-sync-phase suppresses
        ;;    enqueue-completion-event!, so the registered continuation is
        ;;    simply unused for the sync resume),
        ;; - asynchronous completions go through the event queue and find the
        ;;   subscription that is already in place,
        ;; - reactive spins (parallel etc.) that re-complete on signal changes
        ;;   keep using the same continuation across multiple drain dispatches.
        :else
        (let [child-spin-fn (.-spin-fn ^Spin spin-ref)
              child-value (volatile! nil)
              child-error (volatile! nil)
              child-completed? (volatile! false)
              in-sync-phase (volatile! true)
              child-resolve (fn [v]
                              (vreset! child-value v)
                              (vreset! child-completed? true)
                              (ec/spin-cache-result! awaited-spin-id (spin-core/ok v))
                              ;; Commit deps so child registers as signal observer
                              (ec/graph-commit-deps! awaited-spin-id)
                              (when-not @in-sync-phase
                                ;; Async completion: fire event so parent continuation resumes
                                (simple/enqueue-completion-event! ctx awaited-spin-id))
                              v)
              child-reject (fn [e]
                             (vreset! child-error e)
                             (vreset! child-completed? true)
                             (ec/spin-cache-result! awaited-spin-id (spin-core/error e))
                             (ec/graph-commit-deps! awaited-spin-id)
                             (when-not @in-sync-phase
                               (simple/enqueue-completion-event! ctx awaited-spin-id))
                             nil)
              is-reactive-spin (satisfies? spin-core/PSpin spin-ref)
              tracking-snap (rtp/get-state ctx [:spin-tracking spin-id])
              chain-head-snap (when-let [a ec/*chain-head*] @a)
              cont-map (spin-await-cont-map spin-id spin-ref awaited-spin-id
                                            resolve reject source-loc
                                            is-reactive-spin
                                            tracking-snap chain-head-snap)
              ;; Pre-register so any async completion has a subscriber.
              _ (ec/continuation-add! spin-id cont-map)
              _ (log/debug :await/registered-continuation {:parent-id spin-id :awaited-id awaited-spin-id})
              _ (simple/record-await-dependency! ctx spin-id awaited-spin-id)
              ;; Re-apply the awaited spin's captured DOM scope (snapshotted
              ;; at construction in spin/core.cljc::make-spin). Without this,
              ;; the child body would inherit the parent's *execution-context*
              ;; bindings — losing any keyed/scoped DOM context the child was
              ;; constructed under (e.g. ifor-each per-item scope). This is
              ;; the await-handler analogue of the :spin-execution-event fix
              ;; in engine/impl/simple.cljc.
              spin-dom-scope (rtp/get-state ctx [:nodes awaited-spin-id :dom-scope])
              child-ctx (if (seq spin-dom-scope)
                          (update ctx :bindings merge spin-dom-scope)
                          ctx)
              _raw-result (binding [ec/*execution-context* child-ctx
                                    ec/*spin-id* awaited-spin-id
                                    pcps-async/*in-trampoline* false]
                            (child-spin-fn child-resolve child-reject))]
          ;; End sync phase — any future callback invocation is async.
          (vreset! in-sync-phase false)
          (cond
            ;; Synchronous completion — resume parent directly.
            ;; Cache already written by child-resolve/child-reject above.
            ;; The pre-registered continuation is unused for this resume
            ;; (in-sync-phase suppressed the enqueue), but stays in place to
            ;; receive any future re-completions for reactive spins.
            @child-completed?
            (if @child-error
              (spin-core/resume reject @child-error)
              (spin-core/resume resolve @child-value))

            ;; Async — child returned ::incomplete. The continuation is already
            ;; registered above; drain will fire it once child-resolve/reject
            ;; eventually enqueue the :spin-completion event.
            :else
            spin-core/incomplete))))))

(defn- await-deferred
  "Direct await handler for Deferred.

  Deferred implements IFn with 2-arity: (deferred resolve reject)
  Returns ::incomplete to suspend parent until deferred resolves."
  [deferred _spin-id _source-loc resolve reject]
  ;; Call the deferred, it will invoke resolve/reject when ready
  (deferred resolve reject)
  ;; Suspend parent
  spin-core/incomplete)

(defn reactive-spin?
  "Check if value is a Spin. Works across CLJ/CLJS."
  [x]
  (instance? #?(:clj Spin :cljs spin-core/Spin) x))

(defn await-handler
  "Unified direct await handler - dispatches based on type.

  This is the entry point called from CPS-transformed code.
  Handles Spin, Deferred, and errors for SignalRef."
  [awaitable spin-id source-loc resolve reject]
  (try
    ;; Check cancellation at await point
    (eff/check-cancellation! spin-id)

    ;; Type dispatch
    (cond
      (reactive-spin? awaitable)
      (await-spin awaitable spin-id source-loc resolve reject)

      ;; Check Deferred by class name (avoids circular dependency)
      (and awaitable
           (= "org.replikativ.spindel.spin.sync.Deferred"
              #?(:clj (.getName (class awaitable))
                 :cljs (.-name (type awaitable)))))
      (await-deferred awaitable spin-id source-loc resolve reject)

      ;; Check Mailbox by class name (avoids circular dependency)
      ;; Works like Deferred: mailbox calls cont/resume internally if message available
      (and awaitable
           (= "org.replikativ.spindel.spin.sync.Mailbox"
              #?(:clj (.getName (class awaitable))
                 :cljs (.-name (type awaitable)))))
      (do
        (awaitable resolve reject)
        spin-core/incomplete)

      ;; SignalRef is an error
      (track/signal-ref? awaitable)
      (reject (eff/type-error 'await "Spin or Deferred (use track for signals)" awaitable))

      ;; Plain function - treat as async thunk (e.g., from partial-cps async)
      ;; Simple passthrough - effect handlers inside async are responsible for
      ;; registering with spindel runtime if they need to suspend
      (ifn? awaitable)
      (awaitable resolve reject)

      :else
      (reject (eff/type-error 'await "Spin, Deferred, or async thunk" awaitable)))

    (catch #?(:clj Throwable :cljs js/Error) t
      (reject t))))

;; =============================================================================
;; Registration
;; =============================================================================

(eff/register-effect-by-symbol!
  'org.replikativ.spindel.effects.await/await
  ::await-handler
  'org.replikativ.spindel.engine.effects/one-arg->awaitable-map
  'org.replikativ.spindel.effects.await/await-handler)
