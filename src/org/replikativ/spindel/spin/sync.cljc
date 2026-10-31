(ns org.replikativ.spindel.spin.sync
  "Synchronization primitives - Deferred, Mailbox, never"
  (:require [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.context :as ctx]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.atom :as ratom]
            [is.simm.partial-cps.async :as pcps-async]
            [is.simm.partial-cps.sequence :as aseq]))

;; ============================================================================
;; Synchronization Primitives
;; ============================================================================

(deftype Deferred [id state-atom]
  rtp/PDeferred
  (deferred-payload [_this] state-atom)

  #?(:clj clojure.lang.IFn :cljs IFn)
  (#?(:clj invoke :cljs -invoke) [this value]
    (rtp/claim-public-deferred! (ec/current-execution-context) this value))
  (#?(:clj invoke :cljs -invoke) [this resolve reject]
    (rtp/invoke-public-deferred! (ec/current-execution-context) this resolve reject)))

(defn- claim-legacy-deferred! [_this value]
  (let [state-atom (rtp/deferred-payload _this)]
    (let [claim-id (random-uuid)
          claimed-state (swap! state-atom
                               (fn [state]
                                 (if (:delivery-claimed? state)
                                   state
                                   (assoc state :delivery-claimed? true
                                          :delivery-claim-id claim-id))))]
      (if (= claim-id (:delivery-claim-id claimed-state))
       ;; We won - enqueue delivery event and return true
        (do
          (ec/enqueue-event! {:type :deferred-delivery
                              :deferred _this
                              :value value})
          true)
       ;; Someone else already claimed delivery
        false))))

(defn- invoke-legacy-deferred! [_this resolve _reject]
  (let [state-atom (rtp/deferred-payload _this)]
   ;; ATOMIC check-and-add: Use swap! to check assigned? and add to pending atomically
   ;; This prevents race where assignment happens between check and add-to-pending
    (let [current-spin-id ec/*spin-id*
          current-cancel-token ec/*external-await-cancel-token*
          ;; Prune already-cancelled readers whenever we add a new one — same
          ;; cancellation-aware sweep as Mailbox's take. A cancelled await
          ;; (race loser, cont truncation) leaves its reader in `:pending`,
          ;; which is only flushed on delivery; a deferred that is awaited-
          ;; then-cancelled but NEVER delivered would otherwise accumulate
          ;; readers without bound.
          ctx (try (ec/current-execution-context)
                   (catch #?(:clj Throwable :cljs :default) _ nil))
          cancelled-tokens (when ctx (ec/get-state [:engine/cancelled-tokens]))
          dead-reader? (fn [{:keys [spin-id cancel-token]}]
                         (or (and spin-id (ec/spin-is-cancelled? spin-id))
                             (and cancel-token cancelled-tokens
                                  (contains? cancelled-tokens cancel-token))))
          result-state (swap! state-atom
                              (fn [state]
                                (if (:assigned? state)
                                ;; Already assigned - return the immutable state
                                ;; snapshot without registering another reader.
                                  state
                                ;; Not assigned - prune dead readers, then add ours
                                  (update state :pending
                                          (fn [ps]
                                            (conj (if ctx
                                                    (filterv (complement dead-reader?) (or ps []))
                                                    (or ps []))
                                                  {:spin-id current-spin-id
                                                   :cancel-token current-cancel-token
                                                   :resolve resolve}))))))]
      (if (:assigned? result-state)
       ;; Was already assigned - resolve immediately
       ;; CRITICAL: Reset *in-trampoline* to ensure Thunks from recur are trampolined
       ;; When called synchronously inside a spin's trampoline, we need a fresh trampoline
        (binding [pcps-async/*in-trampoline* false]
          (spin-core/resume resolve (:value result-state)))
       ;; Was not assigned - added to pending
        spin-core/incomplete))))

(defn create-deferred
  "Create a world-selected single-assignment Deferred in execution-context.

   Bind the intended context when delivering or reading it. The handle carries
   allocation identity; it does not select its creation world. The selected
   engine determines storage, lifetime and fork support. Native Deferred world
   copying currently refuses until registration recovery is implemented."
  [execution-context]
  (let [dfv-id (keyword (gensym "deferred-"))]
    (->Deferred dfv-id (rtp/create-public-deferred! execution-context dfv-id))))

(defn deliver!
  "Queue a single-assignment attempt in the bound execution context.

   Returns value. The first processed attempt assigns the Deferred; later
   attempts preserve that assignment. Callable `(d value)` separately claims
   delivery rights and returns a winner boolean. Readers resume after the
   assignment commits. Ready work may drain before this function returns.

   External producers must bind their intended execution context."
  [deferred value]
  (rtp/deliver-public-deferred! (ec/current-execution-context) deferred value))

(defn- deliver-legacy-deferred! [deferred value]
  ;; The delivery is processed in the BOUND context. A deferred created in
  ;; another world (a sibling, or a fork of this context) has no state here:
  ;; its readers would never wake. Say so at the call site.
  (ratom/check-present! (ratom/atom-id (rtp/deferred-payload deferred))
                        :deliver)
  ;; Get execution-context from dynamic binding (*execution-context* is available via with-context or binding propagation)
  ;; Enqueue delivery event - caller returns before continuations execute
  (ec/enqueue-event! {:type :deferred-delivery
                      :deferred deferred
                      :value value})
  value)

(extend-type #?(:clj org.replikativ.spindel.engine.context.ExecutionContext
                :cljs ctx/ExecutionContext)
  rtp/PSynchronization
  (create-public-deferred! [context _id]
    (ec/legacy-graph-entry! context)
    (binding [ec/*execution-context* context]
      (ratom/create-atom {:assigned? false :value nil :pending []})))
  (claim-public-deferred! [context deferred value]
    (ec/legacy-graph-entry! context)
    (binding [ec/*execution-context* context]
      (claim-legacy-deferred! deferred value)))
  (deliver-public-deferred! [context deferred value]
    (ec/legacy-graph-entry! context)
    (binding [ec/*execution-context* context]
      (deliver-legacy-deferred! deferred value)))
  (read-public-deferred [context deferred]
    (binding [ec/*execution-context* context]
      (let [state @(rtp/deferred-payload deferred)]
        {:assigned? (boolean (:assigned? state)) :value (:value state)})))
  (invoke-public-deferred! [context deferred resolve reject]
    (ec/legacy-graph-entry! context)
    (binding [ec/*execution-context* context]
      (invoke-legacy-deferred! deferred resolve reject))))

(defn deferred
  "Create a single-assignment Deferred using the current execution context.

   `(d value)` returns true for its first callable delivery claim and false
   thereafter. `(deliver! d value)` queues an unclaimed assignment attempt and
   returns value. Assignment is decided by the first processed attempt.

   Inside a spin, `(await d)` suspends until assignment and returns the assigned
   value to every reader. Nil, false and exception objects are successful data.
   Delivery and reads select the bound world; fork support follows that engine."
  []
  (if-let [execution-context (try (ec/current-execution-context) (catch #?(:clj Throwable :cljs :default) _ nil))]
    (create-deferred execution-context)
    (throw (ex-info "deferred called outside spin context"
                    {:hint "Use create-deferred with explicit execution-context, or call from within a spin"}))))

(defn never
  "A spin that never completes.

   Useful for creating spins that wait indefinitely until cancelled.

   Example:
     (race
       (spin/spin :fast)
       (never))  ; Will never win the race

   Use cases:
   - Placeholder for infinite waiting
   - Timeout patterns (race with sleep)
   - Staggered connection attempts (Happy Eyeballs)"
  []
  (spin-core/make-spin
   (fn [_resolve _reject]
     ;; Never call resolve or reject
     spin-core/incomplete)))

;; ============================================================================
;; Mailbox - Multi-Assignment Queue
;; ============================================================================

;; Empty queue constant for cross-platform use
(def ^:private empty-queue
  "Empty PersistentQueue - proper FIFO data structure."
  #?(:clj clojure.lang.PersistentQueue/EMPTY
     :cljs #queue []))

(deftype Mailbox [id state-atom]
  rtp/PMailbox
  (mailbox-payload [_] state-atom)

  #?(:clj clojure.lang.IFn :cljs IFn)
  (#?(:clj invoke :cljs -invoke) [this message]
    (rtp/post-public-mailbox! (ec/current-execution-context) this message))
  (#?(:clj invoke :cljs -invoke) [this succeed fail]
    (rtp/invoke-public-mailbox! (ec/current-execution-context) this succeed fail)))

(defn- post-legacy-mailbox! [mailbox message]
  (ratom/check-present! (ratom/atom-id (rtp/mailbox-payload mailbox)) :post)
  (ec/enqueue-event! {:type :mailbox-post :mailbox mailbox :msg message})
  nil)

(defn- invoke-legacy-mailbox! [mailbox resolve _reject]
  (let [state-atom (rtp/mailbox-payload mailbox)]
    (let [current-spin-id ec/*spin-id*
          current-cancel-token ec/*external-await-cancel-token*
          ;; Prune already-cancelled waiters whenever we add a new one. A
          ;; cancelled await (race loser, signal-change cont truncation)
          ;; leaves its waiter behind: `post-inline!` only skips/drops
          ;; cancelled waiters when a message ARRIVES, so a mailbox that's
          ;; taken-but-never-posted would accumulate them without bound. By
          ;; sweeping here we bound `:waiters` to the live waiters between
          ;; consecutive takes (the same cancelled-detection `post-inline!`
          ;; uses: whole-spin cancellation OR a cancel-token in
          ;; `:engine/cancelled-tokens`).
          ctx (try (ec/current-execution-context)
                   (catch #?(:clj Throwable :cljs :default) _ nil))
          cancelled-tokens (when ctx (ec/get-state [:engine/cancelled-tokens]))
          dead-waiter? (fn [{:keys [spin-id cancel-token]}]
                         (or (and spin-id (ec/spin-is-cancelled? spin-id))
                             (and cancel-token cancelled-tokens
                                  (contains? cancelled-tokens cancel-token))))
          msg-to-resolve (atom ::not-found)
          _result (swap! state-atom
                         (fn [state]
                           ;; swap! may retry: forget an earlier attempt's take.
                           (reset! msg-to-resolve ::not-found)
                           (if (seq (:queue state))
                           ;; Queue has message - take from front (FIFO)
                             (do
                               (reset! msg-to-resolve (peek (:queue state)))
                             ;; Remove front element
                               (update state :queue pop))
                           ;; Queue empty - prune dead waiters, then add ours
                             (update state :waiters
                                     (fn [ws]
                                       (conj (if ctx (filterv (complement dead-waiter?) ws) ws)
                                             {:spin-id current-spin-id
                                              :cancel-token current-cancel-token
                                              :resolve resolve}))))))]

      (if (not= ::not-found @msg-to-resolve)
       ;; Got message - resume continuation immediately
       ;; CRITICAL: Reset *in-trampoline* to ensure Thunks from recur are trampolined
       ;; When called synchronously inside a spin's trampoline, we need a fresh trampoline
        (binding [pcps-async/*in-trampoline* false]
          (spin-core/resume resolve @msg-to-resolve))
       ;; No message - added to waiters, will be resumed async
        spin-core/incomplete))))

;; ============================================================================
;; Immediate take (no reader registered)
;; ============================================================================

(def ^:no-doc nothing
  "Sentinel returned by `take-now!` when nothing is immediately available.
  An object, compared with `identical?`: no message value can equal it."
  #?(:clj (Object.) :cljs (js-obj)))

(defn ^:no-doc take-now!
  "Atomically take what `x` (a Mailbox or Deferred) can deliver RIGHT NOW,
  without registering a waiter/reader; `nothing` otherwise.

  Mailbox: pops the queue head iff the queue is non-empty (the mailbox
  invariant `queue non-empty => no live waiters` means this cannot jump a
  parked consumer) and `spin-id` is not cancelled — the cancellation probe
  runs inside the swap fn, like post-inline!'s dead-waiter check, so a
  cancelled consumer never consumes a message. Deferred: its value iff
  assigned (immutable once assigned).

  For `await-handler`, which resumes the body with the result and RETURNS
  the resume's value (the recur Thunk) to the body's own trampoline. The
  2-arities keep forcing their own trampoline for every other caller."
  [x spin-id]
  (cond
    (instance? Deferred x)
    (let [s (rtp/read-public-deferred (ec/current-execution-context) x)]
      (if (:assigned? s) (:value s) nothing))

    (instance? Mailbox x)
    (let [result (rtp/take-public-mailbox-now! (ec/current-execution-context) x spin-id)]
      (if (:available? result) (:value result) nothing))

    :else nothing))

(defn- take-legacy-mailbox-now! [mailbox spin-id]
  (let [state-atom (rtp/mailbox-payload mailbox)]
    (if (seq (:queue @state-atom))
      (let [taken (volatile! nothing)]
        (swap! state-atom
               (fn [state]
                 (vreset! taken nothing)
                 (if (and (seq (:queue state))
                          (not (and spin-id (ec/spin-is-cancelled? spin-id))))
                   (do (vreset! taken (peek (:queue state)))
                       (update state :queue pop))
                   state)))
        @taken)
      nothing)))

(declare invoke-legacy-mailbox-next!)

(extend-type #?(:clj org.replikativ.spindel.engine.context.ExecutionContext
                :cljs ctx/ExecutionContext)
  rtp/PMailboxSynchronization
  (create-public-mailbox! [context _id]
    (ec/legacy-graph-entry! context)
    (binding [ec/*execution-context* context]
      (ratom/create-atom {:queue empty-queue :waiters []})))
  (post-public-mailbox! [context mailbox message]
    (ec/legacy-graph-entry! context)
    (binding [ec/*execution-context* context]
      (post-legacy-mailbox! mailbox message)))
  (take-public-mailbox-now! [context mailbox spin-id]
    (ec/legacy-graph-entry! context)
    (binding [ec/*execution-context* context]
      (let [value (take-legacy-mailbox-now! mailbox spin-id)]
        {:available? (not (identical? nothing value)) :value value})))
  (invoke-public-mailbox! [context mailbox succeed fail]
    (ec/legacy-graph-entry! context)
    (binding [ec/*execution-context* context]
      (invoke-legacy-mailbox! mailbox succeed fail)))
  (invoke-public-mailbox-next! [context mailbox succeed fail]
    (ec/legacy-graph-entry! context)
    (binding [ec/*execution-context* context]
      (invoke-legacy-mailbox-next! mailbox succeed fail))))

(defn create-mailbox
  "Create a world-selected FIFO Mailbox with explicit execution context.

   Producers queue messages and return nil. Consumers receive one message each.
   Storage and fork support follow the selected engine; the handle does not
   select its creation world. Native copying requires resource recovery."
  [execution-context]
  (let [id (keyword (gensym "mailbox-"))]
    (->Mailbox id (rtp/create-public-mailbox! execution-context id))))

;; ============================================================================
;; AsyncSeq Extension - Mailbox as Lazy Pull Stream
;; ============================================================================

(defn- invoke-legacy-mailbox-next! [mbx resolve reject]
      ;; Capture execution context to rebind when mailbox calls continuation
  (let [exec-ctx (try (ec/current-execution-context)
                      (catch #?(:clj Throwable :cljs :default) _ nil))
        now (take-now! mbx ec/*spin-id*)]
    (if-not (identical? nothing now)
        ;; Immediately available: resolve on this stack and RETURN the
        ;; resolve's value (cps-fn contract) so a looping consumer's
        ;; trampoline forces its recur Thunk instead of nesting.
      (resolve [now mbx])
        ;; Use the mailbox's 2-arity (consumer) to get next message
        ;; Wrap resolve to:
        ;; 1. Rebind execution context (for nested spindel operations)
        ;; 2. Transform msg -> [msg mbx]
      (mbx
       (fn [msg]
         (if exec-ctx
           (binding [ec/*execution-context* exec-ctx]
             (resolve [msg mbx]))
           (resolve [msg mbx])))
       (fn [error]
         (if exec-ctx
           (binding [ec/*execution-context* exec-ctx]
             (reject error))
           (reject error)))))))

(deftype MailboxNext [mailbox]
  rtp/PMailboxNext
  (mailbox-next-target [_] mailbox)
  #?(:clj clojure.lang.IFn :cljs IFn)
  #?@(:clj [(applyTo [this args] (clojure.lang.AFn/applyToHelper this args))])
  (#?(:clj invoke :cljs -invoke) [_ succeed fail]
    (rtp/invoke-public-mailbox-next! (ec/current-execution-context) mailbox succeed fail)))

(extend-type Mailbox
  aseq/PAsyncSeq
  (anext [mailbox] (->MailboxNext mailbox)))

(defn post!
  "Queue a message in the bound world and return nil.

   Both post! and callable posting enqueue delivery. Consumer code runs outside
   the mutation boundary; ready work may drain before this call returns.
   External producers must bind the intended execution context."
  [mailbox message]
  (rtp/post-public-mailbox! (ec/current-execution-context) mailbox message))

(defn mailbox
  "Create a mailbox using *execution-context*.

   A mailbox is a queue for message passing between spins:
   - Producers post messages (non-blocking, returns nil)
   - Consumers take messages (blocking until available)

   Usage:
     (def mbx (mailbox))
     (mbx :msg)              ; Post :msg (returns nil) - INTERNAL
     (post! mbx :msg)        ; Post from external context - EXTERNAL

     ;; Inside a spin, use await (not @) to take a message
     (require '[org.replikativ.spindel.effects.await :refer [await]])
     (spin/spin
       (let [msg (await mbx)]  ; Awaits until message available
         (process msg)))

   Properties:
   - Multiple messages: Each post adds to queue
   - FIFO: Messages consumed in order posted
   - Multiple consumers: Each message goes to one consumer
   - Blocking take: Taking blocks until message available
   - Posting does not wait for a consumer; both post forms return nil
   - Storage and fork support follow the selected execution engine

   Use cases:
   - Message passing between concurrent spins
   - Event streams / message queues
   - Producer-consumer patterns
   - Multi-agent communication"
  []
  (if-let [execution-context (try (ec/current-execution-context) (catch #?(:clj Throwable :cljs :default) _ nil))]
    (create-mailbox execution-context)
    (throw (ex-info "mailbox called outside spin context"
                    {:hint "Use create-mailbox with explicit execution-context, or call from within a spin"}))))

;; ============================================================================
;; Spawn
;; ============================================================================

(defn- report-spawn-callback-error! [callback error]
  ;; Terminal callbacks observe an already-decided Spin result. Their own
  ;; failures must never re-enter the CPS body and reclassify that result.
  (try
    (binding [#?(:clj *out* :cljs *print-fn*)
              #?(:clj *err* :cljs *print-err-fn*)]
      (println "Error in spawn!" (name callback) "callback:" error))
    (catch #?(:clj Throwable :cljs :default) _
      nil)))

(defn- invoke-spawn-callback! [callback f value]
  (try
    ;; A plain callback, not a continuation: whatever CPS code it starts
    ;; runs as a trampoline of its own, inside this try, whoever completes
    ;; the spin.
    (binding [pcps-async/*in-trampoline* false]
      (f value))
    (catch #?(:clj Throwable :cljs :default) error
      (report-spawn-callback-error! callback error))))

(defn spawn!
  "Start a spin as fire-and-forget. The spin runs asynchronously;
   values are passed to `on-success` (default: ignored), and errors are
   passed to `on-error` (default: prints to stderr).

   Works both inside and outside spins. Does not block.

   Usage:
     (spawn! (spin (do-work)))
     (spawn! (spin (do-work)) {:on-success consume-result})
     (spawn! (spin (do-work)) {:on-error my-handler})

   GC contract: `spawn!` registers the Spin instance in the context's
   `[:engine/spawned spin-id]` slot for the duration of its body. This
   prevents the Spin's Cleaner from firing mid-body when the caller
   has no further reference to it — exactly the
   `(spawn! (spin … (deliver p (await x)) …))` pattern. Without this
   the Spin instance becomes GC-eligible the moment `spawn!` returns
   (no caller-held local), and a `try-gc-cleanup-spin!` between
   suspend and resume reaps the body's await cont — the eventual
   resumption then has no continuation to fire and the body's side
   effects (e.g. delivering to `p`) silently never happen. The slot is
   cleared from the resolve/reject callbacks, after which a later GC
   of the Spin object can safely clean up the now-quiescent node.

   Terminal callbacks observe only the first resolution or rejection of this
   spawn, even if a reactive Spin later reruns. Callback exceptions are
   reported to stderr and cannot alter the Spin result or invoke the other
   terminal callback.

   Returns nil."
  ([s] (spawn! s {}))
  ([s {:keys [on-success on-error]
       :or {on-success (fn [_])
            on-error (fn [e] (binding [#?(:clj *out* :cljs *print-fn*)
                                       #?(:clj *err* :cljs *print-err-fn*)]
                               (println "Error in spawned spin:" e)))}}]
   (let [ctx #?(:clj (try (ec/current-execution-context)
                          (catch Throwable _ nil))
                :cljs (try (ec/current-execution-context)
                           (catch :default _ nil)))
         sid (when ctx (spin-core/spin-id s))
         settled? (atom false)
         release! (fn []
                    (when ctx
                      (binding [ec/*execution-context* ctx]
                        (ec/swap-state! [:engine/spawned]
                                        (fn [m] (dissoc m sid))))))
         settle! (fn [callback f value]
                   ;; A reactive Spin may resolve again after invalidation.
                   ;; spawn! observes only the first terminal outcome of this
                   ;; particular invocation.
                   (when (compare-and-set! settled? false true)
                     (release!)
                     (invoke-spawn-callback! callback f value)))]
     (when ctx
       (binding [ec/*execution-context* ctx]
         (ec/swap-state! [:engine/spawned] (fn [m] (assoc m sid s)))))
     ;; Fire-and-forget: nothing returns what the spin (or a callback it
     ;; resumes) hands back, so it runs as a trampoline of its own, also
     ;; when spawned from inside a body.
     (binding [pcps-async/*in-trampoline* false]
       (s (fn [value] (settle! :on-success on-success value))
          (fn [e] (settle! :on-error on-error e))))
     nil)))
