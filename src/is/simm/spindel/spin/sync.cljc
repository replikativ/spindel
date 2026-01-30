(ns is.simm.spindel.spin.sync
  "Synchronization primitives - Deferred, never"
  (:require [is.simm.spindel.runtime.core :as rtc]
            [is.simm.spindel.spin.core :as spin-core]
            [is.simm.spindel.state.atom :as ratom]
            [is.simm.spindel.spin.continuation :as cont]
            [is.simm.partial-cps.async :as pcps-async]))

;; ============================================================================
;; Synchronization Primitives
;; ============================================================================

(deftype Deferred [id state-atom]
  #?(:clj clojure.lang.IFn :cljs IFn)

  ;; 1-arity: Assign value via event queue (SAFE)
  ;; Always enqueues delivery event to prevent:
  ;; - Stack overflow from long chains (nested trampolines)
  ;; - Circular waits from external contexts
  ;; Safe to call from anywhere: inside spins, futures, threads, callbacks, REPL
  (#?(:clj invoke :cljs -invoke) [_this value]
   ;; Enqueue delivery event - breaks call stack, ensures proper trampoline handling
   (rtc/enqueue-event! {:type :deferred-delivery
                        :deferred _this
                        :value value})
   value)

  ;; 2-arity: Read as spin (resolve, reject) - standard CPS signature
  (#?(:clj invoke :cljs -invoke) [_this resolve _reject]
   ;; ATOMIC check-and-add: Use swap! to check assigned? and add to pending atomically
   ;; This prevents race where assignment happens between check and add-to-pending
   (let [value-to-resolve (atom nil)
         _result-state (swap! state-atom
                             (fn [state]
                               (if (:assigned? state)
                                 ;; Already assigned - capture value for resolution, don't modify state
                                 (do
                                   (reset! value-to-resolve (:value state))
                                   state)
                                 ;; Not assigned - add to pending
                                 (update state :pending (fnil conj []) resolve))))]
     (if-let [value @value-to-resolve]
       ;; Was already assigned - resolve immediately
       ;; Return result (could be Thunk for trampoline)
       (cont/resume resolve value)
       ;; Was not assigned - added to pending
       spin-core/incomplete))))

(defn create-deferred
  "Create a deferred with explicit execution-context.

   State is stored in a fork-safe execution-context atom.
   Fork-safe - state is copied when execution-context is forked.

   Example:
     (def d (create-deferred execution-context))
     (d :value)  ; Assign
     (spin/spin (await d))  ; Read"
  [execution-context]
  (let [dfv-id (keyword (gensym "deferred-"))
        ;; Use fork-safe atom to store deferred state
        ;; Note: create-atom uses *execution-context* dynamically, so we bind it
        state-atom (binding [rtc/*execution-context* execution-context]
                     (ratom/create-atom {:assigned? false
                                         :value nil
                                         :pending []}))
        dfv-obj (->Deferred dfv-id state-atom)]

    ;; TODO: Auto-cleanup on GC (remove state-atom from execution-context when deferred is GC'd)

    dfv-obj))

(defn deliver!
  "Assign a value to deferred from EXTERNAL context (futures, threads, callbacks).

   This is the SAFE way to deliver from external threads/contexts. It enqueues
   a delivery event to prevent circular waits.

   Usage:
     ;; From future (external thread)
     (future
       (Thread/sleep 100)
       (deliver! d :value))  ; Safe - enqueues event, returns immediately

     ;; From callback
     (http-get url
       (fn [response]
         (deliver! d response)))  ; Safe - enqueues event

   Contrast with internal delivery:
     ;; Inside gen-aseq or spin context (SAME execution-context context)
     (d :value)  ; Fast inline delivery - OK because same context

   When to use which:
   - Use (d value) when: Inside gen-aseq yield handlers, inside spins
   - Use deliver! when: From futures, threads, async callbacks, external code

   Why the distinction:
   - Internal: Inline resume is safe (no circular waits)
   - External: Must enqueue to prevent caller waiting for itself

   See ENGINE_AND_EXECUTION_MODEL.md for details."
  [deferred value]
  ;; Get execution-context from dynamic binding (*execution-context* is available via with-execution-context or binding propagation)
  ;; Enqueue delivery event - caller returns before continuations execute
  (rtc/enqueue-event! {:type :deferred-delivery
                       :deferred deferred
                       :value value})
  value)

(defn deferred
  "Create a single-assignment deferred value using *execution-context*.

   A deferred is a synchronization primitive that can be assigned exactly once
   and read multiple times. Readers block until a value is assigned.

   Usage:
     (def d (deferred))
     (d :value)              ; Assign :value, returns :value (INTERNAL delivery)
     (deliver! d :value)     ; Assign from external context (EXTERNAL delivery)

     ;; Inside a spin, use await (not @) to wait for the deferred
     (require '[is.simm.spindel.effects.reactive :refer [await]])
     (spin/spin
       (let [value (await d)]  ; Awaits until d is assigned
         (process value)))

   Properties:
   - Single assignment: First call assigns value, subsequent calls return same value
   - Multiple readers: All readers receive the same assigned value
   - Blocking reads: Reading blocks until value is assigned
   - Fork-safe: State stored in execution-context atom for distributed execution

   Use cases:
   - Coordination between concurrent spins
   - Lazy initialization of shared resources
   - One-time event notification"
  []
  (if-let [execution-context (try (rtc/current-execution-context) (catch #?(:clj Throwable :cljs :default) _ nil))]
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
  #?(:clj clojure.lang.IFn :cljs IFn)

  ;; 1-arity: Post message via event queue (SAFE)
  ;; Always enqueues post event to prevent:
  ;; - Stack overflow from long chains (nested trampolines)
  ;; - Circular waits from external contexts
  ;; Safe to call from anywhere: inside spins, futures, threads, callbacks, REPL
  (#?(:clj invoke :cljs -invoke) [_this msg]
   ;; Enqueue post event - breaks call stack, ensures proper trampoline handling
   (rtc/enqueue-event! {:type :mailbox-post
                        :mailbox _this
                        :msg msg})
   nil)

  ;; 2-arity: Take message (CONSUMER - blocking until available)
  ;; Works like Deferred: call cont/resume if value available, always return incomplete
  ;; Stores spin-id with waiter so cancelled spins can be skipped
  (#?(:clj invoke :cljs -invoke) [_this resolve _reject]
   ;; ATOMIC check-and-take or add-to-waiters
   (let [current-spin-id rtc/*spin-id*
         msg-to-resolve (atom ::not-found)
         _result (swap! state-atom
                       (fn [state]
                         (if (seq (:queue state))
                           ;; Queue has message - take from front (FIFO)
                           (do
                             (reset! msg-to-resolve (peek (:queue state)))
                             ;; Remove front element
                             (update state :queue pop))
                           ;; Queue empty - add to waiters with spin-id
                           (update state :waiters conj {:spin-id current-spin-id
                                                        :resolve resolve}))))]

     (if (not= ::not-found @msg-to-resolve)
       ;; Got message - resume continuation immediately
       ;; Return result (could be Thunk for trampoline)
       (cont/resume resolve @msg-to-resolve)
       ;; No message - added to waiters, will be resumed async
       spin-core/incomplete))))

(defn create-mailbox
  "Create a mailbox with explicit execution-context.

   A mailbox is a queue where producers post messages (non-blocking)
   and consumers take messages (blocking until available).

   State is stored in fork-safe execution-context atom.
   Fork-safe - state is copied when execution-context is forked.

   Example:
     (def mbx (create-mailbox execution-context))
     (mbx :msg)              ; Post message (returns nil)
     (spin/spin (await mbx)) ; Take message (blocks until available)"
  [execution-context]
  (let [mbx-id (keyword (gensym "mailbox-"))
        ;; Use fork-safe atom to store mailbox state
        ;; Note: create-atom uses *execution-context* dynamically, so we bind it
        ;; Queue is PersistentQueue for proper FIFO semantics
        state-atom (binding [rtc/*execution-context* execution-context]
                     (ratom/create-atom {:queue empty-queue  ; PersistentQueue - FIFO
                                         :waiters []}))      ; Consumers waiting for messages
        mbx-obj (->Mailbox mbx-id state-atom)]

    ;; TODO: Auto-cleanup on GC

    mbx-obj))

(defn post!
  "Post a message to mailbox from EXTERNAL context (futures, threads, callbacks).

   This is the SAFE way to post from external threads/contexts. It enqueues
   a post event to prevent blocking the caller.

   Usage:
     ;; From future (external thread)
     (future
       (Thread/sleep 100)
       (post! mbx :msg))  ; Safe - enqueues event, returns immediately

     ;; From callback
     (on-websocket-message
       (fn [msg]
         (post! mbx msg)))  ; Safe - enqueues event

   Contrast with internal posting:
     ;; Inside spin context (SAME execution-context context)
     (mbx :msg)  ; Fast inline posting - OK because same context

   When to use which:
   - Use (mbx msg) when: Inside spins, inside gen-aseq
   - Use post! when: From futures, threads, async callbacks, external code

   Why the distinction:
   - Internal: Inline resume is safe (no circular waits)
   - External: Must enqueue to prevent caller waiting for itself"
  [mailbox msg]
  ;; Enqueue post event - caller returns before waiter resumes
  (rtc/enqueue-event! {:type :mailbox-post
                       :mailbox mailbox
                       :msg msg})
  nil)

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
     (require '[is.simm.spindel.effects.await :refer [await]])
     (spin/spin
       (let [msg (await mbx)]  ; Awaits until message available
         (process msg)))

   Properties:
   - Multiple messages: Each post adds to queue
   - FIFO: Messages consumed in order posted
   - Multiple consumers: Each message goes to one consumer
   - Blocking take: Taking blocks until message available
   - Non-blocking post: Posting always returns immediately
   - Fork-safe: State stored in execution-context atom

   Use cases:
   - Message passing between concurrent spins
   - Event streams / message queues
   - Producer-consumer patterns
   - Multi-agent communication"
  []
  (if-let [execution-context (try (rtc/current-execution-context) (catch #?(:clj Throwable :cljs :default) _ nil))]
    (create-mailbox execution-context)
    (throw (ex-info "mailbox called outside spin context"
                    {:hint "Use create-mailbox with explicit execution-context, or call from within a spin"}))))
