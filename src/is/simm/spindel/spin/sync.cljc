(ns is.simm.spindel.spin.sync
  "Synchronization primitives - Deferred, never"
  (:require [is.simm.spindel.runtime.core :as rtc]
            [is.simm.spindel.spin.core :as spin-core]
            [is.simm.spindel.state.atom :as ratom]
            [is.simm.spindel.spin.continuation :as cont]))

;; ============================================================================
;; Synchronization Primitives
;; ============================================================================

(deftype Deferred [id state-atom]
  #?(:clj clojure.lang.IFn :cljs IFn)

  ;; 1-arity: Assign value (INTERNAL - inline delivery)
  ;; Use this ONLY when called from within the same execution-context context
  ;; For external delivery (futures, threads), use deliver! instead
  (#?(:clj invoke :cljs -invoke) [_this value]
   (let [;; Atomically check if already assigned and capture pending callbacks
         pending-callbacks (atom nil)
         _assigned? (swap! state-atom
                          (fn [state]
                            (if (:assigned? state)
                              ;; Already assigned - no change
                              state
                              ;; First assignment - capture pending and mark assigned
                              (do
                                (reset! pending-callbacks (:pending state))
                                {:assigned? true
                                 :value value
                                 :pending []}))))]

     ;; Notify all pending readers INLINE if this was the first assignment
     ;; SAFE ONLY because caller is in same execution-context context (no circular waits)
     (when-let [pending @pending-callbacks]
       (doseq [resolve pending]
         (cont/resume resolve value)))

     ;; Return the assigned value
     (:value @state-atom)))

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
       (do
         (cont/resume resolve value)
         spin-core/incomplete)
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
        state-atom (ratom/create-atom execution-context
                                      {:assigned? false
                                       :value nil
                                       :pending []})
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
