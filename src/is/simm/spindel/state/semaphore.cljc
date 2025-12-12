(ns is.simm.spindel.state.semaphore
  "Fork-safe semaphores for rate limiting and resource management.

  A semaphore controls access to a limited number of permits. Spins acquire permits
  before accessing resources and release them when done. If no permits are available,
  spins wait in a queue until a permit is released.

  Key features:
  - Fork-safe: State stored in runtime for distributed execution
  - Fair queueing: FIFO order for waiting spins
  - Resource safety: holding ensures permit release even on errors

  Usage:
    (require '[is.simm.spindel.state.semaphore :as sem]
             '[is.simm.spindel.effects.reactive :refer [await]])

    ;; Limit to 10 concurrent database connections
    (def db-sem (sem/semaphore 10))

    (spin/spin
      (await (sem/holding db-sem
               (spin/spin (query-database)))))"
  (:refer-clojure :exclude [])
  (:require [is.simm.spindel.spin.core :as spin]
            [is.simm.spindel.spin.continuation :as cont]
            [is.simm.spindel.runtime.core :as rtc]
            [is.simm.spindel.runtime.protocols :as rtp]))

;; =============================================================================
;; Semaphore - Fork-safe permit-based synchronization
;; =============================================================================

(deftype Semaphore [id]
  #?@(:clj [clojure.lang.IDeref
            (deref [this]
              ;; Use dynamically bound *execution-context* - no captured runtime!
              (rtc/get-state [:semaphores id :permits]))]
      :cljs [IDeref
             (-deref [this]
               ;; Use dynamically bound *execution-context* - no captured runtime!
               (rtc/get-state [:semaphores id :permits]))]))

;; =============================================================================
;; Public API
;; =============================================================================

(defn create-semaphore
  "Create a semaphore with N permits using explicit runtime.

  State is stored in the runtime at [:semaphores sem-id].
  Fork-safe - state is copied when runtime is forked by the implementation.

  IMPORTANT: Semaphore does NOT capture the runtime - it uses dynamic *execution-context* binding.
  This enables proper forking: semaphores work with whatever runtime is bound at use-time.

  Example:
    (def sem (create-semaphore (rtc/current-execution-context) 5))
    @sem  ; => 5 (current permits available)"
  [execution-context max-permits]
  {:pre [(pos? max-permits)]}
  (let [sem-id (keyword (gensym "sem-"))
        sem-obj (->Semaphore sem-id)]  ; No runtime captured!

    ;; Initialize state in runtime
    (binding [rtc/*execution-context* execution-context]
      (rtc/swap-state! [:semaphores sem-id]
                       (fn [_]
                         {:permits max-permits
                          :max-permits max-permits
                          :waiting-queue #?(:clj clojure.lang.PersistentQueue/EMPTY
                                            :cljs cljs.core/PersistentQueue.EMPTY)})))

    ;; TODO: Auto-cleanup on GC (like atom.cljc) if needed

    sem-obj))

(defn semaphore
  "Create a semaphore with N permits.

  Must be called within a spin context (where rtc/*execution-context* is bound).

  Example:
    (def sem (semaphore 10))  ; 10 concurrent permits
    @sem  ; => 10"
  [max-permits]
  {:pre [(pos? max-permits)]}
  (try
    (let [ctx (rtc/current-execution-context)]
      (create-semaphore ctx max-permits))
    (catch #?(:clj Throwable :cljs :default) _
      (throw (ex-info "semaphore called outside spin context"
                      {:hint "Use create-semaphore with explicit runtime, or call from within a spin"
                       :max-permits max-permits})))))

(defn acquire
  "Returns a spin that completes when a permit is acquired.

  If a permit is available: completes immediately with :acquired
  If no permits: waits in FIFO queue until a permit is released

  Uses dynamically bound *execution-context* - works with forked runtimes.

  Example:
    (spin/spin
      (await (acquire sem))
      ;; Now holding permit
      (do-work)
      (release sem))"
  [sem]
  (spin/make-spin
   (fn [resolve reject]
     (let [sem-id (.-id sem)
           got-permit? (atom false)]  ; Capture decision atomically

       ;; Atomically try to acquire or enqueue
       ;; Uses *execution-context* from spin context - no captured runtime!
       (rtc/swap-state! [:semaphores sem-id]
         (fn [state]
           (let [permits (:permits state)]
             (if (pos? permits)
               ;; Permit available - decrement and mark as acquired
               (do
                 (reset! got-permit? true)
                 (update state :permits dec))
               ;; No permits - add to waiting queue
               (update state :waiting-queue
                       conj {:resolve resolve
                             :reject reject
                             :timestamp #?(:clj (System/currentTimeMillis)
                                           :cljs (.now js/Date))})))))

       ;; If we got the permit, resolve immediately
       (when @got-permit?
         (cont/resume resolve :acquired))

       spin/incomplete))))

(defn release
  "Release a permit, waking up the next waiter if any.

  If queue is empty: increments available permits (up to max)
  If queue has waiters: wakes up first waiter with permit

  Uses dynamically bound *execution-context* - works with forked runtimes.

  Example:
    (release sem)

  Throws if trying to release more permits than max (over-release)."
  [sem]
  (let [sem-id (.-id sem)]
    (loop []
      ;; Uses *execution-context* from call context - no captured runtime!
      (let [path [:semaphores sem-id]
            old-state (rtc/get-state path)
            queue (:waiting-queue old-state)
            permits (:permits old-state)
            max-permits (:max-permits old-state)]

        (cond
          ;; Queue not empty - wake up first waiter
          (seq queue)
          (let [waiter (peek queue)
                new-state (update old-state :waiting-queue pop)]
            (if (rtc/cas-state! path old-state new-state)
              (do
                ;; Successfully dequeued - schedule waiter to run on executor
                (rtp/schedule-spin-execution! rtc/*execution-context*
                                              #(cont/resume (:resolve waiter) :acquired))
                :released)
              ;; CAS failed - retry
              (recur)))

          ;; Queue empty - increment permits (up to max)
          (< permits max-permits)
          (let [new-state (update old-state :permits inc)]
            (if (rtc/cas-state! path old-state new-state)
              :released
              ;; CAS failed - retry
              (recur)))

          ;; Already at max permits - error
          :else
          (throw (ex-info "Semaphore over-released"
                          {:permits permits
                           :max-permits max-permits
                           :sem-id sem-id})))))))

(defn holding
  "Execute spin while holding a semaphore permit.

  Automatically releases the permit when the spin completes or fails.
  This is the recommended way to use semaphores (try-finally pattern).

  Returns a spin that:
  1. Acquires a permit (waits if necessary)
  2. Runs the provided spin
  3. Releases the permit (even if spin throws)

  Example:
    (sem/holding db-sem
      (spin/spin
        (await (expensive-database-query))))"
  [sem the-spin]
  (spin/make-spin
   (fn [resolve reject]
     ;; First acquire permit
     (let [acquire-spin (acquire sem)]
       (acquire-spin
        (fn [_acquired]
          ;; Got permit - run the spin with automatic release
          (the-spin
           (fn [result]
             (release sem)  ; Release on success
             (cont/resume resolve result))
           (fn [error]
             (release sem)  ; Release on error
             (cont/resume reject error))))
        reject))
     spin/incomplete)))
