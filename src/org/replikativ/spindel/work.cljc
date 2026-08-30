(ns org.replikativ.spindel.work
  "Structured admission of asynchronous work.

  An admission controller turns a stream of submitted values into owned child
  Spins.  The four strategies are the familiar higher-order FRP policies:

  * `:latest` supersedes the active value and starts its replacement only after
    the old child has quiesced;
  * `:serial` runs values in FIFO order;
  * `:busy` accepts a value only while idle;
  * `:parallel` runs at most `:concurrency` children at once.

  Admission and completion are events (`events`); the current active/queued
  projection is fork-local state (`snapshot`).  The controller owns every
  child it starts, so cancellation cannot orphan work."
  (:refer-clojure :exclude [await])
  (:require [is.simm.partial-cps.sequence :as aseq]
            [org.replikativ.spindel.atom :as ratom]
            [org.replikativ.spindel.effects.await :refer [await]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.executor :as executor]
            [org.replikativ.spindel.pubsub.buffer :as buffer]
            [org.replikativ.spindel.pubsub.mult :as mult]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.sync :as sync]
            #?(:clj [org.replikativ.spindel.spin.cps :as spin-cps :refer [spin]]))
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]]
                            [org.replikativ.spindel.work :refer [task]])))

#?(:clj
   (defmacro task
     "Create a reusable one-shot CPS task for a work-admission controller.

     Unlike `spin`, a task has no runtime identity. The accepting controller
     creates and exclusively owns a fresh resource Spin for each submission."
     [& body]
     (spin-cps/build-cps-fn body (spin-cps/build-breakpoints) &env)))

(defrecord WorkAdmission
           [strategy owner-context inbox event-stream event-bus event-anchor
            state handles runner done])

(def ^:private event-stream-closed ::event-stream-closed)

(deftype EventSource [mailbox]
  aseq/PAsyncSeq
  (anext [this]
    (spin
     (let [event (await mailbox)]
       (when-not (= event-stream-closed event)
         [event this])))))

(deftype Completion [owner-fork-id deferred]
  #?(:clj clojure.lang.IFn :cljs IFn)
  (#?(:clj invoke :cljs -invoke) [_ resolve reject]
    (if (= owner-fork-id (:fork-id (ec/current-execution-context)))
      (deferred resolve reject)
      (reject (ex-info "work completion awaited outside its owning execution context"
                       {:work/reason :foreign-context
                        :work/owner-fork-id owner-fork-id
                        :work/current-fork-id
                        (:fork-id (ec/current-execution-context))})))))

(defn- now []
  #?(:clj (java.util.Date.)
     :cljs (js/Date.)))

(defn- emit! [event-stream event]
  (event-stream (assoc event :work/at (now))))

(defn- public-state [state]
  (-> state
      (dissoc :active :queue :pending-latest :transition-token)
      (assoc :work/active (count (:active state))
             :work/queued (+ (count (:queue state))
                             (if (:pending-latest state) 1 0)))))

(defn- ensure-owner! [admission]
  ;; Continuation slices may restore a distinct ExecutionContext record for the
  ;; same branch. `:fork-id` is the stable branch identity; a real COW fork gets
  ;; a fresh one and is rejected.
  (when-not (= (:fork-id (:owner-context admission))
               (:fork-id (ec/current-execution-context)))
    (throw (ex-info "work controller used outside its owning execution context"
                    {:work/strategy (:strategy admission)
                     :work/reason :foreign-context})))
  admission)

(defn snapshot
  "Return the controller's current fork-local projection.

  The execution context containing the controller must be bound, just as for a
  Spindel atom or signal.  Live child handles are deliberately omitted."
  [admission]
  (ensure-owner! admission)
  (public-state @(:state admission)))

(defn events
  "Create an independent broadcast tap on the controller's event stream.

  This is a hot stream: a tap observes events emitted after it attaches. The
  optional buffer is a Spindel pub/sub buffer. The resource-safe default is a
  sliding 1024-event buffer; pass a fixed buffer when lossless backpressure is
  required, and detach abandoned taps with `untap-events!`."
  ([admission]
   (events admission (buffer/sliding-buffer 1024)))
  ([admission event-buffer]
   (ensure-owner! admission)
   (mult/tap (:event-bus admission) event-buffer)))

(defn completion
  "Return the awaitable completion handle for this controller.

  `close!` and `cancel!` request termination. Await this handle to join actual
  quiescence. It is not a Spin and carries no cancellation/ownership edge back
  to the controller; abandoning an awaiting Spin only abandons that waiter."
  [admission]
  (ensure-owner! admission)
  (->Completion (:fork-id (:owner-context admission)) (:done admission)))

(defn untap-events!
  "Detach an event tap previously returned by `events`."
  [admission event-tap]
  (ensure-owner! admission)
  (mult/untap (:event-bus admission) event-tap)
  nil)

(defn submit!
  "Submit a value and return its work id immediately.

  Returns the work id when the bounded ingress accepted the submission, or nil
  when the controller is closing/terminal or its ingress is full. Logical
  acceptance is asynchronous: consume `events` to observe
  `:work/accepted`, `:work/suppressed`, `:work/rejected`, or
  `:work/superseded`.  Supplying an id makes replay and external correlation
  deterministic."
  ([admission value]
   (submit! admission (random-uuid) value))
  ([admission id value]
   (ensure-owner! admission)
   (let [token (random-uuid)
         state-atom (:state admission)]
     (let [committed (swap! state-atom
                            (fn [state]
                              (if (and (:accepting? state)
                                       (< (:ingress state) (:ingress-capacity state)))
                                (-> state
                                    (assoc :transition-token token)
                                    (update :ingress inc))
                                state)))]
       (when (= token (:transition-token committed))
         (try
           (sync/post! (:inbox admission)
                       {:work/op :submit :work/id id :work/value value})
           id
           (catch #?(:clj Throwable :cljs :default) error
             (swap! state-atom update :ingress dec)
             (throw error))))))))

(defn close!
  "Stop accepting submissions and drain accepted work before closing."
  [admission]
  (ensure-owner! admission)
  (let [token (random-uuid)
        committed (swap! (:state admission)
                         (fn [state]
                           (if (:accepting? state)
                             (assoc state
                                    :transition-token token
                                    :accepting? false
                                    :close-requested? true)
                             state)))]
    (when (= token (:transition-token committed))
      (sync/post! (:inbox admission) {:work/op :close})))
  nil)

(defn cancel!
  "Cancel queued and active work, then stop the controller."
  [admission]
  (ensure-owner! admission)
  (let [token (random-uuid)
        committed (swap! (:state admission)
                         (fn [state]
                           (if (or (:terminal? state) (:cancel-requested? state))
                             state
                             (assoc state
                                    :transition-token token
                                    :accepting? false
                                    :cancel-requested? true))))]
    (when (= token (:transition-token committed))
      (sync/post! (:inbox admission) {:work/op :cancel})))
  nil)

(defn- child-spins [handles]
  (mapv :spin (vals @handles)))

(defn- set-ownership! [runner handles]
  (spin-core/set-owned-spins! (spin-core/spin-id runner)
                              (child-spins handles)))

(defn- queue-capacity? [state]
  (< (count (:queue state)) (:capacity state)))

(defn- rejected! [event-stream state job reason]
  (emit! event-stream {:work/event :work/rejected
                       :work/id (:work/id job)
                       :work/value (:work/value job)
                       :work/reason reason
                       :work/strategy (:strategy state)}))

(defn- accepted! [event-stream state job disposition]
  (emit! event-stream {:work/event :work/accepted
                       :work/id (:work/id job)
                       :work/value (:work/value job)
                       :work/disposition disposition
                       :work/strategy (:strategy state)}))

(defn- pending-id? [state id]
  (or (contains? (:active state) id)
      (= id (some-> state :pending-latest :work/id))
      (some #(= id (:work/id %)) (:queue state))))

(defn- claim-cancellation!
  "Linearize a controller cancellation request against child hand-back."
  [claim reason]
  (let [token (random-uuid)
        committed (swap! claim
                         (fn [status]
                           (if (= :running (:state status))
                             {:state :cancelling
                              :reason reason
                              :transition-token token}
                             status)))]
    (= token (:transition-token committed))))

(defn- hand-back!
  "Publish exactly one semantic outcome for a child callback.

  Spin completion and cancellation are not globally atomic. The controller's
  private claim is: whichever callback/cancellation reaches this boundary first
  determines the work outcome, without changing Spin's fork/runtime semantics."
  [state-atom inbox claim job op payload]
  (let [token (random-uuid)
        committed (swap! claim
                         (fn [status]
                           (case (:state status)
                             :running
                             {:state :handed-back
                              :transition-token token}

                             :cancelling
                             (assoc status
                                    :state :cancelled
                                    :transition-token token)

                             status)))]
    (when (and (= token (:transition-token committed))
               (not (:terminal? @state-atom)))
      (if (= :cancelled (:state committed))
        (inbox {:work/op :child-cancelled
                :work/id (:work/id job)
                :work/reason (:reason committed)})
        (inbox (merge {:work/op op :work/id (:work/id job)} payload))))))

(defn- start-child!
  [runner state-atom handles inbox event-stream work-fn job]
  (try
    (let [task-fn (work-fn (:work/value job))]
      (when-not (fn? task-fn)
        (throw (ex-info "work function must return a CPS task"
                        {:work/id (:work/id job)
                         :work/value (:work/value job)
                         :returned task-fn})))
      (let [child (spin-core/make-spin task-fn)
            entry (assoc job :started-at (now))
            claim (clojure.core/atom {:state :running})
            state (swap! state-atom assoc-in [:active (:work/id job)] entry)
            ctx (ec/current-execution-context)]
        (swap! handles assoc (:work/id job) {:spin child :claim claim})
        (set-ownership! runner handles)
        (emit! event-stream {:work/event :work/started
                             :work/id (:work/id job)
                             :work/value (:work/value job)
                             :work/strategy (:strategy state)})
        (executor/execute!
         (:executor ctx)
         (executor/alive-fn
          ctx
          (fn []
            (binding [ec/*execution-context* ctx]
              (child (fn [value]
                       (hand-back! state-atom inbox claim job
                                   :child-completed {:work/result value}))
                     (fn [error]
                       (hand-back! state-atom inbox claim job
                                   :child-failed {:work/error error})))))))
        state))
    (catch #?(:clj Throwable :cljs :default) error
      (swap! state-atom update :active dissoc (:work/id job))
      (swap! handles dissoc (:work/id job))
      (set-ownership! runner handles)
      (emit! event-stream {:work/event :work/failed
                           :work/id (:work/id job)
                           :work/value (:work/value job)
                           :work/error error
                           :work/phase :construction})
      @state-atom)))

(defn- start-capacity!
  [runner state-atom handles inbox event-stream work-fn]
  (loop [state @state-atom]
    (if (and (seq (:queue state))
             (< (count (:active state)) (:concurrency state)))
      (let [job (first (:queue state))]
        (swap! state-atom update :queue #(vec (rest %)))
        (start-child! runner state-atom handles inbox event-stream work-fn job)
        (recur @state-atom))
      state)))

(defn- finish-child!
  [runner state-atom handles inbox event-stream work-fn msg]
  (when-let [entry (get-in @state-atom [:active (:work/id msg)])]
    (let [superseded? (= :superseded (:cancel-reason entry))
          failed? (= :child-failed (:work/op msg))]
      (swap! state-atom update :active dissoc (:work/id msg))
      (swap! handles dissoc (:work/id msg))
      (set-ownership! runner handles)
      (emit! event-stream
             (cond
               (= :cancelled (:cancel-reason entry))
               {:work/event :work/cancelled
                :work/id (:work/id msg)
                :work/value (:work/value entry)
                :work/reason :controller-cancelled}

               superseded?
               {:work/event :work/superseded
                :work/id (:work/id msg)
                :work/value (:work/value entry)}

               failed?
               {:work/event :work/failed
                :work/id (:work/id msg)
                :work/value (:work/value entry)
                :work/error (:work/error msg)}

               :else
               {:work/event :work/completed
                :work/id (:work/id msg)
                :work/value (:work/value entry)
                :work/result (:work/result msg)}))
      (when (and (= :latest (:strategy @state-atom))
                 (empty? (:active @state-atom))
                 (:pending-latest @state-atom))
        (let [job (:pending-latest @state-atom)]
          (swap! state-atom assoc :pending-latest nil)
          (start-child! runner state-atom handles inbox event-stream work-fn job)))
      (when (#{:serial :parallel} (:strategy @state-atom))
        (start-capacity! runner state-atom handles inbox event-stream work-fn)))))

(defn- cancel-active!
  "Request cancellation for active children that have not handed back.

  The private claim serializes cancellation with callbacks. An already cached
  Spin is left to hand back its result; otherwise cancellation can win until
  the callback crosses the controller boundary."
  [state-atom handles reason]
  (doseq [[id {:keys [spin claim]}] @handles]
    (when (and (nil? (ec/spin-current-result (spin-core/spin-id spin)))
               (claim-cancellation! claim reason))
      ;; Record the reason before cancel-spin! invokes a parked reject callback.
      (swap! state-atom assoc-in [:active id :cancel-reason] reason)
      (spin-core/cancel-spin! spin))))

(defn- submit-latest-fixed!
  [runner state-atom handles inbox event-stream work-fn job]
  (let [state @state-atom]
    (if (empty? (:active state))
      (do (accepted! event-stream state job :started)
          (start-child! runner state-atom handles inbox event-stream work-fn job))
      (do
        (when-let [pending (:pending-latest state)]
          (emit! event-stream {:work/event :work/superseded
                               :work/id (:work/id pending)
                               :work/value (:work/value pending)
                               :work/reason :newer-submission}))
        (accepted! event-stream state job :pending-supersession)
        (swap! state-atom assoc :pending-latest job)
        (cancel-active! state-atom handles :superseded)))))

(defn- handle-submit!
  [runner state-atom handles inbox event-stream work-fn job]
  (let [state @state-atom]
    (cond
      (:cancelled? state)
      (emit! event-stream {:work/event :work/cancelled
                           :work/id (:work/id job)
                           :work/value (:work/value job)
                           :work/reason :controller-cancelled})

      (pending-id? state (:work/id job))
      (rejected! event-stream state job :duplicate-id)

      :else
      (case (:strategy state)
        :latest
        (submit-latest-fixed! runner state-atom handles inbox event-stream work-fn job)

        :busy
        (if (empty? (:active state))
          (do (accepted! event-stream state job :started)
              (start-child! runner state-atom handles inbox event-stream work-fn job))
          (emit! event-stream {:work/event :work/suppressed
                               :work/id (:work/id job)
                               :work/value (:work/value job)
                               :work/reason :busy}))

        :serial
        (if (and (< (count (:active state)) (:concurrency state))
                 (empty? (:queue state)))
          (do (accepted! event-stream state job :started)
              (start-child! runner state-atom handles inbox event-stream work-fn job))
          (if (queue-capacity? state)
            (do (accepted! event-stream state job :queued)
                (swap! state-atom update :queue conj job))
            (rejected! event-stream state job :capacity)))

        :parallel
        (if (and (< (count (:active state)) (:concurrency state))
                 (empty? (:queue state)))
          (do (accepted! event-stream state job :started)
              (start-child! runner state-atom handles inbox event-stream work-fn job))
          (if (queue-capacity? state)
            (do (accepted! event-stream state job :queued)
                (swap! state-atom update :queue conj job))
            (rejected! event-stream state job :capacity)))))))

(defn- drain-complete? [state]
  (and (or (and (:close-requested? state)
                (not (:cancel-requested? state)))
           (and (:cancel-requested? state)
                (:cancel-command-seen? state)))
       (zero? (:ingress state))
       (empty? (:active state))
       (empty? (:queue state))
       (nil? (:pending-latest state))))

(defn- cancel-pending! [event-stream state]
  (doseq [job (cond-> (:queue state)
                (:pending-latest state) (conj (:pending-latest state)))]
    (emit! event-stream {:work/event :work/cancelled
                         :work/id (:work/id job)
                         :work/value (:work/value job)
                         :work/reason :controller-cancelled})))

(defn- abort-controller!
  "Terminalize a controller whose lifetime Spin was cancelled externally."
  [runner state-atom handles event-stream]
  (when-not (:terminal? @state-atom)
    (let [state @state-atom
          live @handles]
      (cancel-pending! event-stream state)
      ;; Claim terminal state before cancelling children so their callbacks do
      ;; not enqueue hand-back messages to a runner that is unwinding.
      (swap! state-atom assoc
             :accepting? false
             :cancel-requested? true
             :cancel-command-seen? true
             :cancelled? true
             :terminal? true
             :ingress 0
             :queue []
             :pending-latest nil
             :active {})
      (doseq [[id entry] (:active state)]
        (let [{:keys [spin claim]} (get live id)
              cached (when spin
                       (ec/spin-current-result (spin-core/spin-id spin)))
              cancel-reason (:cancel-reason entry)]
          (if (#{:cancelled :superseded} cancel-reason)
            (do
              (emit! event-stream
                     {:work/event (if (= :superseded cancel-reason)
                                    :work/superseded
                                    :work/cancelled)
                      :work/id id
                      :work/value (:work/value entry)
                      :work/reason (if (= :superseded cancel-reason)
                                     :newer-submission
                                     :owner-cancelled)})
              (when (and spin claim
                         (claim-cancellation! claim cancel-reason))
                (spin-core/cancel-spin! spin)))
            (if cached
              (emit! event-stream
                     (if (= :ok (:variant cached))
                       {:work/event :work/completed
                        :work/id id
                        :work/value (:work/value entry)
                        :work/result (:payload cached)}
                       {:work/event :work/failed
                        :work/id id
                        :work/value (:work/value entry)
                        :work/error (:payload cached)}))
              (do
                (emit! event-stream {:work/event :work/cancelled
                                     :work/id id
                                     :work/value (:work/value entry)
                                     :work/reason :owner-cancelled})
                (when (and spin claim
                           (claim-cancellation! claim :cancelled))
                  (spin-core/cancel-spin! spin)))))))
      (reset! handles {})
      (set-ownership! runner handles)
      (emit! event-stream {:work/event :work/controller-cancelled
                           :work/strategy (:strategy state)})
      (event-stream event-stream-closed))))

(defn work-admission
  "Create and start a structured work-admission controller.

  `work-fn` receives each accepted value and must return a one-shot CPS task,
  normally built with `task`. The controller creates and exclusively owns a
  fresh resource Spin for every accepted execution. Task functions themselves
  may safely be reused. Options:

  * `:strategy` — one of `:latest`, `:serial`, `:busy`, `:parallel`;
  * `:concurrency` — active child limit (`:parallel` only; default 4);
  * `:capacity` — maximum accepted waiting values (default 1024);
  * `:ingress-capacity` — maximum submissions awaiting dispatch (default 1024).

  Creation requires a bound execution context. The controller is live and
  process-local. Its projection lives in Spindel runtime state, but forking a
  context does not duplicate in-flight external execution; construct a new
  controller inside an independently executing branch."
  ([work-fn]
   (work-admission {} work-fn))
  ([{:keys [strategy concurrency capacity ingress-capacity]
     :or {strategy :serial concurrency 4 capacity 1024 ingress-capacity 1024}}
    work-fn]
   (when-not (#{:latest :serial :busy :parallel} strategy)
     (throw (ex-info "unknown work admission strategy" {:strategy strategy})))
   (when-not (and (integer? concurrency) (pos? concurrency))
     (throw (ex-info "concurrency must be a positive integer"
                     {:concurrency concurrency})))
   (when-not (and (integer? capacity) (not (neg? capacity)))
     (throw (ex-info "capacity must be a non-negative integer"
                     {:capacity capacity})))
   (when-not (and (integer? ingress-capacity) (pos? ingress-capacity))
     (throw (ex-info "ingress-capacity must be a positive integer"
                     {:ingress-capacity ingress-capacity})))
   (let [owner-context (ec/current-execution-context)
         effective-concurrency (if (= strategy :parallel) concurrency 1)
         inbox (sync/mailbox)
         event-stream (sync/mailbox)
         event-bus (mult/mult (EventSource. event-stream))
         ;; Start the hot pump immediately. This private sliding tap bounds the
         ;; no-observer case without retaining an unbounded replay history.
         event-anchor (mult/tap event-bus (buffer/sliding-buffer 1))
         handles (clojure.core/atom {})
         state (ratom/atom {:strategy strategy
                            :concurrency effective-concurrency
                            :capacity capacity
                            :ingress-capacity ingress-capacity
                            :ingress 0
                            :accepting? true
                            :close-requested? false
                            :cancel-requested? false
                            :cancel-command-seen? false
                            :terminal? false
                            :cancelled? false
                            :active {}
                            :queue []
                            :pending-latest nil})
         runner-ref (clojure.core/atom nil)
         done (sync/deferred)
         runner (spin
                 (try
                   (loop []
                     (let [msg (await inbox)]
                       (case (:work/op msg)
                         :submit
                         (do (swap! state update :ingress dec)
                             (handle-submit! @runner-ref state handles inbox event-stream work-fn msg))

                         :child-completed
                         (finish-child! @runner-ref state handles inbox event-stream work-fn msg)

                         :child-failed
                         (finish-child! @runner-ref state handles inbox event-stream work-fn msg)

                         :child-cancelled
                         (finish-child! @runner-ref state handles inbox event-stream work-fn msg)

                         :close
                         nil

                         :cancel
                         (do
                           (cancel-pending! event-stream @state)
                           (swap! state
                                  (fn [s]
                                    (-> s
                                        (assoc :cancelled? true
                                               :cancel-command-seen? true
                                               :queue []
                                               :pending-latest nil))))
                           (cancel-active! state handles :cancelled))

                         nil)
                       (if (drain-complete? @state)
                         (do (swap! state assoc :terminal? true)
                             (emit! event-stream
                                    {:work/event (if (:cancel-requested? @state)
                                                   :work/controller-cancelled
                                                   :work/controller-closed)
                                     :work/strategy strategy})
                             (event-stream event-stream-closed)
                             (let [result (public-state @state)]
                               (done result)
                               result))
                         (recur))))
                   (finally
                     (abort-controller! @runner-ref state handles event-stream)
                     (done (public-state @state)))))
         admission (->WorkAdmission strategy owner-context inbox event-stream
                                    event-bus event-anchor state handles runner
                                    done)]
     (reset! runner-ref runner)
     (sync/spawn! runner)
     admission)))

(defn latest
  "Create `:latest` admission: supersede active work before replacement."
  ([work-fn] (latest {} work-fn))
  ([opts work-fn]
   (work-admission (assoc opts :strategy :latest) work-fn)))

(defn serial
  "Create FIFO `:serial` admission."
  ([work-fn] (serial {} work-fn))
  ([opts work-fn]
   (work-admission (assoc opts :strategy :serial) work-fn)))

(defn busy
  "Create `:busy` admission, suppressing submissions while work is active."
  ([work-fn] (busy {} work-fn))
  ([opts work-fn]
   (work-admission (assoc opts :strategy :busy) work-fn)))

(defn parallel
  "Create bounded `:parallel` admission."
  ([work-fn] (parallel {} work-fn))
  ([opts work-fn]
   (work-admission (assoc opts :strategy :parallel) work-fn)))
