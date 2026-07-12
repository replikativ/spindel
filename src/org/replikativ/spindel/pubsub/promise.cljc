(ns ^:no-doc org.replikativ.spindel.pubsub.promise
  "Internal single-delivery promise used by the pubsub coordination
  layers (mult / pub / partitioned) for their item-available /
  space-available signalling.

  Replaces the three private `make-promise` copies that previously
  lived in mult.cljc, pub.cljc and partitioned.cljc — each of which ran
  its watchers INLINE ON THE DELIVERER'S STACK. That was the last place
  engine continuations executed on arbitrary foreign threads
  (`untap!` / `close-tap!` / `publish!` are called from user threads),
  and only mult's copy had the PR #28 per-watcher fault isolation.

  Resume-as-event (#27 Phase B): `deliver!` now hands each watcher to
  the drain of the CONTEXT THE WATCHER WAS REGISTERED UNDER as a
  `:cont-resume` event. That gives every watcher:
  - execution on engine-owned threads with the right
    `*execution-context*` / `*in-trampoline*` bound by the handler
    (deleting the cross-ctx rebinding wrapper each copy carried);
  - the drain's uniform cancellation re-check (`spin-is-cancelled?` on
    the registering spin) and failure route (fault report + owning-spin
    rejection) — structural isolation instead of a local try/catch.

  Enqueueing on the WATCHER's ctx (not the deliverer's) preserves the
  fork semantics the old wrapper existed for: a fork-ctx pump delivering
  to awaiters registered on the parent ctx completes them against their
  own ctx (see pubsub/fork_ctx_reentrancy_test.cljc).

  A watcher registered with NO reachable context (a raw `:await-spin`
  invocation outside the engine — tests, embedder glue) degenerates to
  a guarded inline invoke: fault-reported, never silently swallowed,
  never propagated to the deliverer.

  The promise itself is a plain JVM/JS atom, NOT ctx-backed state:
  per-item promises are created on the pump hot path (one per item per
  tap), and ctx-backed atoms would grow context state without bound and
  tax every fork copy."
  (:require [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.fault :as fault]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.spin.core :as spin-core]
            [is.simm.partial-cps.async :as pcps-async]))

(defn- deliver-to-watcher!
  "Route one watcher's resume: through the watcher's own ctx drain as a
  `:cont-resume` event when a ctx was captured at registration, else a
  guarded inline invoke on the deliverer's stack (degenerate path)."
  [{:keys [ctx spin-id resolve]} value]
  (if ctx
    (rtp/enqueue! ctx {:type :cont-resume
                       :site :promise
                       :spin-id spin-id
                       :resolve resolve
                       :value value})
    (try
      (pcps-async/invoke-continuation resolve value)
      (catch #?(:clj Throwable :cljs :default) e
        #?(:clj (when (instance? InterruptedException e)
                  (.interrupt (Thread/currentThread))))
        (fault/report-fault! ::fault/continuation-fault
                             {:site :promise :spin-id spin-id :error e})))))

(defn make-promise
  "Create a single-delivery promise: delivered once, readable many
  times. Returns `{:state atom, :deliver! (fn [value]), :await-spin
  (fn [] spin)}` — the exact contract of the three former private
  copies. Uses compare-and-set! so no side effects run inside a
  retry-able swap fn."
  []
  (let [state (atom {:delivered? false :value nil :watchers []})]
    {:state state
     :deliver!
     (fn [value]
       (loop []
         (let [s @state]
           (if (:delivered? s)
             value ;; Already delivered - no-op
             (if (compare-and-set! state s {:delivered? true :value value :watchers []})
               ;; CAS succeeded — watchers were removed atomically with
               ;; the delivery (one-shot by construction), so each may be
               ;; handed to the drain as its own :cont-resume event.
               (do (doseq [w (:watchers s)]
                     (deliver-to-watcher! w value))
                   value)
               ;; CAS failed (concurrent modification) - retry
               (recur))))))
     :await-spin
     (fn []
       (spin-core/make-spin
        (fn [resolve _reject]
          ;; Capture the registering spin's identity NOW — the handler
          ;; re-checks cancellation against it at delivery time, and the
          ;; ctx is where the resume event must be enqueued.
          (let [ctx (try (ec/current-execution-context)
                         (catch #?(:clj Throwable :cljs :default) _ nil))
                watcher {:ctx ctx
                         :spin-id ec/*spin-id*
                         :resolve resolve}]
            (loop []
              (let [s @state]
                (if (:delivered? s)
                  ;; Fast path: already delivered — same-spin inline
                  ;; resume on the awaiting body's own stack (the spin is
                  ;; the subject of the currently executing work; its
                  ;; failure route is armed by its own CPS wrapping).
                  (resolve (:value s))
                  ;; Try to add watcher via CAS
                  (when-not (compare-and-set! state s (update s :watchers conj watcher))
                    ;; CAS failed - retry (re-checks delivered? next round)
                    (recur))))))
          spin-core/incomplete)))}))

(defn deliver-promise! [p value]
  ((:deliver! p) value))

(defn promise-spin [p]
  ((:await-spin p)))
