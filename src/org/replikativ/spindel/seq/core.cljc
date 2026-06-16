(ns org.replikativ.spindel.seq.core
  "Core async sequence generation - gen-aseq macro and yield"
  (:refer-clojure :exclude [for await])
  (:require [is.simm.partial-cps.sequence :as pcps-seq :refer [PAsyncSeq]]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.effects.await :refer [await]]
            [is.simm.partial-cps.async :as async]
            #?(:clj [is.simm.partial-cps.ioc :as ioc])
            #?(:clj [org.replikativ.spindel.effects.yield :as yield-eff]))
  ;; Make macros available to CLJS via require-macros
  #?(:cljs (:require-macros [org.replikativ.spindel.seq.core :refer [gen-aseq for]]
                            [org.replikativ.spindel.spin.cps :refer [spin]]))
  #?(:clj (:require [org.replikativ.spindel.spin.cps :as spin-cps :refer [spin]])))

;; =============================================================================
;; Extend nil to PAsyncSeq (spin-based anext)
;; =============================================================================

(extend-type nil
  PAsyncSeq
  (anext [_]
    (spin-core/make-spin
     (fn [resolve _reject]
       (resolve nil)))))

;; =============================================================================
;; yield - Breakpoint for async sequence generation
;; =============================================================================

(defn yield
  "Suspend execution and emit a value in an async sequence.

   Must only be called inside a gen-aseq; outside, this throws.

   Example:
     (gen-aseq
       (yield 1)
       (yield 2)
       (yield 3))  ; Generates sequence [1 2 3]"
  [& _]
  (throw (ex-info "yield called outside of gen-aseq context (should be CPS-transformed)" {})))

;; =============================================================================
;; ASeqGenerator - Lazy async sequence generator using CPS yield
;; =============================================================================

(defn- execute-cps-with-yield-handler!
  "Execute cps-fn with *yield-handler* bound to the given handler.

  CRITICAL: In CLJS, we can't use `binding` because it restores the value
  in a finally block when the synchronous code returns. But CPS code may
  return ::incomplete (suspended) while continuations are still pending.
  Those continuations need the yield-handler to still be set!

  Solution: Manually set the var and DON'T restore it here. The value will
  be restored when anext completes (either via yield-handler or termination).
  This is safe because each anext creates a fresh yield-handler for that
  specific execution context."
  [cps-fn yield-handler resolve-fn reject-fn]
  #?(:cljs
     ;; CLJS: Set var value directly, don't restore on return
     ;; The yield-handler is specific to this execution context
     (do
       (set! ec/*yield-handler* yield-handler)
       (cps-fn resolve-fn reject-fn))
     :clj
     ;; CLJ: binding works correctly with thread-local semantics
     (binding [ec/*yield-handler* yield-handler]
       (cps-fn resolve-fn reject-fn))))

;; `sink-atom` holds the deferred for the *current* anext step. Each anext
;; resets it to a fresh single-shot deferred that BOTH the yield handler and
;; the terminal resolve/reject deliver to (tagged `[:yield …]` / `[:ok …]` /
;; `[:error …]`). The body runs until exactly one of those fires, so the
;; step-deferred is delivered exactly once, drains its `:pending`, and becomes
;; GC-eligible. This replaces the previous design — a single long-lived
;; `shared-term-deferred` raced against a fresh yield-deferred each step — which
;; stranded one never-removed `resolve` continuation on the shared deferred's
;; `:pending` per consumed element (the cancelled race loser), accumulating
;; unboundedly inside engine state for long/infinite generators. anext calls on
;; a generator are strictly sequential (each yields its continuation in
;; `rest-gen`), so a single current-step sink is sufficient.
(deftype ASeqGenerator [gen-id cps-fn sink-atom resolve-fn reject-fn]
  PAsyncSeq
  (anext [_]
    (spin
     (let [;; Fresh single-shot deferred for THIS anext call.
           step-deferred (sync/deferred)

            ;; Point the terminal resolve/reject (shared closures) at this
            ;; step's deferred before running the body.
           _ (reset! sink-atom step-deferred)

            ;; Yield handler delivers [:yield marker] to the same deferred.
           yield-handler (fn [marker _cont]
                           (step-deferred [:yield marker]))

            ;; Execute CPS with yield-handler bound
            ;; IMPORTANT: Use helper function to establish binding OUTSIDE CPS transformation
            ;; The binding form inside a spin macro body gets CPS-transformed, which breaks
            ;; the binding semantics in CLJS. By calling a helper function, the binding
            ;; happens in regular (non-CPS) code.
           _ (execute-cps-with-yield-handler! cps-fn yield-handler resolve-fn reject-fn)

            ;; Await the single per-step deferred (no race, nothing to leak).
           result (await step-deferred)]

        ;; Pattern match on result
       (cond
          ;; Yielded a value
         (and (vector? result) (= :yield (first result)))
         (let [[_ marker] result
               yield-value (:value marker)
               cont-r (:continuation-r marker)

                ;; wrapped-cps-fn is called by anext on the continuation
                ;; It needs to re-establish yield-handler for subsequent yields
                ;; Note: yield-handler will be set by the calling anext's binding block
               wrapped-cps-fn (fn [_r _e]
                                (binding [async/*in-trampoline* false]
                                   ;; Resume continuation - the yield-handler will
                                   ;; already be bound by the calling anext
                                  (let [result (spin-core/resume cont-r nil)]
                                    result)))

               rest-gen (ASeqGenerator.
                         (keyword (str (name gen-id) "-cont"))
                         wrapped-cps-fn
                         sink-atom
                         resolve-fn
                         reject-fn)]
           [yield-value rest-gen])

          ;; Body completed (sequence terminated)
         (and (vector? result) (= :ok (first result)))
         nil

          ;; Body raised
         (and (vector? result) (= :error (first result)))
         (throw (second result))

          ;; Unexpected
         :else
         (throw (ex-info "Unexpected gen-aseq step result" {:result result}))))))

  Object
  (toString [_this]
    (str "#<ASeqGenerator " gen-id ">")))

;; =============================================================================
;; Helper Functions
;; =============================================================================

(defn wrap-yield-continuation
  "Wrap CPS-transformed code to handle yield.

   The gen-aseq macro will CPS-transform the body, replacing:
     (yield x) → (make-yield-breakpoint x resume-fn)

   This ensures suspension points are respected."
  [cps-fn]
  cps-fn)

(defn make-gen-aseq
  "Create an ASeqGenerator from a CPS function.

   The CPS function receives (resolve-fn reject-fn) and should:
   - Call yield-handler for each yielded value (via *yield-handler*)
   - Call resolve-fn when complete
   - Call reject-fn on error

   The resolve/reject closures (shared across the whole generator chain, since
   the body's continuation captures them) deliver to whatever per-anext
   deferred is currently installed in `sink-atom`. anext resets `sink-atom`
   before running the body, so each step terminates into its own short-lived
   deferred — nothing accumulates across steps."
  [cps-fn gen-id]
  ;; Holds the current anext step's deferred; reset by ASeqGenerator.anext.
  ;; A plain atom (not a fork-safe runtime atom): it's transient per-step
  ;; coordination, deliberately kept OUT of engine state so it neither
  ;; accumulates nor gets copied on fork.
  (let [sink-atom (atom nil)

        ;; resolve-fn delivers [:ok result] to the current step's deferred.
        resolve-fn (fn [result]
                     (when-let [d @sink-atom]
                       (d [:ok result]))
                     result)

        ;; reject-fn delivers [:error err] to the current step's deferred.
        ;; Don't throw here - let anext re-throw after awaiting.
        reject-fn (fn [err]
                    (when-let [d @sink-atom]
                      (d [:error err]))
                    nil)]

    (ASeqGenerator. gen-id cps-fn sink-atom resolve-fn reject-fn)))

;; =============================================================================
;; gen-aseq Macro
;; =============================================================================

#?(:clj
   (defmacro gen-aseq
     "Generate a lazy async sequence using yield.

      Similar to lazy-seq, but for async values. Each yield suspends and emits
      a value. When the body completes, the sequence terminates.

      Cold semantics: Each anext creates a new execution context. Multiple
      consumers get independent lazy sequences.

      Example:
        (gen-aseq
          (yield 1)
          (yield 2)
          (yield 3))  ; Generates sequence [1 2 3]

        (gen-aseq
          (loop [n 0]
            (when (< n 5)
              (yield n)
              (recur (inc n)))))  ; Generates [0 1 2 3 4]

      Requires *execution-context* to be bound (automatically happens in spin context).

      Implementation: CPS-transforms the body, replacing yield with suspension
      points. Returns ASeqGenerator that executes until next yield."
     [& body]
     (let [ns-name (str *ns*)
           {:keys [line column]} (meta &form)
           col (or column 0)

           ;; Generate unique ID for this generator instance
           gen-id-expr `(keyword (str "gen-aseq-" ~ns-name "-" ~line "-" ~col "-" (random-uuid)))

           ;; Get current runtime (will be bound dynamically)
           runtime-expr `(ec/current-execution-context)

           ;; Build breakpoints: Start with all spin breakpoints (await, track, extensible effects)
           ;; then add yield breakpoint
           spin-breakpoints (spin-cps/build-breakpoints)

           ;; Create yield breakpoint
           yield-bp-vname (symbol (str "yield-bp__" (Math/abs (hash `yield))))
           _ (intern *ns* yield-bp-vname (yield-eff/make-yield-breakpoint))
           yield-bp-var (symbol (str *ns*) (name yield-bp-vname))

           ;; Merge spin breakpoints with yield breakpoint
           ;; Register both the original and re-exported symbol so yield works
           ;; whether required from seq.core or spindel.core
           breakpoints-map (assoc spin-breakpoints
                                  `org.replikativ.spindel.seq.core/yield yield-bp-var
                                  'org.replikativ.spindel.core/yield yield-bp-var)

           ;; CPS-transform the body using partial-cps machinery
           ;; ioc/invert handles macro expansion internally via expand-macro
           ;; Don't use macroexpand-all as it introduces CLJ-specific code for CLJS targets
           r (gensym "term-cont")
           e (gensym "err-cont")
           params {:r r :e e :env &env :breakpoints breakpoints-map}
           expanded (cons 'do body)
           ;; Use :js-globals to detect CLJS (same as ioc/invert does internally)
           is-cljs? (:js-globals &env)
           ;; Trampoline via partial-cps's runtime/thunk? + force-thunk — an
           ;; ns-qualified VAR reference resolves under any macro re-scoping.
           ;; Inlining `(instance? is.simm.partial_cps.runtime.Thunk x)` (a dotted
           ;; TYPE symbol) broke on cljs when re-scoped (e.g. by cljs.test/async);
           ;; partial-cps now provides the helpers centrally, so the old is-cljs?
           ;; thunk-type branch is gone.
           cps-fn-code `(fn [~r ~e]
                          (try
                            (if is.simm.partial-cps.async/*in-trampoline*
                              ~(ioc/invert params expanded)
                              (binding [is.simm.partial-cps.async/*in-trampoline* true]
                                (loop [result# ~(ioc/invert params expanded)]
                                  (if (is.simm.partial-cps.runtime/thunk? result#)
                                    (recur (is.simm.partial-cps.runtime/force-thunk result#))
                                    result#))))
                            (catch ~(if is-cljs? :default `Throwable) t# (~e t#))))]

       `(binding [ec/*execution-context* ~runtime-expr]
          (let [gen-id# ~gen-id-expr
                cps-fn# ~cps-fn-code]
            (make-gen-aseq cps-fn# gen-id#))))))

;; =============================================================================
;; for Macro - Async sequence comprehension with spindel context
;; =============================================================================

#?(:clj
   (defmacro for
     "Async sequence comprehension with spindel's breakpoints and execution context.

  Like clojure.core/for but for async sequences. Supports await, track, and other
  spindel effects in the body. Returns a lazy async sequence that can be consumed
  with anext.

  Automatically captures the current execution context so that spins created in
  the body have access to spindel's runtime.

  Example:
    (spin
      (let [aseq (for [x [1 2 3]
                       :when (odd? x)]
                   (await (async-double x)))]
        (loop [s aseq acc []]
          (if-let [[v rest-s] (await (anext s))]
            (recur rest-s (conj acc v))
            acc))))

  Supports all for modifiers: :let, :when, :while, and multiple bindings."
     [seq-exprs body-expr]
     `(pcps-seq/for-with
       {:breakpoints (spin-cps/build-breakpoints)
        :bindings [[ec/*execution-context* (ec/current-execution-context)]]}
       ~seq-exprs
       ~body-expr)))
