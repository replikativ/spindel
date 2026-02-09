(ns org.replikativ.spindel.sequence.core
  "Core async sequence generation - gen-aseq macro and yield"
  (:refer-clojure :exclude [for])
  (:require [is.simm.partial-cps.sequence :as pcps-seq :refer [PAsyncSeq]]
            [org.replikativ.spindel.runtime.core :as rtc]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.continuation :as cont]
            [org.replikativ.spindel.spin.sync :as sync]
            [org.replikativ.spindel.spin.combinators :refer [race]]
            [org.replikativ.spindel.effects.await :refer [await]]
            [is.simm.partial-cps.async :as async]
            #?(:clj [is.simm.partial-cps.ioc :as ioc])
            #?(:clj [org.replikativ.spindel.effects.yield :as yield-eff]))
  ;; Make macros available to CLJS via require-macros
  #?(:cljs (:require-macros [org.replikativ.spindel.sequence.core :refer [gen-aseq for]]
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
       (set! rtc/*yield-handler* yield-handler)
       (cps-fn resolve-fn reject-fn))
     :clj
     ;; CLJ: binding works correctly with thread-local semantics
     (binding [rtc/*yield-handler* yield-handler]
       (cps-fn resolve-fn reject-fn))))

(deftype ASeqGenerator [gen-id cps-fn shared-term-deferred resolve-fn reject-fn]
  PAsyncSeq
  (anext [_]
    (spin
      (let [;; Fresh yield deferred for THIS anext call
            yield-deferred (sync/deferred)

            ;; Yield handler delivers [:yield marker]
            yield-handler (fn [marker _cont]
                            (yield-deferred [:yield marker]))

            ;; Execute CPS with yield-handler bound
            ;; IMPORTANT: Use helper function to establish binding OUTSIDE CPS transformation
            ;; The binding form inside a spin macro body gets CPS-transformed, which breaks
            ;; the binding semantics in CLJS. By calling a helper function, the binding
            ;; happens in regular (non-CPS) code.
            _ (execute-cps-with-yield-handler! cps-fn yield-handler resolve-fn reject-fn)

            ;; Race: await whichever completes first
            result (await (race (spin (await yield-deferred))
                                (spin (await shared-term-deferred))))]

        ;; Pattern match on result
        (cond
          ;; Yield won
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
                                   (let [result (cont/resume cont-r nil)]
                                     result)))

                rest-gen (ASeqGenerator.
                          (keyword (str (name gen-id) "-cont"))
                          wrapped-cps-fn
                          shared-term-deferred
                          resolve-fn
                          reject-fn)]
            [yield-value rest-gen])

          ;; Termination won
          (and (vector? result) (= :ok (first result)))
          nil

          ;; Error won
          (and (vector? result) (= :error (first result)))
          (throw (second result))

          ;; Unexpected
          :else
          (throw (ex-info "Unexpected race result" {:result result}))))))

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

   Creates shared termination deferred and resolve/reject functions
   that are passed to all continuations."
  [cps-fn gen-id]
  ;; Shared termination deferred for entire sequence lifetime
  (let [shared-term-deferred (sync/deferred)

        ;; Shared resolve-fn delivers [:ok result] to termination deferred
        resolve-fn (fn [result]
                    (shared-term-deferred [:ok result])
                    result)

        ;; Shared reject-fn delivers [:error err] to termination deferred
        ;; Don't throw here - let the race/anext handle the error
        reject-fn (fn [err]
                   (shared-term-deferred [:error err])
                   nil)]

    (ASeqGenerator. gen-id cps-fn shared-term-deferred resolve-fn reject-fn)))

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
           runtime-expr `(rtc/current-execution-context)

           ;; Build breakpoints: Start with all spin breakpoints (await, track, extensible effects)
           ;; then add yield breakpoint
           spin-breakpoints (spin-cps/build-breakpoints)

           ;; Create yield breakpoint
           yield-bp-vname (symbol (str "yield-bp__" (Math/abs (hash `yield))))
           _ (intern *ns* yield-bp-vname (yield-eff/make-yield-breakpoint))
           yield-bp-var (symbol (str *ns*) (name yield-bp-vname))

           ;; Merge spin breakpoints with yield breakpoint
           breakpoints-map (assoc spin-breakpoints
                                  `org.replikativ.spindel.sequence.core/yield yield-bp-var)

           ;; CPS-transform the body using partial-cps machinery
           ;; ioc/invert handles macro expansion internally via expand-macro
           ;; Don't use macroexpand-all as it introduces CLJ-specific code for CLJS targets
           r (gensym "term-cont")
           e (gensym "err-cont")
           params {:r r :e e :env &env :breakpoints breakpoints-map}
           expanded (cons 'do body)
           ;; Use :js-globals to detect CLJS (same as ioc/invert does internally)
           is-cljs? (:js-globals &env)
           ;; Use fully qualified class name - CLJ needs Java package (underscores), CLJS uses var path
           thunk-type (if is-cljs? 'is.simm.partial-cps.runtime/Thunk 'is.simm.partial_cps.runtime.Thunk)
           cps-fn-code `(fn [~r ~e]
                          (try
                            (if is.simm.partial-cps.async/*in-trampoline*
                              ~(ioc/invert params expanded)
                              (binding [is.simm.partial-cps.async/*in-trampoline* true]
                                (loop [result# ~(ioc/invert params expanded)]
                                  (if (instance? ~thunk-type result#)
                                    (recur ((.-f result#)))
                                    result#))))
                            (catch ~(if is-cljs? :default `Throwable) t# (~e t#))))]

       `(binding [rtc/*execution-context* ~runtime-expr]
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
         :bindings [[rtc/*execution-context* (rtc/current-execution-context)]]}
        ~seq-exprs
        ~body-expr)))
