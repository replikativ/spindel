(ns org.replikativ.spindel.engine.bindings
  "Dynamic binding capture and restore across async boundaries.

  Captures thread-local bindings when continuations are created,
  stores them as pure data, and restores them when continuations resume.

  This enables transparent use of dynamic vars (binding) in async code
  without manual capture/restore.

  CLJS Implementation:
  --------------------
  In CLJS, we use a stack-based approach similar to JVM's push/popThreadBindings.
  Each var has a stack of binding frames. When we restore bindings, we push
  new frames onto each var's stack. When done, we pop them off.

  This handles nested async callbacks correctly - each callback gets its own
  frame on the stack, and frames are properly cleaned up in LIFO order.")

;; =============================================================================
;; Ephemeral Binding Keys
;; =============================================================================
;;
;; The ExecutionContext's :bindings map carries fork-scoped values that
;; propagate to child spins and continuations (see engine.context). Most
;; entries are persistent — set at context/fork creation, inherited across
;; every continuation resume.
;;
;; A few entries represent *per-render-pass* scope: values set by element
;; macros (e.g. :dom/parent-addr, :dom/current-slot) that should NOT survive
;; across a track continuation resume, because a track resume marks the start
;; of a new render pass where the surrounding scope re-establishes them.
;; They SHOULD survive await resumes, since those resume mid-body within
;; the same render pass.
;;
;; Libraries that introduce such keys register them here at ns load. The
;; engine consults the registry when resuming track continuations (see
;; engine.impl.simple/resume-single-observer!).

(defonce ^:private ephemeral-keys-atom (atom #{}))

(defn register-ephemeral-binding-key!
  "Register a key in the ExecutionContext's :bindings map as ephemeral.

  Ephemeral keys are cleared when a track continuation resumes (new render
  pass). Persistent keys survive all continuation resumes, as does every
  unregistered key."
  [k]
  (swap! ephemeral-keys-atom conj k)
  nil)

(defn ephemeral-binding-keys
  "Return the current set of registered ephemeral binding keys."
  []
  @ephemeral-keys-atom)

;; =============================================================================
;; CLJS Var Registry
;; =============================================================================

;; In CLJS, `resolve` doesn't work at runtime. Instead, we have runtime.core
;; register its vars here after it loads.

#?(:cljs
   (def registered-vars
     "Atom containing vars registered for capture/restore in CLJS."
     (atom [])))

#?(:cljs
   (defn register-var!
     "Register a dynamic var for capture/restore in CLJS.
     Called by runtime.core after its vars are defined."
     [v]
     (when v
       (swap! registered-vars conj v))))

(defn- get-vars-to-capture
  "Get the list of dynamic vars to capture.

  IMPORTANT: Only bind pure values or closures (immutable references).
  Do NOT bind atoms, refs, agents, or other mutable state outside the runtime!

  Closures are safe as long as they don't close over mutable state outside
  the runtime. The runtime state (*execution-context*) is the single source of truth.

  NOTE: *execution-context* is NOT captured - it's bound explicitly by event handlers when
  resuming continuations. Capturing it would create circular references
  (runtime → continuation → bindings → runtime) and cause StackOverflow."
  []
  #?(:clj
     ;; CLJ: Use resolve at runtime (works in CLJ)
     ;; NOTE: *execution-context* deliberately NOT included - bound by event handlers
     [(resolve 'org.replikativ.spindel.engine.core/*spin-id*)
      (resolve 'org.replikativ.spindel.engine.core/*worker-id*)
      (resolve 'org.replikativ.spindel.engine.core/*yield-handler*)]
     :cljs
     ;; CLJS: Use pre-registered vars
     @registered-vars))

;; =============================================================================
;; Platform-Specific Implementation
;; =============================================================================

#?(:clj
   (defn capture-bindings
     "Capture current values of registered dynamic vars.

     Returns a map of Var -> value for all currently bound vars.
     Unbound vars are omitted.

     Thread-safe, no side effects."
     []
     (into {}
           (keep (fn [^clojure.lang.Var v]
                   (when (.isBound v)
                     [v (.get v)]))
                 (get-vars-to-capture)))))

#?(:cljs
   (defn capture-bindings
     "Capture current values of registered dynamic vars.

     Returns a map of Var -> value for all currently bound vars.
     Unbound vars are omitted.

     In CLJS, dynamic vars have a .-val property that's a thunk.
     We capture the current value (deref the var) for later restoration."
     []
     (let [vars (get-vars-to-capture)]
       (into {}
             (keep (fn [v]
                     ;; v might be nil if registration failed
                     ;; Check if var exists and has a val thunk
                     (when (and v (.-val ^js v))
                       (try
                         [v @v]
                         (catch :default _
                           ;; If deref fails, skip this var
                           nil))))
                   vars)))))

#?(:clj
   (defn restore-bindings
     "Execute function f with restored dynamic bindings.

     bindings - Map of Var -> value (from capture-bindings)
     f - Zero-arg function to execute

     Returns the result of f.

     Thread-safe, properly cleans up bindings in finally block."
     [bindings f]
     (if (empty? bindings)
       (f)
       (do
         (clojure.lang.Var/pushThreadBindings bindings)
         (try
           (f)
           (finally
             (clojure.lang.Var/popThreadBindings)))))))

#?(:cljs
   (defn restore-bindings
     "Execute function f with restored dynamic bindings.

     bindings - Map of Var -> value (from capture-bindings)
     f - Zero-arg function to execute

     Returns the result of f.

     In CLJS, dynamic vars use .-val which is a thunk (nullary fn).
     We save the old thunk, replace with new thunk, execute, restore."
     [bindings f]
     (if (empty? bindings)
       (f)
       ;; Save current thunks (the .-val functions themselves).
       ;; ^js hint suppresses :infer-warning on the field access; CLJS
       ;; vars are JS objects with a mutable .-val property.
       (let [saved-thunks (into {}
                               (map (fn [[v _]]
                                      [v (.-val ^js v)])
                                    bindings))]
         ;; Set new thunks that return captured values
         (doseq [[v val] bindings]
           (set! (.-val ^js v) (fn [] val)))
         (try
           (f)
           (finally
             ;; Restore old thunks
             (doseq [[v old-thunk] saved-thunks]
               (set! (.-val ^js v) old-thunk))))))))
