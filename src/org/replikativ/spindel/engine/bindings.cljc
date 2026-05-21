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
;; Spin Scope Keys
;; =============================================================================
;;
;; The ExecutionContext's :bindings map carries fork-scoped values that
;; propagate to child spins and continuations (see engine.context). Most
;; entries are persistent — set at context/fork creation, inherited across
;; every continuation resume, never per-spin.
;;
;; A few entries instead represent a *spin's lexical scope*: values set by
;; an enclosing construct around the point a spin is created (e.g. element
;; macros set :dom/parent-addr / :dom/current-slot). Such a key must be
;; re-established whenever the spin's body runs — on EVERY body-entry path —
;; so the body addresses and behaves consistently no matter which engine
;; path resumed it. `make-spin` snapshots these keys at construction onto
;; the spin's node; the engine re-applies the snapshot on every body entry.
;;
;; Libraries that introduce such keys register them here at ns load. This
;; registry is the engine's only knowledge of them: the engine itself never
;; names a :dom/* (or any other domain) key — it just snapshots and restores
;; whatever was registered.

(defonce ^:private scope-keys-atom (atom #{}))

(defn register-spin-scope-key!
  "Register a key of the ExecutionContext's :bindings map as a *spin scope*
  key.

  Spin scope keys are snapshotted by `make-spin` at construction and
  re-established by the engine on every body-entry path (initial run,
  track resume, await resume). Unregistered keys are not snapshotted —
  persistent context bindings already flow through unchanged."
  [k]
  (swap! scope-keys-atom conj k)
  nil)

(defn spin-scope-keys
  "Return the current set of registered spin scope keys.

  Consumed by `make-spin` (spin/core.cljc) to decide which :bindings
  entries make up a spin's captured construction scope."
  []
  @scope-keys-atom)

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
      (resolve 'org.replikativ.spindel.engine.core/*yield-handler*)
      (resolve 'org.replikativ.spindel.engine.core/*external-await-cancel-token*)]
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
