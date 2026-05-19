(ns org.replikativ.spindel.atom
  (:refer-clojure :exclude [atom])
  (:require [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.state-backend :as backend]))

;; Fork-safe atoms that store state inside the runtime.
;; API is 100% compatible with clojure.core/atom for easy migration.
;; Key differences from clojure.core/atom:
;; - State lives in runtime at [:atoms atom-id]
;; - Supports runtime forking (state is copied with runtime)
;; - Auto-cleanup when GC'd (like Spin)
;; - Created within spin context (uses *execution-context*)

#?(:clj
   (def ^:private atom-cleaner
     "Global cleaner for automatic atom cleanup when GC'd.
     Uses Java 9+ Cleaner API."
     (delay (java.lang.ref.Cleaner/create))))

#?(:cljs
   (def ^:private atom-finalization-registry
     "Global FinalizationRegistry for automatic atom cleanup when GC'd.
     Available in modern browsers and Node 14.6+. Held value is the
     {:atom-id :runtime} pair so the cleanup callback can dissoc the
     entry from the originating runtime's :atoms map."
     (when (exists? js/FinalizationRegistry)
       (js/FinalizationRegistry.
        (fn [held-value]
          (let [{:keys [atom-id runtime]} held-value]
            (binding [ec/*execution-context* runtime]
              (ec/swap-state! [:atoms]
                              (fn [atoms] (dissoc atoms atom-id))))))))))

;; =============================================================================
;; Rebuilt file to resolve prior parse NPE.
;; Global Watcher - Dispatches to Individual Atom Watchers
;; =============================================================================

(defn- install-atom-watcher!
  "Install global watcher on runtime state backend to dispatch to individual atom watchers.

  When any atom value changes, this watcher calls that atom's registered watchers.
  Installed once per backend, called automatically on first create-atom.

  Delegates to PStateBackend protocol for proper backend abstraction.
  Note: add-watch is idempotent with the same key, so calling multiple times is safe."
  [rt]
  ;; Delegate to backend protocol - works with all backend types
  (backend/install-atom-watcher! (:backend rt)))

;; =============================================================================
;; RuntimeAtom - Atom that stores state in runtime
;; =============================================================================

#?(:clj
   (deftype RuntimeAtom [id]
     clojure.lang.IDeref
     (deref [_this]
       ;; Use dynamically bound *execution-context* - no captured runtime!
       (ec/get-state [:atoms id :value]))

     clojure.lang.IMeta
     (meta [_this]
       (ec/get-state [:atoms id :meta]))

     clojure.lang.IRef
     (setValidator [_this _vf]
       ;; Validators not supported for now (could add later if needed)
       (throw (UnsupportedOperationException.
               "Validators not yet supported on runtime atoms")))
     (getValidator [_this] nil)
     (getWatches [_this]
       (ec/get-state [:atoms id :watchers]))
     (addWatch [this key f]
       (ec/swap-state! [:atoms id :watchers]
                       (fn [watchers] (assoc watchers key f)))
       this)
     (removeWatch [this key]
       (ec/swap-state! [:atoms id :watchers]
                       (fn [watchers] (dissoc watchers key)))
       this)

     clojure.lang.IAtom
     (swap [_this f]
       (ec/swap-state! [:atoms id :value] f))
     (swap [_this f arg]
       (ec/swap-state! [:atoms id :value]
                       (fn [v] (f v arg))))
     (swap [_this f arg1 arg2]
       (ec/swap-state! [:atoms id :value]
                       (fn [v] (f v arg1 arg2))))
     (swap [_this f x y args]
       (ec/swap-state! [:atoms id :value]
                       (fn [v] (apply f v x y args))))

     (reset [_this newval]
       (ec/swap-state! [:atoms id :value] (constantly newval)))

     (compareAndSet [_this _oldval _newval]
       ;; CAS not supported for now (could add with custom logic if needed)
       (throw (UnsupportedOperationException.
               "compareAndSet not yet supported on runtime atoms")))))

#?(:cljs
   (deftype RuntimeAtom [id]
     IDeref
     (-deref [_this]
       ;; Use dynamically bound *execution-context* - no captured runtime!
       (ec/get-state [:atoms id :value]))

     IMeta
     (-meta [_this]
       (ec/get-state [:atoms id :meta]))

     IWatchable
     (-add-watch [this key f]
       (ec/swap-state! [:atoms id :watchers]
                       (fn [watchers] (assoc watchers key f)))
       this)
     (-remove-watch [this key]
       (ec/swap-state! [:atoms id :watchers]
                       (fn [watchers] (dissoc watchers key)))
       this)

     IReset
     (-reset! [_this newval]
       (ec/swap-state! [:atoms id :value] (constantly newval)))

     ISwap
     (-swap! [_this f]
       (ec/swap-state! [:atoms id :value] f))
     (-swap! [_this f a]
       (ec/swap-state! [:atoms id :value]
                       (fn [v] (f v a))))
     (-swap! [_this f a b]
       (ec/swap-state! [:atoms id :value]
                       (fn [v] (f v a b))))
     (-swap! [_this f a b xs]
       (ec/swap-state! [:atoms id :value]
                       (fn [v] (apply f v a b xs))))))

;; =============================================================================
;; Public API
;; =============================================================================

;; ----------------------------------------------------------------------------
;; Creation
;; ----------------------------------------------------------------------------

(defn create-atom
  "Create a runtime atom with initial value and explicit runtime.

  State is stored in runtime at [:atoms atom-id {:value v :watchers {} :meta m}].
  Automatically cleaned up when GC'd.

  IMPORTANT: RuntimeAtom does NOT capture the runtime - it uses dynamic *execution-context* binding.
  This enables proper forking: atoms work with whatever runtime is bound at use-time.

  Options:
    :meta - Metadata map (stored in runtime for fork-safety)

  Example:
    (def cache (create-atom runtime []))
    (swap! cache conj item)
    @cache  ; => [item]"
  [initial-value & {:keys [meta]}]
  (let [runtime (ec/current-execution-context)
        atom-id (keyword (gensym "atom-"))
        runtime-atom-obj (->RuntimeAtom atom-id)]  ; No runtime captured!

    ;; Install global watcher if needed (auto-install on first use)
    (install-atom-watcher! runtime)

    ;; Initialize state in runtime (value, watchers, and metadata all fork-safe)
    (binding [ec/*execution-context* runtime]
      (ec/swap-state! [:atoms atom-id]
                      (fn [_] {:value initial-value
                               :watchers {}
                               :meta meta})))

    ;; Register for GC cleanup (remove from runtime when atom is GC'd)
    ;; NOTE: The cleanup function DOES capture runtime - this is intentional!
    ;; We want to clean up from the ORIGINAL runtime that created the atom.
    ;; When you fork a runtime, you get a new copy of the :atoms map, so
    ;; the atom-id exists in both runtimes independently.
    #?(:clj
       (.register @atom-cleaner
                  runtime-atom-obj
                  (reify Runnable
                    (run [_]
                      ;; Remove from runtime when GC'd
                      (binding [ec/*execution-context* runtime]
                        (ec/swap-state! [:atoms]
                                        (fn [atoms] (dissoc atoms atom-id)))))))
       :cljs
       ;; Register with FinalizationRegistry when available so the
       ;; runtime's :atoms entry is reclaimed once nothing references the
       ;; RuntimeAtom anymore. On runtimes without FinalizationRegistry
       ;; (older browsers) this is a no-op and the entry persists for the
       ;; lifetime of the context.
       (when atom-finalization-registry
         (.register atom-finalization-registry
                    runtime-atom-obj
                    {:atom-id atom-id :runtime runtime})))

    runtime-atom-obj))

;; ----------------------------------------------------------------------------
;; Dynamic API (preferred inside spins)
;; ----------------------------------------------------------------------------

(defn atom
  "Create a runtime atom using dynamically bound *execution-context*.

  API is 100% compatible with clojure.core/atom.
  Must be called within a spin context (where *execution-context* is bound).

  Usage:
    (let [cache (atom [])]
      (swap! cache conj item)
      @cache)

  Options:
    :meta - Metadata map

  Example:
    (spin runtime
      (let [cache (atom [] :meta {:doc \"My cache\"})]
        (swap! cache conj 1)
        @cache))  ; => [1]"
  [initial-value & {:keys [meta]}]
  (create-atom  initial-value :meta meta))
