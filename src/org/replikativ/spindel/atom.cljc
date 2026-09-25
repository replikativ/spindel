(ns org.replikativ.spindel.atom
  (:refer-clojure :exclude [atom])
  (:require [org.replikativ.spindel.engine.core :as ec]
            [replikativ.logging :as log]))

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
              (ec/swap-state! [:atoms]     (fn [atoms] (dissoc atoms atom-id)))
              (ec/swap-state! [:listeners] (fn [ls] (dissoc ls atom-id))))))))))

;; =============================================================================
;; Missing state: the bound world never had this atom
;; =============================================================================
;;
;; An atom's state lives in the context that created it and in that context's
;; forks (copy-on-write, reads fall through to the parent). Rebinding to any of
;; them is how forking works. Rebinding to a context OUTSIDE that lineage (a
;; sibling, or an ancestor of the creating context) finds no entry: a deref
;; answers nil, a swap starts an unrelated entry, a deferred delivery reaches
;; none of its readers, all silently. The entry cannot have been reaped under a
;; live caller (the Cleaner fires only once the RuntimeAtom is unreachable), so
;; a missing entry at access time always means the wrong world.

(defonce ^{:doc "What an access finds when the bound context has no state for
  the atom: :warn (log once per atom and context), :throw, or :ignore. Tests
  run with :throw."}
  missing-state-mode
  (clojure.core/atom #?(:clj (keyword (or (System/getProperty "spindel.missing-state") "warn"))
                        :cljs :warn)))

(defonce ^:private warned (clojure.core/atom #{}))

(defn check-present!
  "Signal (per `missing-state-mode`) an access to atom `id` in a context that
   has no state for it. `op` names the access. Returns nil."
  [id op]
  (when (and (not= :ignore @missing-state-mode)
             (nil? (ec/get-state [:atoms id])))
    (let [ctx (:fork-id (ec/current-execution-context))
          data {:atom id :op op :context ctx}]
      (if (= :throw @missing-state-mode)
        ;; Logged too: a caller that catches and drops the exception (a
        ;; worker, a future) must not turn the signal back into silence.
        (throw (do (log/error ::missing-state data)
                   (ex-info (str "Runtime atom " id " has no state in the bound context " ctx
                             " (" (name op) "): it belongs to another world")
                        (assoc data :type ::missing-state))))
        (when (and (< (count @warned) 10000)
                   (not (contains? @warned [id ctx])))
          (swap! warned conj [id ctx])
          (log/warn ::missing-state data)))))
  nil)

;; =============================================================================
;; Watch dispatch — swap-site firing (shared with SignalRef via ec/notify-listeners!)
;; =============================================================================

(defn- swap-and-notify!
  "Apply value-fn `f` to the atom's value at [:atoms id :value], then fire its
   listeners with the classic (key ref old new) arity. `old` is captured atomically
   INSIDE the swap; firing happens AFTER the swap returns (never inside it — a swap
   fn can be retried). Listeners live at the fork-local [:listeners id], so a fork
   swap fires the fork's listeners only. Returns the new value."
  [ref id f]
  (check-present! id :swap)
  (let [ov (volatile! nil)
        nv (ec/swap-state! [:atoms id :value]
                           (fn [old] (vreset! ov old) (f old)))]
    (ec/notify-listeners! ref id @ov nv)
    nv))

;; =============================================================================
;; RuntimeAtom - Atom that stores state in runtime
;; =============================================================================

#?(:clj
   (deftype RuntimeAtom [id]
     clojure.lang.IDeref
     (deref [_this]
       ;; Use dynamically bound *execution-context* - no captured runtime!
       (if-let [entry (ec/get-state [:atoms id])]
         (:value entry)
         (check-present! id :deref)))

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
       (ec/get-state [:listeners id]))
     (addWatch [this key f]
       (ec/swap-state! [:listeners id]
                       (fn [watchers] (assoc watchers key f)))
       this)
     (removeWatch [this key]
       (ec/swap-state! [:listeners id]
                       (fn [watchers] (dissoc watchers key)))
       this)

     clojure.lang.IAtom
     (swap [this f]
       (swap-and-notify! this id f))
     (swap [this f arg]
       (swap-and-notify! this id (fn [v] (f v arg))))
     (swap [this f arg1 arg2]
       (swap-and-notify! this id (fn [v] (f v arg1 arg2))))
     (swap [this f x y args]
       (swap-and-notify! this id (fn [v] (apply f v x y args))))

     (reset [this newval]
       (swap-and-notify! this id (constantly newval)))

     (compareAndSet [_this _oldval _newval]
       ;; CAS not supported for now (could add with custom logic if needed)
       (throw (UnsupportedOperationException.
               "compareAndSet not yet supported on runtime atoms")))))

#?(:cljs
   (deftype RuntimeAtom [id]
     IDeref
     (-deref [_this]
       ;; Use dynamically bound *execution-context* - no captured runtime!
       (if-let [entry (ec/get-state [:atoms id])]
         (:value entry)
         (check-present! id :deref)))

     IMeta
     (-meta [_this]
       (ec/get-state [:atoms id :meta]))

     IWatchable
     (-add-watch [this key f]
       (ec/swap-state! [:listeners id]
                       (fn [watchers] (assoc watchers key f)))
       this)
     (-remove-watch [this key]
       (ec/swap-state! [:listeners id]
                       (fn [watchers] (dissoc watchers key)))
       this)

     IReset
     (-reset! [this newval]
       (swap-and-notify! this id (constantly newval)))

     ISwap
     (-swap! [this f]
       (swap-and-notify! this id f))
     (-swap! [this f a]
       (swap-and-notify! this id (fn [v] (f v a))))
     (-swap! [this f a b]
       (swap-and-notify! this id (fn [v] (f v a b))))
     (-swap! [this f a b xs]
       (swap-and-notify! this id (fn [v] (apply f v a b xs))))))

(defn atom-id
  "The id under which runtime atom `a` keeps its state (`[:atoms id]`)."
  [a]
  #?(:clj (.-id ^RuntimeAtom a) :cljs (.-id ^js a)))

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

    ;; Initialize state in runtime (value + metadata, fork-safe). Watchers live
    ;; separately at the fork-local [:listeners atom-id] (added by add-watch).
    (binding [ec/*execution-context* runtime]
      (ec/swap-state! [:atoms atom-id]
                      (fn [_] {:value initial-value
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
                      ;; Remove from runtime when GC'd (value + any listeners)
                      (binding [ec/*execution-context* runtime]
                        (ec/swap-state! [:atoms]     (fn [atoms] (dissoc atoms atom-id)))
                        (ec/swap-state! [:listeners] (fn [ls] (dissoc ls atom-id)))))))
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
