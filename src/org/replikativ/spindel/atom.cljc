(ns org.replikativ.spindel.atom
  (:refer-clojure :exclude [atom])
  (:require [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.engine.cell-handles :as handles]
            [replikativ.logging :as log])
  #?(:clj (:import [java.lang.ref Reference])))

;; Fork-safe atoms that store state inside the runtime.
;; API is 100% compatible with clojure.core/atom for easy migration.
;; Key differences from clojure.core/atom:
;; - State lives in runtime at [:atoms atom-id]
;; - Supports runtime forking (state is copied with runtime)
;; - Auto-cleanup when GC'd (like Spin)
;; - Created within spin context (uses *execution-context*)

;; =============================================================================
;; Missing state: the bound world never had this atom
;; =============================================================================
;;
;; A wrapper resolves against the dynamically bound world. Missing reads use
;; missing-state-mode below; mutations reject absent cells and never recreate
;; them. A live shared host anchor prevents GC cleanup while any alias remains.

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
             (not (rtp/runtime-cell-present? (ec/current-execution-context) id)))
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

(defn- cell-op
  "Keep the wrapper's shared liveness anchor reachable through the operation."
  [ref id op f]
  (try
    (check-present! id op)
    (f (ec/current-execution-context))
    (finally
      #?(:clj (Reference/reachabilityFence ref) :cljs nil))))

(defn- read-cell [ref id op f]
  (try
    (let [ctx (ec/current-execution-context)]
      (if (rtp/runtime-cell-present? ctx id)
        (f ctx id)
        (check-present! id op)))
    (finally
      #?(:clj (Reference/reachabilityFence ref) :cljs nil))))

(defn- swap-and-notify! [ref id f args]
  (cell-op ref id :swap #(rtp/swap-runtime-cell! % ref id f args)))

#?(:clj
   (deftype RuntimeAtom [id anchor]
     clojure.lang.IDeref
     (deref [this] (read-cell this id :deref rtp/runtime-cell-value))

     clojure.lang.IMeta
     (meta [this] (read-cell this id :meta rtp/runtime-cell-meta))

     clojure.lang.IRef
     (setValidator [_this _vf]
       (throw (UnsupportedOperationException.
               "Validators not yet supported on runtime atoms")))
     (getValidator [_this] nil)
     (getWatches [this] (read-cell this id :watches rtp/runtime-cell-watches))
     (addWatch [this key f]
       (cell-op this id :add-watch #(rtp/add-runtime-cell-watch! % id key f))
       this)
     (removeWatch [this key]
       (cell-op this id :remove-watch #(rtp/remove-runtime-cell-watch! % id key))
       this)

     clojure.lang.IAtom
     (swap [this f] (swap-and-notify! this id f []))
     (swap [this f arg] (swap-and-notify! this id f [arg]))
     (swap [this f arg1 arg2] (swap-and-notify! this id f [arg1 arg2]))
     (swap [this f x y args] (swap-and-notify! this id f (concat [x y] args)))
     (reset [this newval] (swap-and-notify! this id (constantly newval) []))
     (compareAndSet [this oldval newval]
       (cell-op this id :compare-and-set
                #(rtp/cas-runtime-cell! % this id oldval newval)))))

#?(:cljs
   (deftype RuntimeAtom [id anchor]
     IDeref
     (-deref [this] (read-cell this id :deref rtp/runtime-cell-value))
     IMeta
     (-meta [this] (read-cell this id :meta rtp/runtime-cell-meta))
     IWatchable
     (-add-watch [this key f]
       (cell-op this id :add-watch #(rtp/add-runtime-cell-watch! % id key f))
       this)
     (-remove-watch [this key]
       (cell-op this id :remove-watch #(rtp/remove-runtime-cell-watch! % id key))
       this)
     IReset
     (-reset! [this newval] (swap-and-notify! this id (constantly newval) []))
     ISwap
     (-swap! [this f] (swap-and-notify! this id f []))
     (-swap! [this f a] (swap-and-notify! this id f [a]))
     (-swap! [this f a b] (swap-and-notify! this id f [a b]))
     (-swap! [this f a b xs] (swap-and-notify! this id f (concat [a b] xs)))))

(defn ->RuntimeAtom
  "Reconstruct a wrapper retaining the allocation's canonical liveness anchor."
  [id]
  (RuntimeAtom. id (handles/anchor id)))

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
  "Create a runtime atom in the dynamically bound runtime.

  Legacy contexts store value and metadata at [:atoms atom-id].
  Automatically cleaned up when GC'd.

  IMPORTANT: RuntimeAtom does NOT capture the runtime - it uses dynamic *execution-context* binding.
  This enables proper forking: atoms work with whatever runtime is bound at use-time.

  Options:
    :meta - Metadata map (stored in runtime for fork-safety)

  Example:
    (def cache (create-atom []))
    (swap! cache conj item)
    (deref cache)  ; => [item]"
  [initial-value & {:keys [meta]}]
  (let [{:keys [id anchor]} (rtp/allocate-runtime-cell!
                             (ec/current-execution-context) initial-value {:meta meta})]
    (RuntimeAtom. id anchor)))

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
      (deref cache))

  Options:
    :meta - Metadata map

  Example:
    (spin runtime
      (let [cache (atom [] :meta {:doc \"My cache\"})]
        (swap! cache conj 1)
        (deref cache)))  ; => [1]"
  [initial-value & {:keys [meta]}]
  (create-atom  initial-value :meta meta))
