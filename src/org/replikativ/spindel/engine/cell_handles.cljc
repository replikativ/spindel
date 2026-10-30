(ns org.replikativ.spindel.engine.cell-handles
  "Host liveness for managed cells, independent of any runtime world.

  Every wrapper for a cell retains the same opaque anchor. The registry and
  host finalizer retain neither that anchor nor the stable cleanup target."
  (:require [replikativ.logging :as log])
  #?(:clj (:import [java.lang.ref Cleaner WeakReference])))

(defonce ^:private registrations (atom {}))
#?(:clj (defonce ^:private registry-lock (Object.)))

(defn- weak-reference [value]
  #?(:clj (WeakReference. value)
     :cljs (js/WeakRef. value)))

(defn- weak-value [reference]
  #?(:clj (.get ^WeakReference reference)
     :cljs (.deref reference)))

(defn- claim-entry
  "Remove only the registration belonging to this finalizer. Pure so stale
  finalizer claims can be checked without collecting or invalidating aliases."
  [entries id token]
  (if (identical? token (:token (get entries id)))
    (dissoc entries id)
    entries))

(defn- claim! [id token]
  (let [claim (fn []
                (let [entries @registrations
                      entry (get entries id)]
                  (when (and entry (identical? token (:token entry)))
                    (reset! registrations (claim-entry entries id token))
                    entry)))]
    #?(:clj (locking registry-lock (claim))
       :cljs (claim))))

(defn- reap! [id token]
  ;; Claim before dispatch: a failed callback must not retain a registration,
  ;; and a repeated/stale notification must never dispatch a second cleanup.
  (when-let [entry (claim! id token)]
    (when-let [target (weak-value (:target entry))]
      (try
        ((:reap-fn entry) target id)
        (catch #?(:clj Throwable :cljs :default) error
          ;; Cleaner suppresses uncaught failures; explicitly report them.
          (log/error :engine/cell-handle-reap-failed {:id id :error error}))))))

#?(:clj
   (defonce ^:private cleaner (Cleaner/create))
   :cljs
   (defonce ^:private finalizer
     (js/FinalizationRegistry.
      (fn [registration]
        (reap! (:id registration) (:token registration))))))

(defn allocate!
  "Register a globally fresh allocation id and return its strong anchor receipt.

  The caller must transfer this receipt directly into the first wrapper; every
  later wrapper must retain (anchor id). IDs must never be reused, including
  after cleanup. Duplicate registered IDs throw.

  stable-target is held weakly, even while wrappers remain alive. reap-fn is a
  global dispatcher accepting [stable-target id]; it MUST NOT capture a target,
  world, backend, or anchor. Once the last anchor reference dies, cleanup runs
  at most once, and only if the target still exists. Callback failures are
  logged after removing the registration; cleanup is not retried."
  [id stable-target reap-fn]
  (let [allocate (fn []
                   (when (contains? @registrations id)
                     (throw (ex-info "Cell handle allocation already registered"
                                     {:type ::duplicate-allocation :id id})))
                   (let [receipt #?(:clj (Object.) :cljs (js-obj))
                         token #?(:clj (Object.) :cljs (js-obj))
                         entry {:anchor (weak-reference receipt)
                                :target (weak-reference stable-target)
                                :token token
                                :reap-fn reap-fn}]
                     (swap! registrations assoc id entry)
                     #?(:clj (.register ^Cleaner cleaner receipt
                                        (reify Runnable
                                          (run [_] (reap! id token))))
                        :cljs (.register finalizer receipt {:id id :token token}))
                     receipt))]
    #?(:clj (locking registry-lock (allocate))
       :cljs (allocate))))

(defn anchor
  "Return the existing strong anchor for id, or throw ::released.

  This is a lookup, never an allocation: an absent or cleared weak anchor
  cannot be resurrected. Keep the returned value in every reconstructed
  wrapper, including wrappers that have never been dereferenced."
  [id]
  (let [lookup (fn []
                 (or (some-> (get @registrations id) :anchor weak-value)
                     (throw (ex-info "Cell handle has been released"
                                     {:type ::released :id id}))))]
    ;; WeakReference.get establishes a strong reference before releasing the
    ;; lock. A finalizer can only claim after that reference itself dies.
    #?(:clj (locking registry-lock (lookup))
       :cljs (lookup))))
