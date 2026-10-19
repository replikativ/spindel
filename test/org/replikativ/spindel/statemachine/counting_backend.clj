(ns org.replikativ.spindel.statemachine.counting-backend
  "Counts backend API calls, not CAS retries or sub-writes hidden in root swaps.
   Prefix [] denotes whole-state operations. Two-path writes count one commit
   and one touched path for each argument. Counters themselves allocate."
  (:require [org.replikativ.spindel.engine.state-backend :as sb]))

(defn count! [counts operation path]
  (swap! counts update-in [operation (vec (take 1 path))] (fnil inc 0)))

(defrecord CountingBackend [delegate counts state-atom]
  sb/PStateBackend
  (backend-read [_ path]
    (count! counts :reads path)
    (sb/backend-read delegate path))
  (backend-write! [_ path f]
    (count! counts :writes path)
    (count! counts :commits [])
    (sb/backend-write! delegate path f))
  (backend-write-2! [_ pa pb f]
    (count! counts :writes pa)
    (count! counts :writes pb)
    (count! counts :commits [])
    (sb/backend-write-2! delegate pa pb f))
  (backend-deref [_]
    (count! counts :reads [])
    (sb/backend-deref delegate))
  (backend-type [_] (sb/backend-type delegate)))

(defn instrument
  "Attach counters to an AtomBackend context. Other backends can use the
   wrapper directly for protocol calls, but context CAS requires concrete fields."
  [rt]
  ;; Context's AtomBackend CAS implementation accesses this field directly.
  ;; Preserve it so wrapping does not change CAS semantics. Those bypass calls
  ;; are intentionally NOT counted as backend reads/writes.
  (let [delegate (:backend rt)
        counts (atom {})]
    ;; Observe actual successful atom transitions too: context CAS bypasses the
    ;; backend API. This watch counts commits, never failed/retried CAS attempts.
    (add-watch (:state-atom delegate) ::commits
               (fn [_ _ _ _] (count! counts :atom-commits [])))
    [(assoc rt :backend (->CountingBackend delegate counts (:state-atom delegate))) counts]))
