(ns org.replikativ.spindel.spin.supervisor
  "Supervisor for spawned spins with restart policies.

   Follows Erlang/OTP model adapted to spindel's CPS:
   - :one-for-one  — restart only the failed spin
   - :one-for-all  — restart all children when one fails
   - :rest-for-one — restart failed + all children started after it

   The supervisor is itself a spin that monitors children via a mailbox.
   Child failures are discrete events posted to the supervisor's mailbox.

   Usage:
     (supervisor
       [{:id :worker-1 :start (fn [] (spin (do-work-1)))}
        {:id :worker-2 :start (fn [] (spin (do-work-2)))}]
       {:strategy :one-for-one
        :max-restarts 5
        :window-ms 60000
        :on-fatal (fn [e] (log/error! \"Fatal: supervisor giving up\"))})"
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.spin.sync :as sync :refer [spawn! mailbox]]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.log :as log]
            #?(:clj [org.replikativ.spindel.spin.cps :refer [spin]])
            [org.replikativ.spindel.effects.await :refer [await]])
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]])))

;; =============================================================================
;; Internal: Restart Budget
;; =============================================================================

(defn- within-budget?
  "Check if we're within the restart budget.
   Returns true if fewer than max-restarts have occurred in the last window-ms."
  [restart-log max-restarts window-ms]
  (let [now #?(:clj (System/currentTimeMillis) :cljs (.now js/Date))
        cutoff (- now window-ms)
        recent (filter #(> % cutoff) restart-log)]
    (< (count recent) max-restarts)))

(defn- record-restart
  "Add current timestamp to restart log, pruning old entries."
  [restart-log window-ms]
  (let [now #?(:clj (System/currentTimeMillis) :cljs (.now js/Date))
        cutoff (- now window-ms)]
    (conj (vec (filter #(> % cutoff) restart-log)) now)))

;; =============================================================================
;; Internal: Child Management
;; =============================================================================

(defn- spawn-child!
  "Spawn a child spin with error reporting to supervisor mailbox.
   Returns the spawned spin."
  [child-spec sup-mbx]
  (let [child-spin ((:start child-spec))]
    (spawn! child-spin
            {:on-error (fn [e]
                         (log/debug! {:event :supervisor/child-failed
                                      :data {:child-id (:id child-spec)
                                             :error #?(:clj (.getMessage ^Throwable e) :cljs (str e))}})
                         (sup-mbx {:type :child-failed
                                   :id (:id child-spec)
                                   :error e}))})
    child-spin))

(defn- restart-child!
  "Restart a single child. Returns updated children map."
  [children child-id sup-mbx child-specs-by-id]
  (let [spec (get child-specs-by-id child-id)
        new-spin (spawn-child! spec sup-mbx)]
    (assoc children child-id new-spin)))

(defn- restart-all!
  "Restart all children. Returns updated children map."
  [child-specs sup-mbx]
  (reduce (fn [m spec]
            (assoc m (:id spec) (spawn-child! spec sup-mbx)))
          {}
          child-specs))

(defn- restart-rest!
  "Restart failed child + all children after it in the spec order.
   Returns updated children map."
  [children failed-id child-specs sup-mbx child-specs-by-id]
  (let [idx (.indexOf (mapv :id child-specs) failed-id)
        to-restart (subvec (vec child-specs) idx)]
    (reduce (fn [m spec]
              (assoc m (:id spec) (spawn-child! spec sup-mbx)))
            children
            to-restart)))

;; =============================================================================
;; Public API
;; =============================================================================

(defn supervisor
  "Create a supervisor spin that monitors children.

   children is a vector of {:id keyword, :start (fn [] spin)}.
   Each :start fn must return a NEW spin each time (spins are stateless).

   Options:
     :strategy     — :one-for-one (default), :one-for-all, :rest-for-one
     :max-restarts — max restarts in :window-ms (default 5)
     :window-ms    — time window for restart counting (default 60000)
     :on-fatal     — fn called with last error when max-restarts exceeded

   Returns a spin that runs the supervisor loop. Spawn it with spawn!."
  [children & [{:keys [strategy max-restarts window-ms on-fatal]
                :or {strategy :one-for-one
                     max-restarts 5
                     window-ms 60000
                     on-fatal (fn [e]
                                (log/error! {:event :supervisor/fatal
                                             :data {:error e}}))}}]]
  (let [child-specs-by-id (into {} (map (juxt :id identity)) children)]
    (spin
      (let [sup-mbx (mailbox)
            ;; Initial spawn of all children
            initial-children (reduce
                               (fn [m spec]
                                 (assoc m (:id spec) (spawn-child! spec sup-mbx)))
                               {}
                               children)]
        ;; Supervisor loop: listen for child failures
        (loop [active-children initial-children
               restart-log []]
          (let [msg (await sup-mbx)]
            (case (:type msg)
              :child-failed
              (let [failed-id (:id msg)
                    error (:error msg)]
                (if (within-budget? restart-log max-restarts window-ms)
                  ;; Within budget — restart according to strategy
                  (let [new-log (record-restart restart-log window-ms)
                        new-children
                        (case strategy
                          :one-for-one
                          (restart-child! active-children failed-id sup-mbx child-specs-by-id)

                          :one-for-all
                          (restart-all! children sup-mbx)

                          :rest-for-one
                          (restart-rest! active-children failed-id children sup-mbx child-specs-by-id))]
                    (log/debug! {:event :supervisor/restarted
                                 :data {:strategy strategy
                                        :failed-id failed-id
                                        :restarts-in-window (count new-log)}})
                    (recur new-children new-log))

                  ;; Budget exceeded — fatal
                  (do
                    (log/error! {:event :supervisor/max-restarts-exceeded
                                 :data {:failed-id failed-id
                                        :max-restarts max-restarts
                                        :window-ms window-ms}})
                    (on-fatal error))))

              :shutdown
              (log/debug! {:event :supervisor/shutdown})

              ;; Unknown message — ignore
              (recur active-children restart-log))))))))

(defn shutdown!
  "Send shutdown message to a supervisor's mailbox.
   The supervisor must have been started with spawn!."
  [sup-mbx]
  (sup-mbx {:type :shutdown}))
