(ns org.replikativ.spindel.engine.cells
  "Legacy backend implementation of managed runtime cells."
  (:require [org.replikativ.spindel.engine.cell-handles :as handles]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.lifetime :as lifetime]
            [org.replikativ.spindel.engine.state-backend :as backend]))

(defn- require-entry [entry id]
  (or entry
      (throw (ex-info "Runtime cell is absent in the bound world"
                      {:type ::missing-cell :id id}))))

(defn- matching-owner? [state owner]
  (and (= :run (first owner))
       (= owner (get-in state [:nodes (nth owner 2) :lifetime/run]))))

(defn reap-cell! [state-backend id]
  ;; A finalizer is registered only against the allocating backend. Forks and
  ;; frozen descendants retain their independent values until their own sweep.
  (when-not (= :immutable (backend/backend-type state-backend))
    (backend/backend-write!
     state-backend []
     (fn [state]
       (let [owner (get-in state [:atoms id :lifetime/owner])]
         (cond-> (-> state
                     (update :atoms dissoc id)
                     (update :listeners dissoc id))
           (matching-owner? state owner)
           (update-in [:nodes (nth owner 2) :lifetime/owned-sources] disj id)))))))

(defn allocate! [ctx value options]
  (let [id (keyword (str "atom-" (random-uuid)))
        state-backend (:backend ctx)
        owner (lifetime/current-scope ctx)
        anchor (handles/allocate! id state-backend reap-cell!)]
    (backend/backend-write!
     state-backend []
     (fn [state]
       (cond-> (assoc-in state [:atoms id]
                         {:value value :meta (:meta options) :lifetime/owner owner})
         (matching-owner? state owner)
         (update-in [:nodes (nth owner 2) :lifetime/owned-sources] (fnil conj #{}) id))))
    {:id id :anchor anchor}))

(defn present? [ctx id]
  (some? (backend/backend-read (:backend ctx) [:atoms id])))

(defn value [ctx id]
  (:value (backend/backend-read (:backend ctx) [:atoms id])))

(defn cell-meta [ctx id]
  (:meta (backend/backend-read (:backend ctx) [:atoms id])))

(defn watches [ctx id]
  (backend/backend-read (:backend ctx) [:listeners id]))

(defn swap-cell! [ctx ref id f args]
  (let [delivery (volatile! nil)]
    (backend/backend-write!
     (:backend ctx) []
     (fn [state]
       (let [entry (require-entry (get-in state [:atoms id]) id)
             old (:value entry)
             new-value (apply f old args)]
         ;; Capture value and registrations in the same successful CAS. This
         ;; volatile is overwritten on retries; no delivery escapes a retry.
         (vreset! delivery [old new-value (get-in state [:listeners id])])
         (assoc-in state [:atoms id] (assoc entry :value new-value)))))
    (let [[old new-value listeners] @delivery]
      (binding [ec/*execution-context* ctx]
        (ec/notify-listeners! ref id old new-value listeners))
      new-value)))

(defn cas-cell! [ctx ref id old-value new-value]
  (let [delivery (volatile! nil)]
    (backend/backend-write!
     (:backend ctx) []
     (fn [state]
       (let [entry (require-entry (get-in state [:atoms id]) id)
             matches? (identical? old-value (:value entry))]
         (vreset! delivery (when matches? [(get-in state [:listeners id])]))
         (if matches? (assoc-in state [:atoms id] (assoc entry :value new-value)) state))))
    (when-let [[listeners] @delivery]
      (binding [ec/*execution-context* ctx]
        (ec/notify-listeners! ref id old-value new-value listeners)))
    (some? @delivery)))

(defn add-watch! [ctx id key f]
  (backend/backend-write!
   (:backend ctx) []
   (fn [state]
     (require-entry (get-in state [:atoms id]) id)
     (assoc-in state [:listeners id key] f)))
  nil)

(defn remove-watch! [ctx id key]
  (backend/backend-write!
   (:backend ctx) []
   (fn [state]
     (require-entry (get-in state [:atoms id]) id)
     (if (contains? (:listeners state) id)
       (update-in state [:listeners id] dissoc key)
       state)))
  nil)
