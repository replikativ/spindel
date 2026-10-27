(ns org.replikativ.spindel.yggdrasil.construction
  "HOST-only ownership while a native fork has no completed ForkHandle.
   Private lifecycle state is never installed in a semantic execution world."
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.engine.quiescence :as quiescence]
            [org.replikativ.spindel.engine.component :as component]
            [yggdrasil.protocols :as p]
            [yggdrasil.convergent :as yc]
            [yggdrasil.convergent.overlay :as overlay]
            #?(:clj [is.simm.partial-cps.async :refer [async await]]
               :cljs [is.simm.partial-cps.async :refer [await]])
            #?(:clj [yggdrasil.macros :refer [async+sync]]))
  #?(:cljs (:require-macros [yggdrasil.macros :refer [async+sync]]
                            [is.simm.partial-cps.async :refer [async]])))

(deftype ConstructionOwner [state token])
(defn owner? [value] (instance? ConstructionOwner value))
(defn- cell [owner] (.-state ^ConstructionOwner owner))
(defn- token [owner] (.-token ^ConstructionOwner owner))
(defn- refuse! [type] (throw (ex-info "Fork construction ownership is unavailable" {:type type})))
(defn- checked [owner state]
  (when-not (= (token owner) (:token state)) (refuse! ::transferred))
  state)
(defn- update! [owner f]
  (swap! (cell owner) #(f (checked owner %))))

(defn create [system-ids]
  (let [token (random-uuid)]
    (ConstructionOwner. (atom {:id (random-uuid) :token token :status :building
                               :system-ids system-ids :entries [] :active nil}) token)))

(defn info
  "Redacted lifecycle diagnostics; no contexts, native values or callbacks."
  [owner]
  (let [state @(cell owner)]
    {:id (:id state) :status (:status state) :busy? (boolean (:busy? state))
     :receipts (mapv #(select-keys % [:id :system :component/id :kind :phase :depends-on]) (:entries state))}))

(defn observe!
  "A construction-extent registrar. Called outside backend atom mutators.
   :before/:value bracket a registered system hook; :branch acknowledges the
   exact branch before checkout; :context retains the provisional child."
  [owner {:keys [phase signal source value branch context cleanup] :as event}]
  (let [receipt (random-uuid)]
    (let [state (update!
                 owner
                 (fn [state]
                   (when-not (= :building (:status state)) (refuse! ::not-building))
                   (case phase
                     :component-before
                     (do (when (:active state) (refuse! ::nested-acquisition))
                         (-> state
                             (assoc :active (count (:entries state)))
                             (update :entries conj {:id receipt :kind :component
                                                    :component/id (:component/id event)
                                                    :source source :phase :attempting})))

                     (:component-value :component-failure)
                     (let [n (:active state)
                           entry (when (some? n) (get-in state [:entries n]))
                           resource (if (= :component-failure phase) cleanup value)
                           owned? (and resource (not (identical? source resource))
                                       (satisfies? component/PComponentRetirement resource)
                                       (not-any? #(identical? resource (:resource %)) (:entries state)))]
                       (when-not (and (= :component (:kind entry))
                                      (= (:component/id entry) (:component/id event)))
                         (refuse! ::wrong-acquisition))
                       (-> state
                           (assoc :active nil)
                           (assoc-in [:entries n]
                                     (if owned?
                                       (-> entry
                                           (dissoc :source)
                                           (assoc :kind (if (= :component-failure phase)
                                                          :component-recovery :component)
                                                  :phase :owned :resource resource))
                                       (-> entry (dissoc :source) (assoc :phase :empty))))))

                     :before
                     (if-let [system (get (:system-ids state) signal)]
                       (do (when (:active state) (refuse! ::nested-acquisition))
                           (-> state
                               (assoc :active (count (:entries state)))
                               (update :entries conj {:id receipt :system system :signal signal
                                                      :source source :phase :attempting})))
                       state)

                     :branch
                     (if-not (contains? (:system-ids state) signal)
                       state
                       (if-some [n (:active state)]
                         (do (when-not (= signal (get-in state [:entries n :signal])) (refuse! ::wrong-acquisition))
                             (update-in state [:entries n] assoc :kind :branch :phase :owned :resource value :branch branch))
                         (refuse! ::missing-acquisition)))

                     :value
                     (if-some [n (:active state)]
                       (do
                         (when-not (= signal (get-in state [:entries n :signal])) (refuse! ::wrong-acquisition))
                         (let [entry (get-in state [:entries n])
                               entry (cond
                                       (= :branch (:kind entry)) (assoc entry :resource value)
                                       (identical? source value) (assoc entry :phase :empty :source nil)
                                       (overlay/overlay? value) (assoc entry :kind :overlay :phase :owned :resource value)
                                       :else (assoc entry :phase :uncertain :resource value))]
                           (-> state (assoc-in [:entries n] entry) (assoc :active nil))))
                       state)

                     :context (assoc state :context context)
                     :activation (update state :entries conj
                                         {:id receipt :kind :activation :phase :active})
                     (refuse! ::invalid-event))))]
      (when (and (= :value phase) (= :uncertain (:phase (peek (:entries state)))))
        (refuse! ::unsupported-fork-value)))))

(defn failed!
  "Preserve a throwing native constructor as uncertain. Pure component errors
   after all hooks returned have no active native attempt to quarantine."
  [owner error]
  (let [foreign (random-uuid)]
    (update!
     owner
     (fn [state]
       (when-not (= :building (:status state)) (refuse! ::not-building))
       (let [active (:active state)
             state (cond-> state
                     (and (some? active) (= :attempting (get-in state [:entries active :phase])))
                     (assoc-in [:entries active :phase] :uncertain))
             ;; Checkout can acquire another resource after the branch ACK.
             ;; Its thrown result is uncertain even without a known adapter key.
             state (if (and (some? active)
                            (= :owned (get-in state [:entries active :phase])))
                     (update state :entries conj {:id foreign :kind :checkout :phase :uncertain :error error
                                                  :depends-on (get-in state [:entries active :id])})
                     state)]
         (-> state
             (assoc :status :held :active nil :error error)
             (update :entries (fn [entries]
                                (mapv #(if (and (= :activation (:kind %)) (= :active (:phase %)))
                                         (assoc % :phase :uncertain) %) entries)))))))))

(defn resolve-uncertain!
  "Privileged HOST attestation after investigating/reconciling a native failure.
   Does not inspect absence or perform IO. :not-acquired/:disposed acknowledge
   an uncertain acquisition. For :activation, :disposed requires a real host
   cancellation/join proof for all child work; quiescence alone is insufficient.
   :retry-safe permits retrying a disposal only after
   its adapter established that repeating it is safe. Never lifted into SCI."
  [owner receipt-id resolution]
  (update!
   owner
   (fn [state]
     (when (or (:busy? state) (not= :held (:status state))) (refuse! ::busy))
     (let [n (first (keep-indexed #(when (= receipt-id (:id %2)) %1) (:entries state)))
           entry (when n (get-in state [:entries n]))
           allowed (case (:phase entry)
                     :uncertain #{:not-acquired :disposed}
                     :cleanup-uncertain #{:disposed :retry-safe}
                     #{})]
       (when-not (contains? allowed resolution) (refuse! ::invalid-resolution))
       (assoc-in state [:entries n]
                 (if (= :retry-safe resolution)
                   (assoc entry :phase :owned)
                   (-> entry (assoc :phase :disposed) (dissoc :source :resource :error)))))))
  nil)

(defn dispose!
  "Clean acknowledged resources once, in reverse order. Ambiguous outcomes stay
   held until explicit native reconciliation; no guessing or automatic replay.
   A provisional child must be physically quiescent before native release."
  ([owner] (dispose! owner {}))
  ([owner opts]
   (async+sync
    (:sync? (merge yc/default-opts opts))
    (async
     (let [state (update! owner
                          #(cond
                             (= :closed (:status %)) %
                             (or (:busy? %) (not= :held (:status %))) (refuse! ::busy)
                             :else (assoc % :busy? true)))]
       (when-not (= :closed (:status state))
         (try
           (when (some #(and (= :activation (:kind %))
                             (not (#{:disposed :empty} (:phase %)))) (:entries state))
             (refuse! ::activation-unjoined))
           (when (and (:context state) (not (quiescence/quiescent? (:context state))))
             (refuse! ::not-quiescent))
           (loop [indices (seq (reverse (range (count (:entries state)))))]
             (when indices
               (let [n (first indices) entry (get-in @(cell owner) [:entries n])]
                 ;; A heap can retain capabilities into earlier acquisitions.
                 ;; Without an independence manifest, unresolved component
                 ;; cleanup is a barrier to releasing those dependencies.
                 (when (and (#{:component :component-recovery} (:kind entry))
                            (not (#{:owned :disposed :empty} (:phase entry))))
                   (refuse! ::incomplete))
                 (when (and (= :owned (:phase entry))
                            ;; A throwing checkout may still own a live handle
                            ;; into its acknowledged branch. Reconcile it before
                            ;; deleting that dependency; independent ACKs unwind.
                            (not-any? #(and (= (:id entry) (:depends-on %))
                                            (not (#{:disposed :empty} (:phase %))))
                                      (:entries @(cell owner))))
                   (let [error (try
                                 (let [result (case (:kind entry)
                                                :overlay (p/discard! (:resource entry) opts)
                                                :branch (p/delete-branch! (:resource entry) (:branch entry) (merge yc/default-opts opts))
                                                (:component :component-recovery)
                                                (do (component/retire-component! (:resource entry)) nil))]
                                   (when (fn? result) (await result))
                                   nil)
                                 (catch #?(:clj Throwable :cljs :default) error error))]
                     (update! owner
                              #(update-in % [:entries n]
                                          (fn [entry]
                                            (if error
                                              (assoc entry :phase (if (#{:component :component-recovery} (:kind entry))
                                                                    :owned :cleanup-uncertain)
                                                     :error error)
                                              (-> entry (assoc :phase :disposed) (dissoc :source :resource :error))))))
                     (when (and error (#{:component :component-recovery} (:kind entry)))
                       (refuse! ::incomplete))))
                 (recur (next indices)))))
           (let [remaining (some #(not (#{:disposed :empty} (:phase %))) (:entries @(cell owner)))]
             (when remaining (refuse! ::incomplete))
             (update! owner #(-> % (assoc :status :closed) (dissoc :context :error :system-ids))))
           (finally (update! owner #(dissoc % :busy?)))))
       nil)))))

(defn transfer!
  "The complete ForkHandle now owns the resources. Drop construction references."
  [owner]
  (update! owner
           (fn [state]
             (when-not (and (= :building (:status state)) (nil? (:active state))
                            (not (:busy? state))
                            (every? #(or (#{:owned :empty} (:phase %))
                                         (and (= :activation (:kind %)) (= :active (:phase %))))
                                    (:entries state)))
               (refuse! ::not-building))
             (-> state (assoc :status :transferred :entries []) (dissoc :context :system-ids))))
  nil)

(defn offer!
  "Offer one inactive candidate to an atomic HOST owner. Returning true claims
   it after the callback returns; declined/thrown handoffs leave the original
   owner active. A receiver must only store the candidate during this callback."
  [owner receiver]
  (if-not receiver
    {:claimed? false :owner owner}
    (let [_ (update! owner #(do (when (or (:busy? %) (not= :held (:status %))) (refuse! ::busy))
                                (assoc % :busy? :handoff)))
          next-token (random-uuid)
          candidate (ConstructionOwner. (cell owner) next-token)
          outcome (try {:claimed? (true? (receiver candidate))}
                       (catch #?(:clj Throwable :cljs :default) error {:claimed? false :error error}))]
      (if (:claimed? outcome)
        (do (update! owner #(-> % (assoc :token next-token) (dissoc :busy?)))
            {:claimed? true})
        (do (update! owner #(dissoc % :busy?))
            (assoc outcome :owner owner))))))
