(ns org.replikativ.spindel.lifetime.lifecycle
  "Release completion is external observation, never a new owned computation."
  (:require [org.replikativ.spindel.lifetime.cleanup :as cleanup]))

(defn release-id [w] [:world-release w])
(defn- require! [p error data]
  (when-not p (throw (ex-info (name error) (assoc data :error error)))))

(defn receipt! [s {:keys [w release] :as action}]
  (let [row (get-in s [:env :releases w])]
    (require! (and (= release (release-id w)) (= release (:id row)))
              ::invalid-release-receipt {:action action})
    row))

(defn caller-worlds!
  "Authenticate supplied actor evidence before deciding whether a wait joins
   its own required stack. Missing evidence denotes an external coordinator."
  [s {:keys [caller-th th op frame callback] :as action}]
  (require! (nil? th) ::invalid-release-caller {:action action})
  (let [thread (get-in s [:env :threads caller-th])
        operation (when (some? op) (cleanup/operation s op))
        ticket (when (vector? op) (get-in s [:env :native (first op)]))
        raw (when (some? callback) (get-in s [:env :native callback]))]
    (when (some? caller-th)
      (require! (and thread (:world thread) (or (nil? (:run thread)) (:executing? thread)))
                ::invalid-release-caller {:action action}))
    (when (some? op)
      (require! (and operation (cleanup/protected? ticket)
                     (= (second op) (:sequence ticket)) (contains? (:frames operation) frame))
                ::invalid-release-caller {:action action}))
    (when (some? callback)
      (require! (and (cleanup/mailbox-callback? raw) (= frame (:frame raw))
                     (cleanup/mailbox-callback-entered? s raw))
                ::invalid-release-caller {:action action}))
    (require! (or (nil? frame) op callback) ::invalid-release-caller {:action action})
    (set (concat (when (:run thread) [(:world thread)])
                 (when (some? op) [(first (:owner ticket))])
                 (when (some? callback) [(first (:owner raw))])))))

(defn request [s {:keys [w release] :as action}]
  (require! (= release (release-id w)) ::invalid-release-receipt {:action action})
  (if (get-in s [:env :releases w])
    (do (receipt! s action) s)
    (assoc-in s [:env :releases w]
              {:id release :reason (get action :reason :org.replikativ.spindel.engine.protocols/released)
               :phase :releasing :next-observer 0 :observers {}})))

(defn cleanup-worlds
  "Finite causal closure; cycles carry evidence, not recursive wait handles."
  [s w]
  (loop [pending [w] seen #{}]
    (if-let [world (peek pending)]
      (if (contains? seen world) (recur (pop pending) seen)
          (recur (into (pop pending) (map :target-world (vals (get-in s [:env :cleanup-targets world]))))
                 (conj seen world))) seen)))

(defn cleanup-terminal? [s {:keys [target-world cap op]}]
  (let [c (or (get-in s [:caps cap]) (get-in s [:durable :caps cap]))
        record (or (get-in s [:records op]) (get-in s [:durable :records op]))]
    (and (= target-world (:world c)) (= op (:op c)) (= cap (:cap record))
         (= op (:op record)) (= (:kind c) (:kind record))
         (= (:disposition c) (case (:kind record) :discard :discarded :merge :merged nil))
         (true? (:effects-released? record)) (every? #(= :done (:status %)) (:steps record)))))

(defn composed-ready? [s w local-ready?]
  (let [worlds (cleanup-worlds s w)]
    (and (every? #(local-ready? s %) worlds)
         (every? #(cleanup-terminal? s %)
                 (mapcat #(vals (get-in s [:env :cleanup-targets %])) worlds)))))

(defn prune-cleanup-targets [s ready-worlds]
  (let [targets (into {} (keep (fn [[w debts]]
                                 (let [pending (into {} (remove (fn [[_ debt]]
                                                                  (and (contains? ready-worlds (:target-world debt))
                                                                       (cleanup-terminal? s debt))) debts))]
                                   (when (seq pending) [w pending])))
                               (get-in s [:env :cleanup-targets])))]
    (if (seq targets) (assoc-in s [:env :cleanup-targets] targets)
        (update s :env dissoc :cleanup-targets))))

(defn observe [s {:keys [w release observer] :as action}]
  (let [row (receipt! s action) callers (caller-worlds! s action)
        expected [release (inc (:next-observer row))]]
    (require! (not-any? (cleanup-worlds s w) callers) ::release-self-join {:action action})
    (require! (= observer expected) ::not-release-observer {:action action})
    (-> s (update-in [:env :releases w :next-observer] inc)
        (assoc-in [:env :releases w :observers observer]
                  {:state (if (= :joined (:phase row)) :ready :waiting)}))))

(defn- issued-observer? [row observer]
  (and (vector? observer) (= 2 (count observer)) (= (:id row) (first observer))
       (integer? (second observer)) (<= 1 (second observer) (:next-observer row))))

(defn detach [s {:keys [w observer] :as action}]
  (let [row (receipt! s action)]
    (caller-worlds! s action)
    (require! (issued-observer? row observer) ::not-release-observer {:action action})
    (update-in s [:env :releases w :observers] dissoc observer)))

(defn notify [s {:keys [w release observer] :as action}]
  (let [row (receipt! s action)]
    (require! (not-any? #(some? (get action %)) [:th :caller-th :op :frame :callback])
              ::invalid-release-caller {:action action})
    (require! (and (= :joined (:phase row)) (= :ready (get-in row [:observers observer :state])))
              ::not-release-ready {:action action})
    (-> s (update-in [:env :releases w :observers] dissoc observer)
        (update :events conj {:event :release-delivery :world w :release release :observer observer
                              :variant :ok :value nil}))))

(defn stale-producer?
  "An accepted attempt can no longer affect its exact allocation. A retired
   cohort key alone is not proof: another holder of that allocation may remain."
  [s w {:keys [event] :as packet}]
  (let [kind (cond (contains? event :deferred-assignment) :deferred
                   (contains? event :mailbox-post) :mailbox)
        e (get event (case kind :deferred :deferred-assignment :mailbox :mailbox-post nil))
        allocation (:allocation event)
        source (get-in s [:worlds w :entities e])]
    (and (= w (:w packet)) kind (contains? event :allocation)
         (= :released (get-in s [:worlds w :status]))
         (not (and (= kind (:kind source)) (= allocation (:allocation source)) (:owner source)))
         (not-any? (fn [[key cell]]
                     (and (= w (first key)) (= e (nth key 2 nil))
                          (= kind (:kind cell)) (= allocation (:allocation cell)) (seq (:holders cell))))
                   (get-in s [:env :cleanup-cells])))))

(defn refresh [s ready?]
  (let [ready-worlds (set (filter #(ready? s %) (keys (:worlds s))))
        s (prune-cleanup-targets s ready-worlds)]
    (reduce
     (fn [s [w row]]
       (if (and (= :releasing (:phase row)) (contains? ready-worlds w))
         (-> s (update-in [:env :outside] #(vec (remove (partial stale-producer? s w) %)))
             (assoc-in [:env :releases w :phase] :joined)
             (assoc-in [:env :releases w :result] nil)
             (update-in [:env :releases w :observers]
                        #(into {} (for [[id observer] %] [id (assoc observer :state :ready)])))
             (update :events conj {:event :release-joined :world w :release (:id row)})) s))
     s (get-in s [:env :releases]))))
