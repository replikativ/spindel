(ns org.replikativ.spindel.engine.lifetime
  "Ownership metadata for a world's lifetime scopes and runs."
  (:require [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp]))

(defn root-scope [context]
  [:root (:fork-id context)])

(defn run-id [context spin-id token]
  [:run (:fork-id context) spin-id token])

(defn current-run-id [context]
  (let [run ec/*lifetime-run*
        spin-id ec/*spin-id*]
    (cond
      (vector? run) run
      (and (number? run) (= spin-id (first ec/*run-gen*)))
      (run-id context spin-id run)
      spin-id
      (let [node (rtp/get-state context [:nodes spin-id])]
        (when (:run-gen node)
          (run-id context spin-id (or (:lifetime/seq node) 1)))))))

(defn current-scope [context]
  (let [world (:fork-id context)
        explicit ec/*owner-scope*
        run (current-run-id context)]
    (when (and explicit (not= world (second explicit)))
      (throw (ex-info "Scope belongs to another world" {:scope explicit :world world})))
    (cond
      explicit explicit
      (and run (= world (second run))) run
      :else (root-scope context))))

(defn open-scope!
  ([context kind]
   (open-scope! context kind (current-scope context)))
  ([context kind parent]
   (let [id [:scope (:fork-id context) (random-uuid)]]
     (rtp/swap-state! context [:lifetime/scopes id]
                      (constantly {:kind kind :parent parent :status :open}))
     id)))

(defn bindable-scope [context scope]
  (when-not (and (= (:fork-id context) (second scope))
                 (or (= :root (first scope))
                     (and (= :run (first scope))
                          (= scope (rtp/get-state context [:nodes (nth scope 2) :lifetime/run])))
                     (= :open (rtp/get-state context [:lifetime/scopes scope :status]))))
    (throw (ex-info "Scope is not open in this world" {:scope scope :world (:fork-id context)})))
  scope)

#?(:clj
   (defmacro with-owner [scope & body]
     `(let [scope# (bindable-scope (ec/current-execution-context) ~scope)]
        (binding [ec/*owner-scope* scope#]
          ~@body))))

(defn body-run-id [context spin-id]
  (or (rtp/get-state context [:nodes spin-id :lifetime/run])
      (run-id context spin-id (or (rtp/get-state context [:nodes spin-id :lifetime/seq]) 1))))

(defn body-run-seq [context spin-id]
  (or (rtp/get-state context [:nodes spin-id :lifetime/seq]) 1))

(defn successor-run? [previous current]
  (and (= :run (first previous))
       (= :run (first current))
       (= (second previous) (second current))
       (= (nth previous 2) (nth current 2))
       (< (nth previous 3) (nth current 3))))

(defn record-owned-source! [context owner source-id]
  (when (= :run (first owner))
    (rtp/swap-state! context [:nodes (nth owner 2)]
                     (fn [node]
                       (when node
                         (update node :lifetime/owned-sources (fnil conj #{}) source-id))))))
