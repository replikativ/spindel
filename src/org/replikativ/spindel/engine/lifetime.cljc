(ns org.replikativ.spindel.engine.lifetime
  "Ownership metadata for a world's lifetime scopes and runs."
  (:require [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.protocols :as rtp])
  #?(:cljs (:require-macros [org.replikativ.spindel.engine.lifetime :refer [with-owner]])))

(defn legacy-root-scope [context]
  [:root (:fork-id context)])

(defn run-id [context spin-id token]
  [:run (:fork-id context) spin-id token])

(defn current-run-id [context]
  (let [run ec/*lifetime-run*
        spin-id ec/*spin-id*
        node (when spin-id (rtp/get-state context [:nodes spin-id]))]
    (cond
      (and (vector? run) node)
      (run-id context spin-id (nth run 3))
      (and node (number? run) (= spin-id (first ec/*run-gen*)))
      (run-id context spin-id run)
      (:run-gen node)
      (run-id context spin-id (or (:lifetime/seq node) 1)))))

(defn legacy-current-scope [context]
  (let [world (:fork-id context)
        explicit ec/*owner-scope*
        foreign-run? (and (= :run (first explicit))
                          (not= world (second explicit)))]
    (when (and explicit (not= world (second explicit)) (not foreign-run?))
      (throw (ex-info "Scope belongs to another world" {:scope explicit :world world})))
    (cond
      foreign-run?
      (or (current-run-id context) (legacy-root-scope context))
      explicit explicit
      :else (or (current-run-id context) (legacy-root-scope context)))))

(defn legacy-open-scope!
  ([context kind]
   (legacy-open-scope! context kind (legacy-current-scope context)))
  ([context kind parent]
   (let [id [:scope (:fork-id context) (random-uuid)]]
     (rtp/swap-state! context [:lifetime/scopes id]
                      (constantly {:kind kind :parent parent :status :open}))
     id)))

(defn legacy-bindable-scope [context scope]
  (when-not (and (= (:fork-id context) (second scope))
                 (or (= :root (first scope))
                     (and (= :run (first scope))
                          (= scope (rtp/get-state context [:nodes (nth scope 2) :lifetime/run])))
                     (= :open (rtp/get-state context [:lifetime/scopes scope :status]))))
    (throw (ex-info "Scope is not open in this world" {:scope scope :world (:fork-id context)})))
  scope)

(defn legacy-capture-execution-owner [_ owner] owner)

(defn legacy-restore-execution-owner [context captured _current]
  (let [run (current-run-id context)]
    (if (and run (vector? captured) (= :run (first captured))
             (= (nth captured 2) (nth run 2)))
      run
      captured)))

(defn root-scope [context] (rtp/root-execution-owner context))
(defn current-scope [context] (rtp/current-execution-owner context))
(defn open-scope!
  ([context kind] (open-scope! context kind (current-scope context)))
  ([context kind parent] (rtp/open-execution-scope! context kind parent)))
(defn bindable-scope [context scope] (rtp/bindable-execution-owner context scope))
(defn close-scope! [context scope] (rtp/close-execution-scope! context scope))

#?(:clj
   (defmacro with-owner [scope & body]
     `(let [scope# (bindable-scope (ec/current-execution-context) ~scope)]
        (binding [ec/*owner-scope* scope#]
          ~@body))))

(defn body-run-id [context spin-id]
  (let [stored (rtp/get-state context [:nodes spin-id :lifetime/run])]
    (if (= (:fork-id context) (second stored))
      stored
      (run-id context spin-id (or (rtp/get-state context [:nodes spin-id :lifetime/seq]) 1)))))

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
