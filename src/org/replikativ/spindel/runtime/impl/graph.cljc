(ns org.replikativ.spindel.runtime.impl.graph
  "Graph operations for topological sorting and observer ordering.

  Pure computation over the dependency graph stored in context state.
  Used by signal-change processing to determine the correct order
  for re-executing observer spins (glitch-free updates)."
  (:require [org.replikativ.spindel.runtime.nodes :as nodes]))

(defn collect-transitive-observers
  "Collect all spins transitively dependent on initial-spin-ids.

  Given a set of initial spin IDs, follows the spin-observers graph to find
  all spins that directly or indirectly observe these spins.

  Args:
    context - context state map (not the record, the dereferenced state)
    initial-spin-ids - Collection of spin IDs to start from

  Returns: Set of all transitive observer spin IDs"
  [context initial-spin-ids]
  (loop [to-visit (vec initial-spin-ids) visited #{}]
    (if-let [tid (first to-visit)]
      (if (visited tid)
        (recur (rest to-visit) visited)
        (let [node (get-in context [:nodes tid])
              observers (if node (nodes/get-observers node) #{})]
          (recur (into (rest to-visit) observers) (conj visited tid))))
      visited)))

(defn topological-sort
  "Sort spin IDs in topological order based on spin dependencies.

  Ensures spins are executed in dependency order (dependencies before dependents).
  Uses Kahn's algorithm for topological sorting.

  Args:
    context - context state map (not the record, the dereferenced state)
    spin-ids - Collection of spin IDs to sort

  Returns: Vector of spin IDs in topological order"
  [context spin-ids]
  (let [in-degree (reduce (fn [acc tid]
                            (let [node (get-in context [:nodes tid])
                                  deps (if node (nodes/get-deps node) {:signals #{} :spins #{}})
                                  spin-deps (get deps :spins #{})]
                              (assoc acc tid (count (filter spin-ids spin-deps)))))
                          {}
                          spin-ids)
        initial-queue (vec (filter #(zero? (get in-degree % 0)) spin-ids))]
    (loop [queue initial-queue result [] in-deg in-degree]
      (if-let [tid (first queue)]
        (let [new-result (conj result tid)
              node (get-in context [:nodes tid])
              dependent-spins (if node (nodes/get-observers node) #{})
              relevant (filter spin-ids dependent-spins)
              new-in-deg (reduce (fn [deg dep]
                                   (update deg dep dec)) in-deg relevant)
              newly-ready (filter #(zero? (get new-in-deg % 1)) relevant)
              new-queue (into (vec (rest queue)) newly-ready)]
          (recur new-queue new-result new-in-deg))
        result))))

(defn ordered-observers
  "Get observers of a signal in topological order.

  Combines transitive observer collection with topological sorting to ensure
  glitch-free updates.

  Args:
    context - context state map (not the record, the dereferenced state)
    signal-id - Signal ID to get observers for

  Returns: Vector of spin IDs in topological order"
  [context signal-id]
  (let [node (get-in context [:nodes signal-id])
        observers (if node
                    (nodes/get-observers node)
                    #{})]
    (if (seq observers)
      (vec (topological-sort context (collect-transitive-observers context observers)))
      [])))
