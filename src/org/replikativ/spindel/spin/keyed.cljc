(ns org.replikativ.spindel.spin.keyed
  "A keyed parallel: one child spin per key, results in key order.

    (await (keyed :points (range n) (fn [i] (point-spin … i))))

  Each child is created under `(with-key k)`, so its spin id is a function
  of the key (stable across re-runs of the enclosing body and across
  worlds). A child runs later than it is created (`parallel` starts it), so
  a scope around its creation would not reach its sites: name them with the
  key, `(sample d :id [name k :o])`.

  Incrementally it behaves as `parallel` does: when one child re-completes
  (its tracked signals changed, or it was re-run in a fork of its world),
  only that key's slot is patched and the keyed spin re-completes; no other
  child runs and the body does not run again. A re-run of the body (the
  enclosing spin re-evaluated it with a changed environment) re-registers
  every child, and the B-gate re-runs only those whose captured environment
  changed.

  The children are kept in world state (`children`), keyed, so a caller can
  re-run one key's spin on its own; they fork with the world."
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.engine.addressing :as addressing]
            [org.replikativ.spindel.engine.impl.simple :as simple]
            [org.replikativ.spindel.engine.protocols :as rtp]
            [org.replikativ.spindel.spin.core :as spin-core]
            [org.replikativ.spindel.spin.combinators :refer [parallel]]
            [org.replikativ.spindel.effects.await :refer [await]]
            #?(:clj [org.replikativ.spindel.spin.cps :refer [spin]]))
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]])))

(defn- children-path [keyed-id] [:keyed keyed-id :children])

(defn children
  "{key child-spin} of the keyed spin `keyed-id` in the current world, as its
  last body run created them."
  [keyed-id]
  (ec/get-state (children-path keyed-id)))

(defn spin-of
  "The child spin with id `spin-id` of any keyed spin in `world`, or nil."
  [world spin-id]
  (rtp/get-state world [:keyed/spins spin-id]))

(defn keyed
  "A spin resolving to `[(f k) …]` for the keys `ks`, in their order. `name`
  tells keyed spins of one body apart. `f` returns a spin (or any value
  `await` accepts) for a key."
  [name ks f]
  (addressing/with-key [::keyed name]
    (spin
     (let [ks (vec ks)
           kids (mapv (fn [k]
                        (addressing/with-key k (f k)))
                      ks)]
       (let [ids (into #{} (map spin-core/spin-id) kids)
             dropped (remove ids (map spin-core/spin-id (vals (children ec/*spin-id*))))]
         ;; Reclamation releases registry entries by structural ID, including
         ;; when another container holds a different handle for the same spin.
         (ec/swap-state! [:keyed ec/*spin-id*]
                         (constantly {:children (zipmap ks kids) :spin-ids ids}))
         ;; the registry holds the children of the last run only: a key that
         ;; dropped out is released with its spin
         (ec/swap-state! [:keyed/spins]
                         (fn [m] (as-> (or m {}) m
                                   (apply dissoc m dropped)
                                   (into m (map (fn [kid] [(spin-core/spin-id kid) kid])) kids)))))
       (if (seq kids)
         (await (apply parallel kids))
         [])))))

(defn rerun!
  "Run `child` (one key's spin, from `children`) again in the current world,
  and only it: its node is invalidated and its body executed. When it
  re-completes, the keyed spin patches that key's slot and re-completes;
  what awaits it resumes as for any re-completion. In a fork this leaves
  the source world untouched. Returns a CPS operation resolving the
  child's new value."
  [child]
  (fn [resolve reject]
    (let [world (ec/current-execution-context)
          id (spin-core/spin-id child)]
      (ec/swap-state! [:nodes id] simple/invalidate-node)
      (ec/enqueue-event! {:type :spin-execution :id id :spin child
                          :execution-context world
                          :resolve-fn resolve :reject-fn reject}))))
