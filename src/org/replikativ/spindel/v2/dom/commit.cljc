(ns org.replikativ.spindel.v2.dom.commit
  "Commit-time reconciliation on engine v2 (phase-d design §3.3): the diff
  runs where the DOM is written, against the committed caches of the
  mount's store, and the caches advance in the same step as the DOM write.
  A build older than the committed state diffs to its residual against
  it; usually nothing.

  The walk needs each vnode's slot structure (`:slots`), because
  flattening loses the place of a nil child. Element children with equal
  addresses produce no delta: the walk recurses into them and diffs them
  against their own caches. A [:keyed :keyed] slot pair is diffed here,
  from the committed keyed entry to the fragment's items, ordered by the
  fragment's `:keys`. A subtree the walk creates (`render-initial!`) gets
  its caches seeded from its vnodes, not diffed.

  Lifecycle calls are the mount's (`v2.dom.render`): it binds
  `disch/*mount-hooks*` around the walk, and `*leave*` to hear when the
  walk leaves an element it reconciled in place."
  (:require [clojure.set]
            [org.replikativ.spindel.dom.core :as core]
            [org.replikativ.spindel.dom.fragment :as frag]
            [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.incremental.sequence-algebra :as sa]
            [org.replikativ.spindel.v2.dom.cache :as cache]
            [replikativ.logging :as log]))

(def ^:dynamic *leave*
  "Called with each element vnode the walk reconciled in place, when the
   walk leaves it (after its children), or nil."
  nil)

;; ---------------------------------------------------------------------------
;; Helpers

(defn- plain-attrs [vnode] (or (:attrs vnode) {}))

(defn vnode-slots
  "The slot vector of a vnode: its `:slots`, or its children classified
   (correct only when no slot is nil; hand-built vnodes)."
  [vnode]
  (or (:slots vnode)
      (mapv cache/make-slot (or (:children vnode) []))))

(defn- fragment-order+by-key
  "[order by-key items] of a KeyedFragment, ordered by its `:keys`."
  [fragment]
  (let [items (frag/fragment-items fragment)
        order (:keys fragment)]
    (when-not (and (vector? order) (= (count order) (count items)))
      (throw (ex-info "a KeyedFragment needs :keys, one key per item"
                      {:addr (:addr fragment) :keys order :items (count items)})))
    [order (zipmap order items) items]))

(defn- seed-keyed! [store fragment]
  (let [[order by-key items] (fragment-order+by-key fragment)]
    (when-let [fa (:addr fragment)]
      (cache/set-keyed-cache! store fa {:order order :by-key by-key}))
    items))

(defn- attr-cache-value [vnode] (dissoc (plain-attrs vnode) :key :ref))

;; ---------------------------------------------------------------------------
;; Seeding a created subtree

(defn seed-subtree-caches!
  "Writes the caches of a subtree `render-initial!` just created: its DOM is
   exactly its tree. Without this, the next walk would diff it against
   nothing and re-emit its whole mount."
  [store vnode]
  (cond
    (frag/keyed-fragment? vnode)
    (doseq [item (seed-keyed! store vnode)]
      (seed-subtree-caches! store item))

    (and (core/vnode? vnode) (not (core/text-node? vnode)))
    (let [slots (vnode-slots vnode)]
      (when-let [addr (:addr vnode)]
        (cache/set-attr-cache! store addr (attr-cache-value vnode))
        (cache/set-slot-cache! store addr slots))
      (doseq [slot slots]
        (if (= :keyed (:type slot))
          (seed-subtree-caches! store (:value slot))
          (doseq [child (cache/flatten-slot slot)]
            (seed-subtree-caches! store child)))))

    :else nil))

;; ---------------------------------------------------------------------------
;; The mounted model

(defn tree-addrs
  "Every address a committed tree claims: element addresses, fragment call
   sites (they ride `:keyed` slots) and keyed items, recursively."
  [vnode]
  (cond
    (frag/keyed-fragment? vnode)
    (transduce (map tree-addrs) into
               (if-let [a (:addr vnode)] #{a} #{})
               (frag/fragment-items vnode))

    (and (core/vnode? vnode) (not (core/text-node? vnode)))
    (transduce (comp (remove #(= :nil (:type %))) (map :value) (map tree-addrs))
               into
               (if-let [a (:addr vnode)] #{a} #{})
               (vnode-slots vnode))

    :else #{}))

(defn retire-dead!
  "After a commit: every address `prev-vdom` claimed that `new-vdom` does
   not is dead; its caches and its registry entry go. Returns the dead
   addresses."
  [discharge store prev-vdom new-vdom]
  (when prev-vdom
    (let [dead (clojure.set/difference (tree-addrs prev-vdom) (tree-addrs new-vdom))]
      (doseq [a dead]
        (cache/evict! store a)
        (disch/remove-element! discharge a))
      dead)))

;; ---------------------------------------------------------------------------
;; The walk

(declare commit-reconcile*)

;; one warning per unbound address (the condition persists across commits);
;; capped like the discharge's collision throttle
(defonce ^:private logged-unbound (atom #{}))

(defn ^:no-doc logged-unbound-count [] (count @logged-unbound))

(defn- created-value-addrs
  "The addresses of the subtrees a set of applied child deltas created (as
   opposed to reconciled in place)."
  [deltas]
  (into #{}
        (mapcat (fn [{:keys [delta value old-value]}]
                  (case delta
                    (:add :replace-fragment-with-single) (when-let [a (:addr value)] [a])
                    :update (when (and (not (disch/reconcilable? old-value value)) (:addr value))
                              [(:addr value)])
                    (:add-fragment :replace-with-fragment) (keep :addr (frag/fragment-items value))
                    nil)))
        deltas))

(defn- commit-keyed-slot!
  "Commits one [:keyed :keyed] slot: diffs the fragment's items against the
   committed keyed entry, applies, advances the entry, seeds grown items and
   recurses into surviving ones."
  [discharge store parent-el fragment]
  (let [fa (:addr fragment)
        [order by-key _] (fragment-order+by-key fragment)
        committed (when fa (cache/get-keyed-cache store fa))
        prev-order (or (:order committed) [])
        prev-by-key (or (:by-key committed) {})
        diff (sa/keyed-seq-diff order prev-order by-key prev-by-key cache/vnode-value-equal?)
        prev-keys (set prev-order)]
    (when diff
      (disch/apply-seq-diff! discharge parent-el diff (mapv prev-by-key prev-order)))
    (when fa (cache/set-keyed-cache! store fa {:order order :by-key by-key}))
    (doseq [k order :when (not (contains? prev-keys k))]
      (seed-subtree-caches! store (get by-key k)))
    (doseq [k order :when (contains? prev-keys k)]
      (commit-reconcile* discharge store (get by-key k)))))

(defn- commit-reconcile*
  [discharge store vnode]
  (when (and (core/vnode? vnode) (not (core/text-node? vnode)) (:addr vnode))
    (let [addr (:addr vnode)
          el (disch/get-element discharge addr)]
      (if-not el
        ;; a claimed address with no element: loud, not silent (a known
        ;; producer is an ::addr-collision earlier)
        (let [data {:addr addr :tag (:tag vnode) :class (:class (plain-attrs vnode))}]
          (disch/record-violation! ::commit-unbound-addr data)
          (when (disch/first-log? logged-unbound addr)
            (log/warn ::commit-unbound-addr (assoc data :children (count (:children vnode))))))
        (let [new-attrs (attr-cache-value vnode)
              attr-deltas (cache/reconcile-attrs (cache/get-attr-cache store addr) new-attrs)
              new-slots (vnode-slots vnode)
              prev-slots (cache/get-slot-cache store addr)
              {:keys [slots deltas]} (cache/reconcile-children prev-slots (mapv :value new-slots))
              keyed-pairs (into [] (keep-indexed
                                    (fn [i slot]
                                      (when (and (= :keyed (:type slot))
                                                 (= :keyed (:type (get prev-slots i))))
                                        (:value slot))))
                                slots)
              created (created-value-addrs deltas)]
          ;; 1. attrs
          (doseq [{:keys [delta path value]} attr-deltas]
            (case delta
              (:add :update) (disch/set-attribute! discharge el (first path) value)
              :remove (disch/remove-attribute! discharge el (first path))))
          (cache/set-attr-cache! store addr new-attrs)
          ;; 2. structural child deltas
          (doseq [d (cache/adjust-delta-paths slots deltas)]
            (disch/apply-child-delta! discharge el d))
          (cache/set-slot-cache! store addr slots)
          ;; 3. subtrees created in step 2 get seeded caches
          (doseq [{:keys [delta value]} deltas]
            (case delta
              (:add :replace-fragment-with-single :update)
              (when (contains? created (:addr value)) (seed-subtree-caches! store value))
              (:add-fragment :replace-with-fragment) (seed-subtree-caches! store value)
              nil))
          ;; 4. keyed pairs: our own diff, and recursion into surviving items
          (doseq [fragment keyed-pairs]
            (commit-keyed-slot! discharge store el fragment))
          ;; 5. recursion into children reconciled in place
          (doseq [slot slots
                  :when (= :single (:type slot))
                  :let [child (:value slot)]
                  :when (and (core/vnode? child) (not (core/text-node? child)) (:addr child)
                             (not (contains? created (:addr child))))]
            (commit-reconcile* discharge store child))
          (when *leave* (*leave* vnode)))))
    nil))

(defn commit-reconcile!
  "Diffs `vnode` against the committed caches in `store`, applies the
   difference through `discharge` and advances the caches. Precondition:
   the element of `(:addr vnode)` exists (an initial mount goes through
   `render-initial!` and `seed-subtree-caches!`)."
  [discharge store vnode]
  (commit-reconcile* discharge store vnode))

(defn commit-update!
  "One update commit: reconcile the arrived tree `new-vdom` against the
   committed caches, then retire the addresses `prev-vdom` (the last
   committed tree) held that `new-vdom` does not. Returns the dead
   addresses."
  [discharge store prev-vdom new-vdom]
  (commit-reconcile* discharge store new-vdom)
  (retire-dead! discharge store prev-vdom new-vdom))
