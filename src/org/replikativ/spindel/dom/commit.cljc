(ns org.replikativ.spindel.dom.commit
  "Commit-time reconciliation — the diff runs where the DOM is written.

   Why this namespace exists. Under compute-time reconciliation
   (`build-element` diffing against the committed caches and attaching
   `:deltas` to the vnode) there is an unclosable window: when a body slice
   re-executes N times before the first render pass commits — measured live:
   six builds of one container during a single settled expand, driven by the
   parent's `:await-reactive` cont re-firing per child re-completion — all N
   builds diff against the SAME baseline, each carries the same `:add`, and
   more than one distinct vnode object can reach the DOM in separate passes.
   Every dedup guard is keyed on something (object identity, address, pass)
   that some legitimate case must be allowed to pass. Worse, the staging that
   R3 introduced is last-write-wins per address, so the committed baseline can
   advance PAST what the DOM holds (silent lost updates), or aside of it.

   The correction is structural, not another guard: compute the diff AT the
   commit point, against the committed caches, and advance those caches in
   the same step as the DOM write. A stale build arriving later then diffs
   against the already-advanced baseline and collapses to its genuine
   residual — usually nothing, and when it does carry a fresh change (the
   last staggered update in a burst), exactly that change.

   This is option D/E of `.internal/effect-state-design.md`, anticipated by
   `repeat_execution_test.clj`'s unit property: \"against an ADVANCED
   baseline, the second execution is a no-op\".

   What this walk needs from a build that compute-time reconciliation did
   not: the vnode must carry its SLOT STRUCTURE (`:slots` — the classified
   `{:type :value}` vector), because `flatten-slots` destroys the `:nil`-slot
   information the reconciler needs for stable slot indices. And the diff
   must run against the ARRIVED TREE — never against staging, whose
   last-write-wins-per-address semantics are exactly the desync this
   namespace exists to remove.

   Reuses the existing machinery relocated: `cache/reconcile-attrs`,
   `cache/reconcile-children`, `sa/keyed-seq-diff` compute; `discharge`'s
   `apply-child-delta!` / `apply-seq-diff!` / `render-initial!` apply.

   Two behaviours differ deliberately from the compute-time path:

   1. Addr-equal children produce NO delta (reconcile-slot's [:single
      :single] unchanged case) — under compute-time semantics \"the child
      handles its own deltas via discharge-vnode!\"; here there are no child
      deltas, so the walk RECURSES into addr-equal children and diffs them
      against their own per-address caches.

   2. [:keyed :keyed] slot pairs are not answered from fragment build-time
      deltas (there are none); the walk computes `keyed-seq-diff` itself,
      from the committed keyed cache to the fragment's items.

   Fresh subtrees (created here via `render-initial!` inside an applied
   `:add`/`:update`/fragment delta) get their caches SEEDED from their
   vnodes, not diffed — diffing a just-created subtree against its nil cache
   would re-emit its whole mount."
  (:require [org.replikativ.spindel.dom.core :as core]
            [org.replikativ.spindel.dom.cache :as cache]
            [org.replikativ.spindel.dom.fragment :as frag]
            [org.replikativ.spindel.dom.discharge :as disch]
            [org.replikativ.spindel.dom.foreach :as foreach]
            [org.replikativ.spindel.incremental.sequence-algebra :as sa]
            [org.replikativ.spindel.incremental.deltaable :as d]
            [org.replikativ.spindel.engine.core :as ec]
            [replikativ.logging :as log]))

;; =============================================================================
;; Helpers
;; =============================================================================

(defn- plain-attrs [vnode]
  (let [a (:attrs vnode)]
    (cond (nil? a) {}
          (d/deltaable? a) @a
          :else a)))

(defn- plain-children [vnode]
  (let [c (:children vnode)]
    (cond (nil? c) []
          (d/deltaable? c) @c
          :else c)))

(defn vnode-slots
  "The slot-entry vector for a vnode in the commit walk.

   Prefers the `:slots` the build attached (pre-flatten, `:nil` slots
   preserved). Falls back to classifying the flattened children — correct
   only when no conditional slot is currently nil, which is why builds must
   carry `:slots`; the fallback keeps hand-constructed test vnodes and
   legacy paths walkable."
  [vnode]
  (or (:slots vnode)
      (mapv cache/make-slot (plain-children vnode))))

(defn- fragment-order+by-key
  "[order by-key items] for a KeyedFragment's current items."
  [fragment]
  (let [items (frag/fragment-items fragment)
        order (mapv :key items)]
    [order (zipmap order items) items]))

(defn- fragment-cache-value
  "The committed keyed-cache entry for a fragment: vnodes by key + order,
   plus `:items-by-key`/`:was-sync?` carried FROM the fragment (for-each*
   attaches them) — they are what the per-key memoisation reads on the
   next build. Absent on hand-built fragments -> memo simply misses."
  [fragment order by-key]
  {:by-key by-key
   :items-by-key (or (:items-by-key fragment) {})
   :order order
   :was-sync? (boolean (:was-sync? fragment))})

;; =============================================================================
;; Cache seeding for fresh subtrees
;; =============================================================================

(defn seed-subtree-caches!
  "Write the per-address caches for a subtree that was just CREATED by
   `render-initial!` — attrs, slots, and keyed caches derived from the
   vnodes themselves. The subtree's DOM is exactly its tree, so its caches
   must say so; without this, the next commit walk diffs the subtree
   against nil and re-emits its whole mount (the very bug this namespace
   removes, reintroduced one level down)."
  [vnode]
  (cond
    (frag/keyed-fragment? vnode)
    (let [[order by-key items] (fragment-order+by-key vnode)]
      (when-let [fa (:addr vnode)]
        (cache/set-keyed-cache! fa (fragment-cache-value vnode order by-key)))
      (doseq [item items] (seed-subtree-caches! item)))

    (and (core/vnode? vnode) (not (core/text-node? vnode)))
    (let [addr (:addr vnode)
          slots (vnode-slots vnode)]
      (when addr
        (cache/set-attr-cache! addr (dissoc (plain-attrs vnode) :key :ref))
        (cache/set-slot-cache! addr slots))
      (doseq [slot slots
              child (cache/flatten-slot slot)]
        (seed-subtree-caches! child))
      ;; a :keyed slot's fragment addr also needs its keyed cache
      (doseq [slot slots
              :when (= :keyed (:type slot))
              :let [v (:value slot)]
              :when (frag/keyed-fragment? v)]
        (let [[order by-key _] (fragment-order+by-key v)]
          (when-let [fa (:addr v)]
            (cache/set-keyed-cache! fa (fragment-cache-value v order by-key))))))

    :else nil))

;; =============================================================================
;; The commit walk
;; =============================================================================

(declare commit-reconcile!)
(declare commit-reconcile*)

;; One warn per unbound address per process — the condition persists across
;; passes (the stranded subtree is recommitted on every parent re-emission),
;; so unthrottled it floods the console: measured 89 identical lines for one
;; defect. Same policy as discharge's logged-collisions.
(defonce ^:private logged-unbound (atom #{}))

(defn- created-value-addrs
  "Addresses of subtrees a set of just-applied child deltas CREATED (as
   opposed to reconciled in place). These get seeded caches and are excluded
   from the diff recursion."
  [deltas]
  (into #{}
        (mapcat (fn [{:keys [delta value old-value]}]
                  (case delta
                    (:add :replace-fragment-with-single)
                    (when-let [a (:addr value)] [a])
                    ;; :update creates fresh only when NOT reconcilable —
                    ;; mirror apply-child-delta!'s own decision
                    :update
                    (when (and (not (disch/reconcilable? old-value value))
                               (:addr value))
                      [(:addr value)])
                    (:add-fragment :replace-with-fragment)
                    (keep :addr (frag/fragment-items value))
                    nil)))
        deltas))

(defn- commit-keyed-slot!
  "Commit one [:keyed :keyed] slot: diff the fragment's items against the
   COMMITTED keyed cache, apply, advance the cache, and return the item
   addresses that were newly created (grown keys) so the caller can seed
   them. Items surviving by key are recursed into by the caller."
  [discharge parent-el fragment]
  (let [fa (:addr fragment)
        [order by-key items] (fragment-order+by-key fragment)
        committed (when fa (cache/get-keyed-cache fa))
        prev-order (or (:order committed) [])
        prev-by-key (or (:by-key committed) {})
        diff (sa/keyed-seq-diff order prev-order by-key prev-by-key
                                foreach/vnode-value-equal?)
        prev-items (mapv #(get prev-by-key %) prev-order)
        grown-keys (remove (set prev-order) order)]
    (when diff
      (disch/apply-seq-diff! discharge parent-el diff prev-items))
    ;; advance the keyed baseline in the same step as the DOM write
    (when fa
      (cache/set-keyed-cache! fa (fragment-cache-value fragment order by-key)))
    ;; grown keys were created by apply-seq-diff!'s render-initial!
    (doseq [k grown-keys]
      (seed-subtree-caches! (get by-key k)))
    ;; surviving items may have changed internally OR been replaced by the
    ;; diff's :change (render-initial! for incompatible ones is handled by
    ;; apply-seq-diff! itself; compatible ones were reconciled). Recurse to
    ;; bring their attrs/slots current against their own caches.
    (doseq [k (filter (set prev-order) order)]
      (commit-reconcile* discharge (get by-key k)))
    nil))

(defn commit-reconcile!
  "Diff `vnode` against the committed per-address caches, apply the
   difference through `discharge`, and advance the caches — one step.

   Precondition: an element for `(:addr vnode)` exists in the discharge
   (the initial mount goes through `render-initial!` + `seed-subtree-caches!`,
   not through here). Safe to call repeatedly with stale builds: a build
   older than the committed baseline diffs to its residual against the
   CURRENT state, which is exactly what should be applied.

   Returns nil."
  [discharge vnode]
  (commit-reconcile* discharge vnode))

(defn- commit-reconcile*
  [discharge vnode]
  (when (and (core/vnode? vnode)
             (not (core/text-node? vnode))
             (:addr vnode))
    (let [addr (:addr vnode)
          el (disch/get-element discharge addr)]
      (if-not el
        ;; No element for a claimed-committed address: loud, not silent —
        ;; this is the commit-walk analogue of ::deltas-dropped-unbound-addr.
        ;; Known producer: an ::addr-collision earlier (two vnodes, one addr —
        ;; e.g. an unkeyed component instantiated per scope); the collision
        ;; winner's unmount strands the loser here, frozen.
        (when-not (contains? @logged-unbound addr)
          (swap! logged-unbound conj addr)
          (log/warn ::commit-unbound-addr {:addr addr :tag (:tag vnode)
                                           :class (:class (plain-attrs vnode))
                                           :children (count (plain-children vnode))}))
        (let [;; --- attrs: committed -> arrived ---
              new-attrs (dissoc (plain-attrs vnode) :key :ref)
              prev-attrs (cache/get-attr-cache addr)
              attr-deltas (cache/reconcile-attrs prev-attrs new-attrs)
              ;; --- slots: committed -> arrived ---
              new-slots (vnode-slots vnode)
              prev-slots (cache/get-slot-cache addr)
              new-children (mapv :value new-slots)
              {:keys [slots deltas]} (cache/reconcile-children prev-slots new-children)
              ;; [:keyed :keyed] pairs are OURS to diff (behaviour 2 in the
              ;; ns docstring); reconcile-slot's :fragment-update reads
              ;; build-time fragment deltas that no longer exist. Drop any
              ;; it produced and remember the pairs for commit-keyed-slot!.
              keyed-pairs (into []
                                (keep-indexed
                                 (fn [i slot]
                                   (when (and (= :keyed (:type slot))
                                              (= :keyed (:type (get prev-slots i)))
                                              (frag/keyed-fragment? (:value slot)))
                                     (:value slot))))
                                slots)
              structural-deltas (into [] (remove #(= :fragment-update (:delta %))) deltas)
              adjusted (when (seq structural-deltas)
                         (cache/adjust-delta-paths slots structural-deltas))]
          ;; 1. attrs
          (doseq [{:keys [delta path value]} attr-deltas]
            (let [k (first path)]
              (case delta
                (:add :update) (disch/set-attribute! discharge el k value)
                :remove (disch/remove-attribute! discharge el k)
                nil)))
          (cache/set-attr-cache! addr new-attrs)
          ;; 2. structural child deltas (type transitions, adds, removes)
          (doseq [dlt adjusted]
            (disch/apply-child-delta! discharge el dlt))
          (cache/set-slot-cache! addr slots)
          ;; 3. fresh subtrees created in step 2 get seeded caches
          (doseq [a (created-value-addrs structural-deltas)
                  :let [child (some #(when (= a (:addr %)) %)
                                    (map :value structural-deltas))]]
            (when child (seed-subtree-caches! child)))
          ;; fragments made visible in step 2 seed their keyed caches too
          (doseq [{:keys [delta value]} structural-deltas
                  :when (#{:add-fragment :replace-with-fragment} delta)
                  :when (frag/keyed-fragment? value)]
            (let [[order by-key _] (fragment-order+by-key value)]
              (when-let [fa (:addr value)]
                (cache/set-keyed-cache! fa (fragment-cache-value value order by-key))))
            (doseq [item (frag/fragment-items value)]
              (seed-subtree-caches! item)))
          ;; 4. keyed-keyed slots: our own diff + recursion into survivors
          (doseq [fragment keyed-pairs]
            (commit-keyed-slot! discharge el fragment))
          ;; 5. recurse into addr-equal children (behaviour 1 in the ns
          ;; docstring). Freshly created subtrees were seeded above, so
          ;; recursing into them diffs to nothing — the recursion is uniform.
          (let [created (created-value-addrs structural-deltas)]
            (doseq [slot slots
                    :when (= :single (:type slot))
                    :let [child (:value slot)]
                    :when (and (core/vnode? child)
                               (not (core/text-node? child))
                               (:addr child)
                               (not (contains? created (:addr child))))]
              (commit-reconcile* discharge child))))))
    nil))
