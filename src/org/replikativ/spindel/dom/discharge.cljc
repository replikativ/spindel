(ns org.replikativ.spindel.dom.discharge
  "Effect discharge protocol for applying vdom deltas to external targets.

  This namespace defines the protocol for discharging vdom changes to
  real targets (DOM, string for SSR, test mock, etc.).

  **Two delta surfaces:**

  The discharge layer accepts two delta vocabularies that flow through
  the same `apply-child-delta!` dispatcher:

  *Legacy slot-reconciliation deltas* (kept for backwards-compat with
  call sites that haven't migrated):

  - `:add`     — Add child at path
  - `:remove`  — Remove child at path
  - `:update`  — Update (in-place reconcile or destroy+create) at path
  - `:move`    — Move child from one position to another
  - `:add-fragment` / `:remove-fragment` — Fragment becoming visible / invisible
  - `:replace-with-fragment` / `:replace-fragment-with-single`
  - `:fragment-update` / `:replace-all` — Bulk updates / fallback

  *Typed sequence-algebra diffs* (preferred; algebra-native):

  - `:seq-diff` carrying a 5-field map
    `{:degree :grow :shrink :permutation :change :freeze}`
    consumed by `apply-seq-diff!` via the standard incseq pipeline:
    grow → permutation → shrink → change → freeze.

  The typed shape is what producers (foreach, the new combinators)
  emit going forward.

  **Attribute deltas** still come from `DeltaableMap` on attrs:
  `:add`, `:update`, `:remove`.

  Implementations:
  - DOMDischarge (browser.cljs)  — real browser DOM
  - StringDischarge (string.cljc) — HTML string for SSR
  - MockDischarge (this file)    — operation log for tests"
  (:require [org.replikativ.spindel.dom.core :as core]
            [org.replikativ.spindel.dom.cache :as cache]
            [org.replikativ.spindel.dom.fragment :as frag]
            [org.replikativ.spindel.incremental.deltaable :as d]
            [org.replikativ.spindel.incremental.permutation :as perm]
            [replikativ.logging :as log])
  #?(:clj (:import [java.util Collections IdentityHashMap])))

;; =============================================================================
;; Discharge Protocol
;; =============================================================================

(defprotocol PDischarge
  "Protocol for discharging vdom changes to an external target."

  (create-element! [this vnode]
    "Create a new element from vnode. Returns target-specific element reference.")

  (create-text! [this text-content]
    "Create a new text node. Returns target-specific reference.")

  (set-attribute! [this el attr-name attr-value]
    "Set an attribute on element.")

  (remove-attribute! [this el attr-name]
    "Remove an attribute from element.")

  (append-child! [this parent child]
    "Append child element to parent.")

  (insert-child! [this parent child index]
    "Insert child element at index in parent.")

  (remove-child! [this parent index]
    "Remove child at index from parent.")

  (replace-child! [this parent new-child index]
    "Replace child at index with new-child.")

  (move-child! [this parent from-idx to-idx]
    "Move child from one index to another within parent.
     Efficiently repositions DOM node without remove+add.")

  (child-index-of [this parent child]
    "Return the position of `child` in `parent`'s child list, or nil
     when `child` is not a direct child. Used by apply-seq-diff! to
     compute fragment offsets within a parent that also carries
     sibling elements.")

  (set-text-content! [this el text]
    "Set text content of a text node.")

  (get-element [this addr]
    "Get the target element by address keyword (from element map).")

  (set-element! [this addr el]
    "Store element reference by address keyword.")

  (remove-element! [this addr]
    "Drop the element reference for an address keyword. Called when an
     address is unmounted, so the discharge's addr→element registry does
     not retain detached DOM nodes for the lifetime of the tree.")

  (remove-children-range! [this parent start-idx count]
    "Remove multiple children starting at index. Default: call remove-child! in loop.")

  (insert-children! [this parent children start-idx]
    "Insert multiple children starting at index. Default: call insert-child! in loop."))

;; =============================================================================
;; Default implementations for batch operations
;; =============================================================================

(defn default-remove-children-range!
  "Default implementation: remove children one by one from end to start."
  [discharge parent start-idx n]
  ;; Remove from end to preserve indices
  (doseq [i (reverse (range start-idx (+ start-idx n)))]
    (remove-child! discharge parent i)))

(defn default-insert-children!
  "Default implementation: insert children one by one."
  [discharge parent children start-idx]
  (doseq [[offset child] (map-indexed vector children)]
    (insert-child! discharge parent child (+ start-idx offset))))

;; =============================================================================
;; Forward declarations
;; =============================================================================

(declare render-initial!)
(declare call-ref!)
(declare call-refs-on-unmount!)

;; Track addresses claimed during the current render pass. If two different
;; vnodes try to claim the same :addr we have an addressing collision —
;; classic symptom is `(for [x xs] (vnode-fn x))` instead of `ifor-each`,
;; where siblings share source-loc + parent-addr + slot-index. The collision
;; silently corrupts the DOM (later child deltas resolve to whichever vnode
;; won set-element! last), so we error loudly when it happens.
(def ^:dynamic *rendered-addrs* nil)

(defn- vnode-fingerprint
  "Return a small, log-friendly summary of a vnode to help locate collisions."
  [vnode]
  (let [attrs (when-let [a (:attrs vnode)]
                (if (d/deltaable? a) @a a))
        children (when-let [c (:children vnode)]
                   (if (d/deltaable? c) @c c))
        text-content (some (fn [c]
                             (when (and (map? c) (= :text (:tag c)))
                               (:content c)))
                           children)]
    (cond-> {:tag (:tag vnode) :key (:key vnode)}
      (:class attrs)        (assoc :class (:class attrs))
      (:id attrs)           (assoc :id (:id attrs))
      (:data-type attrs)    (assoc :data-type (:data-type attrs))
      text-content          (assoc :text (subs text-content 0 (min 60 (count text-content)))))))

(defonce ^:private logged-collisions (atom #{}))

(defonce ^:private logged-unbound (atom #{}))

(defn register-addr!
  "Register an address as claimed during this render pass.
  Logs an error the first time we see a given collision address (across the
  process lifetime); thereafter the same colliding address is silent so the
  console isn't flooded by per-render repeats."
  [vnode]
  (when (and *rendered-addrs* (:addr vnode))
    (let [addr (:addr vnode)
          seen (get @*rendered-addrs* addr)]
      (if seen
        (when (and (not (identical? seen vnode))
                   (not (contains? @logged-collisions addr)))
          (swap! logged-collisions conj addr)
          (log/error ::addr-collision
                     {:addr addr
                      :prior (vnode-fingerprint seen)
                      :new (vnode-fingerprint vnode)
                      :hint "Two vnodes claim the same :addr in one render pass. Use ifor-each for cardinality-variable lists, or split the call site so each sibling has a distinct source-loc. (Logged once per process — see logged-collisions atom.)"}))
        (swap! *rendered-addrs* assoc addr vnode)))))

;; Addresses whose per-element caches are slated for eviction because a
;; vnode at that address was unmounted this render pass. Eviction is
;; *deferred* to end-of-cycle: an unmount runs before the live subtree is
;; render-initial!'d, so an address can sit in both a destroyed subtree and
;; a live one within one pass (a churned parent whose keyed descendants
;; survive). `flush-pending-evictions!` drops only the addresses absent
;; from `*rendered-addrs*` once the pass is complete.
(def ^:dynamic *pending-evictions* nil)

(defn flush-pending-evictions!
  "Evict the per-element caches of addresses unmounted this render pass
  that no live element claimed. Call once, after the full discharge walk,
  inside the `*pending-evictions*` / `*rendered-addrs*` binding.

  Eager eviction on unmount is unsafe: unmount runs before the live
  subtree is render-initial!'d, so it would wipe the cache of an address
  that a still-live element (a surviving keyed descendant of a churned
  parent) re-claims later in the same pass. By end-of-pass `*rendered-addrs*`
  holds every live address, so (pending - live) is exactly the dead set.

  When a `discharge` is supplied we also drop its addr→element registry entry
  for each dead address (`remove-element!`) — otherwise the registry retains
  the detached DOM node for the lifetime of the tree (it is only ever fully
  cleared by `unmount!`). The 0-arity form keeps the cache-only behavior for
  callers (e.g. focused unit tests) that have no discharge in hand."
  ([] (flush-pending-evictions! nil))
  ([discharge]
   (when (and *pending-evictions* *rendered-addrs*)
     ;; `*rendered-addrs*` holds only addresses that appear ON a vnode, and an
     ;; `ifor-each` call site appears on none — `flatten-slot` splices the
     ;; fragment's items into `:children` and drops the fragment. So a fragment
     ;; could never be found live here, and was exempt from this whole check:
     ;; a dead parent's stale `:keyed` slot cascaded into the cache of a
     ;; fragment the LIVE parent was still rendering, and the next render
     ;; diffed against an empty baseline and re-added every item. Close over
     ;; the committed slots the same way `commit-pending!` does for staging.
     (let [live (cache/live-keyed-closure (keys @*rendered-addrs*))]
       (doseq [addr @*pending-evictions*]
         (when-not (contains? live addr)
           (cache/evict-cache! addr live)
           (when discharge (remove-element! discharge addr))))))))

;; =============================================================================
;; Attribute Delta Application
;; =============================================================================

(defn apply-attr-delta!
  "Apply a single attribute delta to an element."
  [discharge el delta]
  (let [{:keys [delta path value]} delta
        attr-name (first path)]
    (case delta
      :add (set-attribute! discharge el attr-name value)
      :update (set-attribute! discharge el attr-name value)
      :remove (remove-attribute! discharge el attr-name)
      nil)))

;; =============================================================================
;; Key-aware reconciliation
;;
;; When an `:update` child delta arrives, the old DOM element can be reused
;; in place if old-vnode and new-vnode are *compatible* — same `:tag`,
;; `:key`, and `:addr`. We then update only the attributes that actually
;; differ (computed as a diff between old-attrs and new-attrs) and DO NOT
;; re-fire the `:ref` callback. The DOM element identity is preserved, so
;; anything that hooked into `:ref` on mount (rich-text editors, IME state,
;; focus, video players, …) survives across re-renders.
;;
;; Without it, every per-render closure capture in `:on-mount` /
;; `:on-unmount` (whose identity differs on every render) bubbles up as a
;; vnode-value inequality, triggers a `:update` delta from
;; `dom/foreach.cljc/compute-fine-grained-deltas`, and tears down the DOM
;; element. With it, the reused element is just attribute-diffed and the
;; ref callback is left alone.
;;
;; Children reconciliation is intentionally minimal: when both old and new
;; children are non-empty, we delegate to the existing
;; `apply-child-delta!` machinery via the new vnode's own `:children`
;; DeltaableVector deltas (if any). Pure leaf vnodes (foreign-node, text-
;; only nodes) skip this entirely. Recursive deep reconciliation of
;; regular-element children is a follow-up.
;; =============================================================================

(defn reconcilable?
  "True if old-vnode and new-vnode can be reconciled into the same DOM
   element — same shape, same address, same key, same tag.

   Text vnodes are explicitly excluded: they share `{:tag :text}` with
   no `:addr` and no `:key`, so two text nodes with different
   `:content` would trivially satisfy tag/key/addr equality and route
   through `reconcile-vnode!`, where `(get-element discharge nil)`
   returns nil and the update silently no-ops. Forcing text nodes to
   the destroy+create fallback ensures text-content updates actually
   reach the DOM."
  [old-vnode new-vnode]
  (and (core/vnode? old-vnode)
       (core/vnode? new-vnode)
       (not (core/text-node? old-vnode))
       (not (core/text-node? new-vnode))
       (= (:tag old-vnode) (:tag new-vnode))
       (= (:key old-vnode) (:key new-vnode))
       (= (:addr old-vnode) (:addr new-vnode))))

(defn- vnode-attrs [vnode]
  (let [a (:attrs vnode)]
    (cond
      (nil? a) {}
      (d/deltaable? a) @a
      :else a)))

(defn- reconcile-attrs!
  "Apply attribute diff between old-vnode and new-vnode to the existing
   `el`. Only attributes that changed are set; attributes that were
   removed are explicitly removed."
  [discharge el old-vnode new-vnode]
  (let [old-attrs (dissoc (vnode-attrs old-vnode) :key :ref)
        new-attrs (dissoc (vnode-attrs new-vnode) :key :ref)]
    ;; Set attributes that are new or changed.
    (doseq [[k v] new-attrs]
      (when (not= v (get old-attrs k))
        (set-attribute! discharge el k v)))
    ;; Remove attributes that were on the old vnode but not on the new.
    (doseq [k (keys old-attrs)]
      (when-not (contains? new-attrs k)
        (remove-attribute! discharge el k)))))


(declare reconcile-vnode!)

;; =============================================================================
;; SequenceAlgebra-native delta application
;;
;; Producers may emit a single typed `:seq-diff` delta carrying the
;; algebra's five-field record:
;;
;;     {:degree :grow :shrink :permutation :change :freeze}
;;
;; `apply-seq-diff!` realises this onto DOM children. It honours the
;; algebra's application semantics (grow → permutation → shrink →
;; change → freeze) but merges them into a single forward walk over
;; the new positions:
;;
;;  1. Remove the prev elements whose `π(i) ≥ size-after` (doomed by
;;     the impending shrink). Tail-to-head so DOM indices stay stable.
;;
;;  2. Walk new-positions k = 0..size-after-1 in order. For each:
;;     - If the source inverse-permutes to a prev-position < size-before
;;       AND that prev-position survives: move the existing DOM element
;;       there. If `:change[k]` is present *and* compatible with the
;;       prev vnode, reconcile in place; if incompatible, destroy +
;;       render-initial + replace.
;;     - Otherwise the source is a grown slot: render `:change[k]` and
;;       insert at k.
;;
;;  3. `:freeze` is metadata — no DOM op (consumers may use the set
;;     for downstream optimisation; the discharge layer itself does
;;     not).
;;
;; The pos tracking maintains a {prev-i → current-DOM-index} map that
;; gets updated after each move/insert; this is O(n) per op, O(n²)
;; in total for the worst case (full reverse permutation), which is
;; fine for the lists spindel typically renders. A future
;; optimisation can replace the linear-update with an indexed
;; structure if profiling demands it.
;; =============================================================================

(declare reconcilable?)

(defn- doomed-prev?
  "Prev-position i is doomed iff π(i) ≥ size-after."
  [permutation i size-after]
  (>= (perm/apply-perm permutation i) size-after))

(defn- shift-positions!
  "Update tracker map for a single DOM operation that moves an element from
   `from-pos` to `to-pos`. Elements between them shift in the opposite
   direction."
  [tracker from-pos to-pos]
  (cond
    (< from-pos to-pos)
    (doseq [[i p] @tracker
            :when (and (> p from-pos) (<= p to-pos))]
      (swap! tracker assoc i (dec p)))

    (> from-pos to-pos)
    (doseq [[i p] @tracker
            :when (and (>= p to-pos) (< p from-pos))]
      (swap! tracker assoc i (inc p)))))

(defn- shift-positions-on-insert!
  "Update tracker map after inserting a new element at position `at-pos`.
   All existing elements at positions >= at-pos shift right by 1."
  [tracker at-pos]
  (doseq [[i p] @tracker
          :when (>= p at-pos)]
    (swap! tracker assoc i (inc p))))

(defn- shift-positions-on-remove!
  "Update tracker map after removing the element at position `at-pos`. All
   remaining elements at positions > at-pos shift left by 1."
  [tracker at-pos]
  (doseq [[i p] @tracker
          :when (> p at-pos)]
    (swap! tracker assoc i (dec p))))

(defn- fragment-offset
  "Compute the index in `parent-el`'s child list at which this
   fragment's children start. Derived from the first prev-vnode's
   DOM element via `child-index-of` — that element's position IS
   the fragment's start.

   Returns 0 when there's no first prev-vnode (the fragment is
   empty), or when the discharge can't answer `child-index-of`
   (mock, SSR). Both fall back to the legacy assumption that the
   fragment occupies the whole parent — which is correct when the
   fragment IS the whole parent."
  [discharge parent-el prev-vnodes]
  (or (when-let [first-vnode (first prev-vnodes)]
        (when-let [first-el (get-element discharge (:addr first-vnode))]
          (child-index-of discharge parent-el first-el)))
      0))

(defn apply-seq-diff!
  "Apply a SequenceAlgebra diff to the DOM children of `parent-el`.

   `prev-vnodes` is the ordered vector of vnodes that produced the
   current DOM children — the discharge layer doesn't know them
   otherwise, so the producer (or the caller of this function) must
   pass them in. `prev-vnodes`'s length must equal `degree - grow`
   (the size-before).

   Diff fields (all optional except `:degree`):
     :degree      Long — size after grow, before shrink
     :grow        Long — slots added at the tail
     :shrink      Long — slots removed from the tail
     :permutation sparse map {i j} of position moves
     :change      map of post-shrink position → new vnode
     :freeze      set of post-shrink positions (metadata only)

   Fragment offset
   ---------------
   The diff's positions are relative to the fragment's children. When
   the fragment is rendered alongside sibling elements (a heading
   above, a footer below), the fragment's index 0 is at
   parent.childNodes[OFFSET] — not at index 0 of the parent. The
   offset is derived once at entry from the first prev-vnode's DOM
   element position, and added to every index op so the diff lands
   on the fragment's rows, not on siblings.

   Returns nil. Mutates the DOM under `parent-el` and the
   discharge's element registry (`set-element!`)."
  [discharge parent-el
   {:keys [degree grow shrink permutation change]
    :or {grow 0 shrink 0 permutation {} change {}}}
   prev-vnodes]
  (let [size-before (- degree grow)
        size-after  (- degree shrink)
        inv-π       (perm/inverse permutation)
        ;; Offset of this fragment's first child in parent.childNodes.
        ;; Defaults to 0 when there's no first prev-vnode (initial
        ;; render of an empty fragment — the producer's pure-grow diff
        ;; assumes index 0) or when the discharge has no DOM model
        ;; (mock/SSR — they don't track offsets the same way).
        offset      (fragment-offset discharge parent-el prev-vnodes)
        ;; Compute doomed prev-positions (those permuted past size-after).
        doomed (into #{} (filter #(doomed-prev? permutation % size-after))
                     (range size-before))
        ;; Tracker: prev-position → current DOM index *after* the doomed
        ;; positions have been removed. Removing tail-to-head leaves each
        ;; survivor at (original-i - count of doomed indices < i), so
        ;; pre-compute that here in one pass. Indices are FRAGMENT-RELATIVE;
        ;; `offset` is added at every protocol call site.
        tracker (atom (loop [i 0 removed 0 acc {}]
                        (if (= i size-before)
                          acc
                          (if (doomed i)
                            (recur (inc i) (inc removed) acc)
                            (recur (inc i) removed (assoc acc i (- i removed)))))))]
    ;; (1) Remove doomed prev elements, tail-to-head.
    (doseq [i (sort > doomed)]
      (call-refs-on-unmount! (nth prev-vnodes i))
      (remove-child! discharge parent-el (+ offset i)))
    ;; (2) Walk new-positions in order.
    (doseq [k (range size-after)]
      (let [src (perm/apply-perm inv-π k)
            new-vnode (get change k)]
        (cond
          ;; Grown source — must be in :change.
          (>= src size-before)
          (when new-vnode
            (let [new-el (render-initial! discharge new-vnode)]
              (when new-el
                (insert-child! discharge parent-el new-el (+ offset k))
                (shift-positions-on-insert! tracker k))))

          ;; Prev source, survives.
          (not (doomed src))
          (let [current (get @tracker src)
                old-vnode (nth prev-vnodes src)]
            ;; Move into position if needed.
            (when (not= current k)
              (move-child! discharge parent-el (+ offset current) (+ offset k))
              (shift-positions! tracker current k)
              (swap! tracker assoc src k))
            ;; Apply :change at this position if present.
            (when new-vnode
              (if (reconcilable? old-vnode new-vnode)
                (when-let [el (get-element discharge (:addr new-vnode))]
                  (reconcile-vnode! discharge el old-vnode new-vnode)
                  (set-element! discharge (:addr new-vnode) el))
                (do
                  (call-refs-on-unmount! old-vnode)
                  (when-let [new-el (render-initial! discharge new-vnode)]
                    (replace-child! discharge parent-el new-el (+ offset k)))))))

          ;; Source is doomed — this position must be a grown slot or
          ;; the diff is malformed. Skip silently; producer error
          ;; would surface in tests.
          :else nil)))))

(defn- reconcile-vnode!
  "Reconcile new-vnode into the DOM element backing old-vnode. Does NOT
   call `:ref`. Preserves DOM identity. Caller must have verified
   `(reconcilable? old-vnode new-vnode)`.

   Two sources of changes are propagated to the reused element:

   Only the attribute diff between old-vnode and new-vnode, computed by
   `reconcile-attrs!`. Child-level changes are NOT applied here — under
   commit-time reconciliation (dom/commit) the walk recurses into
   addr-equal children and diffs them against their own per-address
   caches; builds attach no deltas of their own."
  [discharge el old-vnode new-vnode]
  (reconcile-attrs! discharge el old-vnode new-vnode))

;; =============================================================================
;; Child Delta Application (New Delta-Direct System)
;; =============================================================================

(defn apply-child-delta!
  "Apply a single child delta from slot reconciliation."
  [discharge el delta]
  (case (:delta delta)
    ;; Simple add: render and insert. The caller (the commit walk) seeds
    ;; the created subtree's caches afterwards — see dom/commit.
    :add
    (let [{:keys [path value]} delta
          index (first path)
          child-el (render-initial! discharge value)]
      (when child-el
        (insert-child! discharge el child-el index)))

    ;; Simple remove
    :remove
    (let [{:keys [path old-value]} delta
          index (first path)]
      ;; Call ref callbacks with nil before removing
      (call-refs-on-unmount! old-value)
      (remove-child! discharge el index))

    ;; Update: in-place reconciliation when old and new are compatible
    ;; (same tag, key, addr). Otherwise fall back to destroy+create.
    ;;
    ;; In-place reconciliation preserves DOM identity, which is what makes
    ;; rich-text editors / focus / IME state survive across re-renders
    ;; whose only "change" is a fresh `:on-mount` / `:on-unmount` closure
    ;; capture on the vnode.
    :update
    (let [{:keys [path value old-value]} delta
          index (first path)]
      (if (reconcilable? old-value value)
        (when-let [child-el (get-element discharge (:addr value))]
          (reconcile-vnode! discharge child-el old-value value)
          ;; Refresh the address → element mapping so any subsequent
          ;; lookups by addr return the same (reused) element.
          (set-element! discharge (:addr value) child-el))
        ;; Incompatible — fall back to the old destroy-and-recreate path.
        (do
          (call-refs-on-unmount! old-value)
          (let [child-el (render-initial! discharge value)]
            (when child-el
              (replace-child! discharge el child-el index))))))

    ;; Fragment becoming visible: render and insert all items
    :add-fragment
    (let [{:keys [path value]} delta
          start-idx (first path)
          items (if (frag/keyed-fragment? value)
                  (frag/fragment-items value)
                  value)]
      (doseq [[offset item] (map-indexed vector items)]
        (let [child-el (render-initial! discharge item)]
          (when child-el
            (insert-child! discharge el child-el (+ start-idx offset))))))

    ;; Fragment becoming nil: remove all items
    :remove-fragment
    (let [{:keys [path old-value]} delta
          start-idx (first path)
          items (if (frag/keyed-fragment? old-value)
                  (frag/fragment-items old-value)
                  old-value)
          n (count items)]
      ;; Call ref callbacks with nil before removing
      (doseq [item items]
        (call-refs-on-unmount! item))
      ;; Remove from end to preserve indices
      (doseq [i (reverse (range start-idx (+ start-idx n)))]
        (remove-child! discharge el i)))

    ;; Single → Fragment: remove single, add all items
    :replace-with-fragment
    (let [{:keys [path value old-value]} delta
          index (first path)
          items (if (frag/keyed-fragment? value)
                  (frag/fragment-items value)
                  value)]
      ;; Call ref callback with nil on old element before removing
      (call-refs-on-unmount! old-value)
      ;; Remove the single element first
      (remove-child! discharge el index)
      ;; Insert all fragment items
      (doseq [[offset item] (map-indexed vector items)]
        (let [child-el (render-initial! discharge item)]
          (when child-el
            (insert-child! discharge el child-el (+ index offset))))))

    ;; Fragment → Single: remove all items, insert single
    :replace-fragment-with-single
    (let [{:keys [path old-value value]} delta
          index (first path)
          old-items (if (frag/keyed-fragment? old-value)
                      (frag/fragment-items old-value)
                      old-value)
          n (count old-items)]
      ;; Call ref callbacks with nil before removing
      (doseq [item old-items]
        (call-refs-on-unmount! item))
      ;; Remove all fragment items from end
      (doseq [i (reverse (range index (+ index n)))]
        (remove-child! discharge el i))
      ;; Insert the single element
      (let [child-el (render-initial! discharge value)]
        (when child-el
          (insert-child! discharge el child-el index))))

    ;; Fragment internal update: apply adjusted deltas
    :fragment-update
    (let [{:keys [adjusted-deltas deltas]} delta
          ;; Use adjusted-deltas if available (have absolute indices)
          ;; Otherwise fall back to deltas
          internal-deltas (or adjusted-deltas deltas)]
      (doseq [d internal-deltas]
        (apply-child-delta! discharge el d)))

    ;; Full replacement fallback
    :replace-all
    (let [{:keys [path old-items items]} delta
          start-idx (or (first path) 0)
          old-count (count old-items)]
      ;; Call ref callbacks with nil before removing
      (doseq [item old-items]
        (call-refs-on-unmount! item))
      ;; Remove all old items from end
      (doseq [i (reverse (range start-idx (+ start-idx old-count)))]
        (remove-child! discharge el i))
      ;; Insert all new items
      (doseq [[offset item] (map-indexed vector items)]
        (let [child-el (render-initial! discharge item)]
          (when child-el
            (insert-child! discharge el child-el (+ start-idx offset))))))

    ;; Move child within collection (reordering)
    :move
    (let [from-idx (first (:from-path delta))
          to-idx (first (:to-path delta))]
      (move-child! discharge el from-idx to-idx))

    ;; Typed sequence-algebra diff: the producer emits a single
    ;; `:seq-diff` carrying the 5-field record. Discharge applies it
    ;; via the algebra's pipeline (grow → permutation → shrink →
    ;; change → freeze) with in-place reuse where keys/addrs match.
    ;;
    ;; The producer must also include `:prev-items` — the ordered
    ;; vector of vnodes the diff is relative to — because discharge
    ;; doesn't otherwise track per-slot vnode identities.
    :seq-diff
    (let [{:keys [diff prev-items]} delta]
      (apply-seq-diff! discharge el diff prev-items))

    ;; Unknown delta type - ignore
    nil))


;; =============================================================================
;; Ref Callback Helpers
;; =============================================================================

(defn- call-ref!
  "Call ref callback safely if present.

  Args:
    vnode - The vnode that may have a :ref function
    el - The DOM element (or nil for unmount)"
  [vnode el]
  (when-let [ref-fn (:ref vnode)]
    (try
      (ref-fn el)
      (catch #?(:clj Exception :cljs :default) e
        (log/error ::ref-callback-error {:tag (:tag vnode)
                                         :el el
                                         :error (str e)})))))

(defn ^:no-doc call-refs-on-unmount!
  "Recursively call ref callbacks with nil for a vnode and its descendants,
  and schedule their per-element caches for eviction. The eviction itself
  is deferred to end-of-cycle (see `*pending-evictions*` /
  `flush-pending-evictions!`) so it cannot wipe a cache that an address
  still-live elsewhere in the same render pass re-claims. Outside a render
  pass (no binding) eviction falls back to eager, as before."
  [vnode]
  (when vnode
    (cond
      (core/text-node? vnode)
      nil  ; Text nodes have no :addr and no refs

      (frag/keyed-fragment? vnode)
      (do
        ;; The fragment's own address (the `ifor-each` call site) holds the
        ;; keyed cache — `:by-key` (every rendered vnode + its handler closures)
        ;; and `:items-by-key`. That address appears on no item vnode, so it
        ;; must be scheduled explicitly or the whole rendered list leaks for the
        ;; lifetime of the context. `for-each*` stamps it via `:addr`.
        (when-let [addr (:addr vnode)]
          (if *pending-evictions*
            (swap! *pending-evictions* conj addr)
            (cache/evict-cache! addr)))
        (doseq [item (frag/fragment-items vnode)]
          (call-refs-on-unmount! item)))

      (core/vnode? vnode)
      (do
        (call-ref! vnode nil)
        (if *pending-evictions*
          (when-let [addr (:addr vnode)]
            (swap! *pending-evictions* conj addr))
          (cache/evict-cache! (:addr vnode)))
        (when-let [children (:children vnode)]
          (let [child-vec (if (d/deltaable? children) @children children)]
            (doseq [child child-vec]
              (call-refs-on-unmount! child)))))

      :else nil)))

;; =============================================================================
;; Initial Render (create all elements)
;; =============================================================================

(defn render-initial!
  "Render entire vdom tree to target for initial mount.

  Creates all elements and stores references."
  [discharge vnode]
  (cond
    (nil? vnode)
    nil

    (core/text-node? vnode)
    (let [el (create-text! discharge (:content vnode))]
      ;; Text nodes don't have :addr — skip storing ref since they're
      ;; always replaced wholesale and never looked up by address
      el)

    (core/fragment? vnode)
    ;; Fragments don't create an element, just render children
    (let [children (when-let [ch (:children vnode)]
                     (if (d/deltaable? ch) @ch ch))]
      (mapv #(render-initial! discharge %) children))

    (frag/keyed-fragment? vnode)
    ;; KeyedFragment: render all items
    (do
      (mapv #(render-initial! discharge %) (frag/fragment-items vnode)))

    (core/vnode? vnode)
    (let [el (create-element! discharge vnode)
          children (when-let [ch (:children vnode)]
                     (if (d/deltaable? ch) @ch ch))]
      ;; Store element reference by stable address
      (set-element! discharge (:addr vnode) el)
      ;; Detect duplicate :addr claims (e.g., siblings from `for` instead of ifor-each)
      (register-addr! vnode)

      ;; Set all attributes (defer :value until after children for <select>)
      (let [raw-attrs (when-let [attrs (:attrs vnode)]
                        (if (d/deltaable? attrs) @attrs attrs))
            deferred-value (get raw-attrs :value)]
        (doseq [[k v] raw-attrs]
          (when (not= k :value)
            (set-attribute! discharge el k v)))

        ;; Render and append children
        (doseq [child children]
          (let [child-el (render-initial! discharge child)]
            (when child-el
              (if (vector? child-el)
                ;; Fragment or KeyedFragment children
                (doseq [c child-el]
                  (append-child! discharge el c))
                (append-child! discharge el child-el)))))

        ;; Set :value after children are in DOM (required for <select>)
        (when deferred-value
          (set-attribute! discharge el :value deferred-value)))

      ;; Call ref callback with element after fully rendered
      (call-ref! vnode el)

      el)

    :else
    nil))

;; =============================================================================
;; Mock Discharge (for testing)
;; =============================================================================

(defrecord MockDischarge [log elements]
  PDischarge

  (create-element! [_ vnode]
    (let [id (gensym "el-")]
      (swap! log conj {:op :create-element :tag (:tag vnode) :id id})
      id))

  (create-text! [_ text]
    (let [id (gensym "text-")]
      (swap! log conj {:op :create-text :text text :id id})
      id))

  (set-attribute! [_ el attr-name attr-value]
    (swap! log conj {:op :set-attr :el el :attr attr-name :value attr-value}))

  (remove-attribute! [_ el attr-name]
    (swap! log conj {:op :remove-attr :el el :attr attr-name}))

  (append-child! [_ parent child]
    (swap! log conj {:op :append-child :parent parent :child child}))

  (insert-child! [_ parent child index]
    (swap! log conj {:op :insert-child :parent parent :child child :index index}))

  (remove-child! [_ parent index]
    (swap! log conj {:op :remove-child :parent parent :index index}))

  (replace-child! [_ parent new-child index]
    (swap! log conj {:op :replace-child :parent parent :child new-child :index index}))

  (move-child! [_ parent from-idx to-idx]
    (swap! log conj {:op :move-child :parent parent :from from-idx :to to-idx}))

  (child-index-of [_ _parent _child]
    ;; The mock discharge has no DOM, so it can't answer this. Callers
    ;; that pass MockDischarge through `apply-seq-diff!` must invoke
    ;; it with an explicit offset (see apply-seq-diff!'s `:offset`
    ;; param) — returning nil here makes the offset default to 0,
    ;; matching the legacy assumption that the fragment occupies the
    ;; whole parent.
    nil)

  (set-text-content! [_ el text]
    (swap! log conj {:op :set-text :el el :text text}))

  (get-element [_ addr]
    (get @elements addr))

  (set-element! [_ addr el]
    (swap! elements assoc addr el))

  (remove-element! [_ addr]
    (swap! elements dissoc addr))

  (remove-children-range! [this parent start-idx n]
    (default-remove-children-range! this parent start-idx n))

  (insert-children! [this parent children start-idx]
    (default-insert-children! this parent children start-idx)))

(defn make-mock-discharge
  "Create a mock discharge for testing.

  Returns {:discharge MockDischarge :log atom :elements atom}"
  []
  (let [log (atom [])
        elements (atom {})]
    {:discharge (->MockDischarge log elements)
     :log log
     :elements elements}))
