(ns org.replikativ.spindel.dom.foreach
  "Delta-driven collection rendering for DOM using `KeyedFragment`.

   `(ifor-each key-fn source render-fn)` renders a collection of values
   to DOM children with per-key memoisation, returning a `KeyedFragment`
   whose `:items` are the rendered vnodes and whose `:deltas` describe
   how those items changed since the previous render.

   Strategy under the typed delta algebra
   --------------------------------------
   `:new` is authoritative — we compute the new vnode list by running
   `render-fn` over `source-new`, memoising per-key when the previous
   render produced a plain element vnode and the source item is `=`.
   Output deltas are then derived by comparing the new key/order with
   the cached previous order. We *do not* inspect upstream source
   deltas — they're advisory hints under the new model and the
   discharge layer cares only about the output deltas.

   Output delta shape
   ------------------
   A single `:seq-diff` delta carrying a SequenceAlgebra 5-field
   record:

       {:delta :seq-diff
        :diff  {:degree :grow :shrink :permutation :change :freeze}
        :prev-items <vector of previous vnodes in DOM order>}

   The discharge layer runs the diff through the algebra's pipeline
   (grow → permutation → shrink → change → freeze), reusing DOM
   elements wherever the new vnode is compatible with the prev vnode
   at the same surviving position (tag + key + addr match).

   Spin support
   ------------
   If `render-fn` returns spins instead of vnodes, the function
   returns a spin that awaits all child spins via loop/recur and then
   builds the KeyedFragment from the resolved vnodes.

   Memoisation
   -----------
   Per-key memoisation is preserved: when the source item at key `k`
   is `=` to its cached predecessor AND the cached vnode is a plain
   element (not a spin or a nested KeyedFragment), we reuse the
   cached vnode without re-running `render-fn`. The vnode's attached
   `:deltas` are cleared so the discharge tree-walk doesn't
   double-apply them.

   What was removed in the rewrite
   -------------------------------
   - Stale-delta detection (the typed algebra makes deltas sound by
     construction; nothing stale can come through).
   - Source-keys-mismatch detection (we don't trust source deltas
     anymore — we always compute `:new` from `source-new`).
   - The dual incremental/full-recompute branches; the full recompute
     was already correct, and dropping the incremental branch shrinks
     this file from ~680 to ~250 LOC."
  (:refer-clojure :exclude [await])
  (:require [org.replikativ.spindel.dom.fragment :as frag]
            [org.replikativ.spindel.dom.addressing :as addr]
            [org.replikativ.spindel.incremental.interval :as iv]
            [org.replikativ.spindel.incremental.deltaable :as d]
            [org.replikativ.spindel.incremental.sequence-algebra :as sa]
            [org.replikativ.spindel.engine.core :as ec]
            [org.replikativ.spindel.spin.cps :refer [spin]]
            [org.replikativ.spindel.effects.await :refer [await]])
  #?(:cljs (:require-macros [org.replikativ.spindel.spin.cps :refer [spin]])))

;; =============================================================================
;; VNode helpers
;; =============================================================================

(defn- vnode-value-equal?
  "Compare two vnodes by their semantic value, not object identity.
   Vnodes contain DeltaableMap/Vector instances that are fresh each
   render, so identity-based `=` would always be false. We dereference
   attrs and children and compare structurally."
  [v1 v2]
  (cond
    (and (nil? v1) (nil? v2)) true
    (or (nil? v1) (nil? v2)) false
    (and (= :text (:tag v1)) (= :text (:tag v2)))
    (= (:content v1) (:content v2))
    (and (:tag v1) (:tag v2))
    (and (= (:tag v1) (:tag v2))
         (= (:key v1) (:key v2))
         (= (if (d/deltaable? (:attrs v1)) @(:attrs v1) (:attrs v1))
            (if (d/deltaable? (:attrs v2)) @(:attrs v2) (:attrs v2)))
         (let [c1 (if (d/deltaable? (:children v1)) @(:children v1) (:children v1))
               c2 (if (d/deltaable? (:children v2)) @(:children v2) (:children v2))]
           (and (= (count c1) (count c2))
                (every? true? (map vnode-value-equal? c1 c2)))))
    :else false))

(defn- spin? [x]
  (instance? org.replikativ.spindel.spin.core.Spin x))

(defn- plain-element-vnode?
  "True iff `v` is a regular element vnode — not a spin, not a
   KeyedFragment. Only plain element vnodes are safe to memoise."
  [v]
  (and (map? v)
       (contains? v :tag)
       (not (spin? v))
       (not (frag/keyed-fragment? v))))

(defn- clear-stale-deltas
  "Strip any `:deltas` field from a vnode and its children. Required
   when reusing a memoised vnode — the discharge tree-walk would
   otherwise re-apply prior deltas and duplicate DOM children."
  [vnode]
  (when vnode
    (cond
      (and (map? vnode) (contains? vnode :content) (not (contains? vnode :tag)))
      vnode

      (and (map? vnode) (contains? vnode :tag))
      (let [cleared (dissoc vnode :deltas)
            cleared (if-let [attrs (:attrs cleared)]
                      (assoc cleared :attrs (d/clear-deltas attrs))
                      cleared)
            children (:children cleared)]
        (if children
          (let [child-vec (if (d/deltaable? children) @children children)]
            (assoc cleared :children
                   (d/deltaable-vector (mapv clear-stale-deltas child-vec))))
          cleared))

      (frag/keyed-fragment? vnode)
      ;; Preserve `:addr` — it is what lets `call-refs-on-unmount!` evict the
      ;; keyed cache at this ifor-each's call site.
      (assoc (frag/keyed-fragment (mapv clear-stale-deltas (frag/fragment-items vnode))
                                  nil)
             :addr (:addr vnode))

      :else vnode)))

;; =============================================================================
;; Cache access
;; =============================================================================

(defn- get-keyed-cache [addr]
  (ec/get-state [:dom/keyed-cache addr]))

(defn- set-keyed-cache! [addr cache-data]
  (ec/swap-state! [:dom/keyed-cache addr] (constantly cache-data)))

;; =============================================================================
;; Delta derivation — package the keyed SequenceAlgebra diff for discharge
;; =============================================================================

(defn- build-seq-diff
  "Build the discharge-layer `:seq-diff` delta for the fragment.

   The keyed-sequence diff itself is computed by the incremental layer
   (`sequence-algebra/keyed-seq-diff`) — identity is the item key, and
   per-key change is detected with structural vnode equality. This
   function only packages the resulting SequenceAlgebra diff as the
   `:seq-diff` delta the discharge tree-walk consumes, attaching
   `:prev-items` (the previous vnodes in DOM order) that `apply-seq-diff!`
   needs.

   Returns the delta in a wrapping vector, or nil when nothing changed."
  [order prev-order by-key prev-by-key]
  (when-let [diff (sa/keyed-seq-diff order prev-order by-key prev-by-key
                                     vnode-value-equal?)]
    [{:delta :seq-diff
      :diff diff
      :prev-items (mapv #(get prev-by-key %) prev-order)}]))

;; =============================================================================
;; Fragment build (sync and async paths)
;; =============================================================================

(defn- build-fragment-result
  "Build the KeyedFragment from resolved (or in-progress) items.
   was-sync? records whether the outer return type is a KeyedFragment
   (true) or a Spin (false). The next full-recompute reads it to
   decide whether per-key vnode memoisation is safe — substituting a
   cached vnode would flip the result type if the render-fn now
   returns a spin."
  [my-addr resolved-items prev-by-key prev-order was-sync?]
  (let [by-key (into {} (map (juxt :key :vnode) resolved-items))
        items-by-key (into {} (keep (fn [r]
                                      (when (contains? r :item)
                                        [(:key r) (:item r)])))
                           resolved-items)
        order (mapv :key resolved-items)
        items (mapv :vnode resolved-items)
        deltas (build-seq-diff order prev-order by-key prev-by-key)]
    (set-keyed-cache! my-addr {:by-key by-key
                               :items-by-key items-by-key
                               :order order
                               :was-sync? was-sync?})
    ;; Stamp the ifor-each call-site address onto the fragment. The keyed cache
    ;; lives at `[:dom/keyed-cache my-addr]`, and `my-addr` appears on NO vnode:
    ;; items carry `keyed-child-address(my-addr, k)`. Without this stamp
    ;; `call-refs-on-unmount!` walks the items and never learns the address that
    ;; holds `:by-key` (every rendered vnode, with its event-handler closures)
    ;; and `:items-by-key` — so unmounting a subtree containing an ifor-each
    ;; retained the whole rendered list for the lifetime of the context.
    (assoc (frag/keyed-fragment items deltas) :addr my-addr)))

;; =============================================================================
;; for-each*
;; =============================================================================

(defn for-each*
  "Render a collection with keyed addressing, returning a
   `KeyedFragment`. If `render-fn` returns spins, the function returns
   a spin that awaits all children and then builds the fragment."
  [source-loc key-fn render-fn source]
  (let [my-addr (addr/current-element-address source-loc)
        source-iv (iv/as-interval source)
        source-new (iv/get-new source-iv)
        prev-cache (get-keyed-cache my-addr)
        prev-by-key (or (:by-key prev-cache) {})
        prev-items-by-key (or (:items-by-key prev-cache) {})
        prev-order (or (:order prev-cache) [])
        prev-was-sync? (:was-sync? prev-cache false)
        ;; Render each item — memoise per-key when the prior render
        ;; was sync AND the cached vnode is a plain element AND the
        ;; source item is equal to its cached predecessor.
        items-with-keys
        (mapv (fn [item]
                (let [k (key-fn item)
                      cached-item (get prev-items-by-key k ::miss)
                      cached-vnode (get prev-by-key k)
                      memo-hit? (and prev-was-sync?
                                     (not= ::miss cached-item)
                                     (= cached-item item)
                                     (plain-element-vnode? cached-vnode))
                      vnode (if memo-hit?
                              (clear-stale-deltas cached-vnode)
                              (addr/with-keyed-context-fn my-addr k
                                #(render-fn item)))]
                  {:key k :vnode vnode :item item}))
              source-new)
        has-spins? (some #(spin? (:vnode %)) items-with-keys)]
    (if has-spins?
      ;; Async path — outer return is a Spin awaiting all per-item
      ;; child spins. When the loop finishes, re-read the keyed cache
      ;; rather than diffing against the captured prev-* — by the time
      ;; an item-flow spin completes, this loop-spin may have already
      ;; emitted a previous fragment, and that emission's cache is the
      ;; correct prev to diff against. Reading stale captures
      ;; double-emits :add deltas for already-mounted items.
      (spin
       (loop [remaining items-with-keys
              resolved []]
         (if (empty? remaining)
           (let [fresh-cache (get-keyed-cache my-addr)
                 fresh-by-key (or (:by-key fresh-cache) {})
                 fresh-order (or (:order fresh-cache) [])]
             (build-fragment-result my-addr resolved fresh-by-key fresh-order false))
           (let [{:keys [key vnode item]} (first remaining)
                 resolved-vnode (if (spin? vnode) (await vnode) vnode)]
             (recur (rest remaining)
                    (conj resolved {:key key :vnode resolved-vnode :item item}))))))
      ;; Sync path
      (build-fragment-result my-addr items-with-keys prev-by-key prev-order true))))

;; =============================================================================
;; Macro
;; =============================================================================

#?(:clj
   (defmacro ifor-each
     "Incremental for-each for DOM rendering.

      Usage:
        (ifor-each :id todos
          (fn [todo]
            (el/li {:key (:id todo)} (:text todo))))

      The render-fn may return a vnode or a spin. When it returns a
      spin, ifor-each's outer return is a spin (awaiting all child
      spins). When it returns a plain vnode, the outer return is a
      KeyedFragment.

      MEMOIZATION CONTRACT: per-key renders are memoized on ITEM
      equality (plain-element vnodes only; spin-returning render-fns
      are never memoized). If an item is `=` to its previous value, the
      cached vnode is reused and render-fn is NOT called — closure
      variables captured by render-fn (a selected id, a lookup map) are
      invisible to the diff. Anything that must trigger a re-render has
      to be part of the item itself:

        ;; WRONG — selected-id changes never re-render old items:
        (ifor-each :id items #(row % (= (:id %) selected-id)))
        ;; RIGHT — encode it in the item:
        (ifor-each :id (mapv #(assoc % :selected? (= (:id %) selected-id)) items)
          #(row % (:selected? %)))"
     [key-fn items render-fn]
     (let [source-loc {:file *file*
                       :line (:line (meta &form))
                       :column (:column (meta &form))}]
       `(for-each* ~source-loc ~key-fn ~render-fn ~items))))
